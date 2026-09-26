#!/usr/bin/env python3
"""lawcheck: property-test every law in a LAWS.bend, before proving it.

Each `law name:` becomes a bendcheck property. Its `for` parameters are
drawn at random; hypotheses (`for h: {L == R : T}`) become preconditions;
the claim `{L == R : T}` is checked with T's equality. A Nat used as a
width (`Word(n)`) is fixed at a few sizes. A hypothesis of the form
`{X == Nat.add(Y, v) : Nat}` or `{1n+Nat.add(E, v) == P : Nat}` solves for
v instead of waiting for random luck.

Usage: lawcheck.py LAWS.bend [--count N] [--seed S] [--widths 1,2,3,8,16]
                             [--only law1,law2] [--keep]
Exit status: 1 if any law has a counterexample.
"""
import argparse, itertools, os, re, shutil, subprocess, sys, tempfile

BEND = os.environ.get("BEND", os.path.expanduser("~/.bend/bin/bend"))
ENV = {**os.environ, "BEND_NO_TELEMETRY": "1"}
CHECK = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "check.bend")


class Unsupported(Exception):
    pass


# Parsing
# -------

def parse(path):
    lines = open(path).read().split("\n")
    imports = [l for l in lines if l.startswith("import ")]
    laws, i = [], 0
    while i < len(lines):
        m = re.match(r"^law\s+([\w.]+)\s*:\s*$", lines[i])
        i += 1
        if not m:
            continue
        body = []
        while i < len(lines) and (lines[i].startswith((" ", "\t")) or not lines[i].strip()):
            if lines[i].strip() and not lines[i].strip().startswith("#"):
                body.append(lines[i].strip())
            i += 1
        laws.append((m.group(1), body))
    return imports, laws


def top_split(s, sep):
    """Split s at top-level occurrences of sep (outside (), [], {})."""
    out, depth, start, j = [], 0, 0, 0
    while j < len(s):
        ch = s[j]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and s.startswith(sep, j):
            out.append(s[start:j])
            j += len(sep)
            start = j
            continue
        j += 1
    out.append(s[start:])
    return out


def equation(s):
    """{L == R : T} -> (L, R, T, negated)"""
    s = s.strip()
    if not (s.startswith("{") and s.endswith("}")):
        raise Unsupported(f"claim is not an equation: {s[:60]}")
    inner = s[1:-1]
    parts = top_split(inner, " : ")
    if len(parts) < 2:
        raise Unsupported("equation without a type")
    body, typ = " : ".join(parts[:-1]), parts[-1].strip()
    for op, neg in ((" == ", False), (" != ", True)):
        sides = top_split(body, op)
        if len(sides) == 2:
            return sides[0].strip(), sides[1].strip(), typ, neg
    raise Unsupported(f"no top-level == in {s[:60]}")


def call(s, fn):
    """fn(a, b, ..) -> [a, b, ..], else None."""
    s = s.strip()
    if not (s.startswith(fn + "(") and s.endswith(")")):
        return None
    args = top_split(s[len(fn) + 1:-1], ",")
    # the prefix must close exactly at the end
    depth = 0
    for j, ch in enumerate(s[len(fn):]):
        depth += ch in "([{"
        depth -= ch in ")]}"
        if depth == 0 and j < len(s) - len(fn) - 1:
            return None
    return [a.strip() for a in args]


def mentions(expr, name):
    return re.search(r"(?<![\w.])" + re.escape(name) + r"(?![\w])", expr) is not None


def subst(text, env):
    for name, val in env.items():
        text = re.sub(r"(?<![\w.])" + re.escape(name) + r"(?![\w])", val, text)
    return text


# Types
# -----

def eq_expr(typ, l, r):
    t = typ.strip()
    if t == "U32":
        return f"U32.is_eq({l}, {r})"
    if t == "Nat":
        return f"Nat.is_eq({l}, {r})"
    if t == "Bool":
        return f"Cmp.is_eq(Bool.cmp({l}, {r}))"
    if t == "Cmp":
        return f"lc_cmp_eq({l}, {r})"
    m = re.fullmatch(r"Word\((.+)\)", t)
    if m:
        return f"Cmp.is_eq(Word.cmp({m.group(1)}, {l}, {r}))"
    raise Unsupported(f"no equality for type {t}")


def kit(typ):
    """(type, generator, shrinker, printer): the last two are closed
    function terms, usable as template arguments"""
    t = typ.strip()
    if t == "U32":
        return t, "BC.Gen.u32()", "BC.Shrink.u32", "U32.show"
    if t == "Nat":
        return t, "BC.Gen.nat()", "BC.Shrink.nat", "Nat.show"
    if t == "Bool":
        return t, "BC.Gen.bool()", "BC.Shrink.bool", "Bool.show"
    m = re.fullmatch(r"Word\((\d+n)\)", t)
    if m:
        k = m.group(1)
        return t, f"BC.Gen.word({k})", f"(lc_w => BC.Shrink.word({k}, lc_w))", f"(lc_w => BC.Show.word({k}, lc_w))"
    raise Unsupported(f"no generator for type {t}")


def combine(kits):
    """right-nested pairs of kits"""
    if len(kits) == 1:
        return kits[0]
    t1, g1, s1, w1 = kits[0]
    t2, g2, s2, w2 = combine(kits[1:])
    d = len(kits)
    return (f"BC.Both<{t1}, {t2}>",
            f"BC.Gen.pair(~{t1}, ~{t2}, ~{g1}, ~{g2})",
            f"(lc_p{d} => BC.Shrink.pair(~{t1}, ~{t2}, ~{s1}, ~{s2}, lc_p{d}))",
            f"(lc_p{d} => BC.Show.pair(~{t1}, ~{t2}, ~{w1}, ~{w2}, lc_p{d}))")


def app(f, arg):
    """apply a closed function term to arg, inlining a lambda"""
    m = re.fullmatch(r"\((\w+) => (.*)\)", f, re.S)
    if m:
        return re.sub(r"(?<![\w.])" + m.group(1) + r"(?![\w])", arg, m.group(2))
    return f"{f}({arg})"


# One law, one width assignment -> one property
# ---------------------------------------------

def law_params(body):
    params, claim = [], []
    for b in body:
        if b.startswith("for "):
            m = re.match(r"for\s+([+-]?)(\w+)\s*:\s*(.*)$", b)
            if not m:
                raise Unsupported(f"cannot read: {b}")
            if " where " in m.group(3):
                raise Unsupported("`where` parameters")
            params.append((m.group(2), m.group(3).strip()))
        elif b.startswith("exs "):
            raise Unsupported("existential (exs)")
        else:
            claim.append(b)
    return params, " ".join(claim)


def width_names(params):
    ws = set()
    for name, typ in params:
        for m in re.finditer(r"Word\((\w+)\)", typ):
            ws.add(m.group(1))
    return [n for n, t in params if n in ws and t == "Nat"]


def assignments(ws, widths):
    if not ws:
        return [{}]
    if len(ws) == 1:
        return [{ws[0]: f"{w}n"} for w in widths]
    combos = [tuple([w] * len(ws)) for w in widths]
    combos += [tuple(widths[(i + k) % len(widths)] for k in range(len(ws))) for i in range(len(widths))]
    seen, out = set(), []
    for c in combos:
        if c not in seen:
            seen.add(c)
            out.append({n: f"{w}n" for n, w in zip(ws, c)})
    return out


def solve(hyps, free):
    """Witnesses for Nat parameters fixed by a hypothesis: {v: expr}."""
    sol = {}
    for l, r, t, neg in hyps:
        if t.strip() != "Nat" or neg:
            continue
        for x, y in ((l, r), (r, l)):
            args = call(y, "Nat.add")
            if args and len(args) == 2 and args[1] in free and args[1] not in sol and not mentions(x, args[1]) \
                    and not mentions(args[0], args[1]):
                sol[args[1]] = f"Nat.sub({x}, {args[0]})"
            m = re.fullmatch(r"1n\+(.*)", x.strip())
            args = call(m.group(1), "Nat.add") if m else None
            if args and len(args) == 2 and args[1] in free and args[1] not in sol and not mentions(y, args[1]) \
                    and not mentions(args[0], args[1]):
                sol[args[1]] = f"Nat.sub(Nat.sub({y}, 1n), {args[0]})"
    return sol


def build(idx, name, params, claim, env):
    params = [(n, subst(t, env)) for n, t in params if n not in env]
    claim = subst(claim, env)
    hyps, vals = [], []
    for n, t in params:
        if t.startswith("{"):
            hyps.append(equation(t))
        else:
            vals.append((n, t))
    sol = solve(hyps, {n for n, t in vals if t == "Nat"})
    drawn = [(n, t) for n, t in vals if n not in sol]
    if not drawn:
        raise Unsupported("nothing to draw")
    l, r, t, neg = equation(claim)
    goal = eq_expr(t, l, r)
    if neg:
        goal = f"Bool.not({goal})"
    pre = [f"Bool.not({eq_expr(ht, hl, hr)})" if hn else eq_expr(ht, hl, hr) for hl, hr, ht, hn in hyps]
    kits = [kit(t) for n, t in drawn]
    T, gen, shr, shw = combine(kits)

    # unpack the nested input into the law's own names
    # (Bend wants every match before the first let)
    lines, lets, cur = [], [], "inp"
    for i, (n, t) in enumerate(drawn):
        if i == len(drawn) - 1:
            lets.append(f"  +{n} = {cur}")
        else:
            lines.append(f"  BC.Both{{{n}_0, rest{i}}} = {cur}")
            lets.append(f"  +{n} = {n}_0")
            cur = f"rest{i}"
    lines += lets
    for v, e in sol.items():
        lines.append(f"  +{v} = {e}")
    cond = "".join(f"Bool.and({p}, " for p in pre) + "True{}" + ")" * len(pre)
    verdict = f"BC.Check.when({cond}, {goal})" if pre else f"BC.Check.holds({goal})"
    label = name + (" [" + ", ".join(f"{k}={v[:-1]}" for k, v in env.items()) + "]" if env else "")
    body = "\n".join(lines)
    src = f"""
# {label}
def lc_gen_{idx}() -> BC.Gen({T}):
  {gen}

def lc_shrink_{idx}(x: {T}) -> +List<{T}>:
  {app(shr, "x")}

def lc_show_{idx}(x: {T}) -> String:
  {app(shw, "x")}

def lc_prop_{idx}(inp: {T}) -> BC.Verdict:
{body}
  {verdict}
"""
    run = f'BC.Check.prop(~{T}, ~lc_gen_{idx}(), ~lc_prop_{idx}, ~lc_shrink_{idx}, ~lc_show_{idx}, "{label}", COUNT, SEED)'
    return label, src, run


CMP_EQ = """
def lc_cmp_eq(a: Cmp, b: Cmp) -> Bool:
  match a b:
    case LT{} LT{}:
      True{}
    case EQ{} EQ{}:
      True{}
    case GT{} GT{}:
      True{}
    case _ _:
      False{}
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("laws")
    ap.add_argument("--count", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--widths", default="1,2,3,8,16")
    ap.add_argument("--only", default="")
    ap.add_argument("--keep", action="store_true", help="keep the generated .bend file")
    a = ap.parse_args()
    widths = [int(w) for w in a.widths.split(",")]
    only = set(filter(None, a.only.split(",")))
    path = os.path.abspath(a.laws)
    root = os.path.dirname(path)
    imports, laws = parse(path)

    defs, runs, skipped = [], [], []
    for name, body in laws:
        if only and name not in only:
            continue
        try:
            params, claim = law_params(body)
            for env in assignments(width_names(params), widths):
                label, src, run = build(len(runs), name, params, claim, env)
                defs.append(src)
                runs.append((label, run))
        except Unsupported as e:
            skipped.append((name, str(e)))

    rel = os.path.relpath(CHECK, root)
    rel = rel if rel.startswith(".") else "./" + rel
    body = "\n".join(f"    r{i} : Bool <- {run.replace('COUNT', f'{a.count}n').replace('SEED', str(a.seed))}"
                     for i, (label, run) in enumerate(runs))
    src = "# generated by lawcheck: do not edit\n\n" + "\n".join(
        [l for l in imports if " as BC" not in l] + [f"import {rel} as BC"]) + "\n" + CMP_EQ + "".join(defs) + \
        f"\ndef main() -> IO(Unit):\n  do IO<Unit>:\n{body}\n    IO.print(\"lawcheck: done\")\n"
    gen_path = os.path.join(root, "lawcheck_run.bend")
    open(gen_path, "w").write(src)
    tmp = tempfile.mkdtemp()
    try:
        r = subprocess.run([BEND, gen_path, "-o", os.path.join(tmp, "lc")], capture_output=True, text=True, env=ENV)
        if r.returncode != 0:
            print(r.stdout[-3000:] + r.stderr[-3000:])
            print(f"lawcheck: the generated tests do not build (kept at {gen_path})")
            return 2
        out = subprocess.run([os.path.join(tmp, "lc")], capture_output=True, text=True).stdout
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
        if not a.keep and os.path.exists(gen_path):
            os.remove(gen_path)

    print(out, end="")
    failed = out.count("  FAILED  ")
    gave_up = out.count("  GAVE UP ")
    passed = out.count("  ok      ")
    for name, why in skipped:
        print(f"  n/a     {name}: {why}")
    print(f"lawcheck: {passed} passed, {failed} failed, {gave_up} gave up (precondition rarely held), "
          f"{len(skipped)} not testable")
    return 1 if failed else 0


sys.exit(main())
