#!/usr/bin/env python3
"""lawcheck: property-test every law in a LAWS.bend, before proving it.

Each `law name:` becomes a bendcheck property. Its `for` parameters are
drawn at random; hypotheses (`for h: {L == R : T}`) become preconditions;
the claim `{L == R : T}` is checked with T's equality. Type parameters are
fixed: a quantity (`for -a: Quant`) to &2 and an element type
(`for -A: Kind(a)`, `Type` or `Data`) to --elem. A Nat used as a width
(`Word(n)`) is tried at a few sizes. A hypothesis `{X == Nat.add(Y, v) : Nat}`
or `{1n+Nat.add(E, v) == P : Nat}` is solved for v instead of waiting for
random luck.

Types: U32, Nat, Bool, Cmp, Word(n), lists (List<q, T>, +List<T>) and
Maybe<q, T> of those.

Usage: lawcheck.py LAWS.bend [--count N] [--seed S] [--widths 1,2,3,8,16]
                             [--elem U32] [--only law1,law2] [--keep]
Exit status: 1 if any law has a counterexample.
"""
import argparse, os, re, shutil, subprocess, sys, tempfile

BEND = os.environ.get("BEND", os.path.expanduser("~/.bend/bin/bend"))
ENV = {**os.environ, "BEND_NO_TELEMETRY": "1"}
CHECK = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "check.bend")


class Unsupported(Exception):
    pass


# Reading laws
# ------------

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
    """Split s at top-level occurrences of sep (outside (), [], {}, and the
    <> of a type application like List<a, A>)."""
    out, depth, start, j = [], 0, 0, 0
    while j < len(s):
        ch = s[j]
        if ch in "([{" or (ch == "<" and j > 0 and (s[j - 1].isalnum() or s[j - 1] == "_")):
            depth += 1
        elif ch in ")]}" or (ch == ">" and depth > 0 and s[j - 1] not in "=-"):
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
    parts = top_split(s[1:-1], " : ")
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
    depth = 0
    for j, ch in enumerate(s[len(fn):]):
        depth += ch in "([{"
        depth -= ch in ")]}"
        if depth == 0 and j < len(s) - len(fn) - 1:
            return None
    return [a.strip() for a in top_split(s[len(fn) + 1:-1], ",")]


def ident(name):
    return r"(?<![\w.])" + re.escape(name) + r"(?![\w])"


def mentions(expr, name):
    return re.search(ident(name), expr) is not None


def subst(text, env):
    for name, val in env.items():
        text = re.sub(ident(name), lambda m: val, text)
    return text


# Types
# -----

def shape(t):
    """('list', q, T) | ('maybe', q, T) | ('base', t)"""
    t = t.strip()
    m = re.fullmatch(r"\+(List|Maybe)<(.+)>", t)
    if m:
        return (m.group(1).lower(), "&2", m.group(2).strip())
    m = re.fullmatch(r"(List|Maybe)<\s*(&[12])\s*,\s*(.+)>", t)
    if m:
        return (m.group(1).lower(), m.group(2), m.group(3).strip())
    m = re.fullmatch(r"(List|Maybe)<(.+)>", t)
    if m:
        return (m.group(1).lower(), "&1", m.group(2).strip())
    return ("base", t)


class Ctx:
    """Collects the helper defs a generated file needs."""

    def __init__(self):
        self.helpers, self.n = {}, 0

    def fresh(self, base):
        self.n += 1
        return f"{base}{self.n}"

    def helper(self, key, make):
        if key not in self.helpers:
            name = f"lc_h{len(self.helpers)}"
            self.helpers[key] = (name, None)
            self.helpers[key] = (name, make(name))
        return self.helpers[key][0]

    def data(self, t):
        """the reusable (Data) form of t"""
        s = shape(t)
        if s[0] == "list":
            return f"List<&2, {self.data(s[2])}>"
        if s[0] == "maybe":
            return f"Maybe<&2, {self.data(s[2])}>"
        return s[1]

    def eq(self, t, l, r):
        s = shape(t)
        if s[0] == "base":
            b = s[1]
            if b == "U32":
                return f"U32.is_eq({l}, {r})"
            if b == "Nat":
                return f"Nat.is_eq({l}, {r})"
            if b == "Bool":
                return f"Cmp.is_eq(Bool.cmp({l}, {r}))"
            if b == "Cmp":
                return f"lc_cmp_eq({l}, {r})"
            m = re.fullmatch(r"Word\((.+)\)", b)
            if m:
                return f"Cmp.is_eq(Word.cmp({m.group(1)}, {l}, {r}))"
            raise Unsupported(f"no equality for type {b}")
        kind, q, inner = s
        T = f"{'List' if kind == 'list' else 'Maybe'}<{q}, {inner}>"
        if kind == "list":
            name = self.helper("eq " + T, lambda nm: f"""
def {nm}(xs: {T}, ys: {T}) -> Bool:
  match xs ys:
    case Nil{{}} Nil{{}}:
      True{{}}
    case Nil{{}} Con{{y, yt}}:
      False{{}}
    case Con{{x, xt}} Nil{{}}:
      False{{}}
    case Con{{x, xt}} Con{{y, yt}}:
      Bool.and({self.eq(inner, 'x', 'y')}, {nm}(xt, yt))
""")
        else:
            name = self.helper("eq " + T, lambda nm: f"""
def {nm}(xs: {T}, ys: {T}) -> Bool:
  match xs ys:
    case None{{}} None{{}}:
      True{{}}
    case None{{}} Some{{y}}:
      False{{}}
    case Some{{x}} None{{}}:
      False{{}}
    case Some{{x}} Some{{y}}:
      {self.eq(inner, 'x', 'y')}
""")
        return f"{name}({l}, {r})"

    def kit(self, t):
        """(Data type, generator, shrinker, printer); the last two are closed
        function terms, usable as template arguments"""
        s = shape(t)
        if s[0] == "list":
            if s[1] == "&1" and shape(s[2])[0] != "base":
                raise Unsupported(f"affine list of structured elements: {t}")
            d, g, sh, w = self.kit(s[2])
            v = self.fresh("lc_l")
            return (f"List<&2, {d}>", f"BC.Gen.list(~{d}, ~{g})",
                    f"({v} => BC.Shrink.list(~{d}, ~{sh}, {v}))", f"({v} => BC.Show.list(~{d}, ~{w}, {v}))")
        if s[0] == "maybe":
            if s[1] == "&1":
                raise Unsupported(f"affine Maybe: {t}")
            d, g, sh, w = self.kit(s[2])
            v = self.fresh("lc_m")
            return (f"Maybe<&2, {d}>", f"BC.Gen.maybe(~{d}, ~{g})",
                    f"({v} => BC.Shrink.maybe(~{d}, ~{sh}, {v}))", f"({v} => BC.Show.maybe(~{d}, ~{w}, {v}))")
        b = s[1]
        if b == "U32":
            return b, "BC.Gen.u32()", "BC.Shrink.u32", "U32.show"
        if b == "Nat":
            return b, "BC.Gen.nat()", "BC.Shrink.nat", "Nat.show"
        if b == "Bool":
            return b, "BC.Gen.bool()", "BC.Shrink.bool", "Bool.show"
        m = re.fullmatch(r"Word\((\d+n)\)", b)
        if m:
            k, v = m.group(1), self.fresh("lc_w")
            return b, f"BC.Gen.word({k})", f"({v} => BC.Shrink.word({k}, {v}))", f"({v} => BC.Show.word({k}, {v}))"
        raise Unsupported(f"no generator for type {b}")

    def linear(self, t):
        """a def copying a drawn (Data) list into the affine list type t"""
        s = shape(t)
        d = self.data(t)
        return self.helper("lin " + t, lambda nm: f"""
def {nm}(xs: {d}) -> List<&1, {s[2]}>:
  match xs:
    case Nil{{}}:
      Nil{{}}
    case Con{{h, t}}:
      h <> {nm}(t)
""")

    def combine(self, kits):
        """right-nested pairs of kits"""
        if len(kits) == 1:
            return kits[0]
        t1, g1, s1, w1 = kits[0]
        t2, g2, s2, w2 = self.combine(kits[1:])
        v = self.fresh("lc_p")
        return (f"BC.Both<{t1}, {t2}>",
                f"BC.Gen.pair(~{t1}, ~{t2}, ~{g1}, ~{g2})",
                f"({v} => BC.Shrink.pair(~{t1}, ~{t2}, ~{s1}, ~{s2}, {v}))",
                f"({v} => BC.Show.pair(~{t1}, ~{t2}, ~{w1}, ~{w2}, {v}))")


def app(f, arg):
    """apply a closed function term to arg, inlining an outer lambda"""
    m = re.fullmatch(r"\((\w+) => (.*)\)", f, re.S)
    if m:
        return re.sub(ident(m.group(1)), lambda _: arg, m.group(2))
    return f"{f}({arg})"


# One law, one assignment of widths -> one property
# -------------------------------------------------

def law_params(body, elem):
    params, claim, fixed = [], [], {}
    for b in body:
        if b.startswith("for "):
            m = re.match(r"for\s+([+-]?)(\w+)\s*:\s*(.*)$", b)
            if not m:
                raise Unsupported(f"cannot read: {b}")
            n, t = m.group(2), m.group(3).strip()
            if " where " in t:
                raise Unsupported("`where` parameters")
            if t == "Quant":
                fixed[n] = "&2"
            elif t in ("Type", "Data") or t.startswith("Kind("):
                fixed[n] = elem
            else:
                params.append((n, t))
        elif b.startswith("exs "):
            raise Unsupported("existential (exs)")
        else:
            claim.append(b)
    return params, " ".join(claim), fixed


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
            if args and len(args) == 2 and args[1] in free and args[1] not in sol \
                    and not mentions(x, args[1]) and not mentions(args[0], args[1]):
                sol[args[1]] = f"Nat.sub({x}, {args[0]})"
            m = re.fullmatch(r"1n\+(.*)", x.strip())
            args = call(m.group(1), "Nat.add") if m else None
            if args and len(args) == 2 and args[1] in free and args[1] not in sol \
                    and not mentions(y, args[1]) and not mentions(args[0], args[1]):
                sol[args[1]] = f"Nat.sub(Nat.sub({y}, 1n), {args[0]})"
    return sol


def build(ctx, idx, name, params, claim, env):
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
    # an affine list is drawn reusable, then copied at each use
    uses = {}
    for n, t in drawn:
        s = shape(t)
        if s[0] == "list" and s[1] == "&1":
            uses[n] = f"{ctx.linear(t)}({n})"
    claim = subst(claim, uses)
    hyps = [(subst(l, uses), subst(r, uses), t, ng) for l, r, t, ng in hyps]
    l, r, t, neg = equation(claim)
    goal = ctx.eq(t, l, r)
    if neg:
        goal = f"Bool.not({goal})"
    pre = [f"Bool.not({ctx.eq(ht, hl, hr)})" if hn else ctx.eq(ht, hl, hr) for hl, hr, ht, hn in hyps]
    T, gen, shr, shw = ctx.combine([ctx.kit(t) for n, t in drawn])

    # take the nested input apart into the law's own names
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
    ap.add_argument("--elem", default="U32", help="element type for type parameters")
    ap.add_argument("--only", default="")
    ap.add_argument("--keep", action="store_true", help="keep the generated .bend file")
    a = ap.parse_args()
    widths = [int(w) for w in a.widths.split(",")]
    only = set(filter(None, a.only.split(",")))
    path = os.path.abspath(a.laws)
    root = os.path.dirname(path)
    imports, laws = parse(path)

    ctx, defs, runs, skipped = Ctx(), [], [], []
    for name, body in laws:
        if only and name not in only:
            continue
        try:
            params, claim, fixed = law_params(body, a.elem)
            params = [(n, subst(t, fixed)) for n, t in params]
            claim = subst(claim, fixed)
            built = [build(ctx, len(runs) + k, name, params, claim, env)
                     for k, env in enumerate(assignments(width_names(params), widths))]
            for label, src, run in built:
                defs.append(src)
                runs.append((label, run))
        except Unsupported as e:
            skipped.append((name, str(e)))

    rel = os.path.relpath(CHECK, root)
    rel = rel if rel.startswith(".") else "./" + rel
    body = "\n".join(f"    r{i} : Bool <- {run.replace('COUNT', f'{a.count}n').replace('SEED', str(a.seed))}"
                     for i, (label, run) in enumerate(runs))
    helpers = "".join(src for name, src in ctx.helpers.values())
    src = ("# generated by lawcheck: do not edit\n\n"
           + "\n".join([l for l in imports if " as BC" not in l] + [f"import {rel} as BC"]) + "\n"
           + CMP_EQ + helpers + "".join(defs)
           + f"\ndef main() -> IO(Unit):\n  do IO<Unit>:\n{body}\n    IO.print(\"lawcheck: done\")\n")
    gen_path = os.path.join(root, "lawcheck_run.bend")
    out = ""
    if runs:
        open(gen_path, "w").write(src)
        tmp = tempfile.mkdtemp()
        keep = a.keep
        try:
            r = subprocess.run([BEND, gen_path, "-o", os.path.join(tmp, "lc")], capture_output=True, text=True, env=ENV)
            if r.returncode != 0:
                print(r.stdout[-3000:] + r.stderr[-3000:])
                print(f"lawcheck: the generated tests do not build (kept at {gen_path})")
                keep = True
                return 2
            out = subprocess.run([os.path.join(tmp, "lc")], capture_output=True, text=True).stdout
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
            if not keep and os.path.exists(gen_path):
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
