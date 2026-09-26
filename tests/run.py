#!/usr/bin/env python3
"""bendcheck's test suite. Every expectation is exact: true properties
pass, false ones fail with the smallest counterexample, runs are
deterministic, and the JS build agrees with the native one."""
import os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BEND = os.environ.get("BEND", os.path.expanduser("~/.bend/bin/bend"))
ENV = {**os.environ, "BEND_NO_TELEMETRY": "1"}
fails = 0


def check(name, ok, detail=""):
    global fails
    print(f"{'ok  ' if ok else 'FAIL'}  {name}")
    if detail and not ok:
        print(f"      {detail}")
    fails += not ok


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, env=ENV, cwd=ROOT, **kw)


r = run([BEND, "check.bend", "--check-only"])
check("library type-checks", "All terms check." in r.stdout + r.stderr, r.stdout + r.stderr)

with tempfile.TemporaryDirectory() as d:
    b = os.path.join(d, "selftest")
    r = run([BEND, "tests/selftest.bend", "-o", b])
    check("selftest builds", r.returncode == 0, r.stdout + r.stderr)
    c1, c2 = run([b]), run([b])
    out = c1.stdout
    check("add_comm passes 1000 tests", "  ok      add_comm (1000 tests)" in out, out)
    check("div_mod passes, skipping b == 0",
          re.search(r"  ok      div_mod \(1000 tests, \d+ skipped\)", out) is not None, out)
    check("x < 1000 fails at exactly 1000",
          "FAILED  below_1000 (false)" in out and "counterexample: 1000\n" in out, out)
    m = re.search(r"FAILED  add_grows \(false\).*\n\s+counterexample: \((\d+), (\d+)\)", out)
    check("a + b >= a fails at a + b == 2^32",
          m is not None and int(m[1]) + int(m[2]) == 2 ** 32, out)
    check("reverse == id fails at [0, 1]", "counterexample: [0, 1]" in out, out)
    check("a failing suite exits 1",
          c1.returncode == 1 and "3 of 5 properties failed" in c1.stderr, c1.stderr)
    check("same seed, same run", c1.stdout == c2.stdout)
    r = run([BEND, "tests/selftest.bend", "-o", b + ".js"])
    j = run(["node", b + ".js"])
    check("JS build agrees with native",
          j.stdout == c1.stdout and j.returncode == 1, j.stdout[:500] + j.stderr[-500:])

expect = {
    "u32_add_sub": "ok", "u32_sub_comm": "(0, 1)",
    "shl_exact [n=1]": "1", "shl_exact [n=3]": "4", "shl_exact [n=8]": "128",
    "shl_bound [n=1]": "ok", "shl_bound [n=3]": "ok", "shl_bound [n=8]": "ok",
    "sub_off_by_one [n=1]": "(0, 0)", "sub_off_by_one [n=3]": "(0, 0)",
    "sub_off_by_one [n=8]": "(0, 0)",
    # the minimal counterexample is symmetric: either side may keep the 2
    "cmp_low_bit [n=1]": "ok", "cmp_low_bit [n=3]": {"(0, 2)", "(2, 0)"},
    "cmp_low_bit [n=8]": {"(0, 2)", "(2, 0)"},
    "nat_add_sub": "ok",
    "append_assoc": "ok", "reverse_append_draft": "([0], [1])", "get_set": "ok",
    "get_set_unbounded": "([], (0, 0))", "concat_append": "ok",
    "maybe_bind_some": "ok", "maybe_bind_none": "Some(0)",
}
for seed in ("1", "7"):
    r = run([sys.executable, "tools/lawcheck.py", "tests/laws/LAWS.bend",
             "--widths", "1,3,8", "--seed", seed])
    got = {}
    for m in re.finditer(r"  ok      (.+?) \(\d+ tests", r.stdout):
        got[m[1]] = "ok"
    for m in re.finditer(r"  FAILED  (.+?) after .*\n\s+counterexample: (.+)", r.stdout):
        got[m[1]] = m[2]
    wrong = {k: (v, got.get(k)) for k, v in expect.items()
             if got.get(k) not in (v if isinstance(v, set) else {v})}
    check(f"lawcheck (seed {seed}): true laws pass, false laws fail minimally",
          not wrong, f"expected vs got: {wrong}")
    check(f"lawcheck (seed {seed}): exs is not testable, exit 1",
          "n/a     exists_half: existential (exs)" in r.stdout and r.returncode == 1,
          r.stdout[-400:])

print("ALL TESTS PASSED" if not fails else f"{fails} TESTS FAILED")
sys.exit(1 if fails else 0)
