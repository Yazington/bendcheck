#!/usr/bin/env python3
"""Mutation tests for bendcheck: each mutant breaks the library in one
place; tests/run.py must notice every one."""
import os, shutil, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

MUTANTS = [
    ("runner treats a failure as a pass", "check.bend",
     "            case Fails{}:\n              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Shrinking{1n+done, x, shrink(x), 0n})",
     "            case Fails{}:\n              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Next{1n+done, skipped, left, (i + 1 : U32), r})"),
    ("U32 shrinker gives up", "check.bend",
     "  +y = x\n  Shrink.u32.go(33n, U32.is_zero(y), y, y)", "  Nil{}"),
    ("random stream never advances", "check.bend",
     "      Both{Rand.mix(s2), Rand{s2, size}}", "      Both{Rand.mix(s), Rand{s, size}}"),
    ("preconditions inverted", "check.bend",
     "  match pre:\n    case True{}:\n      Check.holds(b)\n    case False{}:\n      Skip{}",
     "  match pre:\n    case False{}:\n      Check.holds(b)\n    case True{}:\n      Skip{}"),
    ("list shrinker never drops elements", "check.bend",
     "      Nil{} <> t <> List.cat(", "      List.cat("),
    ("shrinking keeps a passing candidate", "check.bend",
     "            case Holds{}:\n              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Shrinking{done, x, rest, steps})",
     "            case Holds{}:\n              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Shrinking{done, c, shrink(c), 1n+steps})"),
]


def main():
    bad = 0
    for name, f, old, new in MUTANTS:
        with tempfile.TemporaryDirectory() as t:
            d = os.path.join(t, "bc")
            shutil.copytree(ROOT, d, ignore=shutil.ignore_patterns(".git", "build"))
            src = open(os.path.join(d, f)).read()
            if old not in src:
                print(f"STALE    {name}"); bad += 1; continue
            open(os.path.join(d, f), "w").write(src.replace(old, new, 1))
            r = subprocess.run([sys.executable, os.path.join(d, "tests", "run.py")], capture_output=True, text=True, timeout=900)
            if r.returncode == 0:
                print(f"SURVIVED {name}"); bad += 1
            else:
                print(f"killed   {name}")
    print(f"{len(MUTANTS) - bad}/{len(MUTANTS)} mutants killed")
    return 1 if bad else 0


sys.exit(main())
