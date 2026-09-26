# bendcheck

Property-based testing for Bend: state what must hold, let random inputs try
to break it, and get the smallest counterexample back.

Bend asks for proofs, and proofs are expensive to write for a claim that turns
out to be false. bendcheck is the cheap step before the proof: it tests a
property on hundreds of inputs in milliseconds, and `lawcheck` does it for
every law in a `LAWS.bend` file with no test code at all.

Built against Bend 2.0.28. `./check.sh` runs every check.

## Install

From BendHub:

```python
import 0x738b30530890e825e0ab81092b94cbfc/check.bend as Q
```

or clone this repo and `import ./bendcheck/check.bend as Q`. `lawcheck` needs
the clone (it is a Python script that generates and runs Bend).

## A property

```python
import Base
import ./bendcheck/check.bend as Q

# false: x < 1000
def below_1000(x: U32) -> Q.Verdict:
  Q.Check.holds((x < 1000 : U32))

def main() -> IO(Unit):
  do IO<Unit>:
    ok : Bool <- Q.Check.prop(~U32, ~Q.Gen.u32(), ~below_1000, ~Q.Shrink.u32, ~U32.show,
                              "below_1000", 1000n, 1)
    Q.Check.summary([ok])
```

```text
  FAILED  below_1000 after 1 tests, 24 shrinks
          counterexample: 1000
          seed: 1
1 of 1 properties failed
```

`Check.prop` takes the input type, a generator, the property, a shrinker and a
printer, all as templates (`~`), then a name, a test count and a seed. The
same seed gives the same run, natively and on JS. `Check.summary` exits with
status 1 if any property failed.

## lawcheck: test your laws before you prove them

```sh
python3 tools/lawcheck.py path/to/LAWS.bend [--count 200] [--seed 1] [--widths 1,2,3,8,16]
```

Every `law` becomes a property. Its `for` parameters are drawn at random,
hypotheses (`for h: {L == R : T}`) become preconditions, and the claim is
checked with its type's equality (`U32`, `Nat`, `Bool`, `Cmp`, `Word(n)`). A
`Nat` used as a width (`Word(n)`) is fixed at a few sizes. A hypothesis
`{X == Nat.add(Y, v) : Nat}` or `{1n+Nat.add(E, v) == P : Nat}` is solved for
`v`, so laws like "if `a = b + d` then `a - b = d`" get real tests instead of
waiting for random luck.

```text
  FAILED  shl_exact [n=8] after 3 tests, 4 shrinks
          counterexample: 128
  FAILED  sub_off_by_one [n=3] after 1 tests, 2 shrinks
          counterexample: (0, 0)
  n/a     exists_half: existential (exs)
lawcheck: 6 passed, 9 failed, 0 gave up (precondition rarely held), 1 not testable
```

On [wordlib](https://github.com/Yazington/wordlib)'s 44 proved laws it runs
157 properties across widths: 153 pass, and 4 give up because their
precondition (two random words with equal values, say) almost never holds.

## The pieces

| | |
|---|---|
| **Generators** (`Gen(A)`, a monad: `do Gen<A>:`) | `u32` (one draw in eight an edge value: 0, 2^31, 2^32-1 and neighbours), `below(n)`, `small`, `nat`, `bool`, `word(n)`, `pair`, `list`, `map` |
| **Shrinkers** (`A -> +List<A>`, most aggressive first) | `u32` (binary search towards 0), `nat`, `bool`, `word` (zero, half, one bit fewer), `pair`, `list` (empty, tail, smaller head, smaller tail), `none` |
| **Printers** | `Show.pair`, `Show.list`, `Show.word`, plus Base's `U32.show`, `Nat.show`, `Bool.show` |
| **Verdicts** | `Check.holds(b)`, and `Check.when(pre, b)`, which skips inputs failing `pre` |
| **Running** | `Check.run` (a `Report`), `Check.prop` (prints, returns `Bool`), `Check.summary` |

Pairs are `Q.Both<A, B>`, built with `Q.Both{a, b}` and taken apart with
`Q.Both{a, b} = p`. It is a datatype rather than Bend's `A & B` so that both
parts can be reused and nested pairs need no annotations.

## Writing properties in Bend

- Generators, properties, shrinkers and printers are passed as templates, since
  a Bend closure may be called only once. Pass top-level defs, or closed
  lambdas like `~(w => Q.Shrink.word(8n, w))`.
- Take plain parameters and rebind to reuse: `def p(x: U32) -> Q.Verdict:`,
  then `+y = x` inside.
- Inputs must be `Data`: lists as `+List<A>`, pairs as `Q.Both<A, B>`.
- The runner is a single state machine with fuel, because Bend has no mutual
  recursion; it always terminates, and on running out of fuel mid-shrink it
  reports the best counterexample so far.

## How it is verified

`./check.sh` runs:

1. `tests/run.py`: exact expectations. True properties pass; false ones fail
   at their smallest counterexample (`1000`, `[0, 1]`, a pair summing to exactly
   2^32); runs are deterministic; the JS build prints the same bytes as the
   native one; `lawcheck` passes the true laws in `tests/laws` and fails every
   false one at a minimal input, under two seeds.
2. `tests/mutants.py`: 6 planted bugs (a runner that ignores failures, a
   shrinker that gives up, a random stream that never advances, inverted
   preconditions, and two shrinking bugs). The test suite catches each one.

The random stream is lowbias32 over a Weyl sequence, checked against a Python
reference.

## Limits

- Compiled `Nat` stops the program past 2^48, so keep `Nat` products small
  (lawcheck's default widths stay under 16 bits).
- A property whose precondition rarely holds gives up rather than passing.
- lawcheck reads the common law shapes; existentials, `where` parameters and
  claims that are not equations are reported as not testable.

## License

MIT. See `LICENSE`.
