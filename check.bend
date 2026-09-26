# bendcheck: property-based testing for Bend.
#
# A property is a def from an input to a Verdict. Check.run draws inputs
# from a generator, tests each, and on the first failure shrinks the input
# to a minimal counterexample. Generators, properties, shrinkers and
# printers are passed as templates (~), so they may be used many times.

import Base

# a pair whose parts may both be reused (a datatype rather than Sigma,
# so nested pairs take apart without annotations)
type Both<-A: Data, -B: Data> is Data:
  Both{fst: A, snd: B}

# Randomness
# ==========

# a 32-bit counter hashed by lowbias32; size bounds sized generators
type Rand is Data:
  Rand{seed: U32, size: U32}

# lowbias32 (C. Wellons): a fast, well-mixed 32-bit hash
def Rand.mix(+x: U32) -> U32:
  +a = (U32.xor(x, U32.shrn(x, 16n)) * 2146121005 : U32)
  +b = (U32.xor(a, U32.shrn(a, 15n)) * 2221713035 : U32)
  U32.xor(b, U32.shrn(b, 16n))

def Rand.new(seed: U32) -> Rand:
  Rand{Rand.mix(seed), 1}

def Rand.next(r: Rand) -> Both<U32, Rand>:
  match r:
    case Rand{s, size}:
      +s2 = (s + 2654435769 : U32)
      Both{Rand.mix(s2), Rand{s2, size}}

def Rand.sized(r: Rand, size: U32) -> Rand:
  match r:
    case Rand{s, old}:
      Rand{s, size}

# Generators
# ==========

def Gen(-A: Data) -> Type:
  Rand -> Both<A, Rand>

def Gen.pure(-A: Data, x: A) -> Gen(A):
  r => Both{x, r}

def Gen.bind.k(-A: Data, -B: Data, f: A -> Gen(B), ar: Both<A, Rand>) -> Both<B, Rand>:
  Both{a, r} = ar
  f(a)(r)

def Gen.bind(-A: Data, -B: Data, m: Gen(A), f: A -> Gen(B)) -> Gen(B):
  r => Gen.bind.k(A, B, f, m(r))

def Gen.map.k(-A: Data, -B: Data, f: A -> B, ar: Both<A, Rand>) -> Both<B, Rand>:
  Both{a, r} = ar
  Both{f(a), r}

def Gen.map(-A: Data, -B: Data, f: A -> B, m: Gen(A)) -> Gen(B):
  r => Gen.map.k(A, B, f, m(r))

# 32 uniform bits
def Gen.bits(r: Rand) -> Both<U32, Rand>:
  Rand.next(r)

# the current size (grows with the test index)
def Gen.size(r: Rand) -> Both<U32, Rand>:
  match r:
    case Rand{s, +size}:
      Both{size, Rand{s, size}}

# uniform in [0, n); 0 when n is 0
def Gen.below(+n: U32) -> Gen(U32):
  do Gen<U32>:
    x : U32 <- Gen.bits
    return (x % n : U32)

def Gen.bool() -> Gen(Bool):
  do Gen<Bool>:
    x : U32 <- Gen.bits
    return U32.is_eq((x .&. 1 : U32), 1)

# values that break code: zero, one, powers of two and their neighbours
def Gen.edges() -> +List<U32>:
  [0, 1, 2, 3, 7, 8, 127, 128, 255, 256, 32767, 32768, 65535, 65536,
   2147483647, 2147483648, 4294967294, 4294967295]

def List.nth_u32(xs: +List<U32>, i: Nat) -> U32:
  match xs i:
    case Nil{} _:
      0
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      List.nth_u32(t, j)

def Gen.u32.pick(edge: Bool, k: U32, x: U32) -> U32:
  match edge:
    case True{}:
      List.nth_u32(Gen.edges(), U32.to_nat((U32.shrn(k, 3n) % 18 : U32)))
    case False{}:
      x

# any U32, one draw in eight an edge value
def Gen.u32() -> Gen(U32):
  do Gen<U32>:
    +k : U32 <- Gen.bits
    x : U32 <- Gen.bits
    return Gen.u32.pick(U32.is_zero((k .&. 7 : U32)), k, x)

# a U32 in [0, size]
def Gen.small() -> Gen(U32):
  do Gen<U32>:
    n : U32 <- Gen.size
    x : U32 <- Gen.below((n + 1 : U32))
    return x

# a Nat in [0, size]
def Gen.nat() -> Gen(Nat):
  Gen.map(U32, Nat, x => U32.to_nat(x), Gen.small())

# a Word of n random bits
def Gen.word(n: Nat) -> Gen(Word(n)):
  match n:
    case 0n:
      Gen.pure(Word(0n), WNil{})
    case 1n+p:
      do Gen<Word(1n+p)>:
        b : Bool <- Gen.bool()
        t : Word(p) <- Gen.word(p)
        return WCon{b, t}

def Gen.pair(~A: Data, ~B: Data, ~ga: Gen(A), ~gb: Gen(B)) -> Gen(Both<A, B>):
  do Gen<Both<A, B>>:
    a : A <- ga
    b : B <- gb
    return Both{a, b}

def Gen.list.n(~A: Data, ~g: Gen(A), n: Nat) -> Gen(+List<A>):
  match n:
    case 0n:
      Gen.pure(+List<A>, Nil{})
    case 1n+p:
      do Gen<+List<A>>:
        x : A <- g
        xs : +List<A> <- Gen.list.n(~A, ~g, p)
        return x <> xs

# a list of up to size elements
def Gen.list(~A: Data, ~g: Gen(A)) -> Gen(+List<A>):
  do Gen<+List<A>>:
    n : U32 <- Gen.size
    k : U32 <- Gen.below((n + 1 : U32))
    xs : +List<A> <- Gen.list.n(~A, ~g, U32.to_nat(k))
    return xs

# Shrinking
# =========
# A shrinker lists smaller candidates, most aggressive first.

def Shrink.none(-A: Data, x: A) -> +List<A>:
  Nil{}

# x - x, x - x/2, x - x/4, ..., x - 1: a binary search towards 0
def Shrink.u32.go(fuel: Nat, stop: Bool, +x: U32, +d: U32) -> +List<U32>:
  match fuel stop:
    case 0n _:
      Nil{}
    case 1n+f True{}:
      Nil{}
    case 1n+f False{}:
      +h = U32.shrn(d, 1n)
      (x - d : U32) <> Shrink.u32.go(f, U32.is_zero(h), x, h)

def Shrink.u32(x: U32) -> +List<U32>:
  +y = x
  Shrink.u32.go(33n, U32.is_zero(y), y, y)

def Shrink.nat.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+Shrink.nat.half(q)

def Shrink.nat(x: Nat) -> +List<Nat>:
  match x:
    case 0n:
      Nil{}
    case 1n++p:
      [0n, Shrink.nat.half(1n+p), p]

def Shrink.bool(b: Bool) -> +List<Bool>:
  match b:
    case True{}:
      [False{}]
    case False{}:
      Nil{}

def Shrink.word.tails(+p: Nat, +b: Bool, ts: +List<Word(p)>) -> +List<Word(1n+p)>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      WCon{b, t} <> Shrink.word.tails(p, b, rest)

def Shrink.word.head(+p: Nat, b: Bool, +t: Word(p), ts: +List<Word(p)>) -> +List<Word(1n+p)>:
  match b:
    case True{}:
      WCon{False{}, t} <> Shrink.word.tails(p, True{}, ts)
    case False{}:
      Shrink.word.tails(p, False{}, ts)

# clear one set bit at a time, lowest first
def Shrink.word.bits(n: Nat, w: Word(n)) -> +List<Word(n)>:
  match n w:
    case 0n WNil{}:
      Nil{}
    case 1n++p WCon{b, +t}:
      Shrink.word.head(p, b, t, Shrink.word.bits(p, t))

def Shrink.word.nonzero(+n: Nat, +w: Word(n), zero: Bool) -> +List<Word(n)>:
  match zero:
    case True{}:
      Nil{}
    case False{}:
      Word.zero(n) <> Word.shr(n, w) <> Shrink.word.bits(n, w)

# zero, then half, then one bit fewer
def Shrink.word(+n: Nat, w: Word(n)) -> +List<Word(n)>:
  +v = w
  Shrink.word.nonzero(n, v, Nat.is_eq(Word.to_nat(n, v), 0n))

def Shrink.pair.l(~A: Data, ~B: Data, +b: B, xs: +List<A>) -> +List<Both<A, B>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Both{h, b} <> Shrink.pair.l(~A, ~B, b, t)

def Shrink.pair.r(~A: Data, ~B: Data, +a: A, ys: +List<B>) -> +List<Both<A, B>>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Both{a, h} <> Shrink.pair.r(~A, ~B, a, t)

def List.cat(~A: Data, xs: +List<A>, ys: +List<A>) -> +List<A>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      h <> List.cat(~A, t, ys)

# shrink the left, then the right
def Shrink.pair(~A: Data, ~B: Data, ~sa: A -> +List<A>, ~sb: B -> +List<B>, p: Both<A, B>) -> +List<Both<A, B>>:
  Both{a0, b0} = p
  +a = a0
  +b = b0
  List.cat(~Both<A, B>, Shrink.pair.l(~A, ~B, b, sa(a)), Shrink.pair.r(~A, ~B, a, sb(b)))

def Shrink.list.cons(~A: Data, +h: A, ts: +List<+List<A>>) -> +List<+List<A>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      (h <> t) <> Shrink.list.cons(~A, h, rest)

def Shrink.list.heads(~A: Data, hs: +List<A>, +t: +List<A>) -> +List<+List<A>>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, rest}:
      (h <> t) <> Shrink.list.heads(~A, rest, t)

# the empty list, the tail, then a smaller head, then a smaller tail
def Shrink.list(~A: Data, ~s: A -> +List<A>, xs: +List<A>) -> +List<+List<A>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Nil{} <> t <> List.cat(~(+List<A>), Shrink.list.heads(~A, s(h), t), Shrink.list.cons(~A, h, Shrink.list(~A, ~s, t)))

# Showing
# =======

def Show.pair(~A: Data, ~B: Data, ~sa: A -> String, ~sb: B -> String, p: Both<A, B>) -> String:
  Both{a, b} = p
  "(" ++ sa(a) ++ ", " ++ sb(b) ++ ")"

def Show.list.tail(~A: Data, ~s: A -> String, xs: +List<A>) -> String:
  match xs:
    case Nil{}:
      "]"
    case Con{h, t}:
      ", " ++ s(h) ++ Show.list.tail(~A, ~s, t)

def Show.list(~A: Data, ~s: A -> String, xs: +List<A>) -> String:
  match xs:
    case Nil{}:
      "[]"
    case Con{h, t}:
      "[" ++ s(h) ++ Show.list.tail(~A, ~s, t)

# a word by its value
def Show.word(n: Nat, w: Word(n)) -> String:
  Nat.show(Word.to_nat(n, w))

# Properties
# ==========

type Verdict is Data:
  Holds{}
  Fails{}
  Skip{}

def Check.holds(b: Bool) -> Verdict:
  match b:
    case True{}:
      Holds{}
    case False{}:
      Fails{}

# a property with a precondition: inputs failing pre are skipped
def Check.when(pre: Bool, b: Bool) -> Verdict:
  match pre:
    case True{}:
      Check.holds(b)
    case False{}:
      Skip{}

# Running
# =======

type Report is Data:
  Passed{tests: Nat, skipped: Nat}
  Failed{tests: Nat, shrinks: Nat, input: String}
  GaveUp{tests: Nat, skipped: Nat}

# The runner is one state machine, since Bend has no mutual recursion.
# i is the test index; it sets the size, which grows up to 100.
type St<-A: Data> is Data:
  Next{done: Nat, skipped: Nat, left: Nat, i: U32, r: Rand}
  Drawn{done: Nat, skipped: Nat, left: Nat, i: U32, xr: Both<A, Rand>}
  Tested{done: Nat, skipped: Nat, left: Nat, i: U32, r: Rand, x: A, v: Verdict}
  Shrinking{done: Nat, x: A, cands: +List<A>, steps: Nat}
  Retest{done: Nat, x: A, c: A, rest: +List<A>, steps: Nat, v: Verdict}

def Check.size(+i: U32) -> U32:
  ((i % 100 : U32) + 1 : U32)

# when fuel runs out: a failure keeps its best counterexample so far
def Check.stop(~A: Data, ~show: A -> String, st: St<A>) -> Report:
  match st:
    case Next{done, skipped, left, i, r}:
      GaveUp{done, skipped}
    case Drawn{done, skipped, left, i, xr}:
      GaveUp{done, skipped}
    case Tested{done, skipped, left, i, r, x, v}:
      GaveUp{done, skipped}
    case Shrinking{done, x, cands, steps}:
      Failed{done, steps, show(x)}
    case Retest{done, x, c, rest, steps, v}:
      Failed{done, steps, show(x)}

def Check.go(~A: Data, ~gen: Gen(A), ~prop: A -> Verdict, ~shrink: A -> +List<A>, ~show: A -> String,
  fuel: Nat, st: St<A>) -> Report:
  match fuel:
    case 0n:
      Check.stop(~A, ~show, st)
    case 1n+f:
      match st:
        case Next{done, skipped, left, +i, r}:
          match left:
            case 0n:
              Passed{done, skipped}
            case 1n+l:
              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f,
                Drawn{done, skipped, l, i, gen(Rand.sized(r, Check.size(i)))})
        case Drawn{done, skipped, left, i, xr}:
          Both{x0, r} = xr
          +x = x0
          Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Tested{done, skipped, left, i, r, x, prop(x)})
        case Tested{done, skipped, left, i, r, +x, v}:
          match v:
            case Holds{}:
              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Next{1n+done, skipped, left, (i + 1 : U32), r})
            case Skip{}:
              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Next{done, 1n+skipped, 1n+left, (i + 1 : U32), r})
            case Fails{}:
              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Shrinking{1n+done, x, shrink(x), 0n})
        case Shrinking{done, x, cands, steps}:
          match cands:
            case Nil{}:
              Failed{done, steps, show(x)}
            case Con{+c, rest}:
              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Retest{done, x, c, rest, steps, prop(c)})
        case Retest{done, x, +c, rest, steps, v}:
          match v:
            case Fails{}:
              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Shrinking{done, c, shrink(c), 1n+steps})
            case Holds{}:
              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Shrinking{done, x, rest, steps})
            case Skip{}:
              Check.go(~A, ~gen, ~prop, ~shrink, ~show, f, Shrinking{done, x, rest, steps})

# test prop on count inputs from gen; skipped inputs are redrawn, up to
# ten skips per test
def Check.run(~A: Data, ~gen: Gen(A), ~prop: A -> Verdict, ~shrink: A -> +List<A>, ~show: A -> String,
  +count: Nat, seed: U32) -> Report:
  Check.go(~A, ~gen, ~prop, ~shrink, ~show, Nat.add(Nat.mul(count, 40n), 20000n),
    Next{0n, 0n, count, 0, Rand.new(seed)})

def Check.skips(s: Nat) -> String:
  match s:
    case 0n:
      ""
    case 1n+p:
      ", " ++ Nat.show(s) ++ " skipped"

def Check.print(name: String, seed: U32, rep: Report) -> IO(Bool):
  match rep:
    case Passed{n, s}:
      do IO<Bool>:
        IO.print("  ok      " ++ name ++ " (" ++ Nat.show(n) ++ " tests" ++ Check.skips(s) ++ ")")
        return True{}
    case Failed{n, k, input}:
      do IO<Bool>:
        IO.print("  FAILED  " ++ name ++ " after " ++ Nat.show(n) ++ " tests, " ++ Nat.show(k) ++ " shrinks")
        IO.print("          counterexample: " ++ input)
        IO.print("          seed: " ++ U32.show(seed))
        return False{}
    case GaveUp{n, s}:
      do IO<Bool>:
        IO.print("  GAVE UP " ++ name ++ ": " ++ Nat.show(n) ++ " tests, " ++ Nat.show(s) ++ " skipped")
        return False{}

def Check.prop(~A: Data, ~gen: Gen(A), ~prop: A -> Verdict, ~shrink: A -> +List<A>, ~show: A -> String,
  name: String, count: Nat, +seed: U32) -> IO(Bool):
  Check.print(name, seed, Check.run(~A, ~gen, ~prop, ~shrink, ~show, count, seed))

def Check.count_failed(bs: +List<Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{b, t}:
      match b:
        case True{}:
          Check.count_failed(t)
        case False{}:
          1n+Check.count_failed(t)

def Check.summary.end(total: Nat, failed: Nat, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.print(Nat.show(total) ++ " properties passed")
    case False{}:
      IO.die(Unit, 1, Nat.show(failed) ++ " of " ++ Nat.show(total) ++ " properties failed")

# print a summary; exit with status 1 if any property failed
def Check.summary(+bs: +List<Bool>) -> IO(Unit):
  +failed = Check.count_failed(bs)
  Check.summary.end(List.length(&2, Bool, bs), failed, Nat.is_eq(failed, 0n))
