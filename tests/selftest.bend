# bendcheck's own tests: true properties must pass; false ones must fail
# and shrink to the smallest counterexample.

import Base
import ../check.bend as Q

def show_u32s(p: Q.Both<U32, U32>) -> String:
  Q.Show.pair(~U32, ~U32, ~U32.show, ~U32.show, p)

def shrink_u32s(p: Q.Both<U32, U32>) -> +List<Q.Both<U32, U32>>:
  Q.Shrink.pair(~U32, ~U32, ~Q.Shrink.u32, ~Q.Shrink.u32, p)

def gen_u32s() -> Q.Gen(Q.Both<U32, U32>):
  Q.Gen.pair(~U32, ~U32, ~Q.Gen.u32(), ~Q.Gen.u32())

# true: a + b == b + a
def add_comm(p: Q.Both<U32, U32>) -> Q.Verdict:
  Q.Both{a0, b0} = p
  +a = a0
  +b = b0
  Q.Check.holds(U32.is_eq((a + b : U32), (b + a : U32)))

# true when b != 0: (a / b) * b + a % b == a
def div_mod(p: Q.Both<U32, U32>) -> Q.Verdict:
  Q.Both{a0, b0} = p
  +a = a0
  +b = b0
  Q.Check.when(U32.is_ne(b, 0), U32.is_eq((((a / b : U32) * b : U32) + (a % b : U32) : U32), a))

# false: x < 1000 (smallest counterexample: 1000)
def below_1000(x: U32) -> Q.Verdict:
  Q.Check.holds((x < 1000 : U32))

# false: a + b >= a (overflow; smallest: a + b == 2^32)
def add_grows(p: Q.Both<U32, U32>) -> Q.Verdict:
  Q.Both{a0, b0} = p
  +a = a0
  +b = b0
  Q.Check.holds(((a + b : U32) >= a : U32))

def rev.go(xs: +List<U32>, acc: +List<U32>) -> +List<U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev.go(t, h <> acc)

def list_eq(xs: +List<U32>, ys: +List<U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, ys2}:
      False{}
    case Con{x, xs2} Nil{}:
      False{}
    case Con{x, xs2} Con{y, ys2}:
      Bool.and(U32.is_eq(x, y), list_eq(xs2, ys2))

# false: reversing changes nothing (smallest: two different elements)
def rev_id(xs: +List<U32>) -> Q.Verdict:
  +ys = xs
  Q.Check.holds(list_eq(rev.go(ys, Nil{}), ys))

def show_list(xs: +List<U32>) -> String:
  Q.Show.list(~U32, ~U32.show, xs)

def shrink_list(xs: +List<U32>) -> +List<+List<U32>>:
  Q.Shrink.list(~U32, ~Q.Shrink.u32, xs)

def gen_list() -> Q.Gen(+List<U32>):
  Q.Gen.list(~U32, ~Q.Gen.u32())

def main() -> IO(Unit):
  do IO<Unit>:
    a : Bool <- Q.Check.prop(~Q.Both<U32, U32>, ~gen_u32s(), ~add_comm, ~shrink_u32s, ~show_u32s, "add_comm", 1000n, 1)
    b : Bool <- Q.Check.prop(~Q.Both<U32, U32>, ~gen_u32s(), ~div_mod, ~shrink_u32s, ~show_u32s, "div_mod", 1000n, 2)
    c : Bool <- Q.Check.prop(~U32, ~Q.Gen.u32(), ~below_1000, ~Q.Shrink.u32, ~U32.show, "below_1000 (false)", 1000n, 3)
    d : Bool <- Q.Check.prop(~Q.Both<U32, U32>, ~gen_u32s(), ~add_grows, ~shrink_u32s, ~show_u32s, "add_grows (false)", 1000n, 4)
    e : Bool <- Q.Check.prop(~+List<U32>, ~gen_list(), ~rev_id, ~shrink_list, ~show_list, "rev_id (false)", 1000n, 5)
    Q.Check.summary([a, b, c, d, e])
