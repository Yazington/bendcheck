# lawcheck's own test laws: some true, some false. tests/lawcheck_test.py
# knows which is which.

import Base
import ./code.bend as C

# TRUE: adding then subtracting b gives a back (U32 wraps both ways)
law u32_add_sub:
  for +a: U32
  for +b: U32
  {U32.sub(U32.add(a, b), b) == a : U32}

# FALSE: subtraction commutes
law u32_sub_comm:
  for +a: U32
  for +b: U32
  {U32.sub(a, b) == U32.sub(b, a) : U32}

# FALSE: shl doubles exactly (it drops the top bit)
law shl_exact:
  for n: Nat
  for +w: Word(n)
  {Word.to_nat(n, Word.shl(n, w)) == Nat.double(Word.to_nat(n, w)) : Nat}

# TRUE: shl doubles, less the top bit when it is set
law shl_bound:
  for n: Nat
  for +w: Word(n)
  {Nat.is_le(Word.to_nat(n, Word.shl(n, w)), Nat.double(Word.to_nat(n, w))) == True{} : Bool}

# FALSE: an off-by-one subtraction law, under a hypothesis lawcheck solves
law sub_off_by_one:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +d: Nat
  for h: {Word.to_nat(n, a) == Nat.add(Word.to_nat(n, b), d) : Nat}
  {Word.to_nat(n, Word.sub(n, a, b)) == 1n+d : Nat}

# FALSE: comparison ignores the high bits
law cmp_low_bit:
  for n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, a, b) == Bool.cmp(C.lsb(n, a), C.lsb(n, b)) : Cmp}

# TRUE: Nat subtraction undoes addition
law nat_add_sub:
  for +a: Nat
  for +b: Nat
  {Nat.sub(Nat.add(a, b), b) == a : Nat}

# NOT TESTABLE: an existential
law exists_half:
  for n: Nat
  exs h: Nat
  {Nat.add(h, h) == n : Nat}

# TRUE: append is associative (any quantity, any element type)
law append_assoc:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  for zs: List<a, A>
  {List.append(a, A, List.append(a, A, xs, ys), zs) == List.append(a, A, xs, List.append(a, A, ys, zs)) : List<a, A>}

# FALSE: reversing an append keeps the order (smallest: ([0], [1]))
law reverse_append_draft:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.reverse(a, A, List.append(a, A, xs, ys)) == List.append(a, A, List.reverse(a, A, xs), List.reverse(a, A, ys)) : List<a, A>}

# TRUE: a set index reads back, when in range (a Maybe claim under a precondition)
law get_set:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for x: A
  for h: {Nat.is_lt(n, List.length(a, A, xs)) == True{} : Bool}
  {List.get(a, A, List.set(a, A, xs, n, x), n) == Some{x} : Maybe<a, A>}

# FALSE: get after set, with no bound (smallest: the empty list)
law get_set_unbounded:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for x: A
  {List.get(a, A, List.set(a, A, xs, n, x), n) == Some{x} : Maybe<a, A>}

# TRUE: flattening distributes over append (lists of lists)
law concat_append:
  for -a: Quant
  for -A: Kind(a)
  for xss: List<a, List<a, A>>
  for yss: List<a, List<a, A>>
  {List.concat(a, A, List.append(a, List<a, A>, xss, yss)) == List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) : List<a, A>}

# TRUE: binding a Maybe to Some changes nothing
law maybe_bind_some:
  for m: Maybe<&2, U32>
  {Maybe.bind(&2, U32, U32, m, x => Some{x}) == m : Maybe<&2, U32>}

# FALSE: binding a Maybe to None changes nothing (smallest: Some(0))
law maybe_bind_none:
  for m: Maybe<&2, U32>
  {Maybe.bind(&2, U32, U32, m, x => None{}) == m : Maybe<&2, U32>}
