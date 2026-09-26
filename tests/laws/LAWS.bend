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
