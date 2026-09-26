# code under test for tests/laws/LAWS.bend

import Base

# the lowest bit (False for the empty word)
def lsb(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          b
