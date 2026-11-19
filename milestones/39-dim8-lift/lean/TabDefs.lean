import Glue2
/-! Checks for the cover tables. -/
namespace Dim8Lift.Tab
open Dim8Lift.Sym

/-- generators of B_n on the low n coordinates (they fix bits n..7) -/
def inB (n c : Nat) : Bool := (decide (c < 28) && decide ((Cube.pairs8.getD c (0, 0)).2 < n)) || (decide (28 ≤ c) && decide (c < 28 + n))

def chk (n : Nat) (R : Nat) (w : List Nat) (rep : Nat) : Bool :=
  w.all (inB n) && (List.range (2 ^ n)).all fun u =>
    decide (applyW w u < 2 ^ n) && (R.testBit (applyW w u) == rep.testBit u)

end Dim8Lift.Tab
