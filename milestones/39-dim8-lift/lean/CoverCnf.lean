import Glue2
/-! Cover CNFs on Q_n (n ≤ 6, vertices u < 2^n of Q8 with the high bits zero).

`coverCnf n units ctrs blocks`: degree ≤ 2 inside Q_n, selection-conditioned levels (≤ 64), unit clauses,
`atMost` counters `(lits, k)`, and one blocking clause per listed set (a mask over [0, 2^n)).  Variables:
`s u = u + 1`, `o u j = 65 + 64 u + (j - 1)`, `a u i j = 4161 + 384 u + 64 i + (j - 1)`, counters from 28738. -/
set_option linter.deprecated false
namespace Dim8Lift.Cover
open Dim8Lift Dim8Lift.Cnf Dim8Lift.Cube Snake9.LocalWindow

def cs (u : Nat) : Nat := u + 1
def co (u j : Nat) : Nat := 65 + 64 * u + (j - 1)
def ca (u i j : Nat) : Nat := 4161 + 384 * u + 64 * i + (j - 1)
def cbase : Nat := 28738

def pairsN (n : Nat) : List (Nat × Nat) := pairs8.filter fun p => p.2 < n
def triplesN (n : Nat) : List (Nat × Nat × Nat) := triples8.filter fun t => t.2.2 < n

def cDeg (n : Nat) : List (List Int) :=
  (List.range (2 ^ n)).flatMap fun u => (triplesN n).map fun (a, b, c) =>
    [neg (cs u), neg (cs (fx u a)), neg (cs (fx u b)), neg (cs (fx u c))]

def cLvlU (n u : Nat) : List (List Int) :=
  ((List.range 63).map fun j0 => [neg (co u (j0 + 2)), pos (co u (j0 + 1))]) ++
  ((List.range n).flatMap fun i => (List.range 64).flatMap fun j0 =>
    [[neg (ca u i (j0 + 1)), pos (cs (fx u i))], [neg (ca u i (j0 + 1)), neg (co (fx u i) (j0 + 1))]]) ++
  ((pairsN n).flatMap fun (i1, i2) =>
    [neg (cs u), neg (cs (fx u i1)), neg (cs (fx u i2)), pos (co u 1)] ::
    (List.range 64).map fun j0 =>
      ([neg (cs u), neg (cs (fx u i1)), neg (cs (fx u i2))] ++ (if j0 + 1 < 64 then [pos (co u (j0 + 2))] else [])) ++
        (List.range n).map fun i => pos (ca u i (j0 + 1)))

def cLvl (n : Nat) : List (List Int) := (List.range (2 ^ n)).flatMap (cLvlU n)

def cBlk (n : Nat) (blocks : List Nat) : List (List Int) :=
  blocks.map fun R => (List.range (2 ^ n)).map fun u => if R.testBit u then neg (cs u) else pos (cs u)

def cUnits (units : List (Nat × Bool)) : List (List Int) :=
  units.map fun (u, b) => if b then [pos (cs u)] else [neg (cs u)]

/-- counters placed consecutively from `cbase`, each with stride `64 * k` -/
def cCtrs : Nat → List (List Int × Nat) → List (List Int)
  | _, [] => []
  | b, (xs, k) :: rest => atMost b k xs ++ cCtrs (b + 64 * k) rest

def coverCnf (n : Nat) (units : List (Nat × Bool)) (ctrs : List (List Int × Nat)) (blocks : List Nat) :
    List (List Int) :=
  cUnits units ++ cDeg n ++ cLvl n ++ cCtrs cbase ctrs ++ cBlk n blocks

end Dim8Lift.Cover
