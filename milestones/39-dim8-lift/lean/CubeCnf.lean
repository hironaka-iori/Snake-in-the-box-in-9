import Counter
import Premise
/-! The cube CNF of Q8 (milestone 29's encoding with a fixed copy), generated in Lean.

Variables (D = 64 levels, n = 8):
* `sV u = u + 1` selection, `u < 256`;
* `oV u j` (1 ≤ j ≤ 64): level of `u` is at least `j`;
* `aV u i j`: neighbour `u ^^^ 2^i` is selected with level `< j`;
* `pV u a b` (a < b): both neighbours `u ^^^ 2^a`, `u ^^^ 2^b` selected; `twoV u`, `anyV u`;
* `e1V u` (selected, not two selected neighbours), `e0V u` (selected, no selected neighbour);
* sequential counters from `cbase`: endpoints `≤ 2c`, unselected `≤ 256 - L`, and every
  6-subcube except copy 0 has at most `k = |A|` selected vertices.
Copy 0 (`u < 64`) is fixed to the mask `A`. -/
namespace Dim8Lift.Cube
open Dim8Lift.Cnf

def sV (u : Nat) : Nat := u + 1
def oV (u j : Nat) : Nat := 257 + 64 * u + (j - 1)
def aV (u i j : Nat) : Nat := 16641 + 512 * u + 64 * i + (j - 1)
def pV (u a b : Nat) : Nat := 147713 + 64 * u + 8 * a + b
def twoV (u : Nat) : Nat := 164097 + u
def anyV (u : Nat) : Nat := 164353 + u
def e1V (u : Nat) : Nat := 164609 + u
def e0V (u : Nat) : Nat := 164865 + u
def cbase : Nat := 165121

def fx (u i : Nat) : Nat := u ^^^ 2 ^ i

def R256 : List Nat := List.range 256
def pairs8 : List (Nat × Nat) := (List.range 8).flatMap fun a => ((List.range 8).filter (a < ·)).map (a, ·)
def triples8 : List (Nat × Nat × Nat) :=
  pairs8.flatMap fun (a, b) => ((List.range 8).filter (b < ·)).map (a, b, ·)

/-- degree at most 2 -/
def famDeg : List (List Int) :=
  R256.flatMap fun u => triples8.map fun (a, b, c) => [neg (sV u), neg (sV (fx u a)), neg (sV (fx u b)), neg (sV (fx u c))]

/-- levels -/
def lvlMono (u : Nat) : List (List Int) := (List.range 63).map fun j0 => [neg (oV u (j0 + 2)), pos (oV u (j0 + 1))]
def lvlA1 (u i j0 : Nat) : List Int := [neg (aV u i (j0 + 1)), pos (sV (fx u i))]
def lvlA2 (u i j0 : Nat) : List Int := [neg (aV u i (j0 + 1)), neg (oV (fx u i) (j0 + 1))]
def lvlAux (u : Nat) : List (List Int) :=
  (List.range 8).flatMap fun i => (List.range 64).flatMap fun j0 => [lvlA1 u i j0, lvlA2 u i j0]
def lvlOne (u : Nat) : List Int := [neg (twoV u), pos (oV u 1)]
def lvlStep (u j0 : Nat) : List Int :=
  (neg (twoV u) :: (if j0 + 1 < 64 then [pos (oV u (j0 + 2))] else [])) ++
    (List.range 8).map fun i => pos (aV u i (j0 + 1))
def lvlU (u : Nat) : List (List Int) :=
  lvlMono u ++ lvlAux u ++ lvlOne u :: (List.range 64).map (lvlStep u)
def famLvl : List (List Int) := R256.flatMap lvlU

/-- pair, two, any, e1, e0 definitions (full equivalences) -/
def defPair (u a b : Nat) : List (List Int) :=
  [[neg (pV u a b), pos (sV (fx u a))], [neg (pV u a b), pos (sV (fx u b))],
   [pos (pV u a b), neg (sV (fx u a)), neg (sV (fx u b))], [neg (pV u a b), pos (twoV u)]]
def defTwo (u : Nat) : List Int := neg (twoV u) :: pairs8.map fun (a, b) => pos (pV u a b)
def defAny1 (u a : Nat) : List Int := [neg (sV (fx u a)), pos (anyV u)]
def defAny (u : Nat) : List Int := neg (anyV u) :: (List.range 8).map fun a => pos (sV (fx u a))
def defE (u : Nat) : List (List Int) :=
  [[neg (e1V u), pos (sV u)], [neg (e1V u), neg (twoV u)], [pos (e1V u), neg (sV u), pos (twoV u)],
   [neg (e0V u), pos (sV u)], [neg (e0V u), neg (anyV u)], [pos (e0V u), neg (sV u), pos (anyV u)]]
def defU (u : Nat) : List (List Int) :=
  (pairs8.flatMap fun (a, b) => defPair u a b) ++ defTwo u :: ((List.range 8).map (defAny1 u)) ++
    defAny u :: defE u
def famDef : List (List Int) := R256.flatMap defU

def famC4 : List (List Int) :=
  R256.flatMap fun u => pairs8.filterMap fun (a, b) =>
      if u.testBit a || u.testBit b then none
      else some [neg (sV u), neg (sV (fx u a)), neg (sV (fx (fx u a) b)), neg (sV (fx u b))]

/-- 4-cycles and induced 6-cycles of 3-subcubes (implied by degree and levels; kept for propagation) -/
def famCyc : List (List Int) :=
  (R256.flatMap fun u => pairs8.filterMap fun (a, b) =>
      if u.testBit a || u.testBit b then none
      else some [neg (sV u), neg (sV (fx u a)), neg (sV (fx (fx u a) b)), neg (sV (fx u b))]) ++
  (R256.flatMap fun u => triples8.flatMap fun (a, b, c) =>
      if u.testBit a || u.testBit b || u.testBit c then []
      else (List.range 8).filterMap fun x =>
        let m := 2 ^ a + 2 ^ b + 2 ^ c
        let ex := (if x % 2 = 1 then 2 ^ a else 0) + (if x / 2 % 2 = 1 then 2 ^ b else 0) + (if x / 4 % 2 = 1 then 2 ^ c else 0)
        if ex < m - ex then
          some (((List.range 8).filter (fun y => y != x && y != 7 - x)).map fun y =>
            neg (sV (u + (if y % 2 = 1 then 2 ^ a else 0) + (if y / 2 % 2 = 1 then 2 ^ b else 0) + (if y / 4 % 2 = 1 then 2 ^ c else 0))))
        else none)

/-- the 6-subcubes other than copy 0: missing coordinates `a < b`, values `(va, vb)` of them -/
def subcubes : List (List Nat) :=
  pairs8.flatMap fun (a, b) => (List.range 4).filterMap fun v =>
    if a = 6 ∧ b = 7 ∧ v = 0 then none
    else some (R256.filter fun u => u.testBit a == (v % 2 == 1) && u.testBit b == (v / 2 == 1))

def endLits : List Int := R256.flatMap fun u => [pos (e1V u), pos (e0V u)]
def unselLits : List Int := R256.map fun u => neg (sV u)

/-- counters: endpoints ≤ 2c, unselected ≤ 256 - L, every other 6-subcube ≤ k; returns the clause list -/
def famCnt (c L k : Nat) : List (List Int) :=
  let b1 := cbase + 512 * (2 * c)
  let b2 := b1 + 256 * (256 - L)
  atMost cbase (2 * c) endLits ++ atMost b1 (256 - L) unselLits ++
  ((List.range subcubes.length).flatMap fun q =>
    atMost (b2 + q * 256 * k) k ((subcubes.getD q []).map fun u => pos (sV u)))

def famFix (A : Nat) : List (List Int) :=
  (List.range 64).map fun u => if A.testBit u then [pos (sV u)] else [neg (sV u)]

def cubeCnf (c L A k : Nat) : List (List Int) :=
  famFix A ++ famDeg ++ famLvl ++ famDef ++ famCyc ++ famCnt c L k

def cubeCnfNoCyc (c L A k : Nat) : List (List Int) :=
  famFix A ++ famDeg ++ famLvl ++ famDef ++ famCnt c L k

end Dim8Lift.Cube

namespace Dim8Lift.Cube
def cubeCnfC4 (c L A k : Nat) : List (List Int) :=
  famFix A ++ famDeg ++ famLvl ++ famDef ++ famC4 ++ famCnt c L k
end Dim8Lift.Cube
