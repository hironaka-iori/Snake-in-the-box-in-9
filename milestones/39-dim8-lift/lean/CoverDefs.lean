import CoverBridge
import TabDefs
/-! The two cover CNF families and generator facts used by the cover proof. -/
set_option linter.deprecated false
set_option maxRecDepth 200000
namespace Dim8Lift.Tab
open Dim8Lift Dim8Lift.Cnf Dim8Lift.Cube Dim8Lift.Cover Dim8Lift.Sym

def pcN (n m : Nat) : Nat := cnt n (fun u => m.testBit u)

def unsel5 : List Int := (List.range 32).map fun u => neg (cs u)
/-- every Q5 forest with ≥ 15 vertices is one of `blocks` -/
def c5Cnf (blocks : List Nat) : List (List Int) := coverCnf 5 [] [(unsel5, 17)] blocks

def selB : List Int := (List.range 32).map fun u => pos (cs (32 + u))
def unselB : List Int := (List.range 32).map fun u => neg (cs (32 + u))
/-- every Q6 forest with low half `r5`, other half `B`, `29 - |r5| ≤ |B| ≤ |r5|`, is one of `blocks` -/
def c6Cnf (r5 : Nat) (blocks : List Nat) : List (List Int) :=
  coverCnf 6 ((List.range 32).map fun u => (u, r5.testBit u)) [(selB, pcN 32 r5), (unselB, 32 - (29 - pcN 32 r5))] blocks

theorem pres6_F : ∀ c : Fin 36, inB 6 c.val = true → ∀ u : Fin 256, decide (gen c.val u.val < 64) = decide (u.val < 64) := by
  decide
theorem pres5_F : ∀ c : Fin 36, inB 5 c.val = true → ∀ u : Fin 256,
    decide (gen c.val u.val < 32) = decide (u.val < 32) ∧ decide (gen c.val u.val < 64) = decide (u.val < 64) := by
  decide
theorem flip5_F : ∀ u : Fin 256, decide (gen 33 u.val < 32) = decide (32 ≤ u.val ∧ u.val < 64) ∧
    decide (gen 33 u.val < 64) = decide (u.val < 64) := by decide

end Dim8Lift.Tab
