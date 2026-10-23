import CycleExclusion100
import LocalWindowDirBridge
import Mathlib.Tactic

namespace Snake9.LocalWindow.FourPosition
open Tags
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def window := CycleWindow100.window
def directions : List Nat := [0,1,2,3,4,2,0,3]
def bounds : List (Nat × Nat) := [(0,2),(0,21),(0,21),(0,21),(0,3),(0,5),(0,2)]

/-- Only the endpoint counter and four upper counters occur in the core.
Unused counters are replaced by the valid empty endpoint counter. -/
def ctrs : List Ctr := CycleWindow100.ctrs.mapIdx fun i ct =>
  if i ∈ [0,1,9,11,13] then ct else dfltCtr

theorem checked : checkAll CycleWindow100.meaning ctrs window bounds
    CycleWindow100.tags CycleWindow100.raw = true := by decide +kernel

theorem sat : ∀ S E : Nat → Bool,
    Axioms S E window (centresOf window bounds) →
      ∃ τ, cnfTrue τ CycleWindow100.cnf = true :=
  fun S E h => ⟨tau S E CycleWindow100.meaning ctrs,
    sound CycleWindow100.meaning ctrs window bounds CycleWindow100.tags
      CycleWindow100.raw checked S E h⟩

theorem refuted : Refuted window bounds :=
  Tags.refuted_of_sat sat CycleWindow100.unsat

theorem excluded_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + directions.length ≤ m)
    (hP : ∀ j, j < directions.length → P.fwd (dir p (r+j)) = directions.getD j 0)
    (hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) : False :=
  refuted_bridge p P r (cs := directions) refuted ⟨rfl,rfl,by decide⟩ (by decide) hr hP hb

theorem four_position_excluded {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 2) (h5 : coreAlpha p (r+5) ≤ 3)
    (h6 : coreAlpha p (r+6) ≤ 5) (h7 : coreAlpha p (r+7) ≤ 2) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply excluded_in_snake p (mkPerm [a,b,c,d,e]) r hr
  · intro j hj
    have hj8 : j < 8 := by simpa [directions] using hj
    rw [hd j hj8]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 4 (by simp)
    · exact hs 2 (by simp)
    · exact hs 0 (by simp)
    · exact hs 3 (by simp)
  · intro i hi
    have hi7 : i < 7 := by simpa [bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]

theorem four_position_alternative {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0) :
    3 ≤ coreAlpha p (r+1) ∨ 4 ≤ coreAlpha p (r+5) ∨
      6 ≤ coreAlpha p (r+6) ∨ 3 ≤ coreAlpha p (r+7) := by
  by_contra h
  have h1 : coreAlpha p (r+1) ≤ 2 := by omega
  have h5 : coreAlpha p (r+5) ≤ 3 := by omega
  have h6 : coreAlpha p (r+6) ≤ 5 := by omega
  have h7 : coreAlpha p (r+7) ≤ 2 := by omega
  exact four_position_excluded p r a b c d e hn h9 hr hd h1 h5 h6 h7

#print axioms refuted
#print axioms excluded_in_snake
#print axioms four_position_excluded
#print axioms four_position_alternative
end Snake9.LocalWindow.FourPosition
