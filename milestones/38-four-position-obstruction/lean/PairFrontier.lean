import CycleExclusion381
import CycleExclusion382
import CycleExclusion383
import LocalWindowDirBridge
import CorePositivity
import Mathlib.Tactic

namespace Snake9.LocalWindow.PairFrontier
set_option maxHeartbeats 0

def directions : List Nat := [0,1,2,3,4,2,0,3]
def caps (A B : Nat) : List (Nat × Nat) :=
  [(0,A),(0,21),(0,21),(0,21),(0,21),(0,21),(0,B)]

theorem caps_excluded (A B : Nat) (h : Refuted CycleWindow381.window (caps A B))
    {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0)
    (hA : coreAlpha p (r+1) ≤ A) (hB : coreAlpha p (r+7) ≤ B) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply refuted_bridge p (mkPerm [a,b,c,d,e]) r (cs := directions) h
    ⟨rfl,rfl,by decide⟩ (by simp [caps,directions]) hr
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
    have hi7 : i < 7 := by simpa [caps] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [caps, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]

theorem pair_frontier {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0) :
    2 ≤ coreAlpha p (r+1) ∧
    (coreAlpha p (r+1) ≤ 2 → 4 ≤ coreAlpha p (r+7)) ∧
    (coreAlpha p (r+7) ≤ 1 → 9 ≤ coreAlpha p (r+1)) := by
  refine ⟨?_,?_,?_⟩
  · by_contra hh
    exact caps_excluded 1 21 CycleWindow381.refuted p r a b c d e hn h9 hr hd
      (by omega) (coreAlpha_le_21 p (by omega) (by omega))
  · intro hA
    by_contra hh
    exact caps_excluded 2 3 CycleWindow382.refuted p r a b c d e hn h9 hr hd hA (by omega)
  · intro hB
    by_contra hh
    exact caps_excluded 8 1 CycleWindow383.refuted p r a b c d e hn h9 hr hd (by omega) hB

theorem frontier_arithmetic (A B : Nat) (hA : 2 ≤ A) (hB : 1 ≤ B)
    (h2 : A ≤ 2 → 4 ≤ B) (h1 : B ≤ 1 → 9 ≤ A) :
    5 ≤ A+B ∧ 8 ≤ 2*A+B ∧ 15 ≤ A+6*B := by
  by_cases ha : A ≤ 2
  · have := h2 ha; omega
  · by_cases hb : B ≤ 1
    · have := h1 hb; omega
    · omega

theorem pair_inequalities {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0) :
    5 ≤ coreAlpha p (r+1)+coreAlpha p (r+7) ∧
    8 ≤ 2*coreAlpha p (r+1)+coreAlpha p (r+7) ∧
    15 ≤ coreAlpha p (r+1)+6*coreAlpha p (r+7) := by
  obtain ⟨hA,h2,h1⟩ := pair_frontier p r a b c d e hn h9 hr hd
  have hp := FrontierPositivity.core_positive p (r+7) (by omega)
  exact frontier_arithmetic _ _ hA hp h2 h1

theorem singleton_forces_excess {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0)
    (hy : coreAlpha p (r+7) = 1) :
    3 ≤ coreAlpha p (r+1) - min 6 (coreAlpha p (r+1)) := by
  have h := (pair_frontier p r a b c d e hn h9 hr hd).2.2 (by omega)
  omega

theorem occurrence_excess (delta : Nat → Nat) (J : Finset Nat) (N : Nat)
    (hJ : ∀ r ∈ J, r+1 < N) (hdelta : ∀ r ∈ J, 3 ≤ delta (r+1)) :
    3*J.card ≤ ∑ j ∈ Finset.range N, delta j := by
  have hinj : Set.InjOn (fun r : Nat => r+1) (↑J : Set Nat) := by
    intro a ha b hb h
    exact Nat.add_right_cancel h
  have hsub : J.image (fun r => r+1) ⊆ Finset.range N := by
    intro j hj
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hJ r hr)
  calc
    3*J.card = ∑ r ∈ J, (3 : Nat) := by simp [Nat.mul_comm]
    _ ≤ ∑ r ∈ J, delta (r+1) := Finset.sum_le_sum hdelta
    _ = ∑ j ∈ J.image (fun r => r+1), delta j := (Finset.sum_image hinj).symm
    _ ≤ ∑ j ∈ Finset.range N, delta j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)

#print axioms caps_excluded
#print axioms pair_frontier
#print axioms frontier_arithmetic
#print axioms pair_inequalities
#print axioms singleton_forces_excess
#print axioms occurrence_excess
end Snake9.LocalWindow.PairFrontier
