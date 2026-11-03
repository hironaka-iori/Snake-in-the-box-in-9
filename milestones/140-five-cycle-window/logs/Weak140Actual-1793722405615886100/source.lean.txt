import Weak140Semantics
import LocalWindowUnsat.CycleBase140
import DirectionWindowBridge
import Mathlib.Tactic

namespace Snake9.Weak140
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.LocalWindow.CycleBase140 (window)
set_option maxHeartbeats 2000000

theorem actual_canonical_frame {m : Nat} (p : Snake m) (r n : Nat)
    (hr : r+n ≤ m) :
    ∃ u : List Nat, u.Nodup ∧ (∀ d ∈ u, d < 9) ∧ u.length ≤ 9 ∧
      ∀ j, j < n → (canon (dsOf p r n)).getD j 0 < u.length ∧
        u.getD ((canon (dsOf p r n)).getD j 0) 0 = dir p (r+j) := by
  let u := seenAfter [] (dsOf p r n)
  have hu : u.Nodup := seenAfter_nodup [] _ List.nodup_nil
  have hu9 : ∀ d ∈ u, d < 9 := by
    intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  have hulen : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hmem : ∀ j, j < n → (dsOf p r n).getD j 0 ∈ u := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [length_dsOf] using hj)]
    exact List.getElem_mem _
  have hcs : ∀ j, j < n → (canon (dsOf p r n)).getD j 0 < u.length ∧
      u.getD ((canon (dsOf p r n)).getD j 0) 0 = dir p (r+j) := by
    intro j hj
    have hjlen : j < (dsOf p r n).length := by simpa [length_dsOf] using hj
    have e : (canon (dsOf p r n)).getD j 0 = idx u ((dsOf p r n).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hjlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlen]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j hj), ?_⟩
    rw [getD_idx _ _ (hmem j hj), getD_dsOf p hj]
  exact ⟨u, hu, hu9, hulen, hcs⟩



#print axioms actual_canonical_frame

theorem refuted : Refuted window bounds :=
  Tags.refuted_of_sat sat Snake9.LocalWindow.CycleBase140.unsat

theorem actual_refuted {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) : False := by
  obtain ⟨u,hu,hu9,huLen,hcs⟩ := actual_canonical_frame p r 6 hr
  have hsp := mkPerm_spec hu hu9 huLen
  have hP : ∀ j, j < 6 → (mkPerm u).fwd (dir p (r+j)) =
      ([0,1,2,0,3,2] : List Nat).getD j 0 := by
    intro j hj
    obtain ⟨hi,hd⟩ := hcs j hj
    rw [hshape] at hi hd
    rw [← hd]
    exact hsp _ hi
  have hc : Canon window [0,1,2,0,3,2] := ⟨rfl,rfl,by decide⟩
  exact refuted_bridge p (mkPerm u) r refuted hc (by decide) hr hP hb


#print axioms refuted
#print axioms actual_refuted

theorem actual_weak_counts {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (h1 : coreAlpha p (r+1) = 3)
    (h2 : coreAlpha p (r+2) ≤ 5)
    (h3 : coreAlpha p (r+3) = 4)
    (h4 : coreAlpha p (r+4) ≤ 5)
    (h5 : coreAlpha p (r+5) = 3) : False := by
  apply actual_refuted p r hr hshape
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp_all [bounds, Nat.add_assoc]

theorem actual_one_count_ge_six {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (h1 : coreAlpha p (r+1) = 3)
    (h3 : coreAlpha p (r+3) = 4)
    (h5 : coreAlpha p (r+5) = 3) :
    6 ≤ coreAlpha p (r+2) ∨ 6 ≤ coreAlpha p (r+4) := by
  by_contra h
  push_neg at h
  exact actual_weak_counts p r hr hshape h1 (by omega) h3 (by omega) h5

#print axioms actual_weak_counts
#print axioms actual_one_count_ge_six
end Snake9.Weak140
