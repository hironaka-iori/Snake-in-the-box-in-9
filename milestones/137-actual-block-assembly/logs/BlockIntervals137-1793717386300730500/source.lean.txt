import IntervalBlocks136
import IntervalCount136

namespace Snake9.BlockIntervals137

theorem head_last_bounds_of_sorted (b : List Nat) :
    b ≠ [] → b.Pairwise (fun u v => u < v) →
    b.headD 0 ∈ b ∧ b.getLastD 0 ∈ b ∧
      ∀ u ∈ b, b.headD 0 ≤ u ∧ u ≤ b.getLastD 0 := by
  induction b with
  | nil => simp
  | cons x xs ih =>
      intro _ hsorted
      cases xs with
      | nil => simp [List.getLastD_cons]
      | cons y ys =>
          have htail := (List.pairwise_cons.mp hsorted).2
          obtain ⟨_,hlast,hbounds⟩ := ih (by simp) htail
          have hlastEq : (x :: y :: ys).getLastD 0 =
              (y :: ys).getLastD 0 := by
            simp only [List.getLastD_cons]
          refine ⟨by simp,?_,?_⟩
          · rw [hlastEq]
            exact List.mem_cons_of_mem x hlast
          · intro u hu
            constructor
            · change x ≤ u
              rcases List.mem_cons.mp hu with hu | hu
              · subst u
                exact Nat.le_refl _
              · exact Nat.le_of_lt ((List.pairwise_cons.mp hsorted).1 u hu)
            · rw [hlastEq]
              rcases List.mem_cons.mp hu with hu | hu
              · subst u
                have hxy := (List.pairwise_cons.mp hsorted).1 y (by simp)
                have hyLast := (hbounds y (by simp)).2
                omega
              · exact (hbounds u hu).2

theorem exists_blocks_with_intervals {β : Type*}
    (f : Nat → β) (I : Finset Nat)
    (hsep : ∀ u ∈ I, ∀ v ∈ I, u < v → f u ≠ f v → u + 3 ≤ v) :
    ∃ B : List (List Nat),
      B.flatten = I.sort (· ≤ ·) ∧
      (∀ b ∈ B, b ≠ []) ∧
      (∀ b ∈ B, b.Pairwise (fun u v => u < v)) ∧
      (∀ b ∈ B, ∀ u ∈ b, ∀ v ∈ b, f u = f v) ∧
      (∀ b ∈ B, b.headD 0 ∈ b ∧ b.getLastD 0 ∈ b) ∧
      (∀ b ∈ B, ∀ u ∈ b, b.headD 0 ≤ u ∧ u ≤ b.getLastD 0) ∧
      B.Pairwise (fun b c => b.getLastD 0 + 3 ≤ c.headD 0) ∧
      (∀ b ∈ B, ∀ z ∈ Finset.Icc (b.headD 0) (b.getLastD 0 + 3),
        ∃ w ∈ b, w ≤ z ∧ z ≤ w + 3) ∧
      (I.Nonempty → I.card + 2 * B.length + 1 ≤
        ((B.map (fun b => Finset.Icc (b.headD 0) (b.getLastD 0 + 3))).toFinset.biUnion id).card) := by
  obtain ⟨B,hflat,hne,hsorted,hlabel,hgap,hcross⟩ :=
    IntervalBlocks136.exists_blocks_for_finset f I hsep
  have hends : ∀ b ∈ B, b.headD 0 ∈ b ∧ b.getLastD 0 ∈ b := by
    intro b hb
    have h := head_last_bounds_of_sorted b (hne b hb) (hsorted b hb)
    exact ⟨h.1,h.2.1⟩
  have hbounds : ∀ b ∈ B, ∀ u ∈ b,
      b.headD 0 ≤ u ∧ u ≤ b.getLastD 0 := by
    intro b hb
    exact (head_last_bounds_of_sorted b (hne b hb) (hsorted b hb)).2.2
  have hintervalSep : B.Pairwise
      (fun b c => b.getLastD 0 + 3 ≤ c.headD 0) := by
    apply List.Pairwise.imp_of_mem ?_ hcross
    intro b c hb hc hbc
    exact hbc (b.getLastD 0) (hends b hb).2
      (c.headD 0) (hends c hc).1
  have hcoverage : ∀ b ∈ B,
      ∀ z ∈ Finset.Icc (b.headD 0) (b.getLastD 0 + 3),
        ∃ w ∈ b, w ≤ z ∧ z ≤ w + 3 := by
    intro b hb z hz
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hz
    exact IntervalBlocks136.covered_between_members b (hsorted b hb) (hgap b hb)
      (b.headD 0) (hends b hb).1 (b.getLastD 0) (hends b hb).2 z hlo hhi
  refine ⟨B,hflat,hne,hsorted,hlabel,hends,hbounds,hintervalSep,hcoverage,?_⟩
  intro hI
  have hB : B ≠ [] := by
    intro he
    obtain ⟨u,hu⟩ := hI
    have huFlat : u ∈ B.flatten := by
      rw [hflat]
      simpa using hu
    rw [he] at huFlat
    simp at huFlat
  have hnodup : ∀ b ∈ B, b.Nodup := by
    intro b hb
    change b.Pairwise (fun u v => u ≠ v)
    exact (hsorted b hb).imp (fun h => Nat.ne_of_lt h)
  have hcount := IntervalCount136.starts_add_two_blocks_add_one_le_union B
    (fun b => b.headD 0) (fun b => b.getLastD 0)
    hB hnodup hne hbounds hintervalSep
  simpa only [hflat, Finset.length_sort] using hcount

#print axioms head_last_bounds_of_sorted
#print axioms exists_blocks_with_intervals

end Snake9.BlockIntervals137
