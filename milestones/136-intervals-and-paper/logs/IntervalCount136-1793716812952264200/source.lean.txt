import IntervalBlocks136

namespace Snake9.IntervalCount136

/-
The first estimate applies to any ordered finite sets of natural numbers.
It also allows empty sets; no nonemptiness hypothesis is needed here.
-/
theorem sum_card_le_union_card_add_length_sub_one (L : List (Finset Nat)) :
    L.Pairwise (fun A B => ∀ x ∈ A, ∀ y ∈ B, x ≤ y) →
    (L.map Finset.card).sum ≤
      (L.toFinset.biUnion id).card + (L.length - 1) := by
  induction L with
  | nil => simp
  | cons A L ih =>
      intro horder
      cases L with
      | nil => simp
      | cons B bs =>
          let U := ((B :: bs).toFinset).biUnion id
          have hhead := (List.pairwise_cons.mp horder).1
          have htail := (List.pairwise_cons.mp horder).2
          have hcross : ∀ x ∈ A, ∀ y ∈ U, x ≤ y := by
            intro x hx y hy
            obtain ⟨C,hC,hyC⟩ := Finset.mem_biUnion.mp hy
            exact hhead C (List.mem_toFinset.mp hC) x hx y hyC
          have hinter : (A ∩ U).card ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro x hx y hy
            obtain ⟨hxA,hxU⟩ := Finset.mem_inter.mp hx
            obtain ⟨hyA,hyU⟩ := Finset.mem_inter.mp hy
            exact Nat.le_antisymm (hcross x hxA y hyU) (hcross y hyA x hxU)
          have htailbound : ((B :: bs).map Finset.card).sum ≤
              U.card + ((B :: bs).length - 1) := ih htail
          have hunion := Finset.card_union_add_card_inter A U
          have hlength : 1 ≤ (B :: bs).length := by simp
          have hsum : A.card + ((B :: bs).map Finset.card).sum ≤
              (A ∪ U).card + (B :: bs).length := by
            omega
          simpa [U] using hsum

theorem starts_add_three_blocks_le_interval_card_sum
    (B : List (List Nat)) (lo hi : List Nat → Nat) :
    (∀ b ∈ B, b.Nodup) →
    (∀ b ∈ B, b ≠ []) →
    (∀ b ∈ B, ∀ u ∈ b, lo b ≤ u ∧ u ≤ hi b) →
    B.flatten.length + 3 * B.length ≤
      (B.map (fun b => (Finset.Icc (lo b) (hi b + 3)).card)).sum := by
  induction B with
  | nil => simp
  | cons b B ih =>
      intro hn hne hbound
      have htail := ih
        (fun c hc => hn c (List.mem_cons_of_mem b hc))
        (fun c hc => hne c (List.mem_cons_of_mem b hc))
        (fun c hc => hbound c (List.mem_cons_of_mem b hc))
      obtain ⟨u,hu⟩ := List.exists_mem_of_ne_nil b (hne b (by simp))
      have hlohi : lo b ≤ hi b :=
        (hbound b (by simp) u hu).1.trans (hbound b (by simp) u hu).2
      have hstarts := IntervalBlocks136.number_of_starts_le_span b (lo b) (hi b)
        (hn b (by simp)) (hbound b (by simp))
      have hsingle : b.length + 3 ≤ (Finset.Icc (lo b) (hi b + 3)).card := by
        rw [Nat.card_Icc]
        omega
      simp only [List.flatten_cons, List.length_append, List.length_cons,
        List.map_cons, List.sum_cons]
      omega

theorem expanded_intervals_pairwise
    (B : List (List Nat)) (lo hi : List Nat → Nat)
    (hsep : B.Pairwise (fun b c => hi b + 3 ≤ lo c)) :
    (B.map (fun b => Finset.Icc (lo b) (hi b + 3))).Pairwise
      (fun A C => ∀ x ∈ A, ∀ y ∈ C, x ≤ y) := by
  apply List.pairwise_map.mpr
  apply hsep.imp
  intro b c hbc x hx y hy
  have hxUpper := (Finset.mem_Icc.mp hx).2
  have hyLower := (Finset.mem_Icc.mp hy).1
  omega

theorem starts_add_two_blocks_add_one_le_union
    (B : List (List Nat)) (lo hi : List Nat → Nat)
    (hB : B ≠ [])
    (hn : ∀ b ∈ B, b.Nodup)
    (hne : ∀ b ∈ B, b ≠ [])
    (hbound : ∀ b ∈ B, ∀ u ∈ b, lo b ≤ u ∧ u ≤ hi b)
    (hsep : B.Pairwise (fun b c => hi b + 3 ≤ lo c)) :
    B.flatten.length + 2 * B.length + 1 ≤
      ((B.map (fun b => Finset.Icc (lo b) (hi b + 3))).toFinset.biUnion id).card := by
  have hstarts := starts_add_three_blocks_le_interval_card_sum B lo hi hn hne hbound
  have hintervals := expanded_intervals_pairwise B lo hi hsep
  have hunion := sum_card_le_union_card_add_length_sub_one
    (B.map (fun b => Finset.Icc (lo b) (hi b + 3))) hintervals
  have hunion' :
      (B.map (fun b => (Finset.Icc (lo b) (hi b + 3)).card)).sum ≤
        ((B.map (fun b => Finset.Icc (lo b) (hi b + 3))).toFinset.biUnion id).card +
          (B.length - 1) := by
    simpa only [List.map_map, List.length_map, Function.comp_def] using hunion
  have hlength : 1 ≤ B.length := by
    cases B with
    | nil => exact False.elim (hB rfl)
    | cons b bs => simp
  omega

#print axioms sum_card_le_union_card_add_length_sub_one
#print axioms starts_add_three_blocks_le_interval_card_sum
#print axioms expanded_intervals_pairwise
#print axioms starts_add_two_blocks_add_one_le_union

end Snake9.IntervalCount136
