import Mathlib.Tactic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat

namespace Snake9.IntervalBlocks136

/-
The blocks are constructed by induction. A new least start joins the first
block exactly when its gap to the next start is at most two. Otherwise it
forms a singleton block. No block decomposition is assumed as input.
-/
theorem exists_blocks_of_sorted {β : Type*} (f : Nat → β) (l : List Nat) :
    l.Pairwise (fun u v => u < v) →
    (∀ u ∈ l, ∀ v ∈ l, u < v → f u ≠ f v → u + 3 ≤ v) →
    ∃ B : List (List Nat),
      B.flatten = l ∧
      (∀ b ∈ B, b ≠ []) ∧
      (∀ b ∈ B, ∀ u ∈ b, ∀ v ∈ b, f u = f v) ∧
      (∀ b ∈ B, ∀ e ∈ b.zip (b.drop 1), e.2 ≤ e.1 + 2) ∧
      B.Pairwise (fun b c => ∀ u ∈ b, ∀ v ∈ c, u + 3 ≤ v) := by
  classical
  induction l with
  | nil =>
      intro _ _
      exact ⟨[],by simp⟩
  | cons x xs ih =>
      intro horder hsep
      have hxlt : ∀ y ∈ xs, x < y := (List.pairwise_cons.mp horder).1
      have htail : xs.Pairwise (fun u v => u < v) :=
        (List.pairwise_cons.mp horder).2
      have hseptail : ∀ u ∈ xs, ∀ v ∈ xs,
          u < v → f u ≠ f v → u + 3 ≤ v := by
        intro u hu v hv huv hne
        exact hsep u (List.mem_cons_of_mem x hu)
          v (List.mem_cons_of_mem x hv) huv hne
      obtain ⟨B,hflat,hne,hlabel,hgap,hcross⟩ := ih htail hseptail
      cases B with
      | nil =>
          have hxs : xs = [] := by simpa using hflat.symm
          subst xs
          refine ⟨[[x]],?_,?_,?_,?_,?_⟩ <;> simp
      | cons b bs =>
          cases b with
          | nil => exact False.elim (hne [] (by simp) rfl)
          | cons y ys =>
              have hy : y ∈ xs := by
                rw [← hflat]
                exact List.mem_flatten.mpr ⟨y :: ys,by simp,by simp⟩
              have hxy : x < y := hxlt y hy
              have hheadorder : (y :: (ys ++ bs.flatten)).Pairwise
                  (fun u v => u < v) := by
                have h := htail
                rw [← hflat] at h
                simpa only [List.flatten_cons, List.cons_append] using h
              have hheadcross := (List.pairwise_cons.mp hcross).1
              have hrestcross := (List.pairwise_cons.mp hcross).2
              by_cases hclose : y ≤ x + 2
              · have hsame : f x = f y := by
                  by_contra hdifferent
                  have hfar := hsep x (by simp)
                    y (List.mem_cons_of_mem x hy) hxy hdifferent
                  omega
                refine ⟨(x :: y :: ys) :: bs,?_,?_,?_,?_,?_⟩
                · simpa only [List.flatten_cons, List.cons_append] using
                    congrArg (List.cons x) hflat
                · intro c hc
                  rcases List.mem_cons.mp hc with hc | hc
                  · subst c
                    simp
                  · exact hne c (List.mem_cons_of_mem _ hc)
                · intro c hc u hu v hv
                  rcases List.mem_cons.mp hc with hc | hc
                  · subst c
                    rcases List.mem_cons.mp hu with hu | hu
                    · subst u
                      rcases List.mem_cons.mp hv with hv | hv
                      · subst v
                        rfl
                      · exact hsame.trans (hlabel (y :: ys) (by simp)
                          y (by simp) v hv)
                    · rcases List.mem_cons.mp hv with hv | hv
                      · subst v
                        exact (hlabel (y :: ys) (by simp) u hu y (by simp)).trans
                          hsame.symm
                      · exact hlabel (y :: ys) (by simp) u hu v hv
                  · exact hlabel c (List.mem_cons_of_mem _ hc) u hu v hv
                · intro c hc e he
                  rcases List.mem_cons.mp hc with hc | hc
                  · subst c
                    change e ∈ (x,y) :: ((y :: ys).zip ys) at he
                    rcases List.mem_cons.mp he with he | he
                    · subst e
                      exact hclose
                    · exact hgap (y :: ys) (by simp) e (by
                        simpa only [List.drop_succ_cons, List.drop_zero] using he)
                  · exact hgap c (List.mem_cons_of_mem _ hc) e he
                · apply List.pairwise_cons.mpr
                  refine ⟨?_,hrestcross⟩
                  intro c hc u hu v hv
                  rcases List.mem_cons.mp hu with hu | hu
                  · subst u
                    have hyv := hheadcross c hc y (by simp) v hv
                    omega
                  · exact hheadcross c hc u hu v hv
              · have hfar : x + 3 ≤ y := by omega
                refine ⟨[x] :: (y :: ys) :: bs,?_,?_,?_,?_,?_⟩
                · simpa only [List.flatten_cons, List.singleton_append] using
                    congrArg (List.cons x) hflat
                · intro c hc
                  rcases List.mem_cons.mp hc with hc | hc
                  · subst c
                    simp
                  · exact hne c hc
                · intro c hc u hu v hv
                  rcases List.mem_cons.mp hc with hc | hc
                  · subst c
                    have hu' : u = x := by simpa using hu
                    have hv' : v = x := by simpa using hv
                    rw [hu',hv']
                  · exact hlabel c hc u hu v hv
                · intro c hc e he
                  rcases List.mem_cons.mp hc with hc | hc
                  · subst c
                    simp at he
                  · exact hgap c hc e he
                · apply List.pairwise_cons.mpr
                  refine ⟨?_,hcross⟩
                  intro c hc u hu v hv
                  have hu' : u = x := by simpa using hu
                  subst u
                  have hvflat : v ∈ (((y :: ys) :: bs).flatten) :=
                    List.mem_flatten.mpr ⟨c,hc,hv⟩
                  change v ∈ y :: (ys ++ bs.flatten) at hvflat
                  rcases List.mem_cons.mp hvflat with hvflat | hvflat
                  · subst v
                    exact hfar
                  · have hyv := (List.pairwise_cons.mp hheadorder).1 v hvflat
                    omega

theorem exists_blocks_for_finset {β : Type*} (f : Nat → β) (I : Finset Nat)
    (hsep : ∀ u ∈ I, ∀ v ∈ I, u < v → f u ≠ f v → u + 3 ≤ v) :
    ∃ B : List (List Nat),
      B.flatten = I.sort (· ≤ ·) ∧
      (∀ b ∈ B, b ≠ []) ∧
      (∀ b ∈ B, b.Pairwise (fun u v => u < v)) ∧
      (∀ b ∈ B, ∀ u ∈ b, ∀ v ∈ b, f u = f v) ∧
      (∀ b ∈ B, ∀ e ∈ b.zip (b.drop 1), e.2 ≤ e.1 + 2) ∧
      B.Pairwise (fun b c => ∀ u ∈ b, ∀ v ∈ c, u + 3 ≤ v) := by
  have hsorted : (I.sort (· ≤ ·)).Pairwise (fun u v => u < v) :=
    I.sort_sorted_lt
  have hsepsorted : ∀ u ∈ I.sort (· ≤ ·), ∀ v ∈ I.sort (· ≤ ·),
      u < v → f u ≠ f v → u + 3 ≤ v := by
    intro u hu v hv huv hne
    exact hsep u (by simpa using hu) v (by simpa using hv) huv hne
  obtain ⟨B,hflat,hne,hlabel,hgap,hcross⟩ :=
    exists_blocks_of_sorted f (I.sort (· ≤ ·)) hsorted hsepsorted
  refine ⟨B,hflat,hne,?_,hlabel,hgap,hcross⟩
  have hflatorder : B.flatten.Pairwise (fun u v => u < v) := by
    rw [hflat]
    exact hsorted
  exact (List.pairwise_flatten.mp hflatorder).1

theorem covered_between_members (b : List Nat) :
    b.Pairwise (fun u v => u < v) →
    (∀ e ∈ b.zip (b.drop 1), e.2 ≤ e.1 + 2) →
    ∀ u ∈ b, ∀ v ∈ b, ∀ z, u ≤ z → z ≤ v + 3 →
      ∃ w ∈ b, w ≤ z ∧ z ≤ w + 3 := by
  induction b with
  | nil => simp
  | cons x xs ih =>
      intro horder hgap u hu v hv z huz hzv
      have hxz : x ≤ z := by
        rcases List.mem_cons.mp hu with hu | hu
        · subst u
          exact huz
        · have hxu := (List.pairwise_cons.mp horder).1 u hu
          omega
      by_cases hz : z ≤ x + 3
      · exact ⟨x,by simp,hxz,hz⟩
      · have hvTail : v ∈ xs := by
          rcases List.mem_cons.mp hv with hv | hv
          · subst v
            exact False.elim (hz hzv)
          · exact hv
        cases xs with
        | nil => simp at hvTail
        | cons y ys =>
            have hxy : y ≤ x + 2 := hgap (x,y) (by simp)
            have hyz : y ≤ z := by omega
            have htail := (List.pairwise_cons.mp horder).2
            have hgapTail : ∀ e ∈ (y :: ys).zip ((y :: ys).drop 1),
                e.2 ≤ e.1 + 2 := by
              intro e he
              apply hgap e
              change e ∈ (x,y) :: ((y :: ys).zip ys)
              exact List.mem_cons_of_mem _ (by
                simpa only [List.drop_succ_cons, List.drop_zero] using he)
            obtain ⟨w,hw,hwz,hzw⟩ :=
              ih htail hgapTail y (by simp) v hvTail z hyz hzv
            exact ⟨w,List.mem_cons_of_mem x hw,hwz,hzw⟩

theorem number_of_starts_le_span (b : List Nat) (l r : Nat)
    (hn : b.Nodup) (hbound : ∀ u ∈ b, l ≤ u ∧ u ≤ r) :
    b.length ≤ r - l + 1 := by
  have hsub : b.toFinset ⊆ Finset.Icc l r := by
    intro u hu
    exact Finset.mem_Icc.mpr (hbound u (List.mem_toFinset.mp hu))
  have hcard := Finset.card_le_card hsub
  have hlength := List.toFinset_card_of_nodup hn
  rw [Nat.card_Icc] at hcard
  omega

theorem interval_intersection_card_le_one (l r s t : Nat)
    (hsep : r + 3 ≤ s) :
    ((Finset.Icc l (r + 3)) ∩ (Finset.Icc s (t + 3))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxLeft,hxRight⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyLeft,hyRight⟩ := Finset.mem_inter.mp hy
  have hxUpper := (Finset.mem_Icc.mp hxLeft).2
  have hxLower := (Finset.mem_Icc.mp hxRight).1
  have hyUpper := (Finset.mem_Icc.mp hyLeft).2
  have hyLower := (Finset.mem_Icc.mp hyRight).1
  omega

#print axioms exists_blocks_of_sorted
#print axioms exists_blocks_for_finset
#print axioms covered_between_members
#print axioms number_of_starts_le_span
#print axioms interval_intersection_card_le_one

end Snake9.IntervalBlocks136
