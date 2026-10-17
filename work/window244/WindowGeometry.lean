import PathStructure
import BallClauseLogic

namespace Snake9.Window244
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0

theorem endpoint_iff {m : Nat} (p : Snake m) (v : Vertex) :
    BallClauseLogic.Endpoint p v ↔ v = p.vertex 0 ∨ v = p.vertex (Fin.last m) := by
  constructor
  · rintro ⟨⟨i,rfl⟩,hi⟩
    rcases low_degree_index_is_endpoint p i hi with h | h
    · left; exact congrArg p.vertex (Fin.ext h)
    · right; exact congrArg p.vertex (Fin.ext h)
  · intro h
    rcases h with rfl | rfl
    · refine ⟨⟨0,rfl⟩,?_⟩
      rintro a b ⟨i,rfl⟩ ⟨j,rfl⟩ ha hb
      have hi := (path_adj_iff p 0 i).mp ha
      have hj := (path_adj_iff p 0 j).mp hb
      apply congrArg p.vertex
      apply Fin.ext
      simp only [Fin.val_zero] at hi hj
      omega
    · refine ⟨⟨Fin.last m,rfl⟩,?_⟩
      rintro a b ⟨i,rfl⟩ ⟨j,rfl⟩ ha hb
      have hi := (path_adj_iff p (Fin.last m) i).mp ha
      have hj := (path_adj_iff p (Fin.last m) j).mp hb
      apply congrArg p.vertex
      apply Fin.ext
      simp only [Fin.val_last] at hi hj
      omega

theorem neighbor_exists {m : Nat} (p : Snake m) (hm : 0 < m)
    (v : Vertex) (hv : InPath p v) : ∃ w, InPath p w ∧ Adj v w := by
  obtain ⟨i,rfl⟩ := hv
  by_cases hi : i.val < m
  · exact ⟨p.vertex ⟨i.val+1,by omega⟩,⟨_,rfl⟩,
      (path_adj_iff p _ _).mpr (Or.inl rfl)⟩
  · refine ⟨p.vertex ⟨i.val-1,by omega⟩,⟨_,rfl⟩,?_⟩
    apply (path_adj_iff p _ _).mpr
    right; simp only; omega

theorem neighbor_cover {m : Nat} (p : Snake m) (hm : 0 < m) (v : Vertex)
    (ns : List Vertex) (hc : ∀ w, InPath p w → Adj v w → w ∈ ns) :
    ¬ InPath p v ∨ ∃ w ∈ ns, InPath p w := by
  classical
  by_cases hv : InPath p v
  · obtain ⟨w,hw,ha⟩ := neighbor_exists p hm v hv
    exact Or.inr ⟨w,hc w hw ha,hw⟩
  · exact Or.inl hv

theorem other_cover {m : Nat} (p : Snake m) (v excluded : Vertex)
    (ns : List Vertex) (hc : ∀ w, InPath p w → Adj v w → w ≠ excluded → w ∈ ns) :
    ¬ InPath p v ∨ BallClauseLogic.Endpoint p v ∨ ∃ w ∈ ns, InPath p w := by
  classical
  by_cases hv : InPath p v
  · rcases BallClauseLogic.other_neighbor_or_low p v excluded with h | ⟨w,he,hw,ha⟩
    · exact Or.inr (Or.inl ⟨hv,h⟩)
    · exact Or.inr (Or.inr ⟨w,hc w hw ha he,hw⟩)
  · exact Or.inl hv

theorem nodup_subset_length {α : Type} [DecidableEq α] (xs ys : List α)
    (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction ys generalizing xs with
  | nil => have : xs = [] := List.subset_nil.mp hs; simp [this]
  | cons a ys ih =>
    by_cases ha : a ∈ xs
    · have he := List.length_erase_of_mem ha
      have hb := ih (xs.erase a) (hn.erase a) (by
        intro v hv
        obtain ⟨hne,hv⟩ := hn.mem_erase_iff.mp hv
        rcases List.mem_cons.mp (hs hv) with h | h
        · exact False.elim (hne h)
        · exact h)
      have hp := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega
    · have hb := ih xs hn (by
        intro v hv
        rcases List.mem_cons.mp (hs hv) with h | h
        · exact False.elim (ha (h ▸ hv))
        · exact h)
      simp only [List.length_cons]; omega

/-- Every finite set whose members have two distinct neighbours in the set
is forbidden inside an induced path. This includes every recorded cycle cut;
connectedness and a particular cyclic ordering are unnecessary. -/
theorem selected_no_cycle {m : Nat} (p : Snake m) (vs : List Vertex)
    (hne : vs ≠ [])
    (hdegree : ∀ v ∈ vs, ∃ a ∈ vs, ∃ b ∈ vs,
      a ≠ b ∧ Adj v a ∧ Adj v b) :
    ¬ (∀ v ∈ vs, InPath p v) := by
  intro hselected
  have impossible : ∀ n, ∀ i : Fin (m+1), i.val = n → p.vertex i ∈ vs → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i hin hiv
      obtain ⟨a,ha,b,hb,hab,hva,hvb⟩ := hdegree _ hiv
      obtain ⟨j,hj⟩ := hselected a ha
      obtain ⟨k,hk⟩ := hselected b hb
      have hja := (path_adj_iff p i j).mp (by rw [hj]; exact hva)
      have hka := (path_adj_iff p i k).mp (by rw [hk]; exact hvb)
      have hjk : j.val ≠ k.val := by
        intro he
        apply hab
        calc a = p.vertex j := hj.symm
             _ = p.vertex k := congrArg p.vertex (Fin.ext he)
             _ = b := hk
      have hless : j.val < n ∨ k.val < n := by omega
      rcases hless with h | h
      · exact ih j.val h j rfl (by rw [hj]; exact ha)
      · exact ih k.val h k rfl (by rw [hk]; exact hb)
  cases vs with
  | nil => exact hne rfl
  | cons v vs =>
    obtain ⟨i,hi⟩ := hselected v (by simp)
    exact impossible i.val i rfl (by rw [hi]; simp)

/-- The endpoint counter is bounded by two, including paths of length zero.
Positive-degree clauses separately require a nontrivial path. -/
theorem endpoint_count {m : Nat} (p : Snake m) (vs : List Vertex) (hn : vs.Nodup) :
    (vs.filter (fun v => decide (BallClauseLogic.Endpoint p v))).length ≤ 2 := by
  apply Nat.le_trans (nodup_subset_length _ [p.vertex 0, p.vertex (Fin.last m)]
    (hn.sublist (List.filter_sublist)) ?_) (by simp)
  intro v hv
  obtain ⟨_,he⟩ := List.mem_filter.mp hv
  have he : BallClauseLogic.Endpoint p v := of_decide_eq_true he
  rcases (endpoint_iff p v).mp he with h | h <;> simp [h]

/-- Semantics of every cell in the missing-corner counter. -/
theorem threshold_step (n j : Nat) (b : Bool) (hj : 0 < j) :
    (j ≤ n + (if b then 1 else 0)) ↔
      (j ≤ n ∨ (b = true ∧ j - 1 ≤ n)) := by
  cases b <;> simp <;> omega

/-- Four clause templates for s iff a or (b and c). -/
theorem recurrence_clauses (a b c s : Prop) (hs : s ↔ a ∨ (b ∧ c)) :
    (¬a ∨ s) ∧ (¬b ∨ ¬c ∨ s) ∧ (¬s ∨ a ∨ b) ∧ (¬s ∨ a ∨ c) := by
  classical
  rcases Classical.em a with ha | ha
  · have h := hs.mpr (Or.inl ha)
    exact ⟨Or.inr h, Or.inr (Or.inr h), Or.inr (Or.inl ha), Or.inr (Or.inl ha)⟩
  · by_cases hb : b
    · by_cases hc : c
      · have h := hs.mpr (Or.inr ⟨hb,hc⟩)
        exact ⟨Or.inl ha, Or.inr (Or.inr h), Or.inr (Or.inr hb), Or.inr (Or.inr hc)⟩
      · have hns : ¬s := by intro h; rcases hs.mp h with h | h; exact ha h; exact hc h.2
        exact ⟨Or.inl ha, Or.inr (Or.inl hc), Or.inl hns, Or.inl hns⟩
    · have hns : ¬s := by intro h; rcases hs.mp h with h | h; exact ha h; exact hb h.1
      exact ⟨Or.inl ha, Or.inl hb, Or.inl hns, Or.inl hns⟩

#print axioms selected_no_cycle
#print axioms endpoint_count
#print axioms threshold_step
#print axioms recurrence_clauses
end
end Snake9.Window244

