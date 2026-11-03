import Mathlib.Tactic

namespace Snake9.PathBlock134

/-
The number of true entries is bounded by the number of adjacent pairs with
at least one true entry. An additional unit is needed only for an all-true
list. No distinctness hypothesis is needed for this Boolean counting step.
-/
theorem count_true_le_incident_pairs (l : List Bool) :
    l.count true ≤
      (l.zip (l.drop 1)).countP (fun p => p.1 || p.2) +
        (if l.all id then 1 else 0) := by
  induction l with
  | nil => simp
  | cons b l ih =>
      cases l with
      | nil => cases b <;> simp
      | cons c l =>
          cases b <;> cases c <;> cases h : l.all id <;>
            simp_all [List.count_cons, List.countP_cons] <;> omega

theorem count_true_le_incident_pairs_of_false_mem
    (l : List Bool) (hfalse : false ∈ l) :
    l.count true ≤
      (l.zip (l.drop 1)).countP (fun p => p.1 || p.2) := by
  have h := count_true_le_incident_pairs l
  have hall : l.all id = false := by
    cases hb : l.all id with
    | false => rfl
    | true =>
        have hbad := List.all_eq_true.mp hb false hfalse
        simp at hbad
  simpa [hall] using h

theorem count_true_le_incident_pairs_add_one (l : List Bool) :
    l.count true ≤
      (l.zip (l.drop 1)).countP (fun p => p.1 || p.2) + 1 := by
  have h := count_true_le_incident_pairs l
  cases hall : l.all id <;> simp [hall] at h ⊢ <;> omega

theorem countP_le_incident_pairs {α : Type*} (l : List α) (p : α → Bool) :
    l.countP p ≤
      (l.zip (l.drop 1)).countP (fun e => p e.1 || p e.2) +
        (if l.all p then 1 else 0) := by
  induction l with
  | nil => simp
  | cons b l ih =>
      cases l with
      | nil => cases hb : p b <;> simp [hb]
      | cons c l =>
          cases hb : p b <;> cases hc : p c <;> cases hall : l.all p <;>
            simp_all [List.countP_cons] <;> omega

theorem countP_le_incident_pairs_of_false
    {α : Type*} (l : List α) (p : α → Bool)
    (hfalse : ∃ x ∈ l, p x = false) :
    l.countP p ≤
      (l.zip (l.drop 1)).countP (fun e => p e.1 || p e.2) := by
  have h := countP_le_incident_pairs l p
  obtain ⟨x,hx,hpx⟩ := hfalse
  have hall : l.all p = false := by
    cases hb : l.all p with
    | false => rfl
    | true =>
        have hbad := List.all_eq_true.mp hb x hx
        simp [hpx] at hbad
  simpa [hall] using h

/- Each unordered edge is represented by the finite set of its endpoints. -/
theorem nodup_adjacent_unordered_pairs {α : Type*} [DecidableEq α]
    (l : List α) :
    l.Nodup →
      ((l.zip (l.drop 1)).map (fun e => ({e.1,e.2} : Finset α))).Nodup := by
  induction l with
  | nil => simp
  | cons b l ih =>
      intro hn
      cases l with
      | nil => simp
      | cons c l =>
          have hnot : b ∉ c :: l := (List.nodup_cons.mp hn).1
          have htail : (c :: l).Nodup := (List.nodup_cons.mp hn).2
          change (({b,c} : Finset α) ::
            (((c :: l).zip l).map (fun e => ({e.1,e.2} : Finset α)))).Nodup
          apply List.nodup_cons.mpr
          constructor
          · intro hmem
            obtain ⟨e,he,heq⟩ := List.mem_map.mp hmem
            have hb : b ∈ ({e.1,e.2} : Finset α) := by
              rw [heq]
              simp
            have hfirst : e.1 ∈ c :: l := (List.of_mem_zip he).1
            have hsecond : e.2 ∈ c :: l :=
              List.mem_cons_of_mem c (List.of_mem_zip he).2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with hb | hb
            · exact hnot (hb.symm ▸ hfirst)
            · exact hnot (hb.symm ▸ hsecond)
          · simpa only [List.drop_succ_cons, List.drop_zero] using ih htail

theorem count_incident_pairs_le_card {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Bool) (missing : Finset (Finset α))
    (hn : l.Nodup)
    (hmem : ∀ e ∈ l.zip (l.drop 1),
      (p e.1 || p e.2) = true → ({e.1,e.2} : Finset α) ∈ missing) :
    (l.zip (l.drop 1)).countP (fun e => p e.1 || p e.2) ≤ missing.card := by
  let edges := ((l.zip (l.drop 1)).filter (fun e => p e.1 || p e.2)).map
    (fun e => ({e.1,e.2} : Finset α))
  have hnodup : edges.Nodup := by
    apply List.Nodup.sublist
      (List.Sublist.map (fun e : α × α => ({e.1,e.2} : Finset α))
        List.filter_sublist)
    exact nodup_adjacent_unordered_pairs l hn
  have hsub : edges.toFinset ⊆ missing := by
    intro edge hedge
    obtain ⟨e,he,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hedge)
    obtain ⟨hadj,hinc⟩ := List.mem_filter.mp he
    rw [← heq]
    exact hmem e hadj hinc
  calc
    (l.zip (l.drop 1)).countP (fun e => p e.1 || p e.2) = edges.length := by
      simp [edges, List.countP_eq_length_filter]
    _ = edges.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ missing.card := Finset.card_le_card hsub

theorem countP_le_missing_card {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Bool) (missing : Finset (Finset α))
    (hn : l.Nodup)
    (hmem : ∀ e ∈ l.zip (l.drop 1),
      (p e.1 || p e.2) = true → ({e.1,e.2} : Finset α) ∈ missing) :
    l.countP p ≤ missing.card + (if l.all p then 1 else 0) := by
  exact (countP_le_incident_pairs l p).trans
    (Nat.add_le_add_right (count_incident_pairs_le_card l p missing hn hmem) _)

theorem countP_le_missing_card_of_false {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Bool) (missing : Finset (Finset α))
    (hn : l.Nodup)
    (hmem : ∀ e ∈ l.zip (l.drop 1),
      (p e.1 || p e.2) = true → ({e.1,e.2} : Finset α) ∈ missing)
    (hfalse : ∃ x ∈ l, p x = false) :
    l.countP p ≤ missing.card := by
  exact (countP_le_incident_pairs_of_false l p hfalse).trans
    (count_incident_pairs_le_card l p missing hn hmem)

/-
The remaining geometric application must construct the distinct coordinate
list, prove that its indicated adjacent pairs are missing, and bound the
size of that finite set. No endpoint-occurrence theorem is claimed here.
-/

#print axioms count_true_le_incident_pairs
#print axioms count_true_le_incident_pairs_of_false_mem
#print axioms count_true_le_incident_pairs_add_one
#print axioms countP_le_incident_pairs
#print axioms countP_le_incident_pairs_of_false
#print axioms nodup_adjacent_unordered_pairs
#print axioms count_incident_pairs_le_card
#print axioms countP_le_missing_card
#print axioms countP_le_missing_card_of_false

end Snake9.PathBlock134
