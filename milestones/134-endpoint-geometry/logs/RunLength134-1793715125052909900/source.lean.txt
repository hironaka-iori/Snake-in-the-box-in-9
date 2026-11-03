import PathBlock134

namespace Snake9.RunLength134

/-
A simple path uses at most all available vertices outside the predicate,
plus the missing edges incident to the predicate. If no outside vertex is
available, the usual extra initial vertex contributes one instead.
-/
theorem length_le_outside_card_or_one_add_missing_card
    {α : Type*} [DecidableEq α]
    (l : List α) (U : Finset α) (p : α → Bool)
    (F : Finset (Finset α))
    (hn : l.Nodup)
    (hU : ∀ x ∈ l, x ∈ U)
    (hF : ∀ e ∈ l.zip (l.drop 1),
      (p e.1 || p e.2) = true → ({e.1,e.2} : Finset α) ∈ F) :
    l.length ≤ max 1 ((U.filter (fun x => p x = false)).card) + F.card := by
  let outside := l.filter (fun x => !(p x))
  have hnodup : outside.Nodup :=
    List.Nodup.filter (fun x => !(p x)) hn
  have hsub : outside.toFinset ⊆ U.filter (fun x => p x = false) := by
    intro x hx
    have hx' := List.mem_filter.mp (List.mem_toFinset.mp hx)
    exact Finset.mem_filter.mpr ⟨hU x hx'.1, by simpa using hx'.2⟩
  have hout : l.countP (fun x => !(p x)) ≤
      (U.filter (fun x => p x = false)).card := by
    calc
      l.countP (fun x => !(p x)) = outside.length :=
        List.countP_eq_length_filter
      _ = outside.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
      _ ≤ (U.filter (fun x => p x = false)).card := Finset.card_le_card hsub
  by_cases hfalse : ∃ x ∈ l, p x = false
  · have hin := PathBlock134.countP_le_missing_card_of_false l p F hn hF hfalse
    have hparts : l.length = l.countP p + l.countP (fun x => !(p x)) := by
      simpa using (List.length_eq_countP_add_countP p (l := l))
    have hmax := Nat.le_max_right 1 ((U.filter (fun x => p x = false)).card)
    omega
  · have hall : l.all p = true := by
      apply List.all_eq_true.mpr
      intro x hx
      cases hpx : p x with
      | false => exact False.elim (hfalse ⟨x,hx,hpx⟩)
      | true => rfl
    have heq : l.countP p = l.length :=
      List.countP_eq_length.mpr (List.all_eq_true.mp hall)
    have hin := PathBlock134.countP_le_missing_card l p F hn hF
    have hlength : l.length ≤ F.card + 1 := by
      simpa [hall, heq] using hin
    have hmax := Nat.le_max_left 1 ((U.filter (fun x => p x = false)).card)
    omega

#print axioms length_le_outside_card_or_one_add_missing_card

end Snake9.RunLength134
