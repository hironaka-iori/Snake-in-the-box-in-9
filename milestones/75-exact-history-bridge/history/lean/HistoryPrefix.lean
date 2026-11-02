import Mathlib.Data.List.Infix
import Mathlib.Data.List.Induction

/-! Longest dictionary suffix recognition, independent of finite graph tables.
Closure under dropLast gives closure under every initial segment. -/
namespace Snake9.History75
variable {α : Type} [DecidableEq α]

def PrefixClosed (D : List (List α)) : Prop :=
  ∀ t ∈ D, t.dropLast ∈ D

def IsLongest (D : List (List α)) (w s : List α) : Prop :=
  s ∈ D ∧ s <:+ w ∧ ∀ t ∈ D, t <:+ w → t.length ≤ s.length

def longest (D : List (List α)) : List α → List α
  | [] => []
  | a :: w => if a :: w ∈ D then a :: w else longest D w

theorem longest_spec (D : List (List α)) (h0 : [] ∈ D) (w : List α) :
    IsLongest D w (longest D w) := by
  induction w with
  | nil => exact ⟨h0, List.suffix_rfl, fun t _ ht => ht.length_le⟩
  | cons a w ih =>
    by_cases hd : a :: w ∈ D
    · simp only [longest, if_pos hd]
      exact ⟨hd, List.suffix_rfl, fun t _ ht => ht.length_le⟩
    · simp only [longest, if_neg hd]
      refine ⟨ih.1, ih.2.1.trans (List.suffix_cons a w), ?_⟩
      intro t ht htw
      have hlen : t.length ≤ w.length := by
        have hle := htw.length_le
        simp only [List.length_cons] at hle
        by_contra hn
        have heq : t = a :: w := htw.eq_of_length (by simp; omega)
        exact hd (heq ▸ ht)
      exact ih.2.2 t ht (List.suffix_of_suffix_length_le htw
        (List.suffix_cons a w) hlen)

theorem longest_unique {D : List (List α)} {w s t : List α}
    (hs : IsLongest D w s) (ht : IsLongest D w t) : s = t := by
  have hst := hs.2.2 t ht.1 ht.2.1
  have hts := ht.2.2 s hs.1 hs.2.1
  exact (List.suffix_of_suffix_length_le hs.2.1 ht.2.1 hts).eq_of_length
    (Nat.le_antisymm hts hst)

theorem suffix_append_one {s w : List α} (hs : s <:+ w) (a : α) :
    s ++ [a] <:+ w ++ [a] := by
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u, (List.append_assoc _ _ _).symm⟩

theorem candidates_append_iff {D : List (List α)} (hc : PrefixClosed D)
    {w s : List α} (hs : IsLongest D w s) (a : α) {t : List α}
    (ht : t ∈ D) : t <:+ w ++ [a] ↔ t <:+ s ++ [a] := by
  constructor
  · intro htw
    by_cases hn : t = []
    · simp [hn]
    · have hdrop : t.dropLast <:+ w := by
        obtain ⟨u, hu⟩ := htw
        refine ⟨u, ?_⟩
        have h := congrArg List.dropLast hu
        simpa [List.dropLast_append_of_ne_nil hn] using h
      have hsuf : t.dropLast <:+ s :=
        List.suffix_of_suffix_length_le hdrop hs.2.1 (hs.2.2 _ (hc t ht) hdrop)
      have hlast : t.getLast hn = a := by
        have h := htw.getLast hn
        simpa using h
      rw [← List.dropLast_concat_getLast hn, hlast]
      exact suffix_append_one hsuf a
  · intro hts
    exact hts.trans (suffix_append_one hs.2.1 a)

theorem update_longest {D : List (List α)} (h0 : [] ∈ D)
    (hc : PrefixClosed D) {w s : List α} (hs : IsLongest D w s) (a : α) :
    IsLongest D (w ++ [a]) (longest D (s ++ [a])) := by
  have h := longest_spec D h0 (s ++ [a])
  refine ⟨h.1, (candidates_append_iff hc hs a h.1).mpr h.2.1, ?_⟩
  intro t ht htw
  exact h.2.2 t ht ((candidates_append_iff hc hs a ht).mp htw)

theorem longest_update_eq {D : List (List α)} (h0 : [] ∈ D)
    (hc : PrefixClosed D) (w : List α) (a : α) :
    longest D (longest D w ++ [a]) = longest D (w ++ [a]) := by
  exact longest_unique (update_longest h0 hc (longest_spec D h0 w) a)
    (longest_spec D h0 (w ++ [a]))

/-- Any maximum-length suffix selector has the same value, including a scan
that ignores the empty word and uses it only as the fallback. -/
theorem maximizing_update_eq {D : List (List α)} (h0 : [] ∈ D)
    (hc : PrefixClosed D) {w s t : List α} (hs : IsLongest D w s)
    (a : α) (ht : IsLongest D (s ++ [a]) t) :
    t = longest D (w ++ [a]) := by
  have h := longest_unique ht (longest_spec D h0 (s ++ [a]))
  rw [h]
  exact longest_unique (update_longest h0 hc hs a) (longest_spec D h0 (w ++ [a]))

def run (D : List (List α)) (w : List α) : List α :=
  w.foldl (fun s a => longest D (s ++ [a])) []

theorem run_is_longest {D : List (List α)} (h0 : [] ∈ D)
    (hc : PrefixClosed D) (w : List α) : IsLongest D w (run D w) := by
  induction w using List.reverseRecOn with
  | nil => exact longest_spec D h0 []
  | append_singleton w a ih =>
    simpa [run, List.foldl_append] using update_longest h0 hc ih a

theorem run_eq_longest {D : List (List α)} (h0 : [] ∈ D)
    (hc : PrefixClosed D) (w : List α) : run D w = longest D w :=
  longest_unique (run_is_longest h0 hc w) (longest_spec D h0 w)

theorem emitted_three_is_last_three {D : List (List α)} (h0 : [] ∈ D)
    (hc : PrefixClosed D) (w : List α) (a : α) (sig : List α)
    (hlen : sig.length = 3) (hemits : sig <:+ run D w ++ [a]) :
    sig = (w ++ [a]).drop ((w ++ [a]).length - 3) := by
  have h := hemits.trans (suffix_append_one (run_is_longest h0 hc w).2.1 a)
  simpa [hlen] using List.suffix_iff_eq_drop.mp h

theorem no_emission_first_two {D : List (List α)} (h0 : [] ∈ D)
    (hc : PrefixClosed D) (w : List α) (a : α) (hshort : w.length < 2)
    (sig : List α) (hlen : sig.length = 3) :
    ¬ sig <:+ run D w ++ [a] := by
  intro h
  have hs := (run_is_longest h0 hc w).2.1.length_le
  have hl := h.length_le
  simp only [List.length_append, List.length_singleton, hlen] at hl
  omega

#print axioms longest_spec
#print axioms longest_unique
#print axioms suffix_append_one
#print axioms candidates_append_iff
#print axioms update_longest
#print axioms longest_update_eq
#print axioms maximizing_update_eq
#print axioms run_is_longest
#print axioms run_eq_longest
#print axioms emitted_three_is_last_three
#print axioms no_emission_first_two
end Snake9.History75
