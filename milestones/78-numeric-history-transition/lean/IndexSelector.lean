import NumericHistory
import Mathlib.Tactic

namespace Snake9.History78
open Snake9.History75 Snake9.History77

def eligible (D : List (List Nat)) (w : List Nat) (i : Nat) : Prop :=
  D.getD i [] ≠ [] ∧ D.getD i [] <:+ w

instance (D : List (List Nat)) (w : List Nat) (i : Nat) :
    Decidable (eligible D w i) := inferInstanceAs (Decidable (_ ∧ _))

/-- Increasing-index scan with strict improvement; ties retain the earlier index. -/
def scan (D : List (List Nat)) (w : List Nat) : List Nat → Nat → Nat
  | [], best => best
  | i :: rest, best => scan D w rest
      (if eligible D w i ∧ (D.getD best []).length < (D.getD i []).length
       then i else best)

theorem scan_spec (D : List (List Nat)) (w : List Nat) (ids : List Nat)
    (hids : ∀ i ∈ ids, i < D.length) (best : Nat)
    (hb : best < D.length) (hs : D.getD best [] <:+ w) :
    scan D w ids best < D.length ∧
    D.getD (scan D w ids best) [] <:+ w ∧
    (D.getD best []).length ≤ (D.getD (scan D w ids best) []).length ∧
    ∀ i ∈ ids, eligible D w i →
      (D.getD i []).length ≤ (D.getD (scan D w ids best) []).length := by
  induction ids generalizing best with
  | nil => exact ⟨hb, hs, Nat.le_refl _, fun i hi _ => False.elim (List.not_mem_nil hi)⟩
  | cons i ids ih =>
    have hit : ∀ j ∈ ids, j < D.length := fun j hj => hids j (by simp [hj])
    by_cases h : eligible D w i ∧ (D.getD best []).length < (D.getD i []).length
    · simp only [scan, if_pos h]
      have hr := ih hit i (hids i (by simp)) h.1.2
      refine ⟨hr.1, hr.2.1, Nat.le_trans (Nat.le_of_lt h.2) hr.2.2.1, ?_⟩
      intro j hj he
      rcases List.mem_cons.mp hj with heq | hj
      · subst j; exact hr.2.2.1
      · exact hr.2.2.2 j hj he
    · simp only [scan, if_neg h]
      have hr := ih hit best hb hs
      refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_⟩
      intro j hj he
      rcases List.mem_cons.mp hj with heq | hj
      · subst j
        have hi : (D.getD i []).length ≤ (D.getD best []).length := by
          by_contra hn
          exact h ⟨he, by omega⟩
        exact Nat.le_trans hi hr.2.2.1
      · exact hr.2.2.2 j hj he

def selectIndex (D : List (List Nat)) (w : List Nat) : Nat :=
  scan D w (List.range D.length) 0

theorem getD_mem (D : List (List Nat)) (i : Nat) (hi : i < D.length) :
    D.getD i [] ∈ D := by
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using
    (List.getElem_mem hi : D[i] ∈ D)

theorem selectIndex_spec (D : List (List Nat)) (w : List Nat)
    (hn : 0 < D.length) (h0 : D.getD 0 [] = []) :
    selectIndex D w < D.length ∧
    IsLongest D w (D.getD (selectIndex D w) []) := by
  have hr := scan_spec D w (List.range D.length)
    (fun i hi => List.mem_range.mp hi) 0 hn (by rw [h0]; simp)
  refine ⟨hr.1, getD_mem D _ hr.1, hr.2.1, ?_⟩
  intro t ht hs
  by_cases he : t = []
  · simp [he]
  · have hi := List.idxOf_lt_length ht
    have hd := dictionary_index_decode ht ([] : List Nat)
    have hq : eligible D w (D.idxOf t) := by
      simpa only [eligible, hd] using And.intro he hs
    have bound := hr.2.2.2 (D.idxOf t) (List.mem_range.mpr hi) hq
    simpa only [hd] using bound

theorem eligible_slice_iff (D : List (List Nat)) (w : List Nat) (i : Nat) :
    eligible D w i ↔ D.getD i [] ≠ [] ∧
      (D.getD i []).length ≤ w.length ∧
      w.drop (w.length - (D.getD i []).length) = D.getD i [] := by
  constructor
  · intro h
    exact ⟨h.1, h.2.length_le, (List.suffix_iff_eq_drop.mp h.2).symm⟩
  · rintro ⟨hn, _, hd⟩
    exact ⟨hn, List.suffix_iff_eq_drop.mpr hd.symm⟩

theorem selectIndex_longest (w : List Nat) :
    IsLongest prefixes w (prefixes.getD (selectIndex prefixes w) []) :=
  (selectIndex_spec prefixes w (by rw [prefixes_length]; omega) rfl).2

theorem selectIndex_lt (w : List Nat) : selectIndex prefixes w < 75 := by
  have h := (selectIndex_spec prefixes w (by rw [prefixes_length]; omega) rfl).1
  simpa only [prefixes_length] using h

theorem prefix_getD_injective (i j : Nat) (hi : i < 75) (hj : j < 75)
    (h : prefixes.getD i [] = prefixes.getD j []) : i = j := by
  have hi' : i < prefixes.length := by simpa only [prefixes_length] using hi
  have hj' : j < prefixes.length := by simpa only [prefixes_length] using hj
  have hg : prefixes.get ⟨i,hi'⟩ = prefixes.get ⟨j,hj'⟩ := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
      List.getElem?_eq_getElem hj'] using h
  exact congrArg Fin.val (prefix_index_unique _ _ hg)

theorem selectIndex_eq_history (w : List Nat) :
    selectIndex prefixes w = historyIndex w := by
  apply prefix_getD_injective _ _ (selectIndex_lt w) (history_index_lt w)
  rw [history_decode]
  exact longest_unique (selectIndex_longest w) (exact_history_invariant w)

#print axioms scan_spec
#print axioms getD_mem
#print axioms selectIndex_spec
#print axioms eligible_slice_iff
#print axioms selectIndex_longest
#print axioms selectIndex_lt
#print axioms prefix_getD_injective
#print axioms selectIndex_eq_history
end Snake9.History78
