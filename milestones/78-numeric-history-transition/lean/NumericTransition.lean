import IndexSelector
import HistoryShape

namespace Snake9.History78
open Snake9.History75 Snake9.History77 Snake9.Direction77

def builderNext (q a : Nat) : Nat :=
  selectIndex prefixes (prefixes.getD q [] ++ [a])

theorem builderNext_lt (q a : Nat) : builderNext q a < 75 :=
  selectIndex_lt _

theorem run_append (w : List Nat) (a : Nat) :
    run prefixes (w ++ [a]) = longest prefixes (run prefixes w ++ [a]) := by
  simp [run, List.foldl_append]

theorem numeric_history_update (w : List Nat) (a : Nat) :
    builderNext (historyIndex w) a = historyIndex (w ++ [a]) := by
  unfold builderNext
  rw [history_decode, selectIndex_eq_history]
  unfold historyIndex
  rw [run_eq_longest prefixes_empty prefixes_closed, ← run_append]

theorem actual_history_update {m : Nat} (p : Snake m) (r : Nat) :
    builderNext (actualHistory p r) (directionId p r) = actualHistory p (r+1) := by
  unfold actualHistory
  rw [readDirections_succ]
  exact numeric_history_update _ _

theorem candidate_tie_unique (w : List Nat) (i j : Nat)
    (hi : i < 75) (hj : j < 75)
    (his : prefixes.getD i [] <:+ w) (hjs : prefixes.getD j [] <:+ w)
    (hlen : (prefixes.getD i []).length = (prefixes.getD j []).length) : i = j := by
  apply prefix_getD_injective i j hi hj
  exact (List.suffix_of_suffix_length_le his hjs (Nat.le_of_eq hlen)).eq_of_length hlen

/-- A maximum returned by the builder's candidate selection has this exact index. -/
theorem maximum_index_is_selector (w : List Nat) (i : Nat) (hi : i < 75)
    (hs : prefixes.getD i [] <:+ w)
    (hmax : ∀ j, j < 75 → eligible prefixes w j →
      (prefixes.getD j []).length ≤ (prefixes.getD i []).length) :
    selectIndex prefixes w = i := by
  apply prefix_getD_injective _ _ (selectIndex_lt w) hi
  apply longest_unique (selectIndex_longest w)
  refine ⟨getD_mem prefixes i (by simpa only [prefixes_length] using hi), hs, ?_⟩
  intro t ht hts
  by_cases he : t = []
  · simp [he]
  · have hj := List.idxOf_lt_length ht
    have hd := dictionary_index_decode ht ([] : List Nat)
    have bound := hmax (prefixes.idxOf t) (by simpa only [prefixes_length] using hj)
      (by simpa only [eligible, hd] using And.intro he hts)
    simpa only [hd] using bound

theorem no_candidates_fallback (w : List Nat)
    (hn : ∀ j, j < 75 → ¬ eligible prefixes w j) : selectIndex prefixes w = 0 := by
  apply maximum_index_is_selector w 0 (by omega)
  · change ([] : List Nat) <:+ w
    simp
  · intro j hj he
    exact False.elim (hn j hj he)

theorem builder_target_shape {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m)
    (hq : builderNext (actualHistory p r) (directionId p r) ≠ 0) :
    recordedCompatible.getD (builderNext (actualHistory p r) (directionId p r)) 0 =
      targetId (directionId p r) := by
  rw [actual_history_update] at hq ⊢
  exact actual_target_history_filter p r hr hq

#print axioms builderNext_lt
#print axioms run_append
#print axioms numeric_history_update
#print axioms actual_history_update
#print axioms candidate_tie_unique
#print axioms maximum_index_is_selector
#print axioms no_candidates_fallback
#print axioms builder_target_shape
end Snake9.History78
