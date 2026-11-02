import IntervalGuards

namespace Snake9.History84
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.History77 Snake9.GraphInterpretation74
set_option maxHeartbeats 2000000

theorem canonGo_take_exact (ds seen : List Nat) (k : Nat) :
    (canonGo seen ds).take k = canonGo seen (ds.take k) := by
  induction ds generalizing seen k with
  | nil => simp [canonGo]
  | cons a ds ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simpa only [canonGo, List.take_succ_cons] using
        (congrArg (List.cons (idx seen a)) (ih (if a ∈ seen then seen else seen ++ [a]) k))

theorem canon_take_exact (ds : List Nat) (k : Nat) :
    (canon ds).take k = canon (ds.take k) := canonGo_take_exact ds [] k

theorem canonical_window_slice {m : Nat} (p : Snake m) (r n s w : Nat)
    (hr : r+n ≤ m) (hs : s+w ≤ n) :
    canon (((canon (dsOf p r n)).drop s).take w) =
      canon (dsOf p (r+s) w) := by
  rw [← canon_canon_take, canon_canon_drop, canon_canon_take,
    dsOf_slice p r n s w hr hs]

theorem readDirections_length {m : Nat} (p : Snake m) (r : Nat) :
    (readDirections p r).length = r := by simp [readDirections]

theorem readDirections_last_three {m : Nat} (p : Snake m) (r : Nat) (hr : 2 ≤ r) :
    (readDirections p (r+1)).drop (r-2) =
      [directionId p (r-2), directionId p (r-1), directionId p r] := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ s =>
      have h := List.drop_left' (l₂ :=
        [directionId p s, directionId p (s+1), directionId p (s+2)])
        (readDirections_length p s)
      simpa [Nat.succ_eq_add_one, readDirections_succ, List.append_assoc, Nat.add_assoc] using h

theorem emitted_three_actual {m : Nat} (p : Snake m) (r : Nat) (sig : List Nat)
    (hlen : sig.length = 3)
    (hemit : sig <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++ [directionId p r]) :
    2 ≤ r ∧ sig = [directionId p (r-2), directionId p (r-1), directionId p r] := by
  have he : sig <:+ Snake9.History75.run Snake9.History75.prefixes
      (readDirections p r) ++ [directionId p r] := by
    simpa only [actualHistory, history_decode] using hemit
  have hr : 2 ≤ r := by
    by_contra h
    exact Snake9.History75.no_emission_first_two Snake9.History75.prefixes_empty
      Snake9.History75.prefixes_closed (readDirections p r) (directionId p r)
      (by rw [readDirections_length]; omega) sig hlen he
  have h := Snake9.History75.emitted_three_is_last_three Snake9.History75.prefixes_empty
    Snake9.History75.prefixes_closed (readDirections p r) (directionId p r) sig hlen he
  rw [← readDirections_succ, readDirections_length] at h
  have hi : r+1-3 = r-2 := by omega
  rw [hi, readDirections_last_three p r hr] at h
  exact ⟨hr, h⟩

theorem emitted_three_canonical_slices {m : Nat} (p : Snake m) (r : Nat)
    (sig : List Nat) (hr : r+9 ≤ m) (hlen : sig.length = 3)
    (hemit : sig <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++ [directionId p r]) :
    2 ≤ r ∧ ∀ j, j < 3 →
      canon (((canon (dsOf p (r-2) 11)).drop j).take 9) =
        extensions.getD (sig.getD j 0) [] := by
  obtain ⟨hr2, hsig⟩ := emitted_three_actual p r sig hlen hemit
  refine ⟨hr2, ?_⟩
  intro j hj
  rw [canonical_window_slice p (r-2) 11 j 9 (by omega) (by omega), hsig]
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
    rw [direction_decode p _ (by omega)] <;> congr 2 <;> omega

#print axioms canonGo_take_exact
#print axioms canon_take_exact
#print axioms canonical_window_slice
#print axioms readDirections_length
#print axioms readDirections_last_three
#print axioms emitted_three_actual
#print axioms emitted_three_canonical_slices
end Snake9.History84
