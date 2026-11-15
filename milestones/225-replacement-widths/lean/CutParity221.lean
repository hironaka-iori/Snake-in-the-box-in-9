import Std

set_option Elab.async false

namespace CutParity221

/-- Disagreements along a Boolean walk starting at the supplied value. -/
def changes (start : Bool) : List Bool → List Bool
  | [] => []
  | next :: tail => (start != next) :: changes next tail

private theorem changes_length (start : Bool) (tail : List Bool) :
    (changes start tail).length = tail.length := by
  induction tail generalizing start with
  | nil => rfl
  | cons next tail ih => simp [changes, ih]

private theorem path_change_parity (start finish : Bool) (middle : List Bool) :
    (changes start (middle ++ [finish])).count true % 2 =
      (if start = finish then 0 else 1) := by
  induction middle generalizing start finish with
  | nil => cases start <;> cases finish <;> simp [changes]
  | cons next tail ih =>
      have h := ih next finish
      cases start <;> cases finish <;> cases next <;>
        simp [changes, List.count_cons] at h ⊢ <;> omega

/-- Returning to the initial Boolean value forces an even number of
disagreements, including the last-to-first edge. -/
theorem closed_cycle_even (start : Bool) (rest : List Bool) :
    (changes start (rest ++ [start])).count true % 2 = 0 := by
  simpa using path_change_parity start start rest

private theorem signed_count_identity (marked cuts : List Bool)
    (same_length : marked.length = cuts.length) :
    (marked.zipWith (fun mark cut : Bool =>
      if mark then (if cut then (1 : Int) else 0)
      else (if cut then (-1 : Int) else 0)) cuts).sum =
      (marked.count true : Int) -
      ((marked.zipWith (fun a b : Bool => a != b) cuts).count true : Int) := by
  induction marked generalizing cuts with
  | nil =>
      cases cuts with
      | nil => simp
      | cons cut tail => simp at same_length
  | cons mark tail ih =>
      cases cuts with
      | nil => simp at same_length
      | cons cut remaining =>
          have equal_tail : tail.length = remaining.length := by
            simpa using same_length
          have h := ih remaining equal_tail
          cases mark <;> cases cut <;>
            simp [List.count_cons] at h ⊢ <;> omega

private theorem no_mismatch_equal (marked cuts : List Bool)
    (same_length : marked.length = cuts.length)
    (zero : (marked.zipWith (fun a b : Bool => a != b) cuts).count true = 0) :
    marked = cuts := by
  induction marked generalizing cuts with
  | nil =>
      cases cuts with
      | nil => rfl
      | cons cut tail => simp at same_length
  | cons mark tail ih =>
      cases cuts with
      | nil => simp at same_length
      | cons cut remaining =>
          have equal_tail : tail.length = remaining.length := by
            simpa using same_length
          cases mark <;> cases cut
          · have h := ih remaining equal_tail (by
              simpa [List.count_cons] using zero)
            exact congrArg (List.cons false) h
          · simp [List.count_cons] at zero
          · simp [List.count_cons] at zero
          · have h := ih remaining equal_tail (by
              simpa [List.count_cons] using zero)
            exact congrArg (List.cons true) h

/-- For an odd marked subset of the edges of a closed Boolean walk,
the marked disagreements less the unmarked disagreements are at most
the number of marked edges minus one. Closure is encoded by the final
copy of start; even disagreement parity is derived rather than assumed. -/
theorem odd_cycle_inequality (start : Bool) (rest marked : List Bool)
    (same_length : marked.length = rest.length + 1)
    (odd : marked.count true % 2 = 1) :
    (marked.zipWith (fun mark cut : Bool =>
      if mark then (if cut then (1 : Int) else 0)
      else (if cut then (-1 : Int) else 0))
      (changes start (rest ++ [start]))).sum ≤
      (marked.count true : Int) - 1 := by
  have lengths : marked.length = (changes start (rest ++ [start])).length := by
    simpa [changes_length] using same_length
  have even := closed_cycle_even start rest
  have positive : 0 <
      (marked.zipWith (fun a b : Bool => a != b)
        (changes start (rest ++ [start]))).count true := by
    by_cases zero : (marked.zipWith (fun a b : Bool => a != b)
        (changes start (rest ++ [start]))).count true = 0
    · have equal := no_mismatch_equal marked (changes start (rest ++ [start]))
        lengths zero
      rw [← equal] at even
      omega
    · omega
  rw [signed_count_identity marked (changes start (rest ++ [start])) lengths]
  omega

#print axioms closed_cycle_even
#print axioms odd_cycle_inequality
end CutParity221
