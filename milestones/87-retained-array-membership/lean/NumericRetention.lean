import RetainedPredicates

/-! Executable bounded acceptance predicates. Coverage by the saved rows is separate. -/
namespace Snake9.Retained87
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.History78 Snake9.GraphWalk78
open Snake9.GraphInterpretation75
open Snake9.Guards79 Snake9.ShortRules81 Snake9.History84 Snake9.Reference85
set_option maxHeartbeats 2000000

def referenceForwardB (ds : List Nat) (code s : Nat) (k : Key) : Bool :=
  (canon ((ds.drop (s+2)).take (k.2.length+1)) == k.1) &&
    (code / 6^(6-s-k.2.length) % 6^k.2.length == encodeCounts k.2 0)

def referenceReverseB (ds : List Nat) (code s : Nat) (k : Key) : Bool :=
  (canon (((ds.drop (s+2)).take (k.2.length+1)).reverse) == k.1) &&
    (code / 6^(6-s-k.2.length) % 6^k.2.length == encodeCounts k.2.reverse 0)

def referenceKeep (ds : List Nat) (code : Nat) : Bool :=
  referenceKeys.all fun k => (List.range 7).all fun s =>
    if s+k.2.length ≤ 6 then !(referenceForwardB ds code s k || referenceReverseB ds code s k)
    else true

def encodedBadB (test : CountTest) (f : Nat → Nat) : Bool :=
  match test with
  | .caps bounds => bounds.all (fun b => decide (f b.1 ≤ b.2))
  | .sum positions cap => decide ((positions.map f).sum ≤ cap) &&
      positions.all (fun j => decide (f j < 6))

def shortHitB (ds : List Nat) (code offset : Nat) (reverse : Bool)
    (rule : List Nat × CountTest) : Bool :=
  decide (offset+rule.1.length ≤ 9) &&
    (rule.2.positions.all (fun j => decide
      (3 ≤ offset+orientedPosition rule.1.length reverse j ∧
       offset+orientedPosition rule.1.length reverse j ≤ 8)) &&
    ((canon (if reverse then ((ds.drop offset).take rule.1.length).reverse
      else (ds.drop offset).take rule.1.length) == rule.1) &&
    encodedBadB rule.2 (fun j => digit code
      (offset+orientedPosition rule.1.length reverse j-3))))

def shortKeep (ds : List Nat) (code : Nat) : Bool :=
  shortRules.all fun rule => (List.range 10).all fun offset =>
    [false,true].all fun reverse => !shortHitB ds code offset reverse rule

def historyHitB (q di code : Nat) (rule : List Nat × Nat) : Bool :=
  let hist := Snake9.History75.prefixes.getD q [] ++ [di]
  decide (3 ≤ hist.length) &&
    ((hist.drop (hist.length-3) == rule.1) && decide (digit code rule.2 ≤ 2))

def historyKeep (q di code : Nat) : Bool :=
  historyRules.all fun rule => !historyHitB q di code rule

def intervalHitB (code s w : Nat) (reverse : Bool) (bounds : List (Nat × Nat)) : Bool :=
  (List.range bounds.length).all fun i => decide
    ((bounds.getD i (0,21)).1 ≤ digit code (s + if reverse then w-1-i else i) ∧
      digit code (s + if reverse then w-1-i else i) ≤ (bounds.getD i (0,21)).2)

def intervalRuleHitB (ds : List Nat) (code s : Nat)
    (key : List Nat × List (Nat × Nat)) : Bool :=
  ((canon ((ds.drop (s+2)).take 5) == key.1) && intervalHitB code s 4 false key.2) ||
    ((canon (((ds.drop (s+2)).take 5).reverse) == key.1) && intervalHitB code s 4 true key.2)

def intervalKeep (ds : List Nat) (code : Nat) : Bool :=
  intervalKeys72.all fun key => (List.range 3).all fun s => !intervalRuleHitB ds code s key

def rangeCompatibilityKeep (ds : List Nat) (q code : Nat) : Bool :=
  let di := extensions.idxOf ds
  let nq := builderNext q di
  decide (q < 75) && (decide (di < 505) && (decide (code < 46656) &&
    ((q == 0 || recordedCompatible.getD q 0 == sourceId di) &&
     (nq == 0 || recordedCompatible.getD nq 0 == targetId di))))

def wordKeep (ds : List Nat) (q code : Nat) : Bool :=
  rangeCompatibilityKeep ds q code && (referenceKeep ds code &&
    (shortKeep ds code && (historyKeep q (extensions.idxOf ds) code && intervalKeep ds code)))

def numericKeep (q di code : Nat) : Bool := wordKeep (extensions.getD di []) q code

theorem boolNot_of_no_true (b : Bool) (h : b = true → False) : (!b) = true := by
  cases b <;> simp_all

theorem encodedBadB_iff (test : CountTest) (f : Nat → Nat) :
    encodedBadB test f = true ↔ encodedBad test f := by
  cases test <;> simp [encodedBadB, encodedBad, List.all_eq_true]

theorem intervalHitB_iff (code s w : Nat) (reverse : Bool) (bounds : List (Nat × Nat)) :
    intervalHitB code s w reverse bounds = true ↔ intervalHit code s w reverse bounds := by
  simp [intervalHitB, intervalHit, List.all_eq_true]

theorem referenceKeep_of_actual {m : Nat} (p : Snake m) (r : Nat)
    (h : ActualReferenceFilters p r) : referenceKeep (canon (dsOf p r 9)) (sixCode p r) = true := by
  apply List.all_eq_true.mpr
  intro k hk
  apply List.all_eq_true.mpr
  intro s hs
  by_cases hf : s+k.2.length ≤ 6
  · simp only [hf, ↓reduceIte]
    apply boolNot_of_no_true
    intro hh
    have hh' : forwardHit p r s k ∨ reverseHit p r s k := by
      simpa only [referenceForwardB, referenceReverseB, forwardHit, reverseHit,
        Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] using hh
    rcases hh' with hh' | hh'
    · exact (h k hk s hf).1 hh'
    · exact (h k hk s hf).2 hh'
  · simp only [hf, ↓reduceIte]

theorem shortKeep_of_actual {m : Nat} (p : Snake m) (r : Nat)
    (h : ActualShortFilters p r) : shortKeep (canon (dsOf p r 9)) (sixCode p r) = true := by
  apply List.all_eq_true.mpr
  intro rule hrl
  apply List.all_eq_true.mpr
  intro offset ho
  apply List.all_eq_true.mpr
  intro reverse hv
  apply boolNot_of_no_true
  intro hh
  have hh' : offset+rule.1.length ≤ 9 ∧
      (∀ j ∈ rule.2.positions, 3 ≤ offset+orientedPosition rule.1.length reverse j ∧
        offset+orientedPosition rule.1.length reverse j ≤ 8) ∧
      canon (if reverse then
        (((canon (dsOf p r 9)).drop offset).take rule.1.length).reverse
        else ((canon (dsOf p r 9)).drop offset).take rule.1.length) = rule.1 ∧
      encodedBad rule.2 (fun j => digit (sixCode p r)
        (offset+orientedPosition rule.1.length reverse j-3)) := by
    simpa only [shortHitB, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, beq_iff_eq, encodedBadB_iff] using hh
  exact h rule hrl offset reverse hh'.1 hh'.2.1 hh'.2.2.1 hh'.2.2.2

theorem historyKeep_of_actual {m : Nat} (p : Snake m) (r : Nat)
    (h : ActualHistoryFilters p r) :
    historyKeep (actualHistory p r) (directionId p r) (sixCode p r) = true := by
  apply List.all_eq_true.mpr
  intro rule hrl
  apply boolNot_of_no_true
  intro hh
  apply h rule hrl
  simpa only [historyHitB, builderHistoryHit, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] using hh

theorem intervalKeep_of_actual {m : Nat} (p : Snake m) (r : Nat)
    (h : ActualIntervalFilters p r) : intervalKeep (canon (dsOf p r 9)) (sixCode p r) = true := by
  apply List.all_eq_true.mpr
  intro key hk
  apply List.all_eq_true.mpr
  intro s hs
  have hs' : s ≤ 2 := by have := List.mem_range.mp hs; omega
  apply boolNot_of_no_true
  intro hh
  have hh' :
      (canon (((canon (dsOf p r 9)).drop (s+2)).take 5) = key.1 ∧
        intervalHit (sixCode p r) s 4 false key.2) ∨
      (canon ((((canon (dsOf p r 9)).drop (s+2)).take 5).reverse) = key.1 ∧
        intervalHit (sixCode p r) s 4 true key.2) := by
    simpa only [intervalRuleHitB, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, intervalHitB_iff] using hh
  rcases hh' with hh' | hh'
  · exact (h key hk s hs').1 hh'.1 hh'.2
  · exact (h key hk s hs').2 hh'.1 hh'.2

theorem rangeCompatibilityKeep_of_actual {m : Nat} (p : Snake m) (r : Nat)
    (hr : ActualRanges p r) (hc : ActualHistoryCompatibility p r) :
    rangeCompatibilityKeep (canon (dsOf p r 9)) (actualHistory p r) (sixCode p r) = true := by
  simpa only [rangeCompatibilityKeep, directionId, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq] using
    (show actualHistory p r < 75 ∧ directionId p r < 505 ∧ sixCode p r < 46656 ∧
      (actualHistory p r = 0 ∨
       recordedCompatible.getD (actualHistory p r) 0 = sourceId (directionId p r)) ∧
      (builderNext (actualHistory p r) (directionId p r) = 0 ∨
       recordedCompatible.getD (builderNext (actualHistory p r) (directionId p r)) 0 =
         targetId (directionId p r)) from ⟨hr.1,hr.2.1,hr.2.2,hc.1,hc.2⟩)

theorem wordKeep_of_actual_retained {m : Nat} (p : Snake m) (r : Nat)
    (h : ActualStepRetained p r) :
    wordKeep (canon (dsOf p r 9)) (actualHistory p r) (sixCode p r) = true := by
  obtain ⟨hr,hc,hf,hs,hh,hi⟩ := h
  simp only [wordKeep, Bool.and_eq_true]
  exact ⟨rangeCompatibilityKeep_of_actual p r hr hc,referenceKeep_of_actual p r hf,
    shortKeep_of_actual p r hs,historyKeep_of_actual p r hh,intervalKeep_of_actual p r hi⟩

theorem actual_numeric_keep (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    numericKeep (actualHistory p r) (directionId p r) (sixCode p r) = true := by
  unfold numericKeep
  rw [direction_decode p r hr]
  exact wordKeep_of_actual_retained p r (actual_step_retained h235 h236 p r hr)

#print axioms boolNot_of_no_true
#print axioms encodedBadB_iff
#print axioms intervalHitB_iff
#print axioms referenceKeep_of_actual
#print axioms shortKeep_of_actual
#print axioms historyKeep_of_actual
#print axioms intervalKeep_of_actual
#print axioms rangeCompatibilityKeep_of_actual
#print axioms wordKeep_of_actual_retained
#print axioms actual_numeric_keep
end Snake9.Retained87
