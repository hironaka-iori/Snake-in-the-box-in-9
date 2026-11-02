import PotentialChecker99

/-! The actual-snake argument needs refutations only for the exact reference
union used by numericKeep. This module leaves that union refutation explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.ReferenceAssembly105
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.GraphWalk78 Snake9.Reference85 Snake9.Retained87
open Snake9.DefinedGraph92 Snake9.Assembly87 Snake9.Enumeration87
open Snake9.Certificate88 Snake9.Batch92 Snake9.Weights98 Snake9.CountFree98
open Snake9.CountFreeAdapter73 Snake9.GlobalCharge98 Snake9.PotentialChecker99
open scoped BigOperators

/-- Every exact-union key supplies its own exclusion; neither larger
catalogue proposition is reconstructed or assumed. -/
theorem actual_reference_filters (href : AllRefutedList referenceKeys)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    ActualReferenceFilters p r := by
  intro k hk s hs
  exact refuted_key_retained p r s k hr hs
    (List.all_eq_true.mp referenceKeys_valid k hk)
    (AllRefutedList.mem (l := referenceKeys) href k hk)

/-- The original executable predicate, with all four filter families and
both history-compatibility conditions retained. -/
theorem actual_numeric_keep (href : AllRefutedList referenceKeys)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    numericKeep (actualHistory p r) (directionId p r) (sixCode p r) = true := by
  obtain ⟨hrange,hcompat⟩ := actual_range_compatible p r hr
  obtain ⟨hshort,hhistory,hinterval⟩ := actual_nonreference_filters p r hr
  have hretained : ActualStepRetained p r :=
    ⟨hrange,hcompat,actual_reference_filters href p r hr,
      hshort,hhistory,hinterval⟩
  unfold numericKeep
  rw [direction_decode p r hr]
  exact wordKeep_of_actual_retained p r hretained

/-- Same graph rows, weights, state endpoints and potential range as the
milestone98 theorem, with its two catalogue premises replaced by the exact
union premise. Actual row membership retains the full direction/history/code key. -/
theorem actual_potential_bound (floor : Nat → Nat) (P R : Nat) (π : Nat → Nat)
    (href : AllRefutedList referenceKeys)
    (hR : ∀ s < 1601856, π s ≤ R)
    (hpotential : ∀ row ∈ (rows retainedDiagram).toList,
      P+π (rowTarget row) ≤
        weight floor row.2.1 row.1 row.2.2+π (rowSource row))
    {m : Nat} (p : Snake m) (hm : 9 ≤ m) :
    P*(m-8) ≤ (∑ r ∈ Finset.range (m-8),
      weight floor (actualHistory p r) (directionId p r) (sixCode p r))+R := by
  have hcover := defined_graph_covers retainedDiagram
    retained_class_family assignment_checked
  have hstep : ∀ r < m-8,
      P+π (actualState p (r+1)) ≤
        weight floor (actualHistory p r) (directionId p r) (sixCode p r)+
          π (actualState p r) := by
    intro r hr
    have hfit : r+9 ≤ m := by omega
    obtain ⟨hq,hd,hc⟩ := (actual_range_compatible p r hfit).1
    have hmem : (directionId p r,actualHistory p r,sixCode p r) ∈
        (rows retainedDiagram).toList :=
      hcover (directionId p r) (actualHistory p r) (sixCode p r) hd hq hc
        (actual_numeric_keep href p r hfit)
    have h := hpotential (directionId p r,actualHistory p r,sixCode p r) hmem
    change P+π (edgeTarget (actualHistory p r) (directionId p r) (sixCode p r)) ≤
      weight floor (actualHistory p r) (directionId p r) (sixCode p r)+
        π (edgeSource (actualHistory p r) (directionId p r) (sixCode p r)) at h
    rw [actual_source_state p r hfit,actual_target_state p r hfit] at h
    exact h
  have ht := Snake9.PotentialAssembly98.telescope
    (fun r => weight floor (actualHistory p r) (directionId p r) (sixCode p r))
    (fun r => π (actualState p r)) P (m-8) hstep
  have hstart := hR (actualState p 0) (actualState_lt p 0 (by omega))
  dsimp only at ht
  omega

/-- Completed floor profile. The exact reference union and the complete
graph check remain explicit premises. -/
theorem completed235 (href : AllRefutedList referenceKeys) (π : Nat → Nat)
    (hR : ∀ s < 1601856, π s ≤ 551)
    (hgraph : graphCheck (weight completedCredit) 483 π = true)
    {m : Nat} (p : Snake m) : m ≤ 235 := by
  by_cases hm : 9 ≤ m
  · have hp := actual_potential_bound completedCredit 483 551 π href hR
      (graphCheck_sound (weight completedCredit) 483 π hgraph) p hm
    have hb := completed_total_weight_budget p hm
    omega
  · omega

/-- Conditional floor profile, retaining exactly the five pending local
share premises, the potential range and the complete graph check. -/
theorem conditional234
    (h7301 : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15)
    (h7302 : RefutedShare (winOf [0,1,2,0,3,4]) broadBounds 12 17)
    (h7303 : RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15)
    (h7307 : RefutedShare (winOf [0,1,2,3,4,0]) broadBounds 12 15)
    (h7308 : RefutedShare (winOf [0,1,2,3,4,5]) broadBounds 12 15)
    (href : AllRefutedList referenceKeys) (π : Nat → Nat)
    (hR : ∀ s < 1601856, π s ≤ 602)
    (hgraph : graphCheck (weight conditionalCredit) 496 π = true)
    {m : Nat} (p : Snake m) : m ≤ 234 := by
  by_cases hm : 9 ≤ m
  · have hp := actual_potential_bound conditionalCredit 496 602 π href hR
      (graphCheck_sound (weight conditionalCredit) 496 π hgraph) p hm
    have hb := actual_total_weight_budget conditionalCredit p hm
      (fun r hr => actual_conditional_credit h7301 h7302 h7303 h7307 h7308 p r hr)
    omega
  · omega

#print axioms actual_reference_filters
#print axioms actual_numeric_keep
#print axioms actual_potential_bound
#print axioms completed235
#print axioms conditional234
end Snake9.ReferenceAssembly105
