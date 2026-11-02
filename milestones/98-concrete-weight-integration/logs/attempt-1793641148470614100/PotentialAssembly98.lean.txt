import GlobalCharge98

namespace Snake9.PotentialAssembly98
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.GraphWalk78 Snake9.Weights98 Snake9.CountFree98
open Snake9.CountFreeAdapter73 Snake9.GlobalCharge98 Snake9.ActualGraphKeys98
open Snake9.DefinedGraph92 Snake9.Assembly87 Snake9.Enumeration87
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Batch92
open scoped BigOperators

theorem telescope (w f : Nat → Nat) (P n : Nat)
    (h : ∀ r < n, P+f (r+1) ≤ w r+f r) :
    P*n+f n ≤ (∑ r ∈ Finset.range n, w r)+f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun r hr => h r (by omega))
    have hl := h n (Nat.lt_succ_self n)
    rw [Finset.sum_range_succ, Nat.mul_succ]
    omega

/-- The potential must hold on every row of the defined graph. Its actual
walk uses the same full keys as the weight theorem. -/
theorem actual_potential_bound (floor : Nat → Nat) (P R : Nat) (π : Nat → Nat)
    (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    (hR : ∀ s < 1601856, π s ≤ R)
    (hpotential : ∀ row ∈ (rows retainedDiagram).toList,
      P+π (rowTarget row) ≤ weight floor row.2.1 row.1 row.2.2+π (rowSource row))
    {m : Nat} (p : Snake m) (hm : 9 ≤ m) :
    P*(m-8) ≤ (∑ r ∈ Finset.range (m-8),
      weight floor (actualHistory p r) (directionId p r) (sixCode p r))+R := by
  have hstep : ∀ r < m-8,
      P+π (actualState p (r+1)) ≤
        weight floor (actualHistory p r) (directionId p r) (sixCode p r)+π (actualState p r) := by
    intro r hr
    have hfit : r+9 ≤ m := by omega
    obtain ⟨edge,he⟩ := defined_actual_edge_key retainedDiagram retained_class_family
      assignment_checked h235 h236 p r hfit
    have hmem : (directionId p r,actualHistory p r,sixCode p r) ∈
        (rows retainedDiagram).toList := by
      obtain ⟨hidx,hval⟩ := List.getElem?_eq_some_iff.mp he.1
      rw [← hval]
      exact List.getElem_mem hidx
    have h := hpotential (directionId p r,actualHistory p r,sixCode p r) hmem
    change P+π (edgeTarget (actualHistory p r) (directionId p r) (sixCode p r)) ≤
      weight floor (actualHistory p r) (directionId p r) (sixCode p r)+
        π (edgeSource (actualHistory p r) (directionId p r) (sixCode p r)) at h
    rw [actual_source_state p r hfit,actual_target_state p r hfit] at h
    exact h
  have ht := telescope
    (fun r => weight floor (actualHistory p r) (directionId p r) (sixCode p r))
    (fun r => π (actualState p r)) P (m-8) hstep
  have hstart := hR (actualState p 0) (actualState_lt p 0 (by omega))
  dsimp only at ht
  omega

theorem completed_upper235
    (h235 : AllRefuted6K235) (h236 : AllRefuted236) (π : Nat → Nat)
    (hR : ∀ s < 1601856, π s ≤ 551)
    (hpotential : ∀ row ∈ (rows retainedDiagram).toList,
      483+π (rowTarget row) ≤
        weight completedCredit row.2.1 row.1 row.2.2+π (rowSource row))
    {m : Nat} (p : Snake m) : m ≤ 235 := by
  by_cases hm : 9 ≤ m
  · have hp := actual_potential_bound completedCredit 483 551 π h235 h236 hR hpotential p hm
    have hb := completed_total_weight_budget p hm
    omega
  · omega

theorem conditional_upper234
    (h7301 : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15)
    (h7302 : RefutedShare (winOf [0,1,2,0,3,4]) broadBounds 12 17)
    (h7303 : RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15)
    (h7307 : RefutedShare (winOf [0,1,2,3,4,0]) broadBounds 12 15)
    (h7308 : RefutedShare (winOf [0,1,2,3,4,5]) broadBounds 12 15)
    (h235 : AllRefuted6K235) (h236 : AllRefuted236) (π : Nat → Nat)
    (hR : ∀ s < 1601856, π s ≤ 602)
    (hpotential : ∀ row ∈ (rows retainedDiagram).toList,
      496+π (rowTarget row) ≤
        weight conditionalCredit row.2.1 row.1 row.2.2+π (rowSource row))
    {m : Nat} (p : Snake m) : m ≤ 234 := by
  by_cases hm : 9 ≤ m
  · have hp := actual_potential_bound conditionalCredit 496 602 π h235 h236 hR hpotential p hm
    have hb := actual_total_weight_budget conditionalCredit p hm
      (fun r hr => actual_conditional_credit h7301 h7302 h7303 h7307 h7308 p r hr)
    omega
  · omega

#print axioms telescope
#print axioms actual_potential_bound
#print axioms completed_upper235
#print axioms conditional_upper234
#check @completed_upper235
#check @conditional_upper234
end Snake9.PotentialAssembly98
