import Direction101Batch02

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_34_33 :
    [rule009] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 33 [] ++ [34])) := by rfl

theorem source_34_33 (code : Nat) :
    edgeSource 33 34 code = 1275264+code/6 := by rfl

theorem target_34_33 (code : Nat) :
    edgeTarget 33 34 code = 1399680+code%7776 := by rfl

theorem block_34_33 :
    savedBlockClass (75*34+33) = some 25 ∧
    recordedClassRoot 25 = 2620 := by decide +kernel

theorem completed_34_33 (code : Nat) :
    weight completedCredit 33 34 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule009] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 33 34 [rule009] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_34_33 direction_34.1
    direction_34.2.1 conditioned_34 code

theorem conditional_34_33 (code : Nat) :
    weight conditionalCredit 33 34 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule009] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 33 34 [rule009] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_34_33 direction_34.1
    direction_34.2.2 conditioned_34 code
#print axioms selected_34_33
#print axioms source_34_33
#print axioms target_34_33
#print axioms block_34_33
#print axioms completed_34_33
#print axioms conditional_34_33

end Snake9.Context101
