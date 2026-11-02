import DirectionPilot101

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_0_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [0])) := by rfl

theorem source_0_0 (code : Nat) :
    edgeSource 0 0 code = 0+code/6 := by rfl

theorem target_0_0 (code : Nat) :
    edgeTarget 0 0 code = 225504+code%7776 := by rfl

theorem block_0_0 :
    savedBlockClass (75*0+0) = some 0 ∧
    recordedClassRoot 0 = 185 := by decide +kernel

theorem completed_0_0 (code : Nat) :
    weight completedCredit 0 0 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 0 [] 7 0
    (fun code => 0) selected_0_0 direction_0.1
    direction_0.2.1 conditioned_0 code

theorem conditional_0_0 (code : Nat) :
    weight conditionalCredit 0 0 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 0 [] 7 16
    (fun code => 0) selected_0_0 direction_0.1
    direction_0.2.2 conditioned_0 code
#print axioms selected_0_0
#print axioms source_0_0
#print axioms target_0_0
#print axioms block_0_0
#print axioms completed_0_0
#print axioms conditional_0_0

theorem selected_1_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [1])) := by rfl

theorem source_1_0 (code : Nat) :
    edgeSource 0 1 code = 0+code/6 := by rfl

theorem target_1_0 (code : Nat) :
    edgeTarget 0 1 code = 233280+code%7776 := by rfl

theorem block_1_0 :
    savedBlockClass (75*1+0) = some 1 ∧
    recordedClassRoot 1 = 379 := by decide +kernel

theorem completed_1_0 (code : Nat) :
    weight completedCredit 0 1 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 1 [] 11 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_1_0 direction_1.1
    direction_1.2.1 conditioned_1 code

theorem conditional_1_0 (code : Nat) :
    weight conditionalCredit 0 1 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 1 [] 11 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_1_0 direction_1.1
    direction_1.2.2 conditioned_1 code
#print axioms selected_1_0
#print axioms source_1_0
#print axioms target_1_0
#print axioms block_1_0
#print axioms completed_1_0
#print axioms conditional_1_0

theorem selected_9_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [9])) := by rfl

theorem source_9_0 (code : Nat) :
    edgeSource 0 9 code = 15552+code/6 := by rfl

theorem target_9_0 (code : Nat) :
    edgeTarget 0 9 code = 256608+code%7776 := by rfl

theorem block_9_0 :
    savedBlockClass (75*9+0) = some 7 ∧
    recordedClassRoot 7 = 1278 := by decide +kernel

theorem completed_9_0 (code : Nat) :
    weight completedCredit 0 9 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 9 [] 12 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_9_0 direction_9.1
    direction_9.2.1 conditioned_9 code

theorem conditional_9_0 (code : Nat) :
    weight conditionalCredit 0 9 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 9 [] 12 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_9_0 direction_9.1
    direction_9.2.2 conditioned_9 code
#print axioms selected_9_0
#print axioms source_9_0
#print axioms target_9_0
#print axioms block_9_0
#print axioms completed_9_0
#print axioms conditional_9_0

theorem selected_10_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [10])) := by rfl

theorem source_10_0 (code : Nat) :
    edgeSource 0 10 code = 15552+code/6 := by rfl

theorem target_10_0 (code : Nat) :
    edgeTarget 0 10 code = 279936+code%7776 := by rfl

theorem block_10_0 :
    savedBlockClass (75*10+0) = some 8 ∧
    recordedClassRoot 8 = 1378 := by decide +kernel

theorem completed_10_0 (code : Nat) :
    weight completedCredit 0 10 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 10 [] 12 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_10_0 direction_10.1
    direction_10.2.1 conditioned_10 code

theorem conditional_10_0 (code : Nat) :
    weight conditionalCredit 0 10 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 10 [] 12 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_10_0 direction_10.1
    direction_10.2.2 conditioned_10 code
#print axioms selected_10_0
#print axioms source_10_0
#print axioms target_10_0
#print axioms block_10_0
#print axioms completed_10_0
#print axioms conditional_10_0

theorem selected_12_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [12])) := by rfl

theorem source_12_0 (code : Nat) :
    edgeSource 0 12 code = 23328+code/6 := by rfl

theorem target_12_0 (code : Nat) :
    edgeTarget 0 12 code = 334368+code%7776 := by rfl

theorem block_12_0 :
    savedBlockClass (75*12+0) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_12_0 (code : Nat) :
    weight completedCredit 0 12 code =
      120*(code%6+1)+max (max 14 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 12 [] 14 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_12_0 direction_12.1
    direction_12.2.1 conditioned_12 code

theorem conditional_12_0 (code : Nat) :
    weight conditionalCredit 0 12 code =
      120*(code%6+1)+max (max 14 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 12 [] 14 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_12_0 direction_12.1
    direction_12.2.2 conditioned_12 code
#print axioms selected_12_0
#print axioms source_12_0
#print axioms target_12_0
#print axioms block_12_0
#print axioms completed_12_0
#print axioms conditional_12_0

end Snake9.Context101
