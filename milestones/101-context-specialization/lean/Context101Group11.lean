import Direction101Group07

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_448_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [448])) := by rfl

theorem source_448_0 (code : Nat) :
    edgeSource 0 448 code = 940896+code/6 := by rfl

theorem target_448_0 (code : Nat) :
    edgeTarget 0 448 code = 730944+code%7776 := by rfl

theorem block_448_0 :
    savedBlockClass (75*448+0) = some 115 ∧
    recordedClassRoot 115 = 3910 := by decide +kernel

theorem completed_448_0 (code : Nat) :
    weight completedCredit 0 448 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 448 [] 13 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_448_0 direction_448.1
    direction_448.2.1 conditioned_448 code

theorem conditional_448_0 (code : Nat) :
    weight conditionalCredit 0 448 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 448 [] 13 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_448_0 direction_448.1
    direction_448.2.2 conditioned_448 code
#print axioms selected_448_0
#print axioms source_448_0
#print axioms target_448_0
#print axioms block_448_0
#print axioms completed_448_0
#print axioms conditional_448_0

theorem selected_449_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [449])) := by rfl

theorem source_449_0 (code : Nat) :
    edgeSource 0 449 code = 940896+code/6 := by rfl

theorem target_449_0 (code : Nat) :
    edgeTarget 0 449 code = 738720+code%7776 := by rfl

theorem block_449_0 :
    savedBlockClass (75*449+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_449_0 (code : Nat) :
    weight completedCredit 0 449 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 449 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_449_0 direction_449.1
    direction_449.2.1 conditioned_449 code

theorem conditional_449_0 (code : Nat) :
    weight conditionalCredit 0 449 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 449 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_449_0 direction_449.1
    direction_449.2.2 conditioned_449 code
#print axioms selected_449_0
#print axioms source_449_0
#print axioms target_449_0
#print axioms block_449_0
#print axioms completed_449_0
#print axioms conditional_449_0

theorem selected_450_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [450])) := by rfl

theorem source_450_0 (code : Nat) :
    edgeSource 0 450 code = 948672+code/6 := by rfl

theorem target_450_0 (code : Nat) :
    edgeTarget 0 450 code = 793152+code%7776 := by rfl

theorem block_450_0 :
    savedBlockClass (75*450+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_450_0 (code : Nat) :
    weight completedCredit 0 450 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 450 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_450_0 direction_450.1
    direction_450.2.1 conditioned_450 code

theorem conditional_450_0 (code : Nat) :
    weight conditionalCredit 0 450 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 450 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_450_0 direction_450.1
    direction_450.2.2 conditioned_450 code
#print axioms selected_450_0
#print axioms source_450_0
#print axioms target_450_0
#print axioms block_450_0
#print axioms completed_450_0
#print axioms conditional_450_0

theorem selected_451_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [451])) := by rfl

theorem source_451_0 (code : Nat) :
    edgeSource 0 451 code = 948672+code/6 := by rfl

theorem target_451_0 (code : Nat) :
    edgeTarget 0 451 code = 800928+code%7776 := by rfl

theorem block_451_0 :
    savedBlockClass (75*451+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_451_0 (code : Nat) :
    weight completedCredit 0 451 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 451 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_451_0 direction_451.1
    direction_451.2.1 conditioned_451 code

theorem conditional_451_0 (code : Nat) :
    weight conditionalCredit 0 451 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 451 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_451_0 direction_451.1
    direction_451.2.2 conditioned_451 code
#print axioms selected_451_0
#print axioms source_451_0
#print axioms target_451_0
#print axioms block_451_0
#print axioms completed_451_0
#print axioms conditional_451_0

theorem selected_452_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [452])) := by rfl

theorem source_452_0 (code : Nat) :
    edgeSource 0 452 code = 948672+code/6 := by rfl

theorem target_452_0 (code : Nat) :
    edgeTarget 0 452 code = 808704+code%7776 := by rfl

theorem block_452_0 :
    savedBlockClass (75*452+0) = some 121 ∧
    recordedClassRoot 121 = 3940 := by decide +kernel

theorem completed_452_0 (code : Nat) :
    weight completedCredit 0 452 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 452 [] 10 16
    (fun code => 0) selected_452_0 direction_452.1
    direction_452.2.1 conditioned_452 code

theorem conditional_452_0 (code : Nat) :
    weight conditionalCredit 0 452 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 452 [] 10 16
    (fun code => 0) selected_452_0 direction_452.1
    direction_452.2.2 conditioned_452 code
#print axioms selected_452_0
#print axioms source_452_0
#print axioms target_452_0
#print axioms block_452_0
#print axioms completed_452_0
#print axioms conditional_452_0

theorem selected_453_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [453])) := by rfl

theorem source_453_0 (code : Nat) :
    edgeSource 0 453 code = 948672+code/6 := by rfl

theorem target_453_0 (code : Nat) :
    edgeTarget 0 453 code = 816480+code%7776 := by rfl

theorem block_453_0 :
    savedBlockClass (75*453+0) = some 118 ∧
    recordedClassRoot 118 = 3934 := by decide +kernel

theorem completed_453_0 (code : Nat) :
    weight completedCredit 0 453 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 453 [] 5 0
    (fun code => 0) selected_453_0 direction_453.1
    direction_453.2.1 conditioned_453 code

theorem conditional_453_0 (code : Nat) :
    weight conditionalCredit 0 453 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 453 [] 5 16
    (fun code => 0) selected_453_0 direction_453.1
    direction_453.2.2 conditioned_453 code
#print axioms selected_453_0
#print axioms source_453_0
#print axioms target_453_0
#print axioms block_453_0
#print axioms completed_453_0
#print axioms conditional_453_0

theorem selected_454_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [454])) := by rfl

theorem source_454_0 (code : Nat) :
    edgeSource 0 454 code = 948672+code/6 := by rfl

theorem target_454_0 (code : Nat) :
    edgeTarget 0 454 code = 824256+code%7776 := by rfl

theorem block_454_0 :
    savedBlockClass (75*454+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_454_0 (code : Nat) :
    weight completedCredit 0 454 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 454 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_454_0 direction_454.1
    direction_454.2.1 conditioned_454 code

theorem conditional_454_0 (code : Nat) :
    weight conditionalCredit 0 454 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 454 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_454_0 direction_454.1
    direction_454.2.2 conditioned_454 code
#print axioms selected_454_0
#print axioms source_454_0
#print axioms target_454_0
#print axioms block_454_0
#print axioms completed_454_0
#print axioms conditional_454_0

theorem selected_455_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [455])) := by rfl

theorem source_455_0 (code : Nat) :
    edgeSource 0 455 code = 956448+code/6 := by rfl

theorem target_455_0 (code : Nat) :
    edgeTarget 0 455 code = 769824+code%7776 := by rfl

theorem block_455_0 :
    savedBlockClass (75*455+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_455_0 (code : Nat) :
    weight completedCredit 0 455 code =
      120*(code%6+1)+max (max 28 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 455 [] 28 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_455_0 direction_455.1
    direction_455.2.1 conditioned_455 code

theorem conditional_455_0 (code : Nat) :
    weight conditionalCredit 0 455 code =
      120*(code%6+1)+max (max 28 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 455 [] 28 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_455_0 direction_455.1
    direction_455.2.2 conditioned_455 code
#print axioms selected_455_0
#print axioms source_455_0
#print axioms target_455_0
#print axioms block_455_0
#print axioms completed_455_0
#print axioms conditional_455_0

theorem selected_456_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [456])) := by rfl

theorem source_456_0 (code : Nat) :
    edgeSource 0 456 code = 956448+code/6 := by rfl

theorem target_456_0 (code : Nat) :
    edgeTarget 0 456 code = 746496+code%7776 := by rfl

theorem block_456_0 :
    savedBlockClass (75*456+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_456_0 (code : Nat) :
    weight completedCredit 0 456 code =
      120*(code%6+1)+max (max 19 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 456 [] 19 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_456_0 direction_456.1
    direction_456.2.1 conditioned_456 code

theorem conditional_456_0 (code : Nat) :
    weight conditionalCredit 0 456 code =
      120*(code%6+1)+max (max 19 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 456 [] 19 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_456_0 direction_456.1
    direction_456.2.2 conditioned_456 code
#print axioms selected_456_0
#print axioms source_456_0
#print axioms target_456_0
#print axioms block_456_0
#print axioms completed_456_0
#print axioms conditional_456_0

theorem selected_457_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [457])) := by rfl

theorem source_457_0 (code : Nat) :
    edgeSource 0 457 code = 956448+code/6 := by rfl

theorem target_457_0 (code : Nat) :
    edgeTarget 0 457 code = 754272+code%7776 := by rfl

theorem block_457_0 :
    savedBlockClass (75*457+0) = some 121 ∧
    recordedClassRoot 121 = 3940 := by decide +kernel

theorem completed_457_0 (code : Nat) :
    weight completedCredit 0 457 code =
      120*(code%6+1)+max (max 24 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 457 [] 24 16
    (fun code => 0) selected_457_0 direction_457.1
    direction_457.2.1 conditioned_457 code

theorem conditional_457_0 (code : Nat) :
    weight conditionalCredit 0 457 code =
      120*(code%6+1)+max (max 24 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 457 [] 24 16
    (fun code => 0) selected_457_0 direction_457.1
    direction_457.2.2 conditioned_457 code
#print axioms selected_457_0
#print axioms source_457_0
#print axioms target_457_0
#print axioms block_457_0
#print axioms completed_457_0
#print axioms conditional_457_0

theorem selected_458_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [458])) := by rfl

theorem source_458_0 (code : Nat) :
    edgeSource 0 458 code = 956448+code/6 := by rfl

theorem target_458_0 (code : Nat) :
    edgeTarget 0 458 code = 762048+code%7776 := by rfl

theorem block_458_0 :
    savedBlockClass (75*458+0) = some 118 ∧
    recordedClassRoot 118 = 3934 := by decide +kernel

theorem completed_458_0 (code : Nat) :
    weight completedCredit 0 458 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 458 [] 18 0
    (fun code => 0) selected_458_0 direction_458.1
    direction_458.2.1 conditioned_458 code

theorem conditional_458_0 (code : Nat) :
    weight conditionalCredit 0 458 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 458 [] 18 16
    (fun code => 0) selected_458_0 direction_458.1
    direction_458.2.2 conditioned_458 code
#print axioms selected_458_0
#print axioms source_458_0
#print axioms target_458_0
#print axioms block_458_0
#print axioms completed_458_0
#print axioms conditional_458_0

theorem selected_459_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [459])) := by rfl

theorem source_459_0 (code : Nat) :
    edgeSource 0 459 code = 956448+code/6 := by rfl

theorem target_459_0 (code : Nat) :
    edgeTarget 0 459 code = 769824+code%7776 := by rfl

theorem block_459_0 :
    savedBlockClass (75*459+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_459_0 (code : Nat) :
    weight completedCredit 0 459 code =
      120*(code%6+1)+max (max 28 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 459 [] 28 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_459_0 direction_459.1
    direction_459.2.1 conditioned_459 code

theorem conditional_459_0 (code : Nat) :
    weight conditionalCredit 0 459 code =
      120*(code%6+1)+max (max 28 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 459 [] 28 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_459_0 direction_459.1
    direction_459.2.2 conditioned_459 code
#print axioms selected_459_0
#print axioms source_459_0
#print axioms target_459_0
#print axioms block_459_0
#print axioms completed_459_0
#print axioms conditional_459_0

theorem selected_460_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [460])) := by rfl

theorem source_460_0 (code : Nat) :
    edgeSource 0 460 code = 964224+code/6 := by rfl

theorem target_460_0 (code : Nat) :
    edgeTarget 0 460 code = 1236384+code%7776 := by rfl

theorem block_460_0 :
    savedBlockClass (75*460+0) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_0 (code : Nat) :
    weight completedCredit 0 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 460 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_0 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_0 (code : Nat) :
    weight conditionalCredit 0 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 460 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_0 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_0
#print axioms source_460_0
#print axioms target_460_0
#print axioms block_460_0
#print axioms completed_460_0
#print axioms conditional_460_0

theorem selected_460_10 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 10 [] ++ [460])) := by rfl

theorem source_460_10 (code : Nat) :
    edgeSource 10 460 code = 1096416+code/6 := by rfl

theorem target_460_10 (code : Nat) :
    edgeTarget 10 460 code = 1360800+code%7776 := by rfl

theorem block_460_10 :
    savedBlockClass (75*460+10) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_10 (code : Nat) :
    weight completedCredit 10 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 10 460 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_10 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_10 (code : Nat) :
    weight conditionalCredit 10 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 10 460 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_10 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_10
#print axioms source_460_10
#print axioms target_460_10
#print axioms block_460_10
#print axioms completed_460_10
#print axioms conditional_460_10

theorem selected_460_18 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 18 [] ++ [460])) := by rfl

theorem source_460_18 (code : Nat) :
    edgeSource 18 460 code = 1158624+code/6 := by rfl

theorem target_460_18 (code : Nat) :
    edgeTarget 18 460 code = 1446336+code%7776 := by rfl

theorem block_460_18 :
    savedBlockClass (75*460+18) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_18 (code : Nat) :
    weight completedCredit 18 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 18 460 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_18 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_18 (code : Nat) :
    weight conditionalCredit 18 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 18 460 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_18 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_18
#print axioms source_460_18
#print axioms target_460_18
#print axioms block_460_18
#print axioms completed_460_18
#print axioms conditional_460_18

theorem selected_460_25 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 25 [] ++ [460])) := by rfl

theorem source_460_25 (code : Nat) :
    edgeSource 25 460 code = 1213056+code/6 := by rfl

theorem target_460_25 (code : Nat) :
    edgeTarget 25 460 code = 1524096+code%7776 := by rfl

theorem block_460_25 :
    savedBlockClass (75*460+25) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_25 (code : Nat) :
    weight completedCredit 25 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 25 460 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_25 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_25 (code : Nat) :
    weight conditionalCredit 25 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 25 460 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_25 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_25
#print axioms source_460_25
#print axioms target_460_25
#print axioms block_460_25
#print axioms completed_460_25
#print axioms conditional_460_25

theorem selected_460_31 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 31 [] ++ [460])) := by rfl

theorem source_460_31 (code : Nat) :
    edgeSource 31 460 code = 1259712+code/6 := by rfl

theorem target_460_31 (code : Nat) :
    edgeTarget 31 460 code = 1594080+code%7776 := by rfl

theorem block_460_31 :
    savedBlockClass (75*460+31) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_31 (code : Nat) :
    weight completedCredit 31 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 31 460 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_31 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_31 (code : Nat) :
    weight conditionalCredit 31 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 31 460 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_31 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_31
#print axioms source_460_31
#print axioms target_460_31
#print axioms block_460_31
#print axioms completed_460_31
#print axioms conditional_460_31

theorem selected_460_41 :
    [rule016] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 41 [] ++ [460])) := by rfl

theorem source_460_41 (code : Nat) :
    edgeSource 41 460 code = 1337472+code/6 := by rfl

theorem target_460_41 (code : Nat) :
    edgeTarget 41 460 code = 1360800+code%7776 := by rfl

theorem block_460_41 :
    savedBlockClass (75*460+41) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_41 (code : Nat) :
    weight completedCredit 41 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule016] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 41 460 [rule016] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_41 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_41 (code : Nat) :
    weight conditionalCredit 41 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule016] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 41 460 [rule016] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_41 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_41
#print axioms source_460_41
#print axioms target_460_41
#print axioms block_460_41
#print axioms completed_460_41
#print axioms conditional_460_41

theorem selected_460_48 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 48 [] ++ [460])) := by rfl

theorem source_460_48 (code : Nat) :
    edgeSource 48 460 code = 1391904+code/6 := by rfl

theorem target_460_48 (code : Nat) :
    edgeTarget 48 460 code = 1236384+code%7776 := by rfl

theorem block_460_48 :
    savedBlockClass (75*460+48) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_48 (code : Nat) :
    weight completedCredit 48 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 48 460 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_48 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_48 (code : Nat) :
    weight conditionalCredit 48 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 48 460 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_48 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_48
#print axioms source_460_48
#print axioms target_460_48
#print axioms block_460_48
#print axioms completed_460_48
#print axioms conditional_460_48

theorem selected_460_51 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 51 [] ++ [460])) := by rfl

theorem source_460_51 (code : Nat) :
    edgeSource 51 460 code = 1415232+code/6 := by rfl

theorem target_460_51 (code : Nat) :
    edgeTarget 51 460 code = 1236384+code%7776 := by rfl

theorem block_460_51 :
    savedBlockClass (75*460+51) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_51 (code : Nat) :
    weight completedCredit 51 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 51 460 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_51 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_51 (code : Nat) :
    weight conditionalCredit 51 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 51 460 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_51 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_51
#print axioms source_460_51
#print axioms target_460_51
#print axioms block_460_51
#print axioms completed_460_51
#print axioms conditional_460_51

theorem selected_460_54 :
    [rule030] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 54 [] ++ [460])) := by rfl

theorem source_460_54 (code : Nat) :
    edgeSource 54 460 code = 1438560+code/6 := by rfl

theorem target_460_54 (code : Nat) :
    edgeTarget 54 460 code = 1524096+code%7776 := by rfl

theorem block_460_54 :
    savedBlockClass (75*460+54) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_54 (code : Nat) :
    weight completedCredit 54 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule030] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 54 460 [rule030] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_54 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_54 (code : Nat) :
    weight conditionalCredit 54 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule030] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 54 460 [rule030] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_54 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_54
#print axioms source_460_54
#print axioms target_460_54
#print axioms block_460_54
#print axioms completed_460_54
#print axioms conditional_460_54

theorem selected_460_66 :
    [rule042] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 66 [] ++ [460])) := by rfl

theorem source_460_66 (code : Nat) :
    edgeSource 66 460 code = 1531872+code/6 := by rfl

theorem target_460_66 (code : Nat) :
    edgeTarget 66 460 code = 1446336+code%7776 := by rfl

theorem block_460_66 :
    savedBlockClass (75*460+66) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_66 (code : Nat) :
    weight completedCredit 66 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule042] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 66 460 [rule042] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_66 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_66 (code : Nat) :
    weight conditionalCredit 66 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule042] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 66 460 [rule042] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_66 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_66
#print axioms source_460_66
#print axioms target_460_66
#print axioms block_460_66
#print axioms completed_460_66
#print axioms conditional_460_66

theorem selected_460_73 :
    [rule052] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 73 [] ++ [460])) := by rfl

theorem source_460_73 (code : Nat) :
    edgeSource 73 460 code = 1586304+code/6 := by rfl

theorem target_460_73 (code : Nat) :
    edgeTarget 73 460 code = 1524096+code%7776 := by rfl

theorem block_460_73 :
    savedBlockClass (75*460+73) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_460_73 (code : Nat) :
    weight completedCredit 73 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule052] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 73 460 [rule052] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_73 direction_460.1
    direction_460.2.1 conditioned_460 code

theorem conditional_460_73 (code : Nat) :
    weight conditionalCredit 73 460 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule052] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 73 460 [rule052] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_460_73 direction_460.1
    direction_460.2.2 conditioned_460 code
#print axioms selected_460_73
#print axioms source_460_73
#print axioms target_460_73
#print axioms block_460_73
#print axioms completed_460_73
#print axioms conditional_460_73

theorem selected_461_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [461])) := by rfl

theorem source_461_0 (code : Nat) :
    edgeSource 0 461 code = 964224+code/6 := by rfl

theorem target_461_0 (code : Nat) :
    edgeTarget 0 461 code = 777600+code%7776 := by rfl

theorem block_461_0 :
    savedBlockClass (75*461+0) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_0 (code : Nat) :
    weight completedCredit 0 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_0 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_0 (code : Nat) :
    weight conditionalCredit 0 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_0 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_0
#print axioms source_461_0
#print axioms target_461_0
#print axioms block_461_0
#print axioms completed_461_0
#print axioms conditional_461_0

theorem selected_461_10 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 10 [] ++ [461])) := by rfl

theorem source_461_10 (code : Nat) :
    edgeSource 10 461 code = 1096416+code/6 := by rfl

theorem target_461_10 (code : Nat) :
    edgeTarget 10 461 code = 777600+code%7776 := by rfl

theorem block_461_10 :
    savedBlockClass (75*461+10) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_10 (code : Nat) :
    weight completedCredit 10 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 10 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_10 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_10 (code : Nat) :
    weight conditionalCredit 10 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 10 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_10 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_10
#print axioms source_461_10
#print axioms target_461_10
#print axioms block_461_10
#print axioms completed_461_10
#print axioms conditional_461_10

theorem selected_461_18 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 18 [] ++ [461])) := by rfl

theorem source_461_18 (code : Nat) :
    edgeSource 18 461 code = 1158624+code/6 := by rfl

theorem target_461_18 (code : Nat) :
    edgeTarget 18 461 code = 777600+code%7776 := by rfl

theorem block_461_18 :
    savedBlockClass (75*461+18) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_18 (code : Nat) :
    weight completedCredit 18 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 18 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_18 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_18 (code : Nat) :
    weight conditionalCredit 18 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 18 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_18 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_18
#print axioms source_461_18
#print axioms target_461_18
#print axioms block_461_18
#print axioms completed_461_18
#print axioms conditional_461_18

theorem selected_461_25 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 25 [] ++ [461])) := by rfl

theorem source_461_25 (code : Nat) :
    edgeSource 25 461 code = 1213056+code/6 := by rfl

theorem target_461_25 (code : Nat) :
    edgeTarget 25 461 code = 777600+code%7776 := by rfl

theorem block_461_25 :
    savedBlockClass (75*461+25) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_25 (code : Nat) :
    weight completedCredit 25 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 25 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_25 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_25 (code : Nat) :
    weight conditionalCredit 25 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 25 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_25 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_25
#print axioms source_461_25
#print axioms target_461_25
#print axioms block_461_25
#print axioms completed_461_25
#print axioms conditional_461_25

theorem selected_461_31 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 31 [] ++ [461])) := by rfl

theorem source_461_31 (code : Nat) :
    edgeSource 31 461 code = 1259712+code/6 := by rfl

theorem target_461_31 (code : Nat) :
    edgeTarget 31 461 code = 777600+code%7776 := by rfl

theorem block_461_31 :
    savedBlockClass (75*461+31) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_31 (code : Nat) :
    weight completedCredit 31 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 31 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_31 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_31 (code : Nat) :
    weight conditionalCredit 31 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 31 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_31 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_31
#print axioms source_461_31
#print axioms target_461_31
#print axioms block_461_31
#print axioms completed_461_31
#print axioms conditional_461_31

theorem selected_461_41 :
    [rule017] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 41 [] ++ [461])) := by rfl

theorem source_461_41 (code : Nat) :
    edgeSource 41 461 code = 1337472+code/6 := by rfl

theorem target_461_41 (code : Nat) :
    edgeTarget 41 461 code = 777600+code%7776 := by rfl

theorem block_461_41 :
    savedBlockClass (75*461+41) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_41 (code : Nat) :
    weight completedCredit 41 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule017] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 41 461 [rule017] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_41 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_41 (code : Nat) :
    weight conditionalCredit 41 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule017] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 41 461 [rule017] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_41 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_41
#print axioms source_461_41
#print axioms target_461_41
#print axioms block_461_41
#print axioms completed_461_41
#print axioms conditional_461_41

theorem selected_461_48 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 48 [] ++ [461])) := by rfl

theorem source_461_48 (code : Nat) :
    edgeSource 48 461 code = 1391904+code/6 := by rfl

theorem target_461_48 (code : Nat) :
    edgeTarget 48 461 code = 777600+code%7776 := by rfl

theorem block_461_48 :
    savedBlockClass (75*461+48) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_48 (code : Nat) :
    weight completedCredit 48 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 48 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_48 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_48 (code : Nat) :
    weight conditionalCredit 48 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 48 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_48 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_48
#print axioms source_461_48
#print axioms target_461_48
#print axioms block_461_48
#print axioms completed_461_48
#print axioms conditional_461_48

theorem selected_461_51 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 51 [] ++ [461])) := by rfl

theorem source_461_51 (code : Nat) :
    edgeSource 51 461 code = 1415232+code/6 := by rfl

theorem target_461_51 (code : Nat) :
    edgeTarget 51 461 code = 777600+code%7776 := by rfl

theorem block_461_51 :
    savedBlockClass (75*461+51) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_51 (code : Nat) :
    weight completedCredit 51 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 51 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_51 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_51 (code : Nat) :
    weight conditionalCredit 51 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 51 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_51 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_51
#print axioms source_461_51
#print axioms target_461_51
#print axioms block_461_51
#print axioms completed_461_51
#print axioms conditional_461_51

theorem selected_461_54 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 54 [] ++ [461])) := by rfl

theorem source_461_54 (code : Nat) :
    edgeSource 54 461 code = 1438560+code/6 := by rfl

theorem target_461_54 (code : Nat) :
    edgeTarget 54 461 code = 777600+code%7776 := by rfl

theorem block_461_54 :
    savedBlockClass (75*461+54) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_54 (code : Nat) :
    weight completedCredit 54 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 54 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_54 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_54 (code : Nat) :
    weight conditionalCredit 54 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 54 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_54 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_54
#print axioms source_461_54
#print axioms target_461_54
#print axioms block_461_54
#print axioms completed_461_54
#print axioms conditional_461_54

theorem selected_461_66 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 66 [] ++ [461])) := by rfl

theorem source_461_66 (code : Nat) :
    edgeSource 66 461 code = 1531872+code/6 := by rfl

theorem target_461_66 (code : Nat) :
    edgeTarget 66 461 code = 777600+code%7776 := by rfl

theorem block_461_66 :
    savedBlockClass (75*461+66) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_66 (code : Nat) :
    weight completedCredit 66 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 66 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_66 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_66 (code : Nat) :
    weight conditionalCredit 66 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 66 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_66 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_66
#print axioms source_461_66
#print axioms target_461_66
#print axioms block_461_66
#print axioms completed_461_66
#print axioms conditional_461_66

theorem selected_461_73 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 73 [] ++ [461])) := by rfl

theorem source_461_73 (code : Nat) :
    edgeSource 73 461 code = 1586304+code/6 := by rfl

theorem target_461_73 (code : Nat) :
    edgeTarget 73 461 code = 777600+code%7776 := by rfl

theorem block_461_73 :
    savedBlockClass (75*461+73) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_461_73 (code : Nat) :
    weight completedCredit 73 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 73 461 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_73 direction_461.1
    direction_461.2.1 conditioned_461 code

theorem conditional_461_73 (code : Nat) :
    weight conditionalCredit 73 461 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 73 461 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_461_73 direction_461.1
    direction_461.2.2 conditioned_461 code
#print axioms selected_461_73
#print axioms source_461_73
#print axioms target_461_73
#print axioms block_461_73
#print axioms completed_461_73
#print axioms conditional_461_73

theorem selected_462_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [462])) := by rfl

theorem source_462_0 (code : Nat) :
    edgeSource 0 462 code = 964224+code/6 := by rfl

theorem target_462_0 (code : Nat) :
    edgeTarget 0 462 code = 1244160+code%7776 := by rfl

theorem block_462_0 :
    savedBlockClass (75*462+0) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_0 (code : Nat) :
    weight completedCredit 0 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 462 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_0 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_0 (code : Nat) :
    weight conditionalCredit 0 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 462 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_0 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_0
#print axioms source_462_0
#print axioms target_462_0
#print axioms block_462_0
#print axioms completed_462_0
#print axioms conditional_462_0

theorem selected_462_10 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 10 [] ++ [462])) := by rfl

theorem source_462_10 (code : Nat) :
    edgeSource 10 462 code = 1096416+code/6 := by rfl

theorem target_462_10 (code : Nat) :
    edgeTarget 10 462 code = 1244160+code%7776 := by rfl

theorem block_462_10 :
    savedBlockClass (75*462+10) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_10 (code : Nat) :
    weight completedCredit 10 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 10 462 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_10 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_10 (code : Nat) :
    weight conditionalCredit 10 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 10 462 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_10 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_10
#print axioms source_462_10
#print axioms target_462_10
#print axioms block_462_10
#print axioms completed_462_10
#print axioms conditional_462_10

theorem selected_462_18 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 18 [] ++ [462])) := by rfl

theorem source_462_18 (code : Nat) :
    edgeSource 18 462 code = 1158624+code/6 := by rfl

theorem target_462_18 (code : Nat) :
    edgeTarget 18 462 code = 1244160+code%7776 := by rfl

theorem block_462_18 :
    savedBlockClass (75*462+18) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_18 (code : Nat) :
    weight completedCredit 18 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 18 462 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_18 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_18 (code : Nat) :
    weight conditionalCredit 18 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 18 462 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_18 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_18
#print axioms source_462_18
#print axioms target_462_18
#print axioms block_462_18
#print axioms completed_462_18
#print axioms conditional_462_18

theorem selected_462_25 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 25 [] ++ [462])) := by rfl

theorem source_462_25 (code : Nat) :
    edgeSource 25 462 code = 1213056+code/6 := by rfl

theorem target_462_25 (code : Nat) :
    edgeTarget 25 462 code = 1244160+code%7776 := by rfl

theorem block_462_25 :
    savedBlockClass (75*462+25) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_25 (code : Nat) :
    weight completedCredit 25 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 25 462 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_25 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_25 (code : Nat) :
    weight conditionalCredit 25 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 25 462 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_25 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_25
#print axioms source_462_25
#print axioms target_462_25
#print axioms block_462_25
#print axioms completed_462_25
#print axioms conditional_462_25

theorem selected_462_31 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 31 [] ++ [462])) := by rfl

theorem source_462_31 (code : Nat) :
    edgeSource 31 462 code = 1259712+code/6 := by rfl

theorem target_462_31 (code : Nat) :
    edgeTarget 31 462 code = 1244160+code%7776 := by rfl

theorem block_462_31 :
    savedBlockClass (75*462+31) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_31 (code : Nat) :
    weight completedCredit 31 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 31 462 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_31 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_31 (code : Nat) :
    weight conditionalCredit 31 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 31 462 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_31 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_31
#print axioms source_462_31
#print axioms target_462_31
#print axioms block_462_31
#print axioms completed_462_31
#print axioms conditional_462_31

theorem selected_462_41 :
    [rule018] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 41 [] ++ [462])) := by rfl

theorem source_462_41 (code : Nat) :
    edgeSource 41 462 code = 1337472+code/6 := by rfl

theorem target_462_41 (code : Nat) :
    edgeTarget 41 462 code = 1244160+code%7776 := by rfl

theorem block_462_41 :
    savedBlockClass (75*462+41) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_41 (code : Nat) :
    weight completedCredit 41 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule018] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 41 462 [rule018] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_41 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_41 (code : Nat) :
    weight conditionalCredit 41 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule018] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 41 462 [rule018] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_41 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_41
#print axioms source_462_41
#print axioms target_462_41
#print axioms block_462_41
#print axioms completed_462_41
#print axioms conditional_462_41

theorem selected_462_48 :
    [rule026] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 48 [] ++ [462])) := by rfl

theorem source_462_48 (code : Nat) :
    edgeSource 48 462 code = 1391904+code/6 := by rfl

theorem target_462_48 (code : Nat) :
    edgeTarget 48 462 code = 1244160+code%7776 := by rfl

theorem block_462_48 :
    savedBlockClass (75*462+48) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_48 (code : Nat) :
    weight completedCredit 48 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule026] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 48 462 [rule026] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_48 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_48 (code : Nat) :
    weight conditionalCredit 48 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule026] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 48 462 [rule026] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_48 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_48
#print axioms source_462_48
#print axioms target_462_48
#print axioms block_462_48
#print axioms completed_462_48
#print axioms conditional_462_48

theorem selected_462_51 :
    [rule029] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 51 [] ++ [462])) := by rfl

theorem source_462_51 (code : Nat) :
    edgeSource 51 462 code = 1415232+code/6 := by rfl

theorem target_462_51 (code : Nat) :
    edgeTarget 51 462 code = 1244160+code%7776 := by rfl

theorem block_462_51 :
    savedBlockClass (75*462+51) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_51 (code : Nat) :
    weight completedCredit 51 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule029] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 51 462 [rule029] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_51 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_51 (code : Nat) :
    weight conditionalCredit 51 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule029] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 51 462 [rule029] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_51 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_51
#print axioms source_462_51
#print axioms target_462_51
#print axioms block_462_51
#print axioms completed_462_51
#print axioms conditional_462_51

theorem selected_462_54 :
    [rule031] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 54 [] ++ [462])) := by rfl

theorem source_462_54 (code : Nat) :
    edgeSource 54 462 code = 1438560+code/6 := by rfl

theorem target_462_54 (code : Nat) :
    edgeTarget 54 462 code = 1244160+code%7776 := by rfl

theorem block_462_54 :
    savedBlockClass (75*462+54) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_54 (code : Nat) :
    weight completedCredit 54 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule031] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 54 462 [rule031] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_54 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_54 (code : Nat) :
    weight conditionalCredit 54 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule031] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 54 462 [rule031] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_54 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_54
#print axioms source_462_54
#print axioms target_462_54
#print axioms block_462_54
#print axioms completed_462_54
#print axioms conditional_462_54

theorem selected_462_66 :
    [rule043] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 66 [] ++ [462])) := by rfl

theorem source_462_66 (code : Nat) :
    edgeSource 66 462 code = 1531872+code/6 := by rfl

theorem target_462_66 (code : Nat) :
    edgeTarget 66 462 code = 1244160+code%7776 := by rfl

theorem block_462_66 :
    savedBlockClass (75*462+66) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_66 (code : Nat) :
    weight completedCredit 66 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule043] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 66 462 [rule043] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_66 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_66 (code : Nat) :
    weight conditionalCredit 66 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule043] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 66 462 [rule043] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_66 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_66
#print axioms source_462_66
#print axioms target_462_66
#print axioms block_462_66
#print axioms completed_462_66
#print axioms conditional_462_66

theorem selected_462_73 :
    [rule053] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 73 [] ++ [462])) := by rfl

theorem source_462_73 (code : Nat) :
    edgeSource 73 462 code = 1586304+code/6 := by rfl

theorem target_462_73 (code : Nat) :
    edgeTarget 73 462 code = 1244160+code%7776 := by rfl

theorem block_462_73 :
    savedBlockClass (75*462+73) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_462_73 (code : Nat) :
    weight completedCredit 73 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule053] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 73 462 [rule053] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_73 direction_462.1
    direction_462.2.1 conditioned_462 code

theorem conditional_462_73 (code : Nat) :
    weight conditionalCredit 73 462 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule053] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 73 462 [rule053] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_462_73 direction_462.1
    direction_462.2.2 conditioned_462 code
#print axioms selected_462_73
#print axioms source_462_73
#print axioms target_462_73
#print axioms block_462_73
#print axioms completed_462_73
#print axioms conditional_462_73

theorem selected_463_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [463])) := by rfl

theorem source_463_0 (code : Nat) :
    edgeSource 0 463 code = 972000+code/6 := by rfl

theorem target_463_0 (code : Nat) :
    edgeTarget 0 463 code = 824256+code%7776 := by rfl

theorem block_463_0 :
    savedBlockClass (75*463+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_463_0 (code : Nat) :
    weight completedCredit 0 463 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 463 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_463_0 direction_463.1
    direction_463.2.1 conditioned_463 code

theorem conditional_463_0 (code : Nat) :
    weight conditionalCredit 0 463 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 463 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_463_0 direction_463.1
    direction_463.2.2 conditioned_463 code
#print axioms selected_463_0
#print axioms source_463_0
#print axioms target_463_0
#print axioms block_463_0
#print axioms completed_463_0
#print axioms conditional_463_0

theorem selected_464_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [464])) := by rfl

theorem source_464_0 (code : Nat) :
    edgeSource 0 464 code = 972000+code/6 := by rfl

theorem target_464_0 (code : Nat) :
    edgeTarget 0 464 code = 793152+code%7776 := by rfl

theorem block_464_0 :
    savedBlockClass (75*464+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_464_0 (code : Nat) :
    weight completedCredit 0 464 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 464 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_464_0 direction_464.1
    direction_464.2.1 conditioned_464 code

theorem conditional_464_0 (code : Nat) :
    weight conditionalCredit 0 464 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 464 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_464_0 direction_464.1
    direction_464.2.2 conditioned_464 code
#print axioms selected_464_0
#print axioms source_464_0
#print axioms target_464_0
#print axioms block_464_0
#print axioms completed_464_0
#print axioms conditional_464_0

theorem selected_465_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [465])) := by rfl

theorem source_465_0 (code : Nat) :
    edgeSource 0 465 code = 972000+code/6 := by rfl

theorem target_465_0 (code : Nat) :
    edgeTarget 0 465 code = 800928+code%7776 := by rfl

theorem block_465_0 :
    savedBlockClass (75*465+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_465_0 (code : Nat) :
    weight completedCredit 0 465 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 465 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_465_0 direction_465.1
    direction_465.2.1 conditioned_465 code

theorem conditional_465_0 (code : Nat) :
    weight conditionalCredit 0 465 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 465 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_465_0 direction_465.1
    direction_465.2.2 conditioned_465 code
#print axioms selected_465_0
#print axioms source_465_0
#print axioms target_465_0
#print axioms block_465_0
#print axioms completed_465_0
#print axioms conditional_465_0

theorem selected_466_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [466])) := by rfl

theorem source_466_0 (code : Nat) :
    edgeSource 0 466 code = 972000+code/6 := by rfl

theorem target_466_0 (code : Nat) :
    edgeTarget 0 466 code = 808704+code%7776 := by rfl

theorem block_466_0 :
    savedBlockClass (75*466+0) = some 121 ∧
    recordedClassRoot 121 = 3940 := by decide +kernel

theorem completed_466_0 (code : Nat) :
    weight completedCredit 0 466 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 466 [] 10 16
    (fun code => 0) selected_466_0 direction_466.1
    direction_466.2.1 conditioned_466 code

theorem conditional_466_0 (code : Nat) :
    weight conditionalCredit 0 466 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 466 [] 10 16
    (fun code => 0) selected_466_0 direction_466.1
    direction_466.2.2 conditioned_466 code
#print axioms selected_466_0
#print axioms source_466_0
#print axioms target_466_0
#print axioms block_466_0
#print axioms completed_466_0
#print axioms conditional_466_0

theorem selected_467_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [467])) := by rfl

theorem source_467_0 (code : Nat) :
    edgeSource 0 467 code = 972000+code/6 := by rfl

theorem target_467_0 (code : Nat) :
    edgeTarget 0 467 code = 816480+code%7776 := by rfl

theorem block_467_0 :
    savedBlockClass (75*467+0) = some 118 ∧
    recordedClassRoot 118 = 3934 := by decide +kernel

theorem completed_467_0 (code : Nat) :
    weight completedCredit 0 467 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 467 [] 5 0
    (fun code => 0) selected_467_0 direction_467.1
    direction_467.2.1 conditioned_467 code

theorem conditional_467_0 (code : Nat) :
    weight conditionalCredit 0 467 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 467 [] 5 16
    (fun code => 0) selected_467_0 direction_467.1
    direction_467.2.2 conditioned_467 code
#print axioms selected_467_0
#print axioms source_467_0
#print axioms target_467_0
#print axioms block_467_0
#print axioms completed_467_0
#print axioms conditional_467_0

theorem selected_468_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [468])) := by rfl

theorem source_468_0 (code : Nat) :
    edgeSource 0 468 code = 972000+code/6 := by rfl

theorem target_468_0 (code : Nat) :
    edgeTarget 0 468 code = 824256+code%7776 := by rfl

theorem block_468_0 :
    savedBlockClass (75*468+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_468_0 (code : Nat) :
    weight completedCredit 0 468 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 468 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_468_0 direction_468.1
    direction_468.2.1 conditioned_468 code

theorem conditional_468_0 (code : Nat) :
    weight conditionalCredit 0 468 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 468 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_468_0 direction_468.1
    direction_468.2.2 conditioned_468 code
#print axioms selected_468_0
#print axioms source_468_0
#print axioms target_468_0
#print axioms block_468_0
#print axioms completed_468_0
#print axioms conditional_468_0

theorem selected_469_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [469])) := by rfl

theorem source_469_0 (code : Nat) :
    edgeSource 0 469 code = 979776+code/6 := by rfl

theorem target_469_0 (code : Nat) :
    edgeTarget 0 469 code = 979776+code%7776 := by rfl

theorem block_469_0 :
    savedBlockClass (75*469+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_469_0 (code : Nat) :
    weight completedCredit 0 469 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 469 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_469_0 direction_469.1
    direction_469.2.1 conditioned_469 code

theorem conditional_469_0 (code : Nat) :
    weight conditionalCredit 0 469 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 469 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_469_0 direction_469.1
    direction_469.2.2 conditioned_469 code
#print axioms selected_469_0
#print axioms source_469_0
#print axioms target_469_0
#print axioms block_469_0
#print axioms completed_469_0
#print axioms conditional_469_0

theorem selected_470_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [470])) := by rfl

theorem source_470_0 (code : Nat) :
    edgeSource 0 470 code = 979776+code/6 := by rfl

theorem target_470_0 (code : Nat) :
    edgeTarget 0 470 code = 987552+code%7776 := by rfl

theorem block_470_0 :
    savedBlockClass (75*470+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_470_0 (code : Nat) :
    weight completedCredit 0 470 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 470 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_470_0 direction_470.1
    direction_470.2.1 conditioned_470 code

theorem conditional_470_0 (code : Nat) :
    weight conditionalCredit 0 470 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 470 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_470_0 direction_470.1
    direction_470.2.2 conditioned_470 code
#print axioms selected_470_0
#print axioms source_470_0
#print axioms target_470_0
#print axioms block_470_0
#print axioms completed_470_0
#print axioms conditional_470_0

theorem selected_471_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [471])) := by rfl

theorem source_471_0 (code : Nat) :
    edgeSource 0 471 code = 979776+code/6 := by rfl

theorem target_471_0 (code : Nat) :
    edgeTarget 0 471 code = 995328+code%7776 := by rfl

theorem block_471_0 :
    savedBlockClass (75*471+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_471_0 (code : Nat) :
    weight completedCredit 0 471 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 471 [] 0 0
    (fun code => 0) selected_471_0 direction_471.1
    direction_471.2.1 conditioned_471 code

theorem conditional_471_0 (code : Nat) :
    weight conditionalCredit 0 471 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 471 [] 0 16
    (fun code => 0) selected_471_0 direction_471.1
    direction_471.2.2 conditioned_471 code
#print axioms selected_471_0
#print axioms source_471_0
#print axioms target_471_0
#print axioms block_471_0
#print axioms completed_471_0
#print axioms conditional_471_0

theorem selected_472_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [472])) := by rfl

theorem source_472_0 (code : Nat) :
    edgeSource 0 472 code = 979776+code/6 := by rfl

theorem target_472_0 (code : Nat) :
    edgeTarget 0 472 code = 1003104+code%7776 := by rfl

theorem block_472_0 :
    savedBlockClass (75*472+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_472_0 (code : Nat) :
    weight completedCredit 0 472 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 472 [] 0 16
    (fun code => 0) selected_472_0 direction_472.1
    direction_472.2.1 conditioned_472 code

theorem conditional_472_0 (code : Nat) :
    weight conditionalCredit 0 472 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 472 [] 0 16
    (fun code => 0) selected_472_0 direction_472.1
    direction_472.2.2 conditioned_472 code
#print axioms selected_472_0
#print axioms source_472_0
#print axioms target_472_0
#print axioms block_472_0
#print axioms completed_472_0
#print axioms conditional_472_0

theorem selected_473_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [473])) := by rfl

theorem source_473_0 (code : Nat) :
    edgeSource 0 473 code = 979776+code/6 := by rfl

theorem target_473_0 (code : Nat) :
    edgeTarget 0 473 code = 1010880+code%7776 := by rfl

theorem block_473_0 :
    savedBlockClass (75*473+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_473_0 (code : Nat) :
    weight completedCredit 0 473 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 473 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_473_0 direction_473.1
    direction_473.2.1 conditioned_473 code

theorem conditional_473_0 (code : Nat) :
    weight conditionalCredit 0 473 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 473 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_473_0 direction_473.1
    direction_473.2.2 conditioned_473 code
#print axioms selected_473_0
#print axioms source_473_0
#print axioms target_473_0
#print axioms block_473_0
#print axioms completed_473_0
#print axioms conditional_473_0

theorem selected_474_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [474])) := by rfl

theorem source_474_0 (code : Nat) :
    edgeSource 0 474 code = 979776+code/6 := by rfl

theorem target_474_0 (code : Nat) :
    edgeTarget 0 474 code = 1018656+code%7776 := by rfl

theorem block_474_0 :
    savedBlockClass (75*474+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_474_0 (code : Nat) :
    weight completedCredit 0 474 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 474 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_474_0 direction_474.1
    direction_474.2.1 conditioned_474 code

theorem conditional_474_0 (code : Nat) :
    weight conditionalCredit 0 474 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 474 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_474_0 direction_474.1
    direction_474.2.2 conditioned_474 code
#print axioms selected_474_0
#print axioms source_474_0
#print axioms target_474_0
#print axioms block_474_0
#print axioms completed_474_0
#print axioms conditional_474_0

theorem selected_475_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [475])) := by rfl

theorem source_475_0 (code : Nat) :
    edgeSource 0 475 code = 987552+code/6 := by rfl

theorem target_475_0 (code : Nat) :
    edgeTarget 0 475 code = 863136+code%7776 := by rfl

theorem block_475_0 :
    savedBlockClass (75*475+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_475_0 (code : Nat) :
    weight completedCredit 0 475 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 475 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_475_0 direction_475.1
    direction_475.2.1 conditioned_475 code

theorem conditional_475_0 (code : Nat) :
    weight conditionalCredit 0 475 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 475 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_475_0 direction_475.1
    direction_475.2.2 conditioned_475 code
#print axioms selected_475_0
#print axioms source_475_0
#print axioms target_475_0
#print axioms block_475_0
#print axioms completed_475_0
#print axioms conditional_475_0

theorem selected_476_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [476])) := by rfl

theorem source_476_0 (code : Nat) :
    edgeSource 0 476 code = 987552+code/6 := by rfl

theorem target_476_0 (code : Nat) :
    edgeTarget 0 476 code = 832032+code%7776 := by rfl

theorem block_476_0 :
    savedBlockClass (75*476+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_476_0 (code : Nat) :
    weight completedCredit 0 476 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 476 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_476_0 direction_476.1
    direction_476.2.1 conditioned_476 code

theorem conditional_476_0 (code : Nat) :
    weight conditionalCredit 0 476 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 476 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_476_0 direction_476.1
    direction_476.2.2 conditioned_476 code
#print axioms selected_476_0
#print axioms source_476_0
#print axioms target_476_0
#print axioms block_476_0
#print axioms completed_476_0
#print axioms conditional_476_0

theorem selected_477_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [477])) := by rfl

theorem source_477_0 (code : Nat) :
    edgeSource 0 477 code = 987552+code/6 := by rfl

theorem target_477_0 (code : Nat) :
    edgeTarget 0 477 code = 839808+code%7776 := by rfl

theorem block_477_0 :
    savedBlockClass (75*477+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_477_0 (code : Nat) :
    weight completedCredit 0 477 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 477 [] 0 0
    (fun code => 0) selected_477_0 direction_477.1
    direction_477.2.1 conditioned_477 code

theorem conditional_477_0 (code : Nat) :
    weight conditionalCredit 0 477 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 477 [] 0 16
    (fun code => 0) selected_477_0 direction_477.1
    direction_477.2.2 conditioned_477 code
#print axioms selected_477_0
#print axioms source_477_0
#print axioms target_477_0
#print axioms block_477_0
#print axioms completed_477_0
#print axioms conditional_477_0

theorem selected_478_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [478])) := by rfl

theorem source_478_0 (code : Nat) :
    edgeSource 0 478 code = 987552+code/6 := by rfl

theorem target_478_0 (code : Nat) :
    edgeTarget 0 478 code = 847584+code%7776 := by rfl

theorem block_478_0 :
    savedBlockClass (75*478+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_478_0 (code : Nat) :
    weight completedCredit 0 478 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 478 [] 0 16
    (fun code => 0) selected_478_0 direction_478.1
    direction_478.2.1 conditioned_478 code

theorem conditional_478_0 (code : Nat) :
    weight conditionalCredit 0 478 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 478 [] 0 16
    (fun code => 0) selected_478_0 direction_478.1
    direction_478.2.2 conditioned_478 code
#print axioms selected_478_0
#print axioms source_478_0
#print axioms target_478_0
#print axioms block_478_0
#print axioms completed_478_0
#print axioms conditional_478_0

theorem selected_479_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [479])) := by rfl

theorem source_479_0 (code : Nat) :
    edgeSource 0 479 code = 987552+code/6 := by rfl

theorem target_479_0 (code : Nat) :
    edgeTarget 0 479 code = 1251936+code%7776 := by rfl

theorem block_479_0 :
    savedBlockClass (75*479+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_479_0 (code : Nat) :
    weight completedCredit 0 479 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 479 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_479_0 direction_479.1
    direction_479.2.1 conditioned_479 code

theorem conditional_479_0 (code : Nat) :
    weight conditionalCredit 0 479 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 479 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_479_0 direction_479.1
    direction_479.2.2 conditioned_479 code
#print axioms selected_479_0
#print axioms source_479_0
#print axioms target_479_0
#print axioms block_479_0
#print axioms completed_479_0
#print axioms conditional_479_0

theorem selected_480_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [480])) := by rfl

theorem source_480_0 (code : Nat) :
    edgeSource 0 480 code = 987552+code/6 := by rfl

theorem target_480_0 (code : Nat) :
    edgeTarget 0 480 code = 863136+code%7776 := by rfl

theorem block_480_0 :
    savedBlockClass (75*480+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_480_0 (code : Nat) :
    weight completedCredit 0 480 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 480 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_480_0 direction_480.1
    direction_480.2.1 conditioned_480 code

theorem conditional_480_0 (code : Nat) :
    weight conditionalCredit 0 480 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 480 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_480_0 direction_480.1
    direction_480.2.2 conditioned_480 code
#print axioms selected_480_0
#print axioms source_480_0
#print axioms target_480_0
#print axioms block_480_0
#print axioms completed_480_0
#print axioms conditional_480_0

theorem selected_481_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [481])) := by rfl

theorem source_481_0 (code : Nat) :
    edgeSource 0 481 code = 995328+code/6 := by rfl

theorem target_481_0 (code : Nat) :
    edgeTarget 0 481 code = 902016+code%7776 := by rfl

theorem block_481_0 :
    savedBlockClass (75*481+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_481_0 (code : Nat) :
    weight completedCredit 0 481 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 481 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_481_0 direction_481.1
    direction_481.2.1 conditioned_481 code

theorem conditional_481_0 (code : Nat) :
    weight conditionalCredit 0 481 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 481 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_481_0 direction_481.1
    direction_481.2.2 conditioned_481 code
#print axioms selected_481_0
#print axioms source_481_0
#print axioms target_481_0
#print axioms block_481_0
#print axioms completed_481_0
#print axioms conditional_481_0

end Snake9.Context101
