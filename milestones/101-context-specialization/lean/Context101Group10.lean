import Direction101Group06

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_393_30 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 30 [] ++ [393])) := by rfl

theorem source_393_30 (code : Nat) :
    edgeSource 30 393 code = 1251936+code/6 := by rfl

theorem target_393_30 (code : Nat) :
    edgeTarget 30 393 code = 948672+code%7776 := by rfl

theorem block_393_30 :
    savedBlockClass (75*393+30) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_393_30 (code : Nat) :
    weight completedCredit 30 393 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 30 393 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_393_30 direction_393.1
    direction_393.2.1 conditioned_393 code

theorem conditional_393_30 (code : Nat) :
    weight conditionalCredit 30 393 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 30 393 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_393_30 direction_393.1
    direction_393.2.2 conditioned_393 code
#print axioms selected_393_30
#print axioms source_393_30
#print axioms target_393_30
#print axioms block_393_30
#print axioms completed_393_30
#print axioms conditional_393_30

theorem selected_394_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [394])) := by rfl

theorem source_394_0 (code : Nat) :
    edgeSource 0 394 code = 855360+code/6 := by rfl

theorem target_394_0 (code : Nat) :
    edgeTarget 0 394 code = 956448+code%7776 := by rfl

theorem block_394_0 :
    savedBlockClass (75*394+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_394_0 (code : Nat) :
    weight completedCredit 0 394 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 394 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_394_0 direction_394.1
    direction_394.2.1 conditioned_394 code

theorem conditional_394_0 (code : Nat) :
    weight conditionalCredit 0 394 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 394 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_394_0 direction_394.1
    direction_394.2.2 conditioned_394 code
#print axioms selected_394_0
#print axioms source_394_0
#print axioms target_394_0
#print axioms block_394_0
#print axioms completed_394_0
#print axioms conditional_394_0

theorem selected_394_17 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 17 [] ++ [394])) := by rfl

theorem source_394_17 (code : Nat) :
    edgeSource 17 394 code = 1150848+code/6 := by rfl

theorem target_394_17 (code : Nat) :
    edgeTarget 17 394 code = 956448+code%7776 := by rfl

theorem block_394_17 :
    savedBlockClass (75*394+17) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_394_17 (code : Nat) :
    weight completedCredit 17 394 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 17 394 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_394_17 direction_394.1
    direction_394.2.1 conditioned_394 code

theorem conditional_394_17 (code : Nat) :
    weight conditionalCredit 17 394 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 17 394 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_394_17 direction_394.1
    direction_394.2.2 conditioned_394 code
#print axioms selected_394_17
#print axioms source_394_17
#print axioms target_394_17
#print axioms block_394_17
#print axioms completed_394_17
#print axioms conditional_394_17

theorem selected_394_30 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 30 [] ++ [394])) := by rfl

theorem source_394_30 (code : Nat) :
    edgeSource 30 394 code = 1251936+code/6 := by rfl

theorem target_394_30 (code : Nat) :
    edgeTarget 30 394 code = 956448+code%7776 := by rfl

theorem block_394_30 :
    savedBlockClass (75*394+30) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_394_30 (code : Nat) :
    weight completedCredit 30 394 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 30 394 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_394_30 direction_394.1
    direction_394.2.1 conditioned_394 code

theorem conditional_394_30 (code : Nat) :
    weight conditionalCredit 30 394 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 30 394 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_394_30 direction_394.1
    direction_394.2.2 conditioned_394 code
#print axioms selected_394_30
#print axioms source_394_30
#print axioms target_394_30
#print axioms block_394_30
#print axioms completed_394_30
#print axioms conditional_394_30

theorem selected_395_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [395])) := by rfl

theorem source_395_0 (code : Nat) :
    edgeSource 0 395 code = 855360+code/6 := by rfl

theorem target_395_0 (code : Nat) :
    edgeTarget 0 395 code = 1213056+code%7776 := by rfl

theorem block_395_0 :
    savedBlockClass (75*395+0) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_395_0 (code : Nat) :
    weight completedCredit 0 395 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 395 [] 0 12
    (fun code => 0) selected_395_0 direction_395.1
    direction_395.2.1 conditioned_395 code

theorem conditional_395_0 (code : Nat) :
    weight conditionalCredit 0 395 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 395 [] 0 12
    (fun code => 0) selected_395_0 direction_395.1
    direction_395.2.2 conditioned_395 code
#print axioms selected_395_0
#print axioms source_395_0
#print axioms target_395_0
#print axioms block_395_0
#print axioms completed_395_0
#print axioms conditional_395_0

theorem selected_395_17 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 17 [] ++ [395])) := by rfl

theorem source_395_17 (code : Nat) :
    edgeSource 17 395 code = 1150848+code/6 := by rfl

theorem target_395_17 (code : Nat) :
    edgeTarget 17 395 code = 1438560+code%7776 := by rfl

theorem block_395_17 :
    savedBlockClass (75*395+17) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_395_17 (code : Nat) :
    weight completedCredit 17 395 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 17 395 [] 0 12
    (fun code => 0) selected_395_17 direction_395.1
    direction_395.2.1 conditioned_395 code

theorem conditional_395_17 (code : Nat) :
    weight conditionalCredit 17 395 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 17 395 [] 0 12
    (fun code => 0) selected_395_17 direction_395.1
    direction_395.2.2 conditioned_395 code
#print axioms selected_395_17
#print axioms source_395_17
#print axioms target_395_17
#print axioms block_395_17
#print axioms completed_395_17
#print axioms conditional_395_17

theorem selected_395_30 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 30 [] ++ [395])) := by rfl

theorem source_395_30 (code : Nat) :
    edgeSource 30 395 code = 1251936+code/6 := by rfl

theorem target_395_30 (code : Nat) :
    edgeTarget 30 395 code = 1586304+code%7776 := by rfl

theorem block_395_30 :
    savedBlockClass (75*395+30) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_395_30 (code : Nat) :
    weight completedCredit 30 395 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 30 395 [] 0 12
    (fun code => 0) selected_395_30 direction_395.1
    direction_395.2.1 conditioned_395 code

theorem conditional_395_30 (code : Nat) :
    weight conditionalCredit 30 395 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 30 395 [] 0 12
    (fun code => 0) selected_395_30 direction_395.1
    direction_395.2.2 conditioned_395 code
#print axioms selected_395_30
#print axioms source_395_30
#print axioms target_395_30
#print axioms block_395_30
#print axioms completed_395_30
#print axioms conditional_395_30

theorem selected_396_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [396])) := by rfl

theorem source_396_0 (code : Nat) :
    edgeSource 0 396 code = 855360+code/6 := by rfl

theorem target_396_0 (code : Nat) :
    edgeTarget 0 396 code = 972000+code%7776 := by rfl

theorem block_396_0 :
    savedBlockClass (75*396+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_396_0 (code : Nat) :
    weight completedCredit 0 396 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 396 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_396_0 direction_396.1
    direction_396.2.1 conditioned_396 code

theorem conditional_396_0 (code : Nat) :
    weight conditionalCredit 0 396 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 396 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_396_0 direction_396.1
    direction_396.2.2 conditioned_396 code
#print axioms selected_396_0
#print axioms source_396_0
#print axioms target_396_0
#print axioms block_396_0
#print axioms completed_396_0
#print axioms conditional_396_0

theorem selected_396_17 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 17 [] ++ [396])) := by rfl

theorem source_396_17 (code : Nat) :
    edgeSource 17 396 code = 1150848+code/6 := by rfl

theorem target_396_17 (code : Nat) :
    edgeTarget 17 396 code = 972000+code%7776 := by rfl

theorem block_396_17 :
    savedBlockClass (75*396+17) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_396_17 (code : Nat) :
    weight completedCredit 17 396 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 17 396 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_396_17 direction_396.1
    direction_396.2.1 conditioned_396 code

theorem conditional_396_17 (code : Nat) :
    weight conditionalCredit 17 396 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 17 396 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_396_17 direction_396.1
    direction_396.2.2 conditioned_396 code
#print axioms selected_396_17
#print axioms source_396_17
#print axioms target_396_17
#print axioms block_396_17
#print axioms completed_396_17
#print axioms conditional_396_17

theorem selected_396_30 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 30 [] ++ [396])) := by rfl

theorem source_396_30 (code : Nat) :
    edgeSource 30 396 code = 1251936+code/6 := by rfl

theorem target_396_30 (code : Nat) :
    edgeTarget 30 396 code = 972000+code%7776 := by rfl

theorem block_396_30 :
    savedBlockClass (75*396+30) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_396_30 (code : Nat) :
    weight completedCredit 30 396 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 30 396 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_396_30 direction_396.1
    direction_396.2.1 conditioned_396 code

theorem conditional_396_30 (code : Nat) :
    weight conditionalCredit 30 396 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 30 396 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_396_30 direction_396.1
    direction_396.2.2 conditioned_396 code
#print axioms selected_396_30
#print axioms source_396_30
#print axioms target_396_30
#print axioms block_396_30
#print axioms completed_396_30
#print axioms conditional_396_30

theorem selected_397_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [397])) := by rfl

theorem source_397_0 (code : Nat) :
    edgeSource 0 397 code = 863136+code/6 := by rfl

theorem target_397_0 (code : Nat) :
    edgeTarget 0 397 code = 979776+code%7776 := by rfl

theorem block_397_0 :
    savedBlockClass (75*397+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_397_0 (code : Nat) :
    weight completedCredit 0 397 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 397 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_397_0 direction_397.1
    direction_397.2.1 conditioned_397 code

theorem conditional_397_0 (code : Nat) :
    weight conditionalCredit 0 397 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 397 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_397_0 direction_397.1
    direction_397.2.2 conditioned_397 code
#print axioms selected_397_0
#print axioms source_397_0
#print axioms target_397_0
#print axioms block_397_0
#print axioms completed_397_0
#print axioms conditional_397_0

theorem selected_398_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [398])) := by rfl

theorem source_398_0 (code : Nat) :
    edgeSource 0 398 code = 863136+code/6 := by rfl

theorem target_398_0 (code : Nat) :
    edgeTarget 0 398 code = 987552+code%7776 := by rfl

theorem block_398_0 :
    savedBlockClass (75*398+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_398_0 (code : Nat) :
    weight completedCredit 0 398 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 398 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_398_0 direction_398.1
    direction_398.2.1 conditioned_398 code

theorem conditional_398_0 (code : Nat) :
    weight conditionalCredit 0 398 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 398 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_398_0 direction_398.1
    direction_398.2.2 conditioned_398 code
#print axioms selected_398_0
#print axioms source_398_0
#print axioms target_398_0
#print axioms block_398_0
#print axioms completed_398_0
#print axioms conditional_398_0

theorem selected_399_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [399])) := by rfl

theorem source_399_0 (code : Nat) :
    edgeSource 0 399 code = 863136+code/6 := by rfl

theorem target_399_0 (code : Nat) :
    edgeTarget 0 399 code = 995328+code%7776 := by rfl

theorem block_399_0 :
    savedBlockClass (75*399+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_399_0 (code : Nat) :
    weight completedCredit 0 399 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 399 [] 0 0
    (fun code => 0) selected_399_0 direction_399.1
    direction_399.2.1 conditioned_399 code

theorem conditional_399_0 (code : Nat) :
    weight conditionalCredit 0 399 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 399 [] 0 16
    (fun code => 0) selected_399_0 direction_399.1
    direction_399.2.2 conditioned_399 code
#print axioms selected_399_0
#print axioms source_399_0
#print axioms target_399_0
#print axioms block_399_0
#print axioms completed_399_0
#print axioms conditional_399_0

theorem selected_400_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [400])) := by rfl

theorem source_400_0 (code : Nat) :
    edgeSource 0 400 code = 863136+code/6 := by rfl

theorem target_400_0 (code : Nat) :
    edgeTarget 0 400 code = 1003104+code%7776 := by rfl

theorem block_400_0 :
    savedBlockClass (75*400+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_400_0 (code : Nat) :
    weight completedCredit 0 400 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 400 [] 0 16
    (fun code => 0) selected_400_0 direction_400.1
    direction_400.2.1 conditioned_400 code

theorem conditional_400_0 (code : Nat) :
    weight conditionalCredit 0 400 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 400 [] 0 16
    (fun code => 0) selected_400_0 direction_400.1
    direction_400.2.2 conditioned_400 code
#print axioms selected_400_0
#print axioms source_400_0
#print axioms target_400_0
#print axioms block_400_0
#print axioms completed_400_0
#print axioms conditional_400_0

theorem selected_401_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [401])) := by rfl

theorem source_401_0 (code : Nat) :
    edgeSource 0 401 code = 863136+code/6 := by rfl

theorem target_401_0 (code : Nat) :
    edgeTarget 0 401 code = 1010880+code%7776 := by rfl

theorem block_401_0 :
    savedBlockClass (75*401+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_401_0 (code : Nat) :
    weight completedCredit 0 401 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 401 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_401_0 direction_401.1
    direction_401.2.1 conditioned_401 code

theorem conditional_401_0 (code : Nat) :
    weight conditionalCredit 0 401 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 401 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_401_0 direction_401.1
    direction_401.2.2 conditioned_401 code
#print axioms selected_401_0
#print axioms source_401_0
#print axioms target_401_0
#print axioms block_401_0
#print axioms completed_401_0
#print axioms conditional_401_0

theorem selected_402_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [402])) := by rfl

theorem source_402_0 (code : Nat) :
    edgeSource 0 402 code = 863136+code/6 := by rfl

theorem target_402_0 (code : Nat) :
    edgeTarget 0 402 code = 1018656+code%7776 := by rfl

theorem block_402_0 :
    savedBlockClass (75*402+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_402_0 (code : Nat) :
    weight completedCredit 0 402 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 402 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_402_0 direction_402.1
    direction_402.2.1 conditioned_402 code

theorem conditional_402_0 (code : Nat) :
    weight conditionalCredit 0 402 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 402 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_402_0 direction_402.1
    direction_402.2.2 conditioned_402 code
#print axioms selected_402_0
#print axioms source_402_0
#print axioms target_402_0
#print axioms block_402_0
#print axioms completed_402_0
#print axioms conditional_402_0

theorem selected_403_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [403])) := by rfl

theorem source_403_0 (code : Nat) :
    edgeSource 0 403 code = 870912+code/6 := by rfl

theorem target_403_0 (code : Nat) :
    edgeTarget 0 403 code = 606528+code%7776 := by rfl

theorem block_403_0 :
    savedBlockClass (75*403+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_403_0 (code : Nat) :
    weight completedCredit 0 403 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 403 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_403_0 direction_403.1
    direction_403.2.1 conditioned_403 code

theorem conditional_403_0 (code : Nat) :
    weight conditionalCredit 0 403 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 403 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_403_0 direction_403.1
    direction_403.2.2 conditioned_403 code
#print axioms selected_403_0
#print axioms source_403_0
#print axioms target_403_0
#print axioms block_403_0
#print axioms completed_403_0
#print axioms conditional_403_0

theorem selected_404_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [404])) := by rfl

theorem source_404_0 (code : Nat) :
    edgeSource 0 404 code = 870912+code/6 := by rfl

theorem target_404_0 (code : Nat) :
    edgeTarget 0 404 code = 614304+code%7776 := by rfl

theorem block_404_0 :
    savedBlockClass (75*404+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_404_0 (code : Nat) :
    weight completedCredit 0 404 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 404 [] 0 0
    (fun code => 0) selected_404_0 direction_404.1
    direction_404.2.1 conditioned_404 code

theorem conditional_404_0 (code : Nat) :
    weight conditionalCredit 0 404 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 404 [] 0 16
    (fun code => 0) selected_404_0 direction_404.1
    direction_404.2.2 conditioned_404 code
#print axioms selected_404_0
#print axioms source_404_0
#print axioms target_404_0
#print axioms block_404_0
#print axioms completed_404_0
#print axioms conditional_404_0

theorem selected_405_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [405])) := by rfl

theorem source_405_0 (code : Nat) :
    edgeSource 0 405 code = 870912+code/6 := by rfl

theorem target_405_0 (code : Nat) :
    edgeTarget 0 405 code = 622080+code%7776 := by rfl

theorem block_405_0 :
    savedBlockClass (75*405+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_405_0 (code : Nat) :
    weight completedCredit 0 405 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 405 [] 0 16
    (fun code => 0) selected_405_0 direction_405.1
    direction_405.2.1 conditioned_405 code

theorem conditional_405_0 (code : Nat) :
    weight conditionalCredit 0 405 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 405 [] 0 16
    (fun code => 0) selected_405_0 direction_405.1
    direction_405.2.2 conditioned_405 code
#print axioms selected_405_0
#print axioms source_405_0
#print axioms target_405_0
#print axioms block_405_0
#print axioms completed_405_0
#print axioms conditional_405_0

theorem selected_406_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [406])) := by rfl

theorem source_406_0 (code : Nat) :
    edgeSource 0 406 code = 870912+code/6 := by rfl

theorem target_406_0 (code : Nat) :
    edgeTarget 0 406 code = 629856+code%7776 := by rfl

theorem block_406_0 :
    savedBlockClass (75*406+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_406_0 (code : Nat) :
    weight completedCredit 0 406 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 406 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_406_0 direction_406.1
    direction_406.2.1 conditioned_406 code

theorem conditional_406_0 (code : Nat) :
    weight conditionalCredit 0 406 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 406 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_406_0 direction_406.1
    direction_406.2.2 conditioned_406 code
#print axioms selected_406_0
#print axioms source_406_0
#print axioms target_406_0
#print axioms block_406_0
#print axioms completed_406_0
#print axioms conditional_406_0

theorem selected_407_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [407])) := by rfl

theorem source_407_0 (code : Nat) :
    edgeSource 0 407 code = 870912+code/6 := by rfl

theorem target_407_0 (code : Nat) :
    edgeTarget 0 407 code = 637632+code%7776 := by rfl

theorem block_407_0 :
    savedBlockClass (75*407+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_407_0 (code : Nat) :
    weight completedCredit 0 407 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 407 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_407_0 direction_407.1
    direction_407.2.1 conditioned_407 code

theorem conditional_407_0 (code : Nat) :
    weight conditionalCredit 0 407 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 407 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_407_0 direction_407.1
    direction_407.2.2 conditioned_407 code
#print axioms selected_407_0
#print axioms source_407_0
#print axioms target_407_0
#print axioms block_407_0
#print axioms completed_407_0
#print axioms conditional_407_0

theorem selected_408_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [408])) := by rfl

theorem source_408_0 (code : Nat) :
    edgeSource 0 408 code = 878688+code/6 := by rfl

theorem target_408_0 (code : Nat) :
    edgeTarget 0 408 code = 544320+code%7776 := by rfl

theorem block_408_0 :
    savedBlockClass (75*408+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_408_0 (code : Nat) :
    weight completedCredit 0 408 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 408 [] 22 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_408_0 direction_408.1
    direction_408.2.1 conditioned_408 code

theorem conditional_408_0 (code : Nat) :
    weight conditionalCredit 0 408 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 408 [] 22 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_408_0 direction_408.1
    direction_408.2.2 conditioned_408 code
#print axioms selected_408_0
#print axioms source_408_0
#print axioms target_408_0
#print axioms block_408_0
#print axioms completed_408_0
#print axioms conditional_408_0

theorem selected_409_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [409])) := by rfl

theorem source_409_0 (code : Nat) :
    edgeSource 0 409 code = 878688+code/6 := by rfl

theorem target_409_0 (code : Nat) :
    edgeTarget 0 409 code = 520992+code%7776 := by rfl

theorem block_409_0 :
    savedBlockClass (75*409+0) = some 29 ∧
    recordedClassRoot 29 = 2691 := by decide +kernel

theorem completed_409_0 (code : Nat) :
    weight completedCredit 0 409 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 409 [] 22 0
    (fun code => 0) selected_409_0 direction_409.1
    direction_409.2.1 conditioned_409 code

theorem conditional_409_0 (code : Nat) :
    weight conditionalCredit 0 409 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 409 [] 22 16
    (fun code => 0) selected_409_0 direction_409.1
    direction_409.2.2 conditioned_409 code
#print axioms selected_409_0
#print axioms source_409_0
#print axioms target_409_0
#print axioms block_409_0
#print axioms completed_409_0
#print axioms conditional_409_0

theorem selected_410_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [410])) := by rfl

theorem source_410_0 (code : Nat) :
    edgeSource 0 410 code = 878688+code/6 := by rfl

theorem target_410_0 (code : Nat) :
    edgeTarget 0 410 code = 528768+code%7776 := by rfl

theorem block_410_0 :
    savedBlockClass (75*410+0) = some 43 ∧
    recordedClassRoot 43 = 3318 := by decide +kernel

theorem completed_410_0 (code : Nat) :
    weight completedCredit 0 410 code =
      120*(code%6+1)+max (max 16 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 410 [] 16 16
    (fun code => 0) selected_410_0 direction_410.1
    direction_410.2.1 conditioned_410 code

theorem conditional_410_0 (code : Nat) :
    weight conditionalCredit 0 410 code =
      120*(code%6+1)+max (max 16 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 410 [] 16 16
    (fun code => 0) selected_410_0 direction_410.1
    direction_410.2.2 conditioned_410 code
#print axioms selected_410_0
#print axioms source_410_0
#print axioms target_410_0
#print axioms block_410_0
#print axioms completed_410_0
#print axioms conditional_410_0

theorem selected_411_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [411])) := by rfl

theorem source_411_0 (code : Nat) :
    edgeSource 0 411 code = 878688+code/6 := by rfl

theorem target_411_0 (code : Nat) :
    edgeTarget 0 411 code = 536544+code%7776 := by rfl

theorem block_411_0 :
    savedBlockClass (75*411+0) = some 112 ∧
    recordedClassRoot 112 = 3904 := by decide +kernel

theorem completed_411_0 (code : Nat) :
    weight completedCredit 0 411 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 411 [] 6 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_411_0 direction_411.1
    direction_411.2.1 conditioned_411 code

theorem conditional_411_0 (code : Nat) :
    weight conditionalCredit 0 411 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 411 [] 6 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_411_0 direction_411.1
    direction_411.2.2 conditioned_411 code
#print axioms selected_411_0
#print axioms source_411_0
#print axioms target_411_0
#print axioms block_411_0
#print axioms completed_411_0
#print axioms conditional_411_0

theorem selected_412_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [412])) := by rfl

theorem source_412_0 (code : Nat) :
    edgeSource 0 412 code = 878688+code/6 := by rfl

theorem target_412_0 (code : Nat) :
    edgeTarget 0 412 code = 544320+code%7776 := by rfl

theorem block_412_0 :
    savedBlockClass (75*412+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_412_0 (code : Nat) :
    weight completedCredit 0 412 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 412 [] 22 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_412_0 direction_412.1
    direction_412.2.1 conditioned_412 code

theorem conditional_412_0 (code : Nat) :
    weight conditionalCredit 0 412 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 412 [] 22 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_412_0 direction_412.1
    direction_412.2.2 conditioned_412 code
#print axioms selected_412_0
#print axioms source_412_0
#print axioms target_412_0
#print axioms block_412_0
#print axioms completed_412_0
#print axioms conditional_412_0

theorem selected_413_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [413])) := by rfl

theorem source_413_0 (code : Nat) :
    edgeSource 0 413 code = 886464+code/6 := by rfl

theorem target_413_0 (code : Nat) :
    edgeTarget 0 413 code = 575424+code%7776 := by rfl

theorem block_413_0 :
    savedBlockClass (75*413+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_413_0 (code : Nat) :
    weight completedCredit 0 413 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 413 [] 25 16
    (fun code => 0) selected_413_0 direction_413.1
    direction_413.2.1 conditioned_413 code

theorem conditional_413_0 (code : Nat) :
    weight conditionalCredit 0 413 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 413 [] 25 16
    (fun code => 0) selected_413_0 direction_413.1
    direction_413.2.2 conditioned_413 code
#print axioms selected_413_0
#print axioms source_413_0
#print axioms target_413_0
#print axioms block_413_0
#print axioms completed_413_0
#print axioms conditional_413_0

theorem selected_414_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [414])) := by rfl

theorem source_414_0 (code : Nat) :
    edgeSource 0 414 code = 886464+code/6 := by rfl

theorem target_414_0 (code : Nat) :
    edgeTarget 0 414 code = 552096+code%7776 := by rfl

theorem block_414_0 :
    savedBlockClass (75*414+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_414_0 (code : Nat) :
    weight completedCredit 0 414 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 414 [] 25 16
    (fun code => 0) selected_414_0 direction_414.1
    direction_414.2.1 conditioned_414 code

theorem conditional_414_0 (code : Nat) :
    weight conditionalCredit 0 414 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 414 [] 25 16
    (fun code => 0) selected_414_0 direction_414.1
    direction_414.2.2 conditioned_414 code
#print axioms selected_414_0
#print axioms source_414_0
#print axioms target_414_0
#print axioms block_414_0
#print axioms completed_414_0
#print axioms conditional_414_0

theorem selected_415_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [415])) := by rfl

theorem source_415_0 (code : Nat) :
    edgeSource 0 415 code = 886464+code/6 := by rfl

theorem target_415_0 (code : Nat) :
    edgeTarget 0 415 code = 559872+code%7776 := by rfl

theorem block_415_0 :
    savedBlockClass (75*415+0) = some 56 ∧
    recordedClassRoot 56 = 3453 := by decide +kernel

theorem completed_415_0 (code : Nat) :
    weight completedCredit 0 415 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 415 [] 10 0
    (fun code => 0) selected_415_0 direction_415.1
    direction_415.2.1 conditioned_415 code

theorem conditional_415_0 (code : Nat) :
    weight conditionalCredit 0 415 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 415 [] 10 16
    (fun code => 0) selected_415_0 direction_415.1
    direction_415.2.2 conditioned_415 code
#print axioms selected_415_0
#print axioms source_415_0
#print axioms target_415_0
#print axioms block_415_0
#print axioms completed_415_0
#print axioms conditional_415_0

theorem selected_416_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [416])) := by rfl

theorem source_416_0 (code : Nat) :
    edgeSource 0 416 code = 886464+code/6 := by rfl

theorem target_416_0 (code : Nat) :
    edgeTarget 0 416 code = 567648+code%7776 := by rfl

theorem block_416_0 :
    savedBlockClass (75*416+0) = some 77 ∧
    recordedClassRoot 77 = 3522 := by decide +kernel

theorem completed_416_0 (code : Nat) :
    weight completedCredit 0 416 code =
      120*(code%6+1)+max (max 15 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 416 [] 15 16
    (fun code => 0) selected_416_0 direction_416.1
    direction_416.2.1 conditioned_416 code

theorem conditional_416_0 (code : Nat) :
    weight conditionalCredit 0 416 code =
      120*(code%6+1)+max (max 15 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 416 [] 15 16
    (fun code => 0) selected_416_0 direction_416.1
    direction_416.2.2 conditioned_416 code
#print axioms selected_416_0
#print axioms source_416_0
#print axioms target_416_0
#print axioms block_416_0
#print axioms completed_416_0
#print axioms conditional_416_0

theorem selected_417_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [417])) := by rfl

theorem source_417_0 (code : Nat) :
    edgeSource 0 417 code = 886464+code/6 := by rfl

theorem target_417_0 (code : Nat) :
    edgeTarget 0 417 code = 575424+code%7776 := by rfl

theorem block_417_0 :
    savedBlockClass (75*417+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_417_0 (code : Nat) :
    weight completedCredit 0 417 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 417 [] 25 16
    (fun code => 0) selected_417_0 direction_417.1
    direction_417.2.1 conditioned_417 code

theorem conditional_417_0 (code : Nat) :
    weight conditionalCredit 0 417 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 417 [] 25 16
    (fun code => 0) selected_417_0 direction_417.1
    direction_417.2.2 conditioned_417 code
#print axioms selected_417_0
#print axioms source_417_0
#print axioms target_417_0
#print axioms block_417_0
#print axioms completed_417_0
#print axioms conditional_417_0

theorem selected_418_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [418])) := by rfl

theorem source_418_0 (code : Nat) :
    edgeSource 0 418 code = 894240+code/6 := by rfl

theorem target_418_0 (code : Nat) :
    edgeTarget 0 418 code = 598752+code%7776 := by rfl

theorem block_418_0 :
    savedBlockClass (75*418+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_418_0 (code : Nat) :
    weight completedCredit 0 418 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 418 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_418_0 direction_418.1
    direction_418.2.1 conditioned_418 code

theorem conditional_418_0 (code : Nat) :
    weight conditionalCredit 0 418 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 418 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_418_0 direction_418.1
    direction_418.2.2 conditioned_418 code
#print axioms selected_418_0
#print axioms source_418_0
#print axioms target_418_0
#print axioms block_418_0
#print axioms completed_418_0
#print axioms conditional_418_0

theorem selected_419_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [419])) := by rfl

theorem source_419_0 (code : Nat) :
    edgeSource 0 419 code = 894240+code/6 := by rfl

theorem target_419_0 (code : Nat) :
    edgeTarget 0 419 code = 583200+code%7776 := by rfl

theorem block_419_0 :
    savedBlockClass (75*419+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_419_0 (code : Nat) :
    weight completedCredit 0 419 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 419 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_419_0 direction_419.1
    direction_419.2.1 conditioned_419 code

theorem conditional_419_0 (code : Nat) :
    weight conditionalCredit 0 419 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 419 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_419_0 direction_419.1
    direction_419.2.2 conditioned_419 code
#print axioms selected_419_0
#print axioms source_419_0
#print axioms target_419_0
#print axioms block_419_0
#print axioms completed_419_0
#print axioms conditional_419_0

theorem selected_420_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [420])) := by rfl

theorem source_420_0 (code : Nat) :
    edgeSource 0 420 code = 894240+code/6 := by rfl

theorem target_420_0 (code : Nat) :
    edgeTarget 0 420 code = 590976+code%7776 := by rfl

theorem block_420_0 :
    savedBlockClass (75*420+0) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_420_0 (code : Nat) :
    weight completedCredit 0 420 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 420 [] 0 12
    (fun code => 0) selected_420_0 direction_420.1
    direction_420.2.1 conditioned_420 code

theorem conditional_420_0 (code : Nat) :
    weight conditionalCredit 0 420 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 420 [] 0 12
    (fun code => 0) selected_420_0 direction_420.1
    direction_420.2.2 conditioned_420 code
#print axioms selected_420_0
#print axioms source_420_0
#print axioms target_420_0
#print axioms block_420_0
#print axioms completed_420_0
#print axioms conditional_420_0

theorem selected_421_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [421])) := by rfl

theorem source_421_0 (code : Nat) :
    edgeSource 0 421 code = 894240+code/6 := by rfl

theorem target_421_0 (code : Nat) :
    edgeTarget 0 421 code = 598752+code%7776 := by rfl

theorem block_421_0 :
    savedBlockClass (75*421+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_421_0 (code : Nat) :
    weight completedCredit 0 421 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 421 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_421_0 direction_421.1
    direction_421.2.1 conditioned_421 code

theorem conditional_421_0 (code : Nat) :
    weight conditionalCredit 0 421 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 421 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_421_0 direction_421.1
    direction_421.2.2 conditioned_421 code
#print axioms selected_421_0
#print axioms source_421_0
#print axioms target_421_0
#print axioms block_421_0
#print axioms completed_421_0
#print axioms conditional_421_0

theorem selected_422_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [422])) := by rfl

theorem source_422_0 (code : Nat) :
    edgeSource 0 422 code = 902016+code/6 := by rfl

theorem target_422_0 (code : Nat) :
    edgeTarget 0 422 code = 637632+code%7776 := by rfl

theorem block_422_0 :
    savedBlockClass (75*422+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_422_0 (code : Nat) :
    weight completedCredit 0 422 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 422 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_422_0 direction_422.1
    direction_422.2.1 conditioned_422 code

theorem conditional_422_0 (code : Nat) :
    weight conditionalCredit 0 422 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 422 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_422_0 direction_422.1
    direction_422.2.2 conditioned_422 code
#print axioms selected_422_0
#print axioms source_422_0
#print axioms target_422_0
#print axioms block_422_0
#print axioms completed_422_0
#print axioms conditional_422_0

theorem selected_423_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [423])) := by rfl

theorem source_423_0 (code : Nat) :
    edgeSource 0 423 code = 902016+code/6 := by rfl

theorem target_423_0 (code : Nat) :
    edgeTarget 0 423 code = 606528+code%7776 := by rfl

theorem block_423_0 :
    savedBlockClass (75*423+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_423_0 (code : Nat) :
    weight completedCredit 0 423 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 423 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_423_0 direction_423.1
    direction_423.2.1 conditioned_423 code

theorem conditional_423_0 (code : Nat) :
    weight conditionalCredit 0 423 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 423 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_423_0 direction_423.1
    direction_423.2.2 conditioned_423 code
#print axioms selected_423_0
#print axioms source_423_0
#print axioms target_423_0
#print axioms block_423_0
#print axioms completed_423_0
#print axioms conditional_423_0

theorem selected_424_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [424])) := by rfl

theorem source_424_0 (code : Nat) :
    edgeSource 0 424 code = 902016+code/6 := by rfl

theorem target_424_0 (code : Nat) :
    edgeTarget 0 424 code = 614304+code%7776 := by rfl

theorem block_424_0 :
    savedBlockClass (75*424+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_424_0 (code : Nat) :
    weight completedCredit 0 424 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 424 [] 0 0
    (fun code => 0) selected_424_0 direction_424.1
    direction_424.2.1 conditioned_424 code

theorem conditional_424_0 (code : Nat) :
    weight conditionalCredit 0 424 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 424 [] 0 16
    (fun code => 0) selected_424_0 direction_424.1
    direction_424.2.2 conditioned_424 code
#print axioms selected_424_0
#print axioms source_424_0
#print axioms target_424_0
#print axioms block_424_0
#print axioms completed_424_0
#print axioms conditional_424_0

theorem selected_425_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [425])) := by rfl

theorem source_425_0 (code : Nat) :
    edgeSource 0 425 code = 902016+code/6 := by rfl

theorem target_425_0 (code : Nat) :
    edgeTarget 0 425 code = 622080+code%7776 := by rfl

theorem block_425_0 :
    savedBlockClass (75*425+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_425_0 (code : Nat) :
    weight completedCredit 0 425 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 425 [] 0 16
    (fun code => 0) selected_425_0 direction_425.1
    direction_425.2.1 conditioned_425 code

theorem conditional_425_0 (code : Nat) :
    weight conditionalCredit 0 425 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 425 [] 0 16
    (fun code => 0) selected_425_0 direction_425.1
    direction_425.2.2 conditioned_425 code
#print axioms selected_425_0
#print axioms source_425_0
#print axioms target_425_0
#print axioms block_425_0
#print axioms completed_425_0
#print axioms conditional_425_0

theorem selected_426_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [426])) := by rfl

theorem source_426_0 (code : Nat) :
    edgeSource 0 426 code = 902016+code/6 := by rfl

theorem target_426_0 (code : Nat) :
    edgeTarget 0 426 code = 1220832+code%7776 := by rfl

theorem block_426_0 :
    savedBlockClass (75*426+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_426_0 (code : Nat) :
    weight completedCredit 0 426 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 426 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_426_0 direction_426.1
    direction_426.2.1 conditioned_426 code

theorem conditional_426_0 (code : Nat) :
    weight conditionalCredit 0 426 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 426 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_426_0 direction_426.1
    direction_426.2.2 conditioned_426 code
#print axioms selected_426_0
#print axioms source_426_0
#print axioms target_426_0
#print axioms block_426_0
#print axioms completed_426_0
#print axioms conditional_426_0

theorem selected_427_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [427])) := by rfl

theorem source_427_0 (code : Nat) :
    edgeSource 0 427 code = 902016+code/6 := by rfl

theorem target_427_0 (code : Nat) :
    edgeTarget 0 427 code = 637632+code%7776 := by rfl

theorem block_427_0 :
    savedBlockClass (75*427+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_427_0 (code : Nat) :
    weight completedCredit 0 427 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 427 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_427_0 direction_427.1
    direction_427.2.1 conditioned_427 code

theorem conditional_427_0 (code : Nat) :
    weight conditionalCredit 0 427 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 427 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_427_0 direction_427.1
    direction_427.2.2 conditioned_427 code
#print axioms selected_427_0
#print axioms source_427_0
#print axioms target_427_0
#print axioms block_427_0
#print axioms completed_427_0
#print axioms conditional_427_0

theorem selected_428_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [428])) := by rfl

theorem source_428_0 (code : Nat) :
    edgeSource 0 428 code = 909792+code/6 := by rfl

theorem target_428_0 (code : Nat) :
    edgeTarget 0 428 code = 707616+code%7776 := by rfl

theorem block_428_0 :
    savedBlockClass (75*428+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_428_0 (code : Nat) :
    weight completedCredit 0 428 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 428 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_428_0 direction_428.1
    direction_428.2.1 conditioned_428 code

theorem conditional_428_0 (code : Nat) :
    weight conditionalCredit 0 428 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 428 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_428_0 direction_428.1
    direction_428.2.2 conditioned_428 code
#print axioms selected_428_0
#print axioms source_428_0
#print axioms target_428_0
#print axioms block_428_0
#print axioms completed_428_0
#print axioms conditional_428_0

theorem selected_429_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [429])) := by rfl

theorem source_429_0 (code : Nat) :
    edgeSource 0 429 code = 909792+code/6 := by rfl

theorem target_429_0 (code : Nat) :
    edgeTarget 0 429 code = 715392+code%7776 := by rfl

theorem block_429_0 :
    savedBlockClass (75*429+0) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_429_0 (code : Nat) :
    weight completedCredit 0 429 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 429 [] 13 0
    (fun code => 0) selected_429_0 direction_429.1
    direction_429.2.1 conditioned_429 code

theorem conditional_429_0 (code : Nat) :
    weight conditionalCredit 0 429 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 429 [] 13 16
    (fun code => 0) selected_429_0 direction_429.1
    direction_429.2.2 conditioned_429 code
#print axioms selected_429_0
#print axioms source_429_0
#print axioms target_429_0
#print axioms block_429_0
#print axioms completed_429_0
#print axioms conditional_429_0

theorem selected_430_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [430])) := by rfl

theorem source_430_0 (code : Nat) :
    edgeSource 0 430 code = 909792+code/6 := by rfl

theorem target_430_0 (code : Nat) :
    edgeTarget 0 430 code = 723168+code%7776 := by rfl

theorem block_430_0 :
    savedBlockClass (75*430+0) = some 40 ∧
    recordedClassRoot 40 = 3139 := by decide +kernel

theorem completed_430_0 (code : Nat) :
    weight completedCredit 0 430 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 430 [] 13 16
    (fun code => 0) selected_430_0 direction_430.1
    direction_430.2.1 conditioned_430 code

theorem conditional_430_0 (code : Nat) :
    weight conditionalCredit 0 430 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 430 [] 13 16
    (fun code => 0) selected_430_0 direction_430.1
    direction_430.2.2 conditioned_430 code
#print axioms selected_430_0
#print axioms source_430_0
#print axioms target_430_0
#print axioms block_430_0
#print axioms completed_430_0
#print axioms conditional_430_0

theorem selected_431_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [431])) := by rfl

theorem source_431_0 (code : Nat) :
    edgeSource 0 431 code = 909792+code/6 := by rfl

theorem target_431_0 (code : Nat) :
    edgeTarget 0 431 code = 730944+code%7776 := by rfl

theorem block_431_0 :
    savedBlockClass (75*431+0) = some 115 ∧
    recordedClassRoot 115 = 3910 := by decide +kernel

theorem completed_431_0 (code : Nat) :
    weight completedCredit 0 431 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 431 [] 13 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_431_0 direction_431.1
    direction_431.2.1 conditioned_431 code

theorem conditional_431_0 (code : Nat) :
    weight conditionalCredit 0 431 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 431 [] 13 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_431_0 direction_431.1
    direction_431.2.2 conditioned_431 code
#print axioms selected_431_0
#print axioms source_431_0
#print axioms target_431_0
#print axioms block_431_0
#print axioms completed_431_0
#print axioms conditional_431_0

theorem selected_432_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [432])) := by rfl

theorem source_432_0 (code : Nat) :
    edgeSource 0 432 code = 909792+code/6 := by rfl

theorem target_432_0 (code : Nat) :
    edgeTarget 0 432 code = 738720+code%7776 := by rfl

theorem block_432_0 :
    savedBlockClass (75*432+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_432_0 (code : Nat) :
    weight completedCredit 0 432 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 432 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_432_0 direction_432.1
    direction_432.2.1 conditioned_432 code

theorem conditional_432_0 (code : Nat) :
    weight conditionalCredit 0 432 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 432 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_432_0 direction_432.1
    direction_432.2.2 conditioned_432 code
#print axioms selected_432_0
#print axioms source_432_0
#print axioms target_432_0
#print axioms block_432_0
#print axioms completed_432_0
#print axioms conditional_432_0

theorem selected_433_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [433])) := by rfl

theorem source_433_0 (code : Nat) :
    edgeSource 0 433 code = 917568+code/6 := by rfl

theorem target_433_0 (code : Nat) :
    edgeTarget 0 433 code = 668736+code%7776 := by rfl

theorem block_433_0 :
    savedBlockClass (75*433+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_433_0 (code : Nat) :
    weight completedCredit 0 433 code =
      120*(code%6+1)+max (max 54 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 433 [] 54 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_433_0 direction_433.1
    direction_433.2.1 conditioned_433 code

theorem conditional_433_0 (code : Nat) :
    weight conditionalCredit 0 433 code =
      120*(code%6+1)+max (max 54 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 433 [] 54 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_433_0 direction_433.1
    direction_433.2.2 conditioned_433 code
#print axioms selected_433_0
#print axioms source_433_0
#print axioms target_433_0
#print axioms block_433_0
#print axioms completed_433_0
#print axioms conditional_433_0

theorem selected_434_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [434])) := by rfl

theorem source_434_0 (code : Nat) :
    edgeSource 0 434 code = 917568+code/6 := by rfl

theorem target_434_0 (code : Nat) :
    edgeTarget 0 434 code = 645408+code%7776 := by rfl

theorem block_434_0 :
    savedBlockClass (75*434+0) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_434_0 (code : Nat) :
    weight completedCredit 0 434 code =
      120*(code%6+1)+max (max 45 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 434 [] 45 0
    (fun code => 0) selected_434_0 direction_434.1
    direction_434.2.1 conditioned_434 code

theorem conditional_434_0 (code : Nat) :
    weight conditionalCredit 0 434 code =
      120*(code%6+1)+max (max 45 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 434 [] 45 16
    (fun code => 0) selected_434_0 direction_434.1
    direction_434.2.2 conditioned_434 code
#print axioms selected_434_0
#print axioms source_434_0
#print axioms target_434_0
#print axioms block_434_0
#print axioms completed_434_0
#print axioms conditional_434_0

theorem selected_435_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [435])) := by rfl

theorem source_435_0 (code : Nat) :
    edgeSource 0 435 code = 917568+code/6 := by rfl

theorem target_435_0 (code : Nat) :
    edgeTarget 0 435 code = 653184+code%7776 := by rfl

theorem block_435_0 :
    savedBlockClass (75*435+0) = some 40 ∧
    recordedClassRoot 40 = 3139 := by decide +kernel

theorem completed_435_0 (code : Nat) :
    weight completedCredit 0 435 code =
      120*(code%6+1)+max (max 43 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 435 [] 43 16
    (fun code => 0) selected_435_0 direction_435.1
    direction_435.2.1 conditioned_435 code

theorem conditional_435_0 (code : Nat) :
    weight conditionalCredit 0 435 code =
      120*(code%6+1)+max (max 43 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 435 [] 43 16
    (fun code => 0) selected_435_0 direction_435.1
    direction_435.2.2 conditioned_435 code
#print axioms selected_435_0
#print axioms source_435_0
#print axioms target_435_0
#print axioms block_435_0
#print axioms completed_435_0
#print axioms conditional_435_0

theorem selected_436_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [436])) := by rfl

theorem source_436_0 (code : Nat) :
    edgeSource 0 436 code = 917568+code/6 := by rfl

theorem target_436_0 (code : Nat) :
    edgeTarget 0 436 code = 660960+code%7776 := by rfl

theorem block_436_0 :
    savedBlockClass (75*436+0) = some 115 ∧
    recordedClassRoot 115 = 3910 := by decide +kernel

theorem completed_436_0 (code : Nat) :
    weight completedCredit 0 436 code =
      120*(code%6+1)+max (max 33 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 436 [] 33 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_436_0 direction_436.1
    direction_436.2.1 conditioned_436 code

theorem conditional_436_0 (code : Nat) :
    weight conditionalCredit 0 436 code =
      120*(code%6+1)+max (max 33 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 436 [] 33 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_436_0 direction_436.1
    direction_436.2.2 conditioned_436 code
#print axioms selected_436_0
#print axioms source_436_0
#print axioms target_436_0
#print axioms block_436_0
#print axioms completed_436_0
#print axioms conditional_436_0

theorem selected_437_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [437])) := by rfl

theorem source_437_0 (code : Nat) :
    edgeSource 0 437 code = 917568+code/6 := by rfl

theorem target_437_0 (code : Nat) :
    edgeTarget 0 437 code = 668736+code%7776 := by rfl

theorem block_437_0 :
    savedBlockClass (75*437+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_437_0 (code : Nat) :
    weight completedCredit 0 437 code =
      120*(code%6+1)+max (max 54 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 437 [] 54 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_437_0 direction_437.1
    direction_437.2.1 conditioned_437 code

theorem conditional_437_0 (code : Nat) :
    weight conditionalCredit 0 437 code =
      120*(code%6+1)+max (max 54 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 437 [] 54 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_437_0 direction_437.1
    direction_437.2.2 conditioned_437 code
#print axioms selected_437_0
#print axioms source_437_0
#print axioms target_437_0
#print axioms block_437_0
#print axioms completed_437_0
#print axioms conditional_437_0

theorem selected_438_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [438])) := by rfl

theorem source_438_0 (code : Nat) :
    edgeSource 0 438 code = 925344+code/6 := by rfl

theorem target_438_0 (code : Nat) :
    edgeTarget 0 438 code = 684288+code%7776 := by rfl

theorem block_438_0 :
    savedBlockClass (75*438+0) = some 126 ∧
    recordedClassRoot 126 = 3982 := by decide +kernel

theorem completed_438_0 (code : Nat) :
    weight completedCredit 0 438 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 438 [] 6 16
    (fun code => 0) selected_438_0 direction_438.1
    direction_438.2.1 conditioned_438 code

theorem conditional_438_0 (code : Nat) :
    weight conditionalCredit 0 438 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 438 [] 6 16
    (fun code => 0) selected_438_0 direction_438.1
    direction_438.2.2 conditioned_438 code
#print axioms selected_438_0
#print axioms source_438_0
#print axioms target_438_0
#print axioms block_438_0
#print axioms completed_438_0
#print axioms conditional_438_0

theorem selected_438_6 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 6 [] ++ [438])) := by rfl

theorem source_438_6 (code : Nat) :
    edgeSource 6 438 code = 1065312+code/6 := by rfl

theorem target_438_6 (code : Nat) :
    edgeTarget 6 438 code = 1314144+code%7776 := by rfl

theorem block_438_6 :
    savedBlockClass (75*438+6) = some 126 ∧
    recordedClassRoot 126 = 3982 := by decide +kernel

theorem completed_438_6 (code : Nat) :
    weight completedCredit 6 438 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 6 438 [] 6 16
    (fun code => 0) selected_438_6 direction_438.1
    direction_438.2.1 conditioned_438 code

theorem conditional_438_6 (code : Nat) :
    weight conditionalCredit 6 438 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 6 438 [] 6 16
    (fun code => 0) selected_438_6 direction_438.1
    direction_438.2.2 conditioned_438 code
#print axioms selected_438_6
#print axioms source_438_6
#print axioms target_438_6
#print axioms block_438_6
#print axioms completed_438_6
#print axioms conditional_438_6

theorem selected_439_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [439])) := by rfl

theorem source_439_0 (code : Nat) :
    edgeSource 0 439 code = 925344+code/6 := by rfl

theorem target_439_0 (code : Nat) :
    edgeTarget 0 439 code = 676512+code%7776 := by rfl

theorem block_439_0 :
    savedBlockClass (75*439+0) = some 126 ∧
    recordedClassRoot 126 = 3982 := by decide +kernel

theorem completed_439_0 (code : Nat) :
    weight completedCredit 0 439 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 439 [] 6 16
    (fun code => 0) selected_439_0 direction_439.1
    direction_439.2.1 conditioned_439 code

theorem conditional_439_0 (code : Nat) :
    weight conditionalCredit 0 439 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 439 [] 6 16
    (fun code => 0) selected_439_0 direction_439.1
    direction_439.2.2 conditioned_439 code
#print axioms selected_439_0
#print axioms source_439_0
#print axioms target_439_0
#print axioms block_439_0
#print axioms completed_439_0
#print axioms conditional_439_0

theorem selected_439_6 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 6 [] ++ [439])) := by rfl

theorem source_439_6 (code : Nat) :
    edgeSource 6 439 code = 1065312+code/6 := by rfl

theorem target_439_6 (code : Nat) :
    edgeTarget 6 439 code = 1321920+code%7776 := by rfl

theorem block_439_6 :
    savedBlockClass (75*439+6) = some 126 ∧
    recordedClassRoot 126 = 3982 := by decide +kernel

theorem completed_439_6 (code : Nat) :
    weight completedCredit 6 439 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 6 439 [] 6 16
    (fun code => 0) selected_439_6 direction_439.1
    direction_439.2.1 conditioned_439 code

theorem conditional_439_6 (code : Nat) :
    weight conditionalCredit 6 439 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 6 439 [] 6 16
    (fun code => 0) selected_439_6 direction_439.1
    direction_439.2.2 conditioned_439 code
#print axioms selected_439_6
#print axioms source_439_6
#print axioms target_439_6
#print axioms block_439_6
#print axioms completed_439_6
#print axioms conditional_439_6

theorem selected_440_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [440])) := by rfl

theorem source_440_0 (code : Nat) :
    edgeSource 0 440 code = 925344+code/6 := by rfl

theorem target_440_0 (code : Nat) :
    edgeTarget 0 440 code = 1228608+code%7776 := by rfl

theorem block_440_0 :
    savedBlockClass (75*440+0) = some 126 ∧
    recordedClassRoot 126 = 3982 := by decide +kernel

theorem completed_440_0 (code : Nat) :
    weight completedCredit 0 440 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 440 [] 6 16
    (fun code => 0) selected_440_0 direction_440.1
    direction_440.2.1 conditioned_440 code

theorem conditional_440_0 (code : Nat) :
    weight conditionalCredit 0 440 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 440 [] 6 16
    (fun code => 0) selected_440_0 direction_440.1
    direction_440.2.2 conditioned_440 code
#print axioms selected_440_0
#print axioms source_440_0
#print axioms target_440_0
#print axioms block_440_0
#print axioms completed_440_0
#print axioms conditional_440_0

theorem selected_440_6 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 6 [] ++ [440])) := by rfl

theorem source_440_6 (code : Nat) :
    edgeSource 6 440 code = 1065312+code/6 := by rfl

theorem target_440_6 (code : Nat) :
    edgeTarget 6 440 code = 1228608+code%7776 := by rfl

theorem block_440_6 :
    savedBlockClass (75*440+6) = some 126 ∧
    recordedClassRoot 126 = 3982 := by decide +kernel

theorem completed_440_6 (code : Nat) :
    weight completedCredit 6 440 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 6 440 [] 6 16
    (fun code => 0) selected_440_6 direction_440.1
    direction_440.2.1 conditioned_440 code

theorem conditional_440_6 (code : Nat) :
    weight conditionalCredit 6 440 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 6 440 [] 6 16
    (fun code => 0) selected_440_6 direction_440.1
    direction_440.2.2 conditioned_440 code
#print axioms selected_440_6
#print axioms source_440_6
#print axioms target_440_6
#print axioms block_440_6
#print axioms completed_440_6
#print axioms conditional_440_6

theorem selected_441_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [441])) := by rfl

theorem source_441_0 (code : Nat) :
    edgeSource 0 441 code = 933120+code/6 := by rfl

theorem target_441_0 (code : Nat) :
    edgeTarget 0 441 code = 699840+code%7776 := by rfl

theorem block_441_0 :
    savedBlockClass (75*441+0) = some 117 ∧
    recordedClassRoot 117 = 3932 := by decide +kernel

theorem completed_441_0 (code : Nat) :
    weight completedCredit 0 441 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 441 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_441_0 direction_441.1
    direction_441.2.1 conditioned_441 code

theorem conditional_441_0 (code : Nat) :
    weight conditionalCredit 0 441 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 441 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_441_0 direction_441.1
    direction_441.2.2 conditioned_441 code
#print axioms selected_441_0
#print axioms source_441_0
#print axioms target_441_0
#print axioms block_441_0
#print axioms completed_441_0
#print axioms conditional_441_0

theorem selected_442_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [442])) := by rfl

theorem source_442_0 (code : Nat) :
    edgeSource 0 442 code = 933120+code/6 := by rfl

theorem target_442_0 (code : Nat) :
    edgeTarget 0 442 code = 692064+code%7776 := by rfl

theorem block_442_0 :
    savedBlockClass (75*442+0) = some 117 ∧
    recordedClassRoot 117 = 3932 := by decide +kernel

theorem completed_442_0 (code : Nat) :
    weight completedCredit 0 442 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 442 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_442_0 direction_442.1
    direction_442.2.1 conditioned_442 code

theorem conditional_442_0 (code : Nat) :
    weight conditionalCredit 0 442 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 442 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_442_0 direction_442.1
    direction_442.2.2 conditioned_442 code
#print axioms selected_442_0
#print axioms source_442_0
#print axioms target_442_0
#print axioms block_442_0
#print axioms completed_442_0
#print axioms conditional_442_0

theorem selected_443_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [443])) := by rfl

theorem source_443_0 (code : Nat) :
    edgeSource 0 443 code = 933120+code/6 := by rfl

theorem target_443_0 (code : Nat) :
    edgeTarget 0 443 code = 699840+code%7776 := by rfl

theorem block_443_0 :
    savedBlockClass (75*443+0) = some 117 ∧
    recordedClassRoot 117 = 3932 := by decide +kernel

theorem completed_443_0 (code : Nat) :
    weight completedCredit 0 443 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 443 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_443_0 direction_443.1
    direction_443.2.1 conditioned_443 code

theorem conditional_443_0 (code : Nat) :
    weight conditionalCredit 0 443 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 443 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_443_0 direction_443.1
    direction_443.2.2 conditioned_443 code
#print axioms selected_443_0
#print axioms source_443_0
#print axioms target_443_0
#print axioms block_443_0
#print axioms completed_443_0
#print axioms conditional_443_0

theorem selected_444_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [444])) := by rfl

theorem source_444_0 (code : Nat) :
    edgeSource 0 444 code = 940896+code/6 := by rfl

theorem target_444_0 (code : Nat) :
    edgeTarget 0 444 code = 738720+code%7776 := by rfl

theorem block_444_0 :
    savedBlockClass (75*444+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_444_0 (code : Nat) :
    weight completedCredit 0 444 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 444 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_444_0 direction_444.1
    direction_444.2.1 conditioned_444 code

theorem conditional_444_0 (code : Nat) :
    weight conditionalCredit 0 444 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 444 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_444_0 direction_444.1
    direction_444.2.2 conditioned_444 code
#print axioms selected_444_0
#print axioms source_444_0
#print axioms target_444_0
#print axioms block_444_0
#print axioms completed_444_0
#print axioms conditional_444_0

theorem selected_445_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [445])) := by rfl

theorem source_445_0 (code : Nat) :
    edgeSource 0 445 code = 940896+code/6 := by rfl

theorem target_445_0 (code : Nat) :
    edgeTarget 0 445 code = 707616+code%7776 := by rfl

theorem block_445_0 :
    savedBlockClass (75*445+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_445_0 (code : Nat) :
    weight completedCredit 0 445 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 445 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_445_0 direction_445.1
    direction_445.2.1 conditioned_445 code

theorem conditional_445_0 (code : Nat) :
    weight conditionalCredit 0 445 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 445 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_445_0 direction_445.1
    direction_445.2.2 conditioned_445 code
#print axioms selected_445_0
#print axioms source_445_0
#print axioms target_445_0
#print axioms block_445_0
#print axioms completed_445_0
#print axioms conditional_445_0

theorem selected_446_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [446])) := by rfl

theorem source_446_0 (code : Nat) :
    edgeSource 0 446 code = 940896+code/6 := by rfl

theorem target_446_0 (code : Nat) :
    edgeTarget 0 446 code = 715392+code%7776 := by rfl

theorem block_446_0 :
    savedBlockClass (75*446+0) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_446_0 (code : Nat) :
    weight completedCredit 0 446 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 446 [] 13 0
    (fun code => 0) selected_446_0 direction_446.1
    direction_446.2.1 conditioned_446 code

theorem conditional_446_0 (code : Nat) :
    weight conditionalCredit 0 446 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 446 [] 13 16
    (fun code => 0) selected_446_0 direction_446.1
    direction_446.2.2 conditioned_446 code
#print axioms selected_446_0
#print axioms source_446_0
#print axioms target_446_0
#print axioms block_446_0
#print axioms completed_446_0
#print axioms conditional_446_0

theorem selected_447_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [447])) := by rfl

theorem source_447_0 (code : Nat) :
    edgeSource 0 447 code = 940896+code/6 := by rfl

theorem target_447_0 (code : Nat) :
    edgeTarget 0 447 code = 723168+code%7776 := by rfl

theorem block_447_0 :
    savedBlockClass (75*447+0) = some 40 ∧
    recordedClassRoot 40 = 3139 := by decide +kernel

theorem completed_447_0 (code : Nat) :
    weight completedCredit 0 447 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 447 [] 13 16
    (fun code => 0) selected_447_0 direction_447.1
    direction_447.2.1 conditioned_447 code

theorem conditional_447_0 (code : Nat) :
    weight conditionalCredit 0 447 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 447 [] 13 16
    (fun code => 0) selected_447_0 direction_447.1
    direction_447.2.2 conditioned_447 code
#print axioms selected_447_0
#print axioms source_447_0
#print axioms target_447_0
#print axioms block_447_0
#print axioms completed_447_0
#print axioms conditional_447_0

end Snake9.Context101
