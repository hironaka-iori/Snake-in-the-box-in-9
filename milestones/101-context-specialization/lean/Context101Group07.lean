import Direction101Group04
import Direction101Group05

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_282_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [282])) := by rfl

theorem source_282_0 (code : Nat) :
    edgeSource 0 282 code = 629856+code/6 := by rfl

theorem target_282_0 (code : Nat) :
    edgeTarget 0 282 code = 972000+code%7776 := by rfl

theorem block_282_0 :
    savedBlockClass (75*282+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_282_0 (code : Nat) :
    weight completedCredit 0 282 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 282 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_282_0 direction_282.1
    direction_282.2.1 conditioned_282 code

theorem conditional_282_0 (code : Nat) :
    weight conditionalCredit 0 282 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 282 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_282_0 direction_282.1
    direction_282.2.2 conditioned_282 code
#print axioms selected_282_0
#print axioms source_282_0
#print axioms target_282_0
#print axioms block_282_0
#print axioms completed_282_0
#print axioms conditional_282_0

theorem selected_282_26 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 26 [] ++ [282])) := by rfl

theorem source_282_26 (code : Nat) :
    edgeSource 26 282 code = 1220832+code/6 := by rfl

theorem target_282_26 (code : Nat) :
    edgeTarget 26 282 code = 972000+code%7776 := by rfl

theorem block_282_26 :
    savedBlockClass (75*282+26) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_282_26 (code : Nat) :
    weight completedCredit 26 282 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 26 282 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_282_26 direction_282.1
    direction_282.2.1 conditioned_282 code

theorem conditional_282_26 (code : Nat) :
    weight conditionalCredit 26 282 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 26 282 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_282_26 direction_282.1
    direction_282.2.2 conditioned_282 code
#print axioms selected_282_26
#print axioms source_282_26
#print axioms target_282_26
#print axioms block_282_26
#print axioms completed_282_26
#print axioms conditional_282_26

theorem selected_283_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [283])) := by rfl

theorem source_283_0 (code : Nat) :
    edgeSource 0 283 code = 637632+code/6 := by rfl

theorem target_283_0 (code : Nat) :
    edgeTarget 0 283 code = 1010880+code%7776 := by rfl

theorem block_283_0 :
    savedBlockClass (75*283+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_283_0 (code : Nat) :
    weight completedCredit 0 283 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 283 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_283_0 direction_283.1
    direction_283.2.1 conditioned_283 code

theorem conditional_283_0 (code : Nat) :
    weight conditionalCredit 0 283 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 283 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_283_0 direction_283.1
    direction_283.2.2 conditioned_283 code
#print axioms selected_283_0
#print axioms source_283_0
#print axioms target_283_0
#print axioms block_283_0
#print axioms completed_283_0
#print axioms conditional_283_0

theorem selected_284_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [284])) := by rfl

theorem source_284_0 (code : Nat) :
    edgeSource 0 284 code = 637632+code/6 := by rfl

theorem target_284_0 (code : Nat) :
    edgeTarget 0 284 code = 979776+code%7776 := by rfl

theorem block_284_0 :
    savedBlockClass (75*284+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_284_0 (code : Nat) :
    weight completedCredit 0 284 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 284 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_284_0 direction_284.1
    direction_284.2.1 conditioned_284 code

theorem conditional_284_0 (code : Nat) :
    weight conditionalCredit 0 284 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 284 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_284_0 direction_284.1
    direction_284.2.2 conditioned_284 code
#print axioms selected_284_0
#print axioms source_284_0
#print axioms target_284_0
#print axioms block_284_0
#print axioms completed_284_0
#print axioms conditional_284_0

theorem selected_285_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [285])) := by rfl

theorem source_285_0 (code : Nat) :
    edgeSource 0 285 code = 637632+code/6 := by rfl

theorem target_285_0 (code : Nat) :
    edgeTarget 0 285 code = 987552+code%7776 := by rfl

theorem block_285_0 :
    savedBlockClass (75*285+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_285_0 (code : Nat) :
    weight completedCredit 0 285 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 285 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_285_0 direction_285.1
    direction_285.2.1 conditioned_285 code

theorem conditional_285_0 (code : Nat) :
    weight conditionalCredit 0 285 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 285 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_285_0 direction_285.1
    direction_285.2.2 conditioned_285 code
#print axioms selected_285_0
#print axioms source_285_0
#print axioms target_285_0
#print axioms block_285_0
#print axioms completed_285_0
#print axioms conditional_285_0

theorem selected_286_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [286])) := by rfl

theorem source_286_0 (code : Nat) :
    edgeSource 0 286 code = 637632+code/6 := by rfl

theorem target_286_0 (code : Nat) :
    edgeTarget 0 286 code = 995328+code%7776 := by rfl

theorem block_286_0 :
    savedBlockClass (75*286+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_286_0 (code : Nat) :
    weight completedCredit 0 286 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 286 [] 0 0
    (fun code => 0) selected_286_0 direction_286.1
    direction_286.2.1 conditioned_286 code

theorem conditional_286_0 (code : Nat) :
    weight conditionalCredit 0 286 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 286 [] 0 16
    (fun code => 0) selected_286_0 direction_286.1
    direction_286.2.2 conditioned_286 code
#print axioms selected_286_0
#print axioms source_286_0
#print axioms target_286_0
#print axioms block_286_0
#print axioms completed_286_0
#print axioms conditional_286_0

theorem selected_287_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [287])) := by rfl

theorem source_287_0 (code : Nat) :
    edgeSource 0 287 code = 637632+code/6 := by rfl

theorem target_287_0 (code : Nat) :
    edgeTarget 0 287 code = 1003104+code%7776 := by rfl

theorem block_287_0 :
    savedBlockClass (75*287+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_287_0 (code : Nat) :
    weight completedCredit 0 287 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 287 [] 0 16
    (fun code => 0) selected_287_0 direction_287.1
    direction_287.2.1 conditioned_287 code

theorem conditional_287_0 (code : Nat) :
    weight conditionalCredit 0 287 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 287 [] 0 16
    (fun code => 0) selected_287_0 direction_287.1
    direction_287.2.2 conditioned_287 code
#print axioms selected_287_0
#print axioms source_287_0
#print axioms target_287_0
#print axioms block_287_0
#print axioms completed_287_0
#print axioms conditional_287_0

theorem selected_288_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [288])) := by rfl

theorem source_288_0 (code : Nat) :
    edgeSource 0 288 code = 637632+code/6 := by rfl

theorem target_288_0 (code : Nat) :
    edgeTarget 0 288 code = 1018656+code%7776 := by rfl

theorem block_288_0 :
    savedBlockClass (75*288+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_288_0 (code : Nat) :
    weight completedCredit 0 288 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 288 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_288_0 direction_288.1
    direction_288.2.1 conditioned_288 code

theorem conditional_288_0 (code : Nat) :
    weight conditionalCredit 0 288 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 288 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_288_0 direction_288.1
    direction_288.2.2 conditioned_288 code
#print axioms selected_288_0
#print axioms source_288_0
#print axioms target_288_0
#print axioms block_288_0
#print axioms completed_288_0
#print axioms conditional_288_0

theorem selected_289_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [289])) := by rfl

theorem source_289_0 (code : Nat) :
    edgeSource 0 289 code = 645408+code/6 := by rfl

theorem target_289_0 (code : Nat) :
    edgeTarget 0 289 code = 256608+code%7776 := by rfl

theorem block_289_0 :
    savedBlockClass (75*289+0) = some 7 ∧
    recordedClassRoot 7 = 1278 := by decide +kernel

theorem completed_289_0 (code : Nat) :
    weight completedCredit 0 289 code =
      120*(code%6+1)+max (max 27 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 289 [] 27 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_289_0 direction_289.1
    direction_289.2.1 conditioned_289 code

theorem conditional_289_0 (code : Nat) :
    weight conditionalCredit 0 289 code =
      120*(code%6+1)+max (max 27 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 289 [] 27 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_289_0 direction_289.1
    direction_289.2.2 conditioned_289 code
#print axioms selected_289_0
#print axioms source_289_0
#print axioms target_289_0
#print axioms block_289_0
#print axioms completed_289_0
#print axioms conditional_289_0

theorem selected_290_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [290])) := by rfl

theorem source_290_0 (code : Nat) :
    edgeSource 0 290 code = 645408+code/6 := by rfl

theorem target_290_0 (code : Nat) :
    edgeTarget 0 290 code = 279936+code%7776 := by rfl

theorem block_290_0 :
    savedBlockClass (75*290+0) = some 8 ∧
    recordedClassRoot 8 = 1378 := by decide +kernel

theorem completed_290_0 (code : Nat) :
    weight completedCredit 0 290 code =
      120*(code%6+1)+max (max 27 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 290 [] 27 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_290_0 direction_290.1
    direction_290.2.1 conditioned_290 code

theorem conditional_290_0 (code : Nat) :
    weight conditionalCredit 0 290 code =
      120*(code%6+1)+max (max 27 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 290 [] 27 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_290_0 direction_290.1
    direction_290.2.2 conditioned_290 code
#print axioms selected_290_0
#print axioms source_290_0
#print axioms target_290_0
#print axioms block_290_0
#print axioms completed_290_0
#print axioms conditional_290_0

theorem selected_291_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [291])) := by rfl

theorem source_291_0 (code : Nat) :
    edgeSource 0 291 code = 653184+code/6 := by rfl

theorem target_291_0 (code : Nat) :
    edgeTarget 0 291 code = 287712+code%7776 := by rfl

theorem block_291_0 :
    savedBlockClass (75*291+0) = some 3 ∧
    recordedClassRoot 3 = 669 := by decide +kernel

theorem completed_291_0 (code : Nat) :
    weight completedCredit 0 291 code =
      120*(code%6+1)+max (max 33 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 291 [] 33 16
    (fun code => 0) selected_291_0 direction_291.1
    direction_291.2.1 conditioned_291 code

theorem conditional_291_0 (code : Nat) :
    weight conditionalCredit 0 291 code =
      120*(code%6+1)+max (max 33 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 291 [] 33 16
    (fun code => 0) selected_291_0 direction_291.1
    direction_291.2.2 conditioned_291 code
#print axioms selected_291_0
#print axioms source_291_0
#print axioms target_291_0
#print axioms block_291_0
#print axioms completed_291_0
#print axioms conditional_291_0

theorem selected_292_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [292])) := by rfl

theorem source_292_0 (code : Nat) :
    edgeSource 0 292 code = 653184+code/6 := by rfl

theorem target_292_0 (code : Nat) :
    edgeTarget 0 292 code = 311040+code%7776 := by rfl

theorem block_292_0 :
    savedBlockClass (75*292+0) = some 4 ∧
    recordedClassRoot 4 = 846 := by decide +kernel

theorem completed_292_0 (code : Nat) :
    weight completedCredit 0 292 code =
      120*(code%6+1)+max (max 40 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 292 [] 40 16
    (fun code => 0) selected_292_0 direction_292.1
    direction_292.2.1 conditioned_292 code

theorem conditional_292_0 (code : Nat) :
    weight conditionalCredit 0 292 code =
      120*(code%6+1)+max (max 40 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 292 [] 40 16
    (fun code => 0) selected_292_0 direction_292.1
    direction_292.2.2 conditioned_292 code
#print axioms selected_292_0
#print axioms source_292_0
#print axioms target_292_0
#print axioms block_292_0
#print axioms completed_292_0
#print axioms conditional_292_0

theorem selected_293_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [293])) := by rfl

theorem source_293_0 (code : Nat) :
    edgeSource 0 293 code = 660960+code/6 := by rfl

theorem target_293_0 (code : Nat) :
    edgeTarget 0 293 code = 334368+code%7776 := by rfl

theorem block_293_0 :
    savedBlockClass (75*293+0) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_293_0 (code : Nat) :
    weight completedCredit 0 293 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 293 [] 22 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_293_0 direction_293.1
    direction_293.2.1 conditioned_293 code

theorem conditional_293_0 (code : Nat) :
    weight conditionalCredit 0 293 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 293 [] 22 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_293_0 direction_293.1
    direction_293.2.2 conditioned_293 code
#print axioms selected_293_0
#print axioms source_293_0
#print axioms target_293_0
#print axioms block_293_0
#print axioms completed_293_0
#print axioms conditional_293_0

theorem selected_294_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [294])) := by rfl

theorem source_294_0 (code : Nat) :
    edgeSource 0 294 code = 668736+code/6 := by rfl

theorem target_294_0 (code : Nat) :
    edgeTarget 0 294 code = 342144+code%7776 := by rfl

theorem block_294_0 :
    savedBlockClass (75*294+0) = some 12 ∧
    recordedClassRoot 12 = 1807 := by decide +kernel

theorem completed_294_0 (code : Nat) :
    weight completedCredit 0 294 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 294 [] 12 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_294_0 direction_294.1
    direction_294.2.1 conditioned_294 code

theorem conditional_294_0 (code : Nat) :
    weight conditionalCredit 0 294 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 294 [] 12 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_294_0 direction_294.1
    direction_294.2.2 conditioned_294 code
#print axioms selected_294_0
#print axioms source_294_0
#print axioms target_294_0
#print axioms block_294_0
#print axioms completed_294_0
#print axioms conditional_294_0

theorem selected_295_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [295])) := by rfl

theorem source_295_0 (code : Nat) :
    edgeSource 0 295 code = 668736+code/6 := by rfl

theorem target_295_0 (code : Nat) :
    edgeTarget 0 295 code = 349920+code%7776 := by rfl

theorem block_295_0 :
    savedBlockClass (75*295+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_295_0 (code : Nat) :
    weight completedCredit 0 295 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 295 [] 12 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_295_0 direction_295.1
    direction_295.2.1 conditioned_295 code

theorem conditional_295_0 (code : Nat) :
    weight conditionalCredit 0 295 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 295 [] 12 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_295_0 direction_295.1
    direction_295.2.2 conditioned_295 code
#print axioms selected_295_0
#print axioms source_295_0
#print axioms target_295_0
#print axioms block_295_0
#print axioms completed_295_0
#print axioms conditional_295_0

theorem selected_296_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [296])) := by rfl

theorem source_296_0 (code : Nat) :
    edgeSource 0 296 code = 668736+code/6 := by rfl

theorem target_296_0 (code : Nat) :
    edgeTarget 0 296 code = 357696+code%7776 := by rfl

theorem block_296_0 :
    savedBlockClass (75*296+0) = some 11 ∧
    recordedClassRoot 11 = 1698 := by decide +kernel

theorem completed_296_0 (code : Nat) :
    weight completedCredit 0 296 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 296 [] 12 0
    (fun code => 0) selected_296_0 direction_296.1
    direction_296.2.1 conditioned_296 code

theorem conditional_296_0 (code : Nat) :
    weight conditionalCredit 0 296 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 296 [] 12 16
    (fun code => 0) selected_296_0 direction_296.1
    direction_296.2.2 conditioned_296 code
#print axioms selected_296_0
#print axioms source_296_0
#print axioms target_296_0
#print axioms block_296_0
#print axioms completed_296_0
#print axioms conditional_296_0

theorem selected_297_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [297])) := by rfl

theorem source_297_0 (code : Nat) :
    edgeSource 0 297 code = 668736+code/6 := by rfl

theorem target_297_0 (code : Nat) :
    edgeTarget 0 297 code = 365472+code%7776 := by rfl

theorem block_297_0 :
    savedBlockClass (75*297+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_297_0 (code : Nat) :
    weight completedCredit 0 297 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 297 [] 12 16
    (fun code => 0) selected_297_0 direction_297.1
    direction_297.2.1 conditioned_297 code

theorem conditional_297_0 (code : Nat) :
    weight conditionalCredit 0 297 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 297 [] 12 16
    (fun code => 0) selected_297_0 direction_297.1
    direction_297.2.2 conditioned_297 code
#print axioms selected_297_0
#print axioms source_297_0
#print axioms target_297_0
#print axioms block_297_0
#print axioms completed_297_0
#print axioms conditional_297_0

theorem selected_298_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [298])) := by rfl

theorem source_298_0 (code : Nat) :
    edgeSource 0 298 code = 668736+code/6 := by rfl

theorem target_298_0 (code : Nat) :
    edgeTarget 0 298 code = 373248+code%7776 := by rfl

theorem block_298_0 :
    savedBlockClass (75*298+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_298_0 (code : Nat) :
    weight completedCredit 0 298 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 298 [] 12 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_298_0 direction_298.1
    direction_298.2.1 conditioned_298 code

theorem conditional_298_0 (code : Nat) :
    weight conditionalCredit 0 298 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 298 [] 12 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_298_0 direction_298.1
    direction_298.2.2 conditioned_298 code
#print axioms selected_298_0
#print axioms source_298_0
#print axioms target_298_0
#print axioms block_298_0
#print axioms completed_298_0
#print axioms conditional_298_0

theorem selected_299_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [299])) := by rfl

theorem source_299_0 (code : Nat) :
    edgeSource 0 299 code = 676512+code/6 := by rfl

theorem target_299_0 (code : Nat) :
    edgeTarget 0 299 code = 194400+code%7776 := by rfl

theorem block_299_0 :
    savedBlockClass (75*299+0) = some 105 ∧
    recordedClassRoot 105 = 3849 := by decide +kernel

theorem completed_299_0 (code : Nat) :
    weight completedCredit 0 299 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 299 [] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_299_0 direction_299.1
    direction_299.2.1 conditioned_299 code

theorem conditional_299_0 (code : Nat) :
    weight conditionalCredit 0 299 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 299 [] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_299_0 direction_299.1
    direction_299.2.2 conditioned_299 code
#print axioms selected_299_0
#print axioms source_299_0
#print axioms target_299_0
#print axioms block_299_0
#print axioms completed_299_0
#print axioms conditional_299_0

theorem selected_299_5 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 5 [] ++ [299])) := by rfl

theorem source_299_5 (code : Nat) :
    edgeSource 5 299 code = 1057536+code/6 := by rfl

theorem target_299_5 (code : Nat) :
    edgeTarget 5 299 code = 194400+code%7776 := by rfl

theorem block_299_5 :
    savedBlockClass (75*299+5) = some 105 ∧
    recordedClassRoot 105 = 3849 := by decide +kernel

theorem completed_299_5 (code : Nat) :
    weight completedCredit 5 299 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 5 299 [] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_299_5 direction_299.1
    direction_299.2.1 conditioned_299 code

theorem conditional_299_5 (code : Nat) :
    weight conditionalCredit 5 299 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 5 299 [] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_299_5 direction_299.1
    direction_299.2.2 conditioned_299 code
#print axioms selected_299_5
#print axioms source_299_5
#print axioms target_299_5
#print axioms block_299_5
#print axioms completed_299_5
#print axioms conditional_299_5

theorem selected_299_39 :
    [rule002] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 39 [] ++ [299])) := by rfl

theorem source_299_39 (code : Nat) :
    edgeSource 39 299 code = 1321920+code/6 := by rfl

theorem target_299_39 (code : Nat) :
    edgeTarget 39 299 code = 194400+code%7776 := by rfl

theorem block_299_39 :
    savedBlockClass (75*299+39) = some 105 ∧
    recordedClassRoot 105 = 3849 := by decide +kernel

theorem completed_299_39 (code : Nat) :
    weight completedCredit 39 299 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule002] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 39 299 [rule002] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_299_39 direction_299.1
    direction_299.2.1 conditioned_299 code

theorem conditional_299_39 (code : Nat) :
    weight conditionalCredit 39 299 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule002] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 39 299 [rule002] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_299_39 direction_299.1
    direction_299.2.2 conditioned_299 code
#print axioms selected_299_39
#print axioms source_299_39
#print axioms target_299_39
#print axioms block_299_39
#print axioms completed_299_39
#print axioms conditional_299_39

theorem selected_299_46 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 46 [] ++ [299])) := by rfl

theorem source_299_46 (code : Nat) :
    edgeSource 46 299 code = 1376352+code/6 := by rfl

theorem target_299_46 (code : Nat) :
    edgeTarget 46 299 code = 194400+code%7776 := by rfl

theorem block_299_46 :
    savedBlockClass (75*299+46) = some 105 ∧
    recordedClassRoot 105 = 3849 := by decide +kernel

theorem completed_299_46 (code : Nat) :
    weight completedCredit 46 299 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 46 299 [] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_299_46 direction_299.1
    direction_299.2.1 conditioned_299 code

theorem conditional_299_46 (code : Nat) :
    weight conditionalCredit 46 299 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 46 299 [] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_299_46 direction_299.1
    direction_299.2.2 conditioned_299 code
#print axioms selected_299_46
#print axioms source_299_46
#print axioms target_299_46
#print axioms block_299_46
#print axioms completed_299_46
#print axioms conditional_299_46

theorem selected_300_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [300])) := by rfl

theorem source_300_0 (code : Nat) :
    edgeSource 0 300 code = 676512+code/6 := by rfl

theorem target_300_0 (code : Nat) :
    edgeTarget 0 300 code = 217728+code%7776 := by rfl

theorem block_300_0 :
    savedBlockClass (75*300+0) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_300_0 (code : Nat) :
    weight completedCredit 0 300 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 300 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_300_0 direction_300.1
    direction_300.2.1 conditioned_300 code

theorem conditional_300_0 (code : Nat) :
    weight conditionalCredit 0 300 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 300 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_300_0 direction_300.1
    direction_300.2.2 conditioned_300 code
#print axioms selected_300_0
#print axioms source_300_0
#print axioms target_300_0
#print axioms block_300_0
#print axioms completed_300_0
#print axioms conditional_300_0

theorem selected_300_5 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 5 [] ++ [300])) := by rfl

theorem source_300_5 (code : Nat) :
    edgeSource 5 300 code = 1057536+code/6 := by rfl

theorem target_300_5 (code : Nat) :
    edgeTarget 5 300 code = 1306368+code%7776 := by rfl

theorem block_300_5 :
    savedBlockClass (75*300+5) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_300_5 (code : Nat) :
    weight completedCredit 5 300 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 5 300 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_300_5 direction_300.1
    direction_300.2.1 conditioned_300 code

theorem conditional_300_5 (code : Nat) :
    weight conditionalCredit 5 300 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 5 300 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_300_5 direction_300.1
    direction_300.2.2 conditioned_300 code
#print axioms selected_300_5
#print axioms source_300_5
#print axioms target_300_5
#print axioms block_300_5
#print axioms completed_300_5
#print axioms conditional_300_5

theorem selected_300_39 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 39 [] ++ [300])) := by rfl

theorem source_300_39 (code : Nat) :
    edgeSource 39 300 code = 1321920+code/6 := by rfl

theorem target_300_39 (code : Nat) :
    edgeTarget 39 300 code = 217728+code%7776 := by rfl

theorem block_300_39 :
    savedBlockClass (75*300+39) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_300_39 (code : Nat) :
    weight completedCredit 39 300 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 39 300 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_300_39 direction_300.1
    direction_300.2.1 conditioned_300 code

theorem conditional_300_39 (code : Nat) :
    weight conditionalCredit 39 300 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 39 300 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_300_39 direction_300.1
    direction_300.2.2 conditioned_300 code
#print axioms selected_300_39
#print axioms source_300_39
#print axioms target_300_39
#print axioms block_300_39
#print axioms completed_300_39
#print axioms conditional_300_39

theorem selected_300_46 :
    [rule003] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 46 [] ++ [300])) := by rfl

theorem source_300_46 (code : Nat) :
    edgeSource 46 300 code = 1376352+code/6 := by rfl

theorem target_300_46 (code : Nat) :
    edgeTarget 46 300 code = 1306368+code%7776 := by rfl

theorem block_300_46 :
    savedBlockClass (75*300+46) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_300_46 (code : Nat) :
    weight completedCredit 46 300 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule003] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 46 300 [rule003] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_300_46 direction_300.1
    direction_300.2.1 conditioned_300 code

theorem conditional_300_46 (code : Nat) :
    weight conditionalCredit 46 300 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule003] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 46 300 [rule003] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_300_46 direction_300.1
    direction_300.2.2 conditioned_300 code
#print axioms selected_300_46
#print axioms source_300_46
#print axioms target_300_46
#print axioms block_300_46
#print axioms completed_300_46
#print axioms conditional_300_46

theorem selected_301_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [301])) := by rfl

theorem source_301_0 (code : Nat) :
    edgeSource 0 301 code = 684288+code/6 := by rfl

theorem target_301_0 (code : Nat) :
    edgeTarget 0 301 code = 217728+code%7776 := by rfl

theorem block_301_0 :
    savedBlockClass (75*301+0) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_301_0 (code : Nat) :
    weight completedCredit 0 301 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 301 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_301_0 direction_301.1
    direction_301.2.1 conditioned_301 code

theorem conditional_301_0 (code : Nat) :
    weight conditionalCredit 0 301 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 301 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_301_0 direction_301.1
    direction_301.2.2 conditioned_301 code
#print axioms selected_301_0
#print axioms source_301_0
#print axioms target_301_0
#print axioms block_301_0
#print axioms completed_301_0
#print axioms conditional_301_0

theorem selected_301_27 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 27 [] ++ [301])) := by rfl

theorem source_301_27 (code : Nat) :
    edgeSource 27 301 code = 1228608+code/6 := by rfl

theorem target_301_27 (code : Nat) :
    edgeTarget 27 301 code = 217728+code%7776 := by rfl

theorem block_301_27 :
    savedBlockClass (75*301+27) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_301_27 (code : Nat) :
    weight completedCredit 27 301 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 27 301 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_301_27 direction_301.1
    direction_301.2.1 conditioned_301 code

theorem conditional_301_27 (code : Nat) :
    weight conditionalCredit 27 301 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 27 301 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_301_27 direction_301.1
    direction_301.2.2 conditioned_301 code
#print axioms selected_301_27
#print axioms source_301_27
#print axioms target_301_27
#print axioms block_301_27
#print axioms completed_301_27
#print axioms conditional_301_27

theorem selected_301_38 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 38 [] ++ [301])) := by rfl

theorem source_301_38 (code : Nat) :
    edgeSource 38 301 code = 1314144+code/6 := by rfl

theorem target_301_38 (code : Nat) :
    edgeTarget 38 301 code = 217728+code%7776 := by rfl

theorem block_301_38 :
    savedBlockClass (75*301+38) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_301_38 (code : Nat) :
    weight completedCredit 38 301 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 38 301 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_301_38 direction_301.1
    direction_301.2.1 conditioned_301 code

theorem conditional_301_38 (code : Nat) :
    weight conditionalCredit 38 301 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 38 301 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_301_38 direction_301.1
    direction_301.2.2 conditioned_301 code
#print axioms selected_301_38
#print axioms source_301_38
#print axioms target_301_38
#print axioms block_301_38
#print axioms completed_301_38
#print axioms conditional_301_38

theorem selected_301_47 :
    [rule004] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 47 [] ++ [301])) := by rfl

theorem source_301_47 (code : Nat) :
    edgeSource 47 301 code = 1384128+code/6 := by rfl

theorem target_301_47 (code : Nat) :
    edgeTarget 47 301 code = 217728+code%7776 := by rfl

theorem block_301_47 :
    savedBlockClass (75*301+47) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_301_47 (code : Nat) :
    weight completedCredit 47 301 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule004] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 47 301 [rule004] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_301_47 direction_301.1
    direction_301.2.1 conditioned_301 code

theorem conditional_301_47 (code : Nat) :
    weight conditionalCredit 47 301 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule004] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 47 301 [rule004] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_301_47 direction_301.1
    direction_301.2.2 conditioned_301 code
#print axioms selected_301_47
#print axioms source_301_47
#print axioms target_301_47
#print axioms block_301_47
#print axioms completed_301_47
#print axioms conditional_301_47

theorem selected_302_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [302])) := by rfl

theorem source_302_0 (code : Nat) :
    edgeSource 0 302 code = 684288+code/6 := by rfl

theorem target_302_0 (code : Nat) :
    edgeTarget 0 302 code = 1166400+code%7776 := by rfl

theorem block_302_0 :
    savedBlockClass (75*302+0) = some 105 ∧
    recordedClassRoot 105 = 3849 := by decide +kernel

theorem completed_302_0 (code : Nat) :
    weight completedCredit 0 302 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 302 [] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_302_0 direction_302.1
    direction_302.2.1 conditioned_302 code

theorem conditional_302_0 (code : Nat) :
    weight conditionalCredit 0 302 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 302 [] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_302_0 direction_302.1
    direction_302.2.2 conditioned_302 code
#print axioms selected_302_0
#print axioms source_302_0
#print axioms target_302_0
#print axioms block_302_0
#print axioms completed_302_0
#print axioms conditional_302_0

theorem selected_302_27 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 27 [] ++ [302])) := by rfl

theorem source_302_27 (code : Nat) :
    edgeSource 27 302 code = 1228608+code/6 := by rfl

theorem target_302_27 (code : Nat) :
    edgeTarget 27 302 code = 1539648+code%7776 := by rfl

theorem block_302_27 :
    savedBlockClass (75*302+27) = some 105 ∧
    recordedClassRoot 105 = 3849 := by decide +kernel

theorem completed_302_27 (code : Nat) :
    weight completedCredit 27 302 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 27 302 [] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_302_27 direction_302.1
    direction_302.2.1 conditioned_302 code

theorem conditional_302_27 (code : Nat) :
    weight conditionalCredit 27 302 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 27 302 [] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_302_27 direction_302.1
    direction_302.2.2 conditioned_302 code
#print axioms selected_302_27
#print axioms source_302_27
#print axioms target_302_27
#print axioms block_302_27
#print axioms completed_302_27
#print axioms conditional_302_27

theorem selected_302_38 :
    [rule001] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 38 [] ++ [302])) := by rfl

theorem source_302_38 (code : Nat) :
    edgeSource 38 302 code = 1314144+code/6 := by rfl

theorem target_302_38 (code : Nat) :
    edgeTarget 38 302 code = 1166400+code%7776 := by rfl

theorem block_302_38 :
    savedBlockClass (75*302+38) = some 105 ∧
    recordedClassRoot 105 = 3849 := by decide +kernel

theorem completed_302_38 (code : Nat) :
    weight completedCredit 38 302 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule001] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 38 302 [rule001] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_302_38 direction_302.1
    direction_302.2.1 conditioned_302 code

theorem conditional_302_38 (code : Nat) :
    weight conditionalCredit 38 302 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule001] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 38 302 [rule001] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_302_38 direction_302.1
    direction_302.2.2 conditioned_302 code
#print axioms selected_302_38
#print axioms source_302_38
#print axioms target_302_38
#print axioms block_302_38
#print axioms completed_302_38
#print axioms conditional_302_38

theorem selected_302_47 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 47 [] ++ [302])) := by rfl

theorem source_302_47 (code : Nat) :
    edgeSource 47 302 code = 1384128+code/6 := by rfl

theorem target_302_47 (code : Nat) :
    edgeTarget 47 302 code = 1166400+code%7776 := by rfl

theorem block_302_47 :
    savedBlockClass (75*302+47) = some 105 ∧
    recordedClassRoot 105 = 3849 := by decide +kernel

theorem completed_302_47 (code : Nat) :
    weight completedCredit 47 302 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 47 302 [] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_302_47 direction_302.1
    direction_302.2.1 conditioned_302 code

theorem conditional_302_47 (code : Nat) :
    weight conditionalCredit 47 302 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 47 302 [] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_302_47 direction_302.1
    direction_302.2.2 conditioned_302 code
#print axioms selected_302_47
#print axioms source_302_47
#print axioms target_302_47
#print axioms block_302_47
#print axioms completed_302_47
#print axioms conditional_302_47

theorem selected_303_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [303])) := by rfl

theorem source_303_0 (code : Nat) :
    edgeSource 0 303 code = 684288+code/6 := by rfl

theorem target_303_0 (code : Nat) :
    edgeTarget 0 303 code = 202176+code%7776 := by rfl

theorem block_303_0 :
    savedBlockClass (75*303+0) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_303_0 (code : Nat) :
    weight completedCredit 0 303 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 303 [] 4 0
    (fun code => 0) selected_303_0 direction_303.1
    direction_303.2.1 conditioned_303 code

theorem conditional_303_0 (code : Nat) :
    weight conditionalCredit 0 303 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 303 [] 4 16
    (fun code => 0) selected_303_0 direction_303.1
    direction_303.2.2 conditioned_303 code
#print axioms selected_303_0
#print axioms source_303_0
#print axioms target_303_0
#print axioms block_303_0
#print axioms completed_303_0
#print axioms conditional_303_0

theorem selected_303_27 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 27 [] ++ [303])) := by rfl

theorem source_303_27 (code : Nat) :
    edgeSource 27 303 code = 1228608+code/6 := by rfl

theorem target_303_27 (code : Nat) :
    edgeTarget 27 303 code = 202176+code%7776 := by rfl

theorem block_303_27 :
    savedBlockClass (75*303+27) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_303_27 (code : Nat) :
    weight completedCredit 27 303 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 27 303 [] 4 0
    (fun code => 0) selected_303_27 direction_303.1
    direction_303.2.1 conditioned_303 code

theorem conditional_303_27 (code : Nat) :
    weight conditionalCredit 27 303 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 27 303 [] 4 16
    (fun code => 0) selected_303_27 direction_303.1
    direction_303.2.2 conditioned_303 code
#print axioms selected_303_27
#print axioms source_303_27
#print axioms target_303_27
#print axioms block_303_27
#print axioms completed_303_27
#print axioms conditional_303_27

theorem selected_303_38 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 38 [] ++ [303])) := by rfl

theorem source_303_38 (code : Nat) :
    edgeSource 38 303 code = 1314144+code/6 := by rfl

theorem target_303_38 (code : Nat) :
    edgeTarget 38 303 code = 202176+code%7776 := by rfl

theorem block_303_38 :
    savedBlockClass (75*303+38) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_303_38 (code : Nat) :
    weight completedCredit 38 303 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 38 303 [] 4 0
    (fun code => 0) selected_303_38 direction_303.1
    direction_303.2.1 conditioned_303 code

theorem conditional_303_38 (code : Nat) :
    weight conditionalCredit 38 303 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 38 303 [] 4 16
    (fun code => 0) selected_303_38 direction_303.1
    direction_303.2.2 conditioned_303 code
#print axioms selected_303_38
#print axioms source_303_38
#print axioms target_303_38
#print axioms block_303_38
#print axioms completed_303_38
#print axioms conditional_303_38

theorem selected_303_47 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 47 [] ++ [303])) := by rfl

theorem source_303_47 (code : Nat) :
    edgeSource 47 303 code = 1384128+code/6 := by rfl

theorem target_303_47 (code : Nat) :
    edgeTarget 47 303 code = 202176+code%7776 := by rfl

theorem block_303_47 :
    savedBlockClass (75*303+47) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_303_47 (code : Nat) :
    weight completedCredit 47 303 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 47 303 [] 4 0
    (fun code => 0) selected_303_47 direction_303.1
    direction_303.2.1 conditioned_303 code

theorem conditional_303_47 (code : Nat) :
    weight conditionalCredit 47 303 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 47 303 [] 4 16
    (fun code => 0) selected_303_47 direction_303.1
    direction_303.2.2 conditioned_303 code
#print axioms selected_303_47
#print axioms source_303_47
#print axioms target_303_47
#print axioms block_303_47
#print axioms completed_303_47
#print axioms conditional_303_47

theorem selected_304_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [304])) := by rfl

theorem source_304_0 (code : Nat) :
    edgeSource 0 304 code = 684288+code/6 := by rfl

theorem target_304_0 (code : Nat) :
    edgeTarget 0 304 code = 209952+code%7776 := by rfl

theorem block_304_0 :
    savedBlockClass (75*304+0) = some 102 ∧
    recordedClassRoot 102 = 3829 := by decide +kernel

theorem completed_304_0 (code : Nat) :
    weight completedCredit 0 304 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 304 [] 5 16
    (fun code => 0) selected_304_0 direction_304.1
    direction_304.2.1 conditioned_304 code

theorem conditional_304_0 (code : Nat) :
    weight conditionalCredit 0 304 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 304 [] 5 16
    (fun code => 0) selected_304_0 direction_304.1
    direction_304.2.2 conditioned_304 code
#print axioms selected_304_0
#print axioms source_304_0
#print axioms target_304_0
#print axioms block_304_0
#print axioms completed_304_0
#print axioms conditional_304_0

theorem selected_304_27 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 27 [] ++ [304])) := by rfl

theorem source_304_27 (code : Nat) :
    edgeSource 27 304 code = 1228608+code/6 := by rfl

theorem target_304_27 (code : Nat) :
    edgeTarget 27 304 code = 209952+code%7776 := by rfl

theorem block_304_27 :
    savedBlockClass (75*304+27) = some 102 ∧
    recordedClassRoot 102 = 3829 := by decide +kernel

theorem completed_304_27 (code : Nat) :
    weight completedCredit 27 304 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 27 304 [] 5 16
    (fun code => 0) selected_304_27 direction_304.1
    direction_304.2.1 conditioned_304 code

theorem conditional_304_27 (code : Nat) :
    weight conditionalCredit 27 304 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 27 304 [] 5 16
    (fun code => 0) selected_304_27 direction_304.1
    direction_304.2.2 conditioned_304 code
#print axioms selected_304_27
#print axioms source_304_27
#print axioms target_304_27
#print axioms block_304_27
#print axioms completed_304_27
#print axioms conditional_304_27

theorem selected_304_38 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 38 [] ++ [304])) := by rfl

theorem source_304_38 (code : Nat) :
    edgeSource 38 304 code = 1314144+code/6 := by rfl

theorem target_304_38 (code : Nat) :
    edgeTarget 38 304 code = 209952+code%7776 := by rfl

theorem block_304_38 :
    savedBlockClass (75*304+38) = some 102 ∧
    recordedClassRoot 102 = 3829 := by decide +kernel

theorem completed_304_38 (code : Nat) :
    weight completedCredit 38 304 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 38 304 [] 5 16
    (fun code => 0) selected_304_38 direction_304.1
    direction_304.2.1 conditioned_304 code

theorem conditional_304_38 (code : Nat) :
    weight conditionalCredit 38 304 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 38 304 [] 5 16
    (fun code => 0) selected_304_38 direction_304.1
    direction_304.2.2 conditioned_304 code
#print axioms selected_304_38
#print axioms source_304_38
#print axioms target_304_38
#print axioms block_304_38
#print axioms completed_304_38
#print axioms conditional_304_38

theorem selected_304_47 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 47 [] ++ [304])) := by rfl

theorem source_304_47 (code : Nat) :
    edgeSource 47 304 code = 1384128+code/6 := by rfl

theorem target_304_47 (code : Nat) :
    edgeTarget 47 304 code = 209952+code%7776 := by rfl

theorem block_304_47 :
    savedBlockClass (75*304+47) = some 102 ∧
    recordedClassRoot 102 = 3829 := by decide +kernel

theorem completed_304_47 (code : Nat) :
    weight completedCredit 47 304 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 47 304 [] 5 16
    (fun code => 0) selected_304_47 direction_304.1
    direction_304.2.1 conditioned_304 code

theorem conditional_304_47 (code : Nat) :
    weight conditionalCredit 47 304 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 47 304 [] 5 16
    (fun code => 0) selected_304_47 direction_304.1
    direction_304.2.2 conditioned_304 code
#print axioms selected_304_47
#print axioms source_304_47
#print axioms target_304_47
#print axioms block_304_47
#print axioms completed_304_47
#print axioms conditional_304_47

theorem selected_305_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [305])) := by rfl

theorem source_305_0 (code : Nat) :
    edgeSource 0 305 code = 684288+code/6 := by rfl

theorem target_305_0 (code : Nat) :
    edgeTarget 0 305 code = 1174176+code%7776 := by rfl

theorem block_305_0 :
    savedBlockClass (75*305+0) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_305_0 (code : Nat) :
    weight completedCredit 0 305 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 305 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_305_0 direction_305.1
    direction_305.2.1 conditioned_305 code

theorem conditional_305_0 (code : Nat) :
    weight conditionalCredit 0 305 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 305 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_305_0 direction_305.1
    direction_305.2.2 conditioned_305 code
#print axioms selected_305_0
#print axioms source_305_0
#print axioms target_305_0
#print axioms block_305_0
#print axioms completed_305_0
#print axioms conditional_305_0

theorem selected_305_27 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 27 [] ++ [305])) := by rfl

theorem source_305_27 (code : Nat) :
    edgeSource 27 305 code = 1228608+code/6 := by rfl

theorem target_305_27 (code : Nat) :
    edgeTarget 27 305 code = 1174176+code%7776 := by rfl

theorem block_305_27 :
    savedBlockClass (75*305+27) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_305_27 (code : Nat) :
    weight completedCredit 27 305 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 27 305 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_305_27 direction_305.1
    direction_305.2.1 conditioned_305 code

theorem conditional_305_27 (code : Nat) :
    weight conditionalCredit 27 305 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 27 305 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_305_27 direction_305.1
    direction_305.2.2 conditioned_305 code
#print axioms selected_305_27
#print axioms source_305_27
#print axioms target_305_27
#print axioms block_305_27
#print axioms completed_305_27
#print axioms conditional_305_27

theorem selected_305_38 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 38 [] ++ [305])) := by rfl

theorem source_305_38 (code : Nat) :
    edgeSource 38 305 code = 1314144+code/6 := by rfl

theorem target_305_38 (code : Nat) :
    edgeTarget 38 305 code = 1174176+code%7776 := by rfl

theorem block_305_38 :
    savedBlockClass (75*305+38) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_305_38 (code : Nat) :
    weight completedCredit 38 305 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 38 305 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_305_38 direction_305.1
    direction_305.2.1 conditioned_305 code

theorem conditional_305_38 (code : Nat) :
    weight conditionalCredit 38 305 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 38 305 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_305_38 direction_305.1
    direction_305.2.2 conditioned_305 code
#print axioms selected_305_38
#print axioms source_305_38
#print axioms target_305_38
#print axioms block_305_38
#print axioms completed_305_38
#print axioms conditional_305_38

theorem selected_305_47 :
    [rule025] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 47 [] ++ [305])) := by rfl

theorem source_305_47 (code : Nat) :
    edgeSource 47 305 code = 1384128+code/6 := by rfl

theorem target_305_47 (code : Nat) :
    edgeTarget 47 305 code = 1174176+code%7776 := by rfl

theorem block_305_47 :
    savedBlockClass (75*305+47) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_305_47 (code : Nat) :
    weight completedCredit 47 305 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule025] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 47 305 [rule025] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_305_47 direction_305.1
    direction_305.2.1 conditioned_305 code

theorem conditional_305_47 (code : Nat) :
    weight conditionalCredit 47 305 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule025] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 47 305 [rule025] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_305_47 direction_305.1
    direction_305.2.2 conditioned_305 code
#print axioms selected_305_47
#print axioms source_305_47
#print axioms target_305_47
#print axioms block_305_47
#print axioms completed_305_47
#print axioms conditional_305_47

theorem selected_306_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [306])) := by rfl

theorem source_306_0 (code : Nat) :
    edgeSource 0 306 code = 692064+code/6 := by rfl

theorem target_306_0 (code : Nat) :
    edgeTarget 0 306 code = 225504+code%7776 := by rfl

theorem block_306_0 :
    savedBlockClass (75*306+0) = some 0 ∧
    recordedClassRoot 0 = 185 := by decide +kernel

theorem completed_306_0 (code : Nat) :
    weight completedCredit 0 306 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 306 [] 11 0
    (fun code => 0) selected_306_0 direction_306.1
    direction_306.2.1 conditioned_306 code

theorem conditional_306_0 (code : Nat) :
    weight conditionalCredit 0 306 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 306 [] 11 16
    (fun code => 0) selected_306_0 direction_306.1
    direction_306.2.2 conditioned_306 code
#print axioms selected_306_0
#print axioms source_306_0
#print axioms target_306_0
#print axioms block_306_0
#print axioms completed_306_0
#print axioms conditional_306_0

theorem selected_307_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [307])) := by rfl

theorem source_307_0 (code : Nat) :
    edgeSource 0 307 code = 692064+code/6 := by rfl

theorem target_307_0 (code : Nat) :
    edgeTarget 0 307 code = 248832+code%7776 := by rfl

theorem block_307_0 :
    savedBlockClass (75*307+0) = some 1 ∧
    recordedClassRoot 1 = 379 := by decide +kernel

theorem completed_307_0 (code : Nat) :
    weight completedCredit 0 307 code =
      120*(code%6+1)+max (max 16 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 307 [] 16 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_307_0 direction_307.1
    direction_307.2.1 conditioned_307 code

theorem conditional_307_0 (code : Nat) :
    weight conditionalCredit 0 307 code =
      120*(code%6+1)+max (max 16 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 307 [] 16 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_307_0 direction_307.1
    direction_307.2.2 conditioned_307 code
#print axioms selected_307_0
#print axioms source_307_0
#print axioms target_307_0
#print axioms block_307_0
#print axioms completed_307_0
#print axioms conditional_307_0

theorem selected_308_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [308])) := by rfl

theorem source_308_0 (code : Nat) :
    edgeSource 0 308 code = 699840+code/6 := by rfl

theorem target_308_0 (code : Nat) :
    edgeTarget 0 308 code = 248832+code%7776 := by rfl

theorem block_308_0 :
    savedBlockClass (75*308+0) = some 1 ∧
    recordedClassRoot 1 = 379 := by decide +kernel

theorem completed_308_0 (code : Nat) :
    weight completedCredit 0 308 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 308 [] 18 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_308_0 direction_308.1
    direction_308.2.1 conditioned_308 code

theorem conditional_308_0 (code : Nat) :
    weight conditionalCredit 0 308 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 308 [] 18 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_308_0 direction_308.1
    direction_308.2.2 conditioned_308 code
#print axioms selected_308_0
#print axioms source_308_0
#print axioms target_308_0
#print axioms block_308_0
#print axioms completed_308_0
#print axioms conditional_308_0

theorem selected_309_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [309])) := by rfl

theorem source_309_0 (code : Nat) :
    edgeSource 0 309 code = 699840+code/6 := by rfl

theorem target_309_0 (code : Nat) :
    edgeTarget 0 309 code = 225504+code%7776 := by rfl

theorem block_309_0 :
    savedBlockClass (75*309+0) = some 0 ∧
    recordedClassRoot 0 = 185 := by decide +kernel

theorem completed_309_0 (code : Nat) :
    weight completedCredit 0 309 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 309 [] 13 0
    (fun code => 0) selected_309_0 direction_309.1
    direction_309.2.1 conditioned_309 code

theorem conditional_309_0 (code : Nat) :
    weight conditionalCredit 0 309 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 309 [] 13 16
    (fun code => 0) selected_309_0 direction_309.1
    direction_309.2.2 conditioned_309 code
#print axioms selected_309_0
#print axioms source_309_0
#print axioms target_309_0
#print axioms block_309_0
#print axioms completed_309_0
#print axioms conditional_309_0

theorem selected_310_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [310])) := by rfl

theorem source_310_0 (code : Nat) :
    edgeSource 0 310 code = 699840+code/6 := by rfl

theorem target_310_0 (code : Nat) :
    edgeTarget 0 310 code = 233280+code%7776 := by rfl

theorem block_310_0 :
    savedBlockClass (75*310+0) = some 1 ∧
    recordedClassRoot 1 = 379 := by decide +kernel

theorem completed_310_0 (code : Nat) :
    weight completedCredit 0 310 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 310 [] 17 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_310_0 direction_310.1
    direction_310.2.1 conditioned_310 code

theorem conditional_310_0 (code : Nat) :
    weight conditionalCredit 0 310 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 310 [] 17 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_310_0 direction_310.1
    direction_310.2.2 conditioned_310 code
#print axioms selected_310_0
#print axioms source_310_0
#print axioms target_310_0
#print axioms block_310_0
#print axioms completed_310_0
#print axioms conditional_310_0

theorem selected_311_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [311])) := by rfl

theorem source_311_0 (code : Nat) :
    edgeSource 0 311 code = 699840+code/6 := by rfl

theorem target_311_0 (code : Nat) :
    edgeTarget 0 311 code = 241056+code%7776 := by rfl

theorem block_311_0 :
    savedBlockClass (75*311+0) = some 2 ∧
    recordedClassRoot 2 = 521 := by decide +kernel

theorem completed_311_0 (code : Nat) :
    weight completedCredit 0 311 code =
      120*(code%6+1)+max (max 16 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 311 [] 16 16
    (fun code => 0) selected_311_0 direction_311.1
    direction_311.2.1 conditioned_311 code

theorem conditional_311_0 (code : Nat) :
    weight conditionalCredit 0 311 code =
      120*(code%6+1)+max (max 16 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 311 [] 16 16
    (fun code => 0) selected_311_0 direction_311.1
    direction_311.2.2 conditioned_311 code
#print axioms selected_311_0
#print axioms source_311_0
#print axioms target_311_0
#print axioms block_311_0
#print axioms completed_311_0
#print axioms conditional_311_0

theorem selected_312_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [312])) := by rfl

theorem source_312_0 (code : Nat) :
    edgeSource 0 312 code = 699840+code/6 := by rfl

theorem target_312_0 (code : Nat) :
    edgeTarget 0 312 code = 248832+code%7776 := by rfl

theorem block_312_0 :
    savedBlockClass (75*312+0) = some 1 ∧
    recordedClassRoot 1 = 379 := by decide +kernel

theorem completed_312_0 (code : Nat) :
    weight completedCredit 0 312 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 312 [] 18 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_312_0 direction_312.1
    direction_312.2.1 conditioned_312 code

theorem conditional_312_0 (code : Nat) :
    weight conditionalCredit 0 312 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 312 [] 18 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_312_0 direction_312.1
    direction_312.2.2 conditioned_312 code
#print axioms selected_312_0
#print axioms source_312_0
#print axioms target_312_0
#print axioms block_312_0
#print axioms completed_312_0
#print axioms conditional_312_0

theorem selected_313_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [313])) := by rfl

theorem source_313_0 (code : Nat) :
    edgeSource 0 313 code = 707616+code/6 := by rfl

theorem target_313_0 (code : Nat) :
    edgeTarget 0 313 code = 342144+code%7776 := by rfl

theorem block_313_0 :
    savedBlockClass (75*313+0) = some 12 ∧
    recordedClassRoot 12 = 1807 := by decide +kernel

theorem completed_313_0 (code : Nat) :
    weight completedCredit 0 313 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 313 [] 12 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_313_0 direction_313.1
    direction_313.2.1 conditioned_313 code

theorem conditional_313_0 (code : Nat) :
    weight conditionalCredit 0 313 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 313 [] 12 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_313_0 direction_313.1
    direction_313.2.2 conditioned_313 code
#print axioms selected_313_0
#print axioms source_313_0
#print axioms target_313_0
#print axioms block_313_0
#print axioms completed_313_0
#print axioms conditional_313_0

theorem selected_314_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [314])) := by rfl

theorem source_314_0 (code : Nat) :
    edgeSource 0 314 code = 707616+code/6 := by rfl

theorem target_314_0 (code : Nat) :
    edgeTarget 0 314 code = 349920+code%7776 := by rfl

theorem block_314_0 :
    savedBlockClass (75*314+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_314_0 (code : Nat) :
    weight completedCredit 0 314 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 314 [] 12 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_314_0 direction_314.1
    direction_314.2.1 conditioned_314 code

theorem conditional_314_0 (code : Nat) :
    weight conditionalCredit 0 314 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 314 [] 12 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_314_0 direction_314.1
    direction_314.2.2 conditioned_314 code
#print axioms selected_314_0
#print axioms source_314_0
#print axioms target_314_0
#print axioms block_314_0
#print axioms completed_314_0
#print axioms conditional_314_0

theorem selected_315_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [315])) := by rfl

theorem source_315_0 (code : Nat) :
    edgeSource 0 315 code = 707616+code/6 := by rfl

theorem target_315_0 (code : Nat) :
    edgeTarget 0 315 code = 357696+code%7776 := by rfl

theorem block_315_0 :
    savedBlockClass (75*315+0) = some 11 ∧
    recordedClassRoot 11 = 1698 := by decide +kernel

theorem completed_315_0 (code : Nat) :
    weight completedCredit 0 315 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 315 [] 12 0
    (fun code => 0) selected_315_0 direction_315.1
    direction_315.2.1 conditioned_315 code

theorem conditional_315_0 (code : Nat) :
    weight conditionalCredit 0 315 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 315 [] 12 16
    (fun code => 0) selected_315_0 direction_315.1
    direction_315.2.2 conditioned_315 code
#print axioms selected_315_0
#print axioms source_315_0
#print axioms target_315_0
#print axioms block_315_0
#print axioms completed_315_0
#print axioms conditional_315_0

theorem selected_316_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [316])) := by rfl

theorem source_316_0 (code : Nat) :
    edgeSource 0 316 code = 707616+code/6 := by rfl

theorem target_316_0 (code : Nat) :
    edgeTarget 0 316 code = 365472+code%7776 := by rfl

theorem block_316_0 :
    savedBlockClass (75*316+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_316_0 (code : Nat) :
    weight completedCredit 0 316 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 316 [] 12 16
    (fun code => 0) selected_316_0 direction_316.1
    direction_316.2.1 conditioned_316 code

theorem conditional_316_0 (code : Nat) :
    weight conditionalCredit 0 316 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 316 [] 12 16
    (fun code => 0) selected_316_0 direction_316.1
    direction_316.2.2 conditioned_316 code
#print axioms selected_316_0
#print axioms source_316_0
#print axioms target_316_0
#print axioms block_316_0
#print axioms completed_316_0
#print axioms conditional_316_0

theorem selected_317_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [317])) := by rfl

theorem source_317_0 (code : Nat) :
    edgeSource 0 317 code = 707616+code/6 := by rfl

theorem target_317_0 (code : Nat) :
    edgeTarget 0 317 code = 373248+code%7776 := by rfl

theorem block_317_0 :
    savedBlockClass (75*317+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_317_0 (code : Nat) :
    weight completedCredit 0 317 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 317 [] 12 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_317_0 direction_317.1
    direction_317.2.1 conditioned_317 code

theorem conditional_317_0 (code : Nat) :
    weight conditionalCredit 0 317 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 317 [] 12 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_317_0 direction_317.1
    direction_317.2.2 conditioned_317 code
#print axioms selected_317_0
#print axioms source_317_0
#print axioms target_317_0
#print axioms block_317_0
#print axioms completed_317_0
#print axioms conditional_317_0

theorem selected_318_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [318])) := by rfl

theorem source_318_0 (code : Nat) :
    edgeSource 0 318 code = 715392+code/6 := by rfl

theorem target_318_0 (code : Nat) :
    edgeTarget 0 318 code = 279936+code%7776 := by rfl

theorem block_318_0 :
    savedBlockClass (75*318+0) = some 8 ∧
    recordedClassRoot 8 = 1378 := by decide +kernel

theorem completed_318_0 (code : Nat) :
    weight completedCredit 0 318 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 318 [] 29 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_318_0 direction_318.1
    direction_318.2.1 conditioned_318 code

theorem conditional_318_0 (code : Nat) :
    weight conditionalCredit 0 318 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 318 [] 29 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_318_0 direction_318.1
    direction_318.2.2 conditioned_318 code
#print axioms selected_318_0
#print axioms source_318_0
#print axioms target_318_0
#print axioms block_318_0
#print axioms completed_318_0
#print axioms conditional_318_0

theorem selected_319_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [319])) := by rfl

theorem source_319_0 (code : Nat) :
    edgeSource 0 319 code = 715392+code/6 := by rfl

theorem target_319_0 (code : Nat) :
    edgeTarget 0 319 code = 256608+code%7776 := by rfl

theorem block_319_0 :
    savedBlockClass (75*319+0) = some 7 ∧
    recordedClassRoot 7 = 1278 := by decide +kernel

theorem completed_319_0 (code : Nat) :
    weight completedCredit 0 319 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 319 [] 29 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_319_0 direction_319.1
    direction_319.2.1 conditioned_319 code

theorem conditional_319_0 (code : Nat) :
    weight conditionalCredit 0 319 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 319 [] 29 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_319_0 direction_319.1
    direction_319.2.2 conditioned_319 code
#print axioms selected_319_0
#print axioms source_319_0
#print axioms target_319_0
#print axioms block_319_0
#print axioms completed_319_0
#print axioms conditional_319_0

theorem selected_320_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [320])) := by rfl

theorem source_320_0 (code : Nat) :
    edgeSource 0 320 code = 715392+code/6 := by rfl

theorem target_320_0 (code : Nat) :
    edgeTarget 0 320 code = 264384+code%7776 := by rfl

theorem block_320_0 :
    savedBlockClass (75*320+0) = some 6 ∧
    recordedClassRoot 6 = 1150 := by decide +kernel

theorem completed_320_0 (code : Nat) :
    weight completedCredit 0 320 code =
      120*(code%6+1)+max (max 24 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 320 [] 24 0
    (fun code => 0) selected_320_0 direction_320.1
    direction_320.2.1 conditioned_320 code

theorem conditional_320_0 (code : Nat) :
    weight conditionalCredit 0 320 code =
      120*(code%6+1)+max (max 24 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 320 [] 24 16
    (fun code => 0) selected_320_0 direction_320.1
    direction_320.2.2 conditioned_320 code
#print axioms selected_320_0
#print axioms source_320_0
#print axioms target_320_0
#print axioms block_320_0
#print axioms completed_320_0
#print axioms conditional_320_0

theorem selected_321_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [321])) := by rfl

theorem source_321_0 (code : Nat) :
    edgeSource 0 321 code = 715392+code/6 := by rfl

theorem target_321_0 (code : Nat) :
    edgeTarget 0 321 code = 272160+code%7776 := by rfl

theorem block_321_0 :
    savedBlockClass (75*321+0) = some 43 ∧
    recordedClassRoot 43 = 3318 := by decide +kernel

theorem completed_321_0 (code : Nat) :
    weight completedCredit 0 321 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 321 [] 21 16
    (fun code => 0) selected_321_0 direction_321.1
    direction_321.2.1 conditioned_321 code

theorem conditional_321_0 (code : Nat) :
    weight conditionalCredit 0 321 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 321 [] 21 16
    (fun code => 0) selected_321_0 direction_321.1
    direction_321.2.2 conditioned_321 code
#print axioms selected_321_0
#print axioms source_321_0
#print axioms target_321_0
#print axioms block_321_0
#print axioms completed_321_0
#print axioms conditional_321_0

theorem selected_322_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [322])) := by rfl

theorem source_322_0 (code : Nat) :
    edgeSource 0 322 code = 715392+code/6 := by rfl

theorem target_322_0 (code : Nat) :
    edgeTarget 0 322 code = 279936+code%7776 := by rfl

theorem block_322_0 :
    savedBlockClass (75*322+0) = some 8 ∧
    recordedClassRoot 8 = 1378 := by decide +kernel

theorem completed_322_0 (code : Nat) :
    weight completedCredit 0 322 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 322 [] 29 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_322_0 direction_322.1
    direction_322.2.1 conditioned_322 code

theorem conditional_322_0 (code : Nat) :
    weight conditionalCredit 0 322 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 322 [] 29 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_322_0 direction_322.1
    direction_322.2.2 conditioned_322 code
#print axioms selected_322_0
#print axioms source_322_0
#print axioms target_322_0
#print axioms block_322_0
#print axioms completed_322_0
#print axioms conditional_322_0

theorem selected_323_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [323])) := by rfl

theorem source_323_0 (code : Nat) :
    edgeSource 0 323 code = 723168+code/6 := by rfl

theorem target_323_0 (code : Nat) :
    edgeTarget 0 323 code = 311040+code%7776 := by rfl

theorem block_323_0 :
    savedBlockClass (75*323+0) = some 4 ∧
    recordedClassRoot 4 = 846 := by decide +kernel

theorem completed_323_0 (code : Nat) :
    weight completedCredit 0 323 code =
      120*(code%6+1)+max (max 44 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 323 [] 44 16
    (fun code => 0) selected_323_0 direction_323.1
    direction_323.2.1 conditioned_323 code

theorem conditional_323_0 (code : Nat) :
    weight conditionalCredit 0 323 code =
      120*(code%6+1)+max (max 44 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 323 [] 44 16
    (fun code => 0) selected_323_0 direction_323.1
    direction_323.2.2 conditioned_323 code
#print axioms selected_323_0
#print axioms source_323_0
#print axioms target_323_0
#print axioms block_323_0
#print axioms completed_323_0
#print axioms conditional_323_0

end Snake9.Context101
