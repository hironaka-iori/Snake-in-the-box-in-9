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

theorem selected_324_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [324])) := by rfl

theorem source_324_0 (code : Nat) :
    edgeSource 0 324 code = 723168+code/6 := by rfl

theorem target_324_0 (code : Nat) :
    edgeTarget 0 324 code = 287712+code%7776 := by rfl

theorem block_324_0 :
    savedBlockClass (75*324+0) = some 3 ∧
    recordedClassRoot 3 = 669 := by decide +kernel

theorem completed_324_0 (code : Nat) :
    weight completedCredit 0 324 code =
      120*(code%6+1)+max (max 37 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 324 [] 37 16
    (fun code => 0) selected_324_0 direction_324.1
    direction_324.2.1 conditioned_324 code

theorem conditional_324_0 (code : Nat) :
    weight conditionalCredit 0 324 code =
      120*(code%6+1)+max (max 37 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 324 [] 37 16
    (fun code => 0) selected_324_0 direction_324.1
    direction_324.2.2 conditioned_324 code
#print axioms selected_324_0
#print axioms source_324_0
#print axioms target_324_0
#print axioms block_324_0
#print axioms completed_324_0
#print axioms conditional_324_0

theorem selected_325_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [325])) := by rfl

theorem source_325_0 (code : Nat) :
    edgeSource 0 325 code = 723168+code/6 := by rfl

theorem target_325_0 (code : Nat) :
    edgeTarget 0 325 code = 295488+code%7776 := by rfl

theorem block_325_0 :
    savedBlockClass (75*325+0) = some 4 ∧
    recordedClassRoot 4 = 846 := by decide +kernel

theorem completed_325_0 (code : Nat) :
    weight completedCredit 0 325 code =
      120*(code%6+1)+max (max 38 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 325 [] 38 16
    (fun code => 0) selected_325_0 direction_325.1
    direction_325.2.1 conditioned_325 code

theorem conditional_325_0 (code : Nat) :
    weight conditionalCredit 0 325 code =
      120*(code%6+1)+max (max 38 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 325 [] 38 16
    (fun code => 0) selected_325_0 direction_325.1
    direction_325.2.2 conditioned_325 code
#print axioms selected_325_0
#print axioms source_325_0
#print axioms target_325_0
#print axioms block_325_0
#print axioms completed_325_0
#print axioms conditional_325_0

theorem selected_326_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [326])) := by rfl

theorem source_326_0 (code : Nat) :
    edgeSource 0 326 code = 723168+code/6 := by rfl

theorem target_326_0 (code : Nat) :
    edgeTarget 0 326 code = 303264+code%7776 := by rfl

theorem block_326_0 :
    savedBlockClass (75*326+0) = some 5 ∧
    recordedClassRoot 5 = 1008 := by decide +kernel

theorem completed_326_0 (code : Nat) :
    weight completedCredit 0 326 code =
      120*(code%6+1)+max (max 27 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 326 [] 27 0
    (fun code => 0) selected_326_0 direction_326.1
    direction_326.2.1 conditioned_326 code

theorem conditional_326_0 (code : Nat) :
    weight conditionalCredit 0 326 code =
      120*(code%6+1)+max (max 27 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 326 [] 27 16
    (fun code => 0) selected_326_0 direction_326.1
    direction_326.2.2 conditioned_326 code
#print axioms selected_326_0
#print axioms source_326_0
#print axioms target_326_0
#print axioms block_326_0
#print axioms completed_326_0
#print axioms conditional_326_0

theorem selected_327_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [327])) := by rfl

theorem source_327_0 (code : Nat) :
    edgeSource 0 327 code = 723168+code/6 := by rfl

theorem target_327_0 (code : Nat) :
    edgeTarget 0 327 code = 311040+code%7776 := by rfl

theorem block_327_0 :
    savedBlockClass (75*327+0) = some 4 ∧
    recordedClassRoot 4 = 846 := by decide +kernel

theorem completed_327_0 (code : Nat) :
    weight completedCredit 0 327 code =
      120*(code%6+1)+max (max 44 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 327 [] 44 16
    (fun code => 0) selected_327_0 direction_327.1
    direction_327.2.1 conditioned_327 code

theorem conditional_327_0 (code : Nat) :
    weight conditionalCredit 0 327 code =
      120*(code%6+1)+max (max 44 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 327 [] 44 16
    (fun code => 0) selected_327_0 direction_327.1
    direction_327.2.2 conditioned_327 code
#print axioms selected_327_0
#print axioms source_327_0
#print axioms target_327_0
#print axioms block_327_0
#print axioms completed_327_0
#print axioms conditional_327_0

theorem selected_328_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [328])) := by rfl

theorem source_328_0 (code : Nat) :
    edgeSource 0 328 code = 730944+code/6 := by rfl

theorem target_328_0 (code : Nat) :
    edgeTarget 0 328 code = 334368+code%7776 := by rfl

theorem block_328_0 :
    savedBlockClass (75*328+0) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_328_0 (code : Nat) :
    weight completedCredit 0 328 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 328 [] 25 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_328_0 direction_328.1
    direction_328.2.1 conditioned_328 code

theorem conditional_328_0 (code : Nat) :
    weight conditionalCredit 0 328 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 328 [] 25 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_328_0 direction_328.1
    direction_328.2.2 conditioned_328 code
#print axioms selected_328_0
#print axioms source_328_0
#print axioms target_328_0
#print axioms block_328_0
#print axioms completed_328_0
#print axioms conditional_328_0

theorem selected_329_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [329])) := by rfl

theorem source_329_0 (code : Nat) :
    edgeSource 0 329 code = 730944+code/6 := by rfl

theorem target_329_0 (code : Nat) :
    edgeTarget 0 329 code = 318816+code%7776 := by rfl

theorem block_329_0 :
    savedBlockClass (75*329+0) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_329_0 (code : Nat) :
    weight completedCredit 0 329 code =
      120*(code%6+1)+max (max 19 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 329 [] 19 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_329_0 direction_329.1
    direction_329.2.1 conditioned_329 code

theorem conditional_329_0 (code : Nat) :
    weight conditionalCredit 0 329 code =
      120*(code%6+1)+max (max 19 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 329 [] 19 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_329_0 direction_329.1
    direction_329.2.2 conditioned_329 code
#print axioms selected_329_0
#print axioms source_329_0
#print axioms target_329_0
#print axioms block_329_0
#print axioms completed_329_0
#print axioms conditional_329_0

theorem selected_330_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [330])) := by rfl

theorem source_330_0 (code : Nat) :
    edgeSource 0 330 code = 730944+code/6 := by rfl

theorem target_330_0 (code : Nat) :
    edgeTarget 0 330 code = 326592+code%7776 := by rfl

theorem block_330_0 :
    savedBlockClass (75*330+0) = some 9 ∧
    recordedClassRoot 9 = 1489 := by decide +kernel

theorem completed_330_0 (code : Nat) :
    weight completedCredit 0 330 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 330 [] 18 12
    (fun code => 0) selected_330_0 direction_330.1
    direction_330.2.1 conditioned_330 code

theorem conditional_330_0 (code : Nat) :
    weight conditionalCredit 0 330 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 330 [] 18 12
    (fun code => 0) selected_330_0 direction_330.1
    direction_330.2.2 conditioned_330 code
#print axioms selected_330_0
#print axioms source_330_0
#print axioms target_330_0
#print axioms block_330_0
#print axioms completed_330_0
#print axioms conditional_330_0

theorem selected_331_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [331])) := by rfl

theorem source_331_0 (code : Nat) :
    edgeSource 0 331 code = 730944+code/6 := by rfl

theorem target_331_0 (code : Nat) :
    edgeTarget 0 331 code = 334368+code%7776 := by rfl

theorem block_331_0 :
    savedBlockClass (75*331+0) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_331_0 (code : Nat) :
    weight completedCredit 0 331 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 331 [] 25 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_331_0 direction_331.1
    direction_331.2.1 conditioned_331 code

theorem conditional_331_0 (code : Nat) :
    weight conditionalCredit 0 331 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 331 [] 25 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_331_0 direction_331.1
    direction_331.2.2 conditioned_331 code
#print axioms selected_331_0
#print axioms source_331_0
#print axioms target_331_0
#print axioms block_331_0
#print axioms completed_331_0
#print axioms conditional_331_0

theorem selected_332_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [332])) := by rfl

theorem source_332_0 (code : Nat) :
    edgeSource 0 332 code = 738720+code/6 := by rfl

theorem target_332_0 (code : Nat) :
    edgeTarget 0 332 code = 373248+code%7776 := by rfl

theorem block_332_0 :
    savedBlockClass (75*332+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_332_0 (code : Nat) :
    weight completedCredit 0 332 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 332 [] 12 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_332_0 direction_332.1
    direction_332.2.1 conditioned_332 code

theorem conditional_332_0 (code : Nat) :
    weight conditionalCredit 0 332 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 332 [] 12 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_332_0 direction_332.1
    direction_332.2.2 conditioned_332 code
#print axioms selected_332_0
#print axioms source_332_0
#print axioms target_332_0
#print axioms block_332_0
#print axioms completed_332_0
#print axioms conditional_332_0

theorem selected_333_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [333])) := by rfl

theorem source_333_0 (code : Nat) :
    edgeSource 0 333 code = 738720+code/6 := by rfl

theorem target_333_0 (code : Nat) :
    edgeTarget 0 333 code = 342144+code%7776 := by rfl

theorem block_333_0 :
    savedBlockClass (75*333+0) = some 12 ∧
    recordedClassRoot 12 = 1807 := by decide +kernel

theorem completed_333_0 (code : Nat) :
    weight completedCredit 0 333 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 333 [] 12 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_333_0 direction_333.1
    direction_333.2.1 conditioned_333 code

theorem conditional_333_0 (code : Nat) :
    weight conditionalCredit 0 333 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 333 [] 12 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_333_0 direction_333.1
    direction_333.2.2 conditioned_333 code
#print axioms selected_333_0
#print axioms source_333_0
#print axioms target_333_0
#print axioms block_333_0
#print axioms completed_333_0
#print axioms conditional_333_0

theorem selected_334_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [334])) := by rfl

theorem source_334_0 (code : Nat) :
    edgeSource 0 334 code = 738720+code/6 := by rfl

theorem target_334_0 (code : Nat) :
    edgeTarget 0 334 code = 349920+code%7776 := by rfl

theorem block_334_0 :
    savedBlockClass (75*334+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_334_0 (code : Nat) :
    weight completedCredit 0 334 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 334 [] 12 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_334_0 direction_334.1
    direction_334.2.1 conditioned_334 code

theorem conditional_334_0 (code : Nat) :
    weight conditionalCredit 0 334 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 334 [] 12 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_334_0 direction_334.1
    direction_334.2.2 conditioned_334 code
#print axioms selected_334_0
#print axioms source_334_0
#print axioms target_334_0
#print axioms block_334_0
#print axioms completed_334_0
#print axioms conditional_334_0

theorem selected_335_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [335])) := by rfl

theorem source_335_0 (code : Nat) :
    edgeSource 0 335 code = 738720+code/6 := by rfl

theorem target_335_0 (code : Nat) :
    edgeTarget 0 335 code = 357696+code%7776 := by rfl

theorem block_335_0 :
    savedBlockClass (75*335+0) = some 11 ∧
    recordedClassRoot 11 = 1698 := by decide +kernel

theorem completed_335_0 (code : Nat) :
    weight completedCredit 0 335 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 335 [] 12 0
    (fun code => 0) selected_335_0 direction_335.1
    direction_335.2.1 conditioned_335 code

theorem conditional_335_0 (code : Nat) :
    weight conditionalCredit 0 335 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 335 [] 12 16
    (fun code => 0) selected_335_0 direction_335.1
    direction_335.2.2 conditioned_335 code
#print axioms selected_335_0
#print axioms source_335_0
#print axioms target_335_0
#print axioms block_335_0
#print axioms completed_335_0
#print axioms conditional_335_0

theorem selected_336_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [336])) := by rfl

theorem source_336_0 (code : Nat) :
    edgeSource 0 336 code = 738720+code/6 := by rfl

theorem target_336_0 (code : Nat) :
    edgeTarget 0 336 code = 365472+code%7776 := by rfl

theorem block_336_0 :
    savedBlockClass (75*336+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_336_0 (code : Nat) :
    weight completedCredit 0 336 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 336 [] 12 16
    (fun code => 0) selected_336_0 direction_336.1
    direction_336.2.1 conditioned_336 code

theorem conditional_336_0 (code : Nat) :
    weight conditionalCredit 0 336 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 336 [] 12 16
    (fun code => 0) selected_336_0 direction_336.1
    direction_336.2.2 conditioned_336 code
#print axioms selected_336_0
#print axioms source_336_0
#print axioms target_336_0
#print axioms block_336_0
#print axioms completed_336_0
#print axioms conditional_336_0

theorem selected_337_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [337])) := by rfl

theorem source_337_0 (code : Nat) :
    edgeSource 0 337 code = 738720+code/6 := by rfl

theorem target_337_0 (code : Nat) :
    edgeTarget 0 337 code = 373248+code%7776 := by rfl

theorem block_337_0 :
    savedBlockClass (75*337+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_337_0 (code : Nat) :
    weight completedCredit 0 337 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 337 [] 12 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_337_0 direction_337.1
    direction_337.2.1 conditioned_337 code

theorem conditional_337_0 (code : Nat) :
    weight conditionalCredit 0 337 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 337 [] 12 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_337_0 direction_337.1
    direction_337.2.2 conditioned_337 code
#print axioms selected_337_0
#print axioms source_337_0
#print axioms target_337_0
#print axioms block_337_0
#print axioms completed_337_0
#print axioms conditional_337_0

theorem selected_338_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [338])) := by rfl

theorem source_338_0 (code : Nat) :
    edgeSource 0 338 code = 746496+code/6 := by rfl

theorem target_338_0 (code : Nat) :
    edgeTarget 0 338 code = 412128+code%7776 := by rfl

theorem block_338_0 :
    savedBlockClass (75*338+0) = some 18 ∧
    recordedClassRoot 18 = 2297 := by decide +kernel

theorem completed_338_0 (code : Nat) :
    weight completedCredit 0 338 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 338 [] 21 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_338_0 direction_338.1
    direction_338.2.1 conditioned_338 code

theorem conditional_338_0 (code : Nat) :
    weight conditionalCredit 0 338 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 338 [] 21 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_338_0 direction_338.1
    direction_338.2.2 conditioned_338 code
#print axioms selected_338_0
#print axioms source_338_0
#print axioms target_338_0
#print axioms block_338_0
#print axioms completed_338_0
#print axioms conditional_338_0

theorem selected_339_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [339])) := by rfl

theorem source_339_0 (code : Nat) :
    edgeSource 0 339 code = 746496+code/6 := by rfl

theorem target_339_0 (code : Nat) :
    edgeTarget 0 339 code = 435456+code%7776 := by rfl

theorem block_339_0 :
    savedBlockClass (75*339+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_339_0 (code : Nat) :
    weight completedCredit 0 339 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 339 [] 22 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_339_0 direction_339.1
    direction_339.2.1 conditioned_339 code

theorem conditional_339_0 (code : Nat) :
    weight conditionalCredit 0 339 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 339 [] 22 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_339_0 direction_339.1
    direction_339.2.2 conditioned_339 code
#print axioms selected_339_0
#print axioms source_339_0
#print axioms target_339_0
#print axioms block_339_0
#print axioms completed_339_0
#print axioms conditional_339_0

theorem selected_340_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [340])) := by rfl

theorem source_340_0 (code : Nat) :
    edgeSource 0 340 code = 754272+code/6 := by rfl

theorem target_340_0 (code : Nat) :
    edgeTarget 0 340 code = 451008+code%7776 := by rfl

theorem block_340_0 :
    savedBlockClass (75*340+0) = some 16 ∧
    recordedClassRoot 16 = 2162 := by decide +kernel

theorem completed_340_0 (code : Nat) :
    weight completedCredit 0 340 code =
      120*(code%6+1)+max (max 14 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 340 [] 14 16
    (fun code => 0) selected_340_0 direction_340.1
    direction_340.2.1 conditioned_340 code

theorem conditional_340_0 (code : Nat) :
    weight conditionalCredit 0 340 code =
      120*(code%6+1)+max (max 14 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 340 [] 14 16
    (fun code => 0) selected_340_0 direction_340.1
    direction_340.2.2 conditioned_340 code
#print axioms selected_340_0
#print axioms source_340_0
#print axioms target_340_0
#print axioms block_340_0
#print axioms completed_340_0
#print axioms conditional_340_0

theorem selected_341_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [341])) := by rfl

theorem source_341_0 (code : Nat) :
    edgeSource 0 341 code = 754272+code/6 := by rfl

theorem target_341_0 (code : Nat) :
    edgeTarget 0 341 code = 458784+code%7776 := by rfl

theorem block_341_0 :
    savedBlockClass (75*341+0) = some 15 ∧
    recordedClassRoot 15 = 2085 := by decide +kernel

theorem completed_341_0 (code : Nat) :
    weight completedCredit 0 341 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 341 [] 20 16
    (fun code => 0) selected_341_0 direction_341.1
    direction_341.2.1 conditioned_341 code

theorem conditional_341_0 (code : Nat) :
    weight conditionalCredit 0 341 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 341 [] 20 16
    (fun code => 0) selected_341_0 direction_341.1
    direction_341.2.2 conditioned_341 code
#print axioms selected_341_0
#print axioms source_341_0
#print axioms target_341_0
#print axioms block_341_0
#print axioms completed_341_0
#print axioms conditional_341_0

theorem selected_342_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [342])) := by rfl

theorem source_342_0 (code : Nat) :
    edgeSource 0 342 code = 762048+code/6 := by rfl

theorem target_342_0 (code : Nat) :
    edgeTarget 0 342 code = 474336+code%7776 := by rfl

theorem block_342_0 :
    savedBlockClass (75*342+0) = some 20 ∧
    recordedClassRoot 20 = 2418 := by decide +kernel

theorem completed_342_0 (code : Nat) :
    weight completedCredit 0 342 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 342 [] 9 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_342_0 direction_342.1
    direction_342.2.1 conditioned_342 code

theorem conditional_342_0 (code : Nat) :
    weight conditionalCredit 0 342 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 342 [] 9 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_342_0 direction_342.1
    direction_342.2.2 conditioned_342 code
#print axioms selected_342_0
#print axioms source_342_0
#print axioms target_342_0
#print axioms block_342_0
#print axioms completed_342_0
#print axioms conditional_342_0

theorem selected_343_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [343])) := by rfl

theorem source_343_0 (code : Nat) :
    edgeSource 0 343 code = 769824+code/6 := by rfl

theorem target_343_0 (code : Nat) :
    edgeTarget 0 343 code = 482112+code%7776 := by rfl

theorem block_343_0 :
    savedBlockClass (75*343+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_343_0 (code : Nat) :
    weight completedCredit 0 343 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 343 [] 9 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_343_0 direction_343.1
    direction_343.2.1 conditioned_343 code

theorem conditional_343_0 (code : Nat) :
    weight conditionalCredit 0 343 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 343 [] 9 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_343_0 direction_343.1
    direction_343.2.2 conditioned_343 code
#print axioms selected_343_0
#print axioms source_343_0
#print axioms target_343_0
#print axioms block_343_0
#print axioms completed_343_0
#print axioms conditional_343_0

theorem selected_344_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [344])) := by rfl

theorem source_344_0 (code : Nat) :
    edgeSource 0 344 code = 769824+code/6 := by rfl

theorem target_344_0 (code : Nat) :
    edgeTarget 0 344 code = 489888+code%7776 := by rfl

theorem block_344_0 :
    savedBlockClass (75*344+0) = some 18 ∧
    recordedClassRoot 18 = 2297 := by decide +kernel

theorem completed_344_0 (code : Nat) :
    weight completedCredit 0 344 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 344 [] 9 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_344_0 direction_344.1
    direction_344.2.1 conditioned_344 code

theorem conditional_344_0 (code : Nat) :
    weight conditionalCredit 0 344 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 344 [] 9 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_344_0 direction_344.1
    direction_344.2.2 conditioned_344 code
#print axioms selected_344_0
#print axioms source_344_0
#print axioms target_344_0
#print axioms block_344_0
#print axioms completed_344_0
#print axioms conditional_344_0

theorem selected_345_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [345])) := by rfl

theorem source_345_0 (code : Nat) :
    edgeSource 0 345 code = 769824+code/6 := by rfl

theorem target_345_0 (code : Nat) :
    edgeTarget 0 345 code = 497664+code%7776 := by rfl

theorem block_345_0 :
    savedBlockClass (75*345+0) = some 17 ∧
    recordedClassRoot 17 = 2231 := by decide +kernel

theorem completed_345_0 (code : Nat) :
    weight completedCredit 0 345 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 345 [] 9 0
    (fun code => 0) selected_345_0 direction_345.1
    direction_345.2.1 conditioned_345 code

theorem conditional_345_0 (code : Nat) :
    weight conditionalCredit 0 345 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 345 [] 9 16
    (fun code => 0) selected_345_0 direction_345.1
    direction_345.2.2 conditioned_345 code
#print axioms selected_345_0
#print axioms source_345_0
#print axioms target_345_0
#print axioms block_345_0
#print axioms completed_345_0
#print axioms conditional_345_0

theorem selected_346_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [346])) := by rfl

theorem source_346_0 (code : Nat) :
    edgeSource 0 346 code = 769824+code/6 := by rfl

theorem target_346_0 (code : Nat) :
    edgeTarget 0 346 code = 505440+code%7776 := by rfl

theorem block_346_0 :
    savedBlockClass (75*346+0) = some 21 ∧
    recordedClassRoot 21 = 2479 := by decide +kernel

theorem completed_346_0 (code : Nat) :
    weight completedCredit 0 346 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 346 [] 9 16
    (fun code => 0) selected_346_0 direction_346.1
    direction_346.2.1 conditioned_346 code

theorem conditional_346_0 (code : Nat) :
    weight conditionalCredit 0 346 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 346 [] 9 16
    (fun code => 0) selected_346_0 direction_346.1
    direction_346.2.2 conditioned_346 code
#print axioms selected_346_0
#print axioms source_346_0
#print axioms target_346_0
#print axioms block_346_0
#print axioms completed_346_0
#print axioms conditional_346_0

theorem selected_347_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [347])) := by rfl

theorem source_347_0 (code : Nat) :
    edgeSource 0 347 code = 769824+code/6 := by rfl

theorem target_347_0 (code : Nat) :
    edgeTarget 0 347 code = 513216+code%7776 := by rfl

theorem block_347_0 :
    savedBlockClass (75*347+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_347_0 (code : Nat) :
    weight completedCredit 0 347 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 347 [] 9 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_347_0 direction_347.1
    direction_347.2.1 conditioned_347 code

theorem conditional_347_0 (code : Nat) :
    weight conditionalCredit 0 347 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 347 [] 9 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_347_0 direction_347.1
    direction_347.2.2 conditioned_347 code
#print axioms selected_347_0
#print axioms source_347_0
#print axioms target_347_0
#print axioms block_347_0
#print axioms completed_347_0
#print axioms conditional_347_0

theorem selected_348_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [348])) := by rfl

theorem source_348_0 (code : Nat) :
    edgeSource 0 348 code = 777600+code/6 := by rfl

theorem target_348_0 (code : Nat) :
    edgeTarget 0 348 code = 381024+code%7776 := by rfl

theorem block_348_0 :
    savedBlockClass (75*348+0) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_348_0 (code : Nat) :
    weight completedCredit 0 348 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 348 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_348_0 direction_348.1
    direction_348.2.1 conditioned_348 code

theorem conditional_348_0 (code : Nat) :
    weight conditionalCredit 0 348 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 348 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_348_0 direction_348.1
    direction_348.2.2 conditioned_348 code
#print axioms selected_348_0
#print axioms source_348_0
#print axioms target_348_0
#print axioms block_348_0
#print axioms completed_348_0
#print axioms conditional_348_0

theorem selected_348_49 :
    [rule027] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 49 [] ++ [348])) := by rfl

theorem source_348_49 (code : Nat) :
    edgeSource 49 348 code = 1399680+code/6 := by rfl

theorem target_348_49 (code : Nat) :
    edgeTarget 49 348 code = 381024+code%7776 := by rfl

theorem block_348_49 :
    savedBlockClass (75*348+49) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_348_49 (code : Nat) :
    weight completedCredit 49 348 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule027] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 49 348 [rule027] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_348_49 direction_348.1
    direction_348.2.1 conditioned_348 code

theorem conditional_348_49 (code : Nat) :
    weight conditionalCredit 49 348 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule027] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 49 348 [rule027] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_348_49 direction_348.1
    direction_348.2.2 conditioned_348 code
#print axioms selected_348_49
#print axioms source_348_49
#print axioms target_348_49
#print axioms block_348_49
#print axioms completed_348_49
#print axioms conditional_348_49

theorem selected_349_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [349])) := by rfl

theorem source_349_0 (code : Nat) :
    edgeSource 0 349 code = 777600+code/6 := by rfl

theorem target_349_0 (code : Nat) :
    edgeTarget 0 349 code = 404352+code%7776 := by rfl

theorem block_349_0 :
    savedBlockClass (75*349+0) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_349_0 (code : Nat) :
    weight completedCredit 0 349 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 349 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_349_0 direction_349.1
    direction_349.2.1 conditioned_349 code

theorem conditional_349_0 (code : Nat) :
    weight conditionalCredit 0 349 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 349 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_349_0 direction_349.1
    direction_349.2.2 conditioned_349 code
#print axioms selected_349_0
#print axioms source_349_0
#print axioms target_349_0
#print axioms block_349_0
#print axioms completed_349_0
#print axioms conditional_349_0

theorem selected_349_49 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 49 [] ++ [349])) := by rfl

theorem source_349_49 (code : Nat) :
    edgeSource 49 349 code = 1399680+code/6 := by rfl

theorem target_349_49 (code : Nat) :
    edgeTarget 49 349 code = 404352+code%7776 := by rfl

theorem block_349_49 :
    savedBlockClass (75*349+49) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_349_49 (code : Nat) :
    weight completedCredit 49 349 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 49 349 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_349_49 direction_349.1
    direction_349.2.1 conditioned_349 code

theorem conditional_349_49 (code : Nat) :
    weight conditionalCredit 49 349 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 49 349 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_349_49 direction_349.1
    direction_349.2.2 conditioned_349 code
#print axioms selected_349_49
#print axioms source_349_49
#print axioms target_349_49
#print axioms block_349_49
#print axioms completed_349_49
#print axioms conditional_349_49

theorem selected_350_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [350])) := by rfl

theorem source_350_0 (code : Nat) :
    edgeSource 0 350 code = 785376+code/6 := by rfl

theorem target_350_0 (code : Nat) :
    edgeTarget 0 350 code = 1181952+code%7776 := by rfl

theorem block_350_0 :
    savedBlockClass (75*350+0) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_0 (code : Nat) :
    weight completedCredit 0 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_0 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_0 (code : Nat) :
    weight conditionalCredit 0 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_0 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_0
#print axioms source_350_0
#print axioms target_350_0
#print axioms block_350_0
#print axioms completed_350_0
#print axioms conditional_350_0

theorem selected_350_4 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 4 [] ++ [350])) := by rfl

theorem source_350_4 (code : Nat) :
    edgeSource 4 350 code = 1049760+code/6 := by rfl

theorem target_350_4 (code : Nat) :
    edgeTarget 4 350 code = 1290816+code%7776 := by rfl

theorem block_350_4 :
    savedBlockClass (75*350+4) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_4 (code : Nat) :
    weight completedCredit 4 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 4 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_4 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_4 (code : Nat) :
    weight conditionalCredit 4 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 4 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_4 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_4
#print axioms source_350_4
#print axioms target_350_4
#print axioms block_350_4
#print axioms completed_350_4
#print axioms conditional_350_4

theorem selected_350_9 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 9 [] ++ [350])) := by rfl

theorem source_350_9 (code : Nat) :
    edgeSource 9 350 code = 1088640+code/6 := by rfl

theorem target_350_9 (code : Nat) :
    edgeTarget 9 350 code = 1345248+code%7776 := by rfl

theorem block_350_9 :
    savedBlockClass (75*350+9) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_9 (code : Nat) :
    weight completedCredit 9 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 9 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_9 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_9 (code : Nat) :
    weight conditionalCredit 9 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 9 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_9 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_9
#print axioms source_350_9
#print axioms target_350_9
#print axioms block_350_9
#print axioms completed_350_9
#print axioms conditional_350_9

theorem selected_350_16 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 16 [] ++ [350])) := by rfl

theorem source_350_16 (code : Nat) :
    edgeSource 16 350 code = 1143072+code/6 := by rfl

theorem target_350_16 (code : Nat) :
    edgeTarget 16 350 code = 1423008+code%7776 := by rfl

theorem block_350_16 :
    savedBlockClass (75*350+16) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_16 (code : Nat) :
    weight completedCredit 16 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 16 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_16 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_16 (code : Nat) :
    weight conditionalCredit 16 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 16 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_16 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_16
#print axioms source_350_16
#print axioms target_350_16
#print axioms block_350_16
#print axioms completed_350_16
#print axioms conditional_350_16

theorem selected_350_28 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 28 [] ++ [350])) := by rfl

theorem source_350_28 (code : Nat) :
    edgeSource 28 350 code = 1236384+code/6 := by rfl

theorem target_350_28 (code : Nat) :
    edgeTarget 28 350 code = 1547424+code%7776 := by rfl

theorem block_350_28 :
    savedBlockClass (75*350+28) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_28 (code : Nat) :
    weight completedCredit 28 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 28 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_28 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_28 (code : Nat) :
    weight conditionalCredit 28 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 28 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_28 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_28
#print axioms source_350_28
#print axioms target_350_28
#print axioms block_350_28
#print axioms completed_350_28
#print axioms conditional_350_28

theorem selected_350_29 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 29 [] ++ [350])) := by rfl

theorem source_350_29 (code : Nat) :
    edgeSource 29 350 code = 1244160+code/6 := by rfl

theorem target_350_29 (code : Nat) :
    edgeTarget 29 350 code = 1570752+code%7776 := by rfl

theorem block_350_29 :
    savedBlockClass (75*350+29) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_29 (code : Nat) :
    weight completedCredit 29 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 29 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_29 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_29 (code : Nat) :
    weight conditionalCredit 29 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 29 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_29 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_29
#print axioms source_350_29
#print axioms target_350_29
#print axioms block_350_29
#print axioms completed_350_29
#print axioms conditional_350_29

theorem selected_350_40 :
    [rule014] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 40 [] ++ [350])) := by rfl

theorem source_350_40 (code : Nat) :
    edgeSource 40 350 code = 1329696+code/6 := by rfl

theorem target_350_40 (code : Nat) :
    edgeTarget 40 350 code = 1345248+code%7776 := by rfl

theorem block_350_40 :
    savedBlockClass (75*350+40) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_40 (code : Nat) :
    weight completedCredit 40 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule014] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 40 350 [rule014] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_40 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_40 (code : Nat) :
    weight conditionalCredit 40 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule014] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 40 350 [rule014] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_40 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_40
#print axioms source_350_40
#print axioms target_350_40
#print axioms block_350_40
#print axioms completed_350_40
#print axioms conditional_350_40

theorem selected_350_44 :
    [rule020] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 44 [] ++ [350])) := by rfl

theorem source_350_44 (code : Nat) :
    edgeSource 44 350 code = 1360800+code/6 := by rfl

theorem target_350_44 (code : Nat) :
    edgeTarget 44 350 code = 1547424+code%7776 := by rfl

theorem block_350_44 :
    savedBlockClass (75*350+44) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_44 (code : Nat) :
    weight completedCredit 44 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule020] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 44 350 [rule020] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_44 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_44 (code : Nat) :
    weight conditionalCredit 44 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule020] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 44 350 [rule020] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_44 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_44
#print axioms source_350_44
#print axioms target_350_44
#print axioms block_350_44
#print axioms completed_350_44
#print axioms conditional_350_44

theorem selected_350_50 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 50 [] ++ [350])) := by rfl

theorem source_350_50 (code : Nat) :
    edgeSource 50 350 code = 1407456+code/6 := by rfl

theorem target_350_50 (code : Nat) :
    edgeTarget 50 350 code = 1290816+code%7776 := by rfl

theorem block_350_50 :
    savedBlockClass (75*350+50) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_50 (code : Nat) :
    weight completedCredit 50 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 50 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_50 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_50 (code : Nat) :
    weight conditionalCredit 50 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 50 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_50 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_50
#print axioms source_350_50
#print axioms target_350_50
#print axioms block_350_50
#print axioms completed_350_50
#print axioms conditional_350_50

theorem selected_350_55 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 55 [] ++ [350])) := by rfl

theorem source_350_55 (code : Nat) :
    edgeSource 55 350 code = 1446336+code/6 := by rfl

theorem target_350_55 (code : Nat) :
    edgeTarget 55 350 code = 1547424+code%7776 := by rfl

theorem block_350_55 :
    savedBlockClass (75*350+55) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_55 (code : Nat) :
    weight completedCredit 55 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 55 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_55 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_55 (code : Nat) :
    weight conditionalCredit 55 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 55 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_55 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_55
#print axioms source_350_55
#print axioms target_350_55
#print axioms block_350_55
#print axioms completed_350_55
#print axioms conditional_350_55

theorem selected_350_65 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 65 [] ++ [350])) := by rfl

theorem source_350_65 (code : Nat) :
    edgeSource 65 350 code = 1524096+code/6 := by rfl

theorem target_350_65 (code : Nat) :
    edgeTarget 65 350 code = 1547424+code%7776 := by rfl

theorem block_350_65 :
    savedBlockClass (75*350+65) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_65 (code : Nat) :
    weight completedCredit 65 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 65 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_65 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_65 (code : Nat) :
    weight conditionalCredit 65 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 65 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_65 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_65
#print axioms source_350_65
#print axioms target_350_65
#print axioms block_350_65
#print axioms completed_350_65
#print axioms conditional_350_65

theorem selected_350_74 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 74 [] ++ [350])) := by rfl

theorem source_350_74 (code : Nat) :
    edgeSource 74 350 code = 1594080+code/6 := by rfl

theorem target_350_74 (code : Nat) :
    edgeTarget 74 350 code = 1547424+code%7776 := by rfl

theorem block_350_74 :
    savedBlockClass (75*350+74) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_350_74 (code : Nat) :
    weight completedCredit 74 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 74 350 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_74 direction_350.1
    direction_350.2.1 conditioned_350 code

theorem conditional_350_74 (code : Nat) :
    weight conditionalCredit 74 350 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 74 350 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_350_74 direction_350.1
    direction_350.2.2 conditioned_350 code
#print axioms selected_350_74
#print axioms source_350_74
#print axioms target_350_74
#print axioms block_350_74
#print axioms completed_350_74
#print axioms conditional_350_74

theorem selected_351_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [351])) := by rfl

theorem source_351_0 (code : Nat) :
    edgeSource 0 351 code = 785376+code/6 := by rfl

theorem target_351_0 (code : Nat) :
    edgeTarget 0 351 code = 1189728+code%7776 := by rfl

theorem block_351_0 :
    savedBlockClass (75*351+0) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_0 (code : Nat) :
    weight completedCredit 0 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_0 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_0 (code : Nat) :
    weight conditionalCredit 0 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_0 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_0
#print axioms source_351_0
#print axioms target_351_0
#print axioms block_351_0
#print axioms completed_351_0
#print axioms conditional_351_0

theorem selected_351_4 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 4 [] ++ [351])) := by rfl

theorem source_351_4 (code : Nat) :
    edgeSource 4 351 code = 1049760+code/6 := by rfl

theorem target_351_4 (code : Nat) :
    edgeTarget 4 351 code = 1298592+code%7776 := by rfl

theorem block_351_4 :
    savedBlockClass (75*351+4) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_4 (code : Nat) :
    weight completedCredit 4 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 4 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_4 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_4 (code : Nat) :
    weight conditionalCredit 4 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 4 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_4 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_4
#print axioms source_351_4
#print axioms target_351_4
#print axioms block_351_4
#print axioms completed_351_4
#print axioms conditional_351_4

theorem selected_351_9 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 9 [] ++ [351])) := by rfl

theorem source_351_9 (code : Nat) :
    edgeSource 9 351 code = 1088640+code/6 := by rfl

theorem target_351_9 (code : Nat) :
    edgeTarget 9 351 code = 1189728+code%7776 := by rfl

theorem block_351_9 :
    savedBlockClass (75*351+9) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_9 (code : Nat) :
    weight completedCredit 9 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 9 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_9 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_9 (code : Nat) :
    weight conditionalCredit 9 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 9 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_9 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_9
#print axioms source_351_9
#print axioms target_351_9
#print axioms block_351_9
#print axioms completed_351_9
#print axioms conditional_351_9

theorem selected_351_16 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 16 [] ++ [351])) := by rfl

theorem source_351_16 (code : Nat) :
    edgeSource 16 351 code = 1143072+code/6 := by rfl

theorem target_351_16 (code : Nat) :
    edgeTarget 16 351 code = 1189728+code%7776 := by rfl

theorem block_351_16 :
    savedBlockClass (75*351+16) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_16 (code : Nat) :
    weight completedCredit 16 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 16 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_16 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_16 (code : Nat) :
    weight conditionalCredit 16 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 16 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_16 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_16
#print axioms source_351_16
#print axioms target_351_16
#print axioms block_351_16
#print axioms completed_351_16
#print axioms conditional_351_16

theorem selected_351_28 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 28 [] ++ [351])) := by rfl

theorem source_351_28 (code : Nat) :
    edgeSource 28 351 code = 1236384+code/6 := by rfl

theorem target_351_28 (code : Nat) :
    edgeTarget 28 351 code = 1189728+code%7776 := by rfl

theorem block_351_28 :
    savedBlockClass (75*351+28) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_28 (code : Nat) :
    weight completedCredit 28 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 28 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_28 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_28 (code : Nat) :
    weight conditionalCredit 28 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 28 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_28 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_28
#print axioms source_351_28
#print axioms target_351_28
#print axioms block_351_28
#print axioms completed_351_28
#print axioms conditional_351_28

theorem selected_351_29 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 29 [] ++ [351])) := by rfl

theorem source_351_29 (code : Nat) :
    edgeSource 29 351 code = 1244160+code/6 := by rfl

theorem target_351_29 (code : Nat) :
    edgeTarget 29 351 code = 1189728+code%7776 := by rfl

theorem block_351_29 :
    savedBlockClass (75*351+29) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_29 (code : Nat) :
    weight completedCredit 29 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 29 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_29 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_29 (code : Nat) :
    weight conditionalCredit 29 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 29 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_29 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_29
#print axioms source_351_29
#print axioms target_351_29
#print axioms block_351_29
#print axioms completed_351_29
#print axioms conditional_351_29

theorem selected_351_40 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 40 [] ++ [351])) := by rfl

theorem source_351_40 (code : Nat) :
    edgeSource 40 351 code = 1329696+code/6 := by rfl

theorem target_351_40 (code : Nat) :
    edgeTarget 40 351 code = 1189728+code%7776 := by rfl

theorem block_351_40 :
    savedBlockClass (75*351+40) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_40 (code : Nat) :
    weight completedCredit 40 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 40 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_40 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_40 (code : Nat) :
    weight conditionalCredit 40 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 40 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_40 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_40
#print axioms source_351_40
#print axioms target_351_40
#print axioms block_351_40
#print axioms completed_351_40
#print axioms conditional_351_40

theorem selected_351_44 :
    [rule021] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 44 [] ++ [351])) := by rfl

theorem source_351_44 (code : Nat) :
    edgeSource 44 351 code = 1360800+code/6 := by rfl

theorem target_351_44 (code : Nat) :
    edgeTarget 44 351 code = 1189728+code%7776 := by rfl

theorem block_351_44 :
    savedBlockClass (75*351+44) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_44 (code : Nat) :
    weight completedCredit 44 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule021] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 44 351 [rule021] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_44 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_44 (code : Nat) :
    weight conditionalCredit 44 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule021] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 44 351 [rule021] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_44 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_44
#print axioms source_351_44
#print axioms target_351_44
#print axioms block_351_44
#print axioms completed_351_44
#print axioms conditional_351_44

theorem selected_351_50 :
    [rule028] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 50 [] ++ [351])) := by rfl

theorem source_351_50 (code : Nat) :
    edgeSource 50 351 code = 1407456+code/6 := by rfl

theorem target_351_50 (code : Nat) :
    edgeTarget 50 351 code = 1298592+code%7776 := by rfl

theorem block_351_50 :
    savedBlockClass (75*351+50) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_50 (code : Nat) :
    weight completedCredit 50 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule028] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 50 351 [rule028] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_50 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_50 (code : Nat) :
    weight conditionalCredit 50 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule028] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 50 351 [rule028] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_50 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_50
#print axioms source_351_50
#print axioms target_351_50
#print axioms block_351_50
#print axioms completed_351_50
#print axioms conditional_351_50

theorem selected_351_55 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 55 [] ++ [351])) := by rfl

theorem source_351_55 (code : Nat) :
    edgeSource 55 351 code = 1446336+code/6 := by rfl

theorem target_351_55 (code : Nat) :
    edgeTarget 55 351 code = 1189728+code%7776 := by rfl

theorem block_351_55 :
    savedBlockClass (75*351+55) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_55 (code : Nat) :
    weight completedCredit 55 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 55 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_55 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_55 (code : Nat) :
    weight conditionalCredit 55 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 55 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_55 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_55
#print axioms source_351_55
#print axioms target_351_55
#print axioms block_351_55
#print axioms completed_351_55
#print axioms conditional_351_55

theorem selected_351_65 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 65 [] ++ [351])) := by rfl

theorem source_351_65 (code : Nat) :
    edgeSource 65 351 code = 1524096+code/6 := by rfl

theorem target_351_65 (code : Nat) :
    edgeTarget 65 351 code = 1189728+code%7776 := by rfl

theorem block_351_65 :
    savedBlockClass (75*351+65) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_65 (code : Nat) :
    weight completedCredit 65 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 65 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_65 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_65 (code : Nat) :
    weight conditionalCredit 65 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 65 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_65 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_65
#print axioms source_351_65
#print axioms target_351_65
#print axioms block_351_65
#print axioms completed_351_65
#print axioms conditional_351_65

theorem selected_351_74 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 74 [] ++ [351])) := by rfl

theorem source_351_74 (code : Nat) :
    edgeSource 74 351 code = 1594080+code/6 := by rfl

theorem target_351_74 (code : Nat) :
    edgeTarget 74 351 code = 1189728+code%7776 := by rfl

theorem block_351_74 :
    savedBlockClass (75*351+74) = some 122 ∧
    recordedClassRoot 122 = 3950 := by decide +kernel

theorem completed_351_74 (code : Nat) :
    weight completedCredit 74 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 74 351 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_74 direction_351.1
    direction_351.2.1 conditioned_351 code

theorem conditional_351_74 (code : Nat) :
    weight conditionalCredit 74 351 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 74 351 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_351_74 direction_351.1
    direction_351.2.2 conditioned_351 code
#print axioms selected_351_74
#print axioms source_351_74
#print axioms target_351_74
#print axioms block_351_74
#print axioms completed_351_74
#print axioms conditional_351_74

theorem selected_352_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [352])) := by rfl

theorem source_352_0 (code : Nat) :
    edgeSource 0 352 code = 785376+code/6 := by rfl

theorem target_352_0 (code : Nat) :
    edgeTarget 0 352 code = 388800+code%7776 := by rfl

theorem block_352_0 :
    savedBlockClass (75*352+0) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_0 (code : Nat) :
    weight completedCredit 0 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 352 [] 0 0
    (fun code => 0) selected_352_0 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_0 (code : Nat) :
    weight conditionalCredit 0 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 352 [] 0 16
    (fun code => 0) selected_352_0 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_0
#print axioms source_352_0
#print axioms target_352_0
#print axioms block_352_0
#print axioms completed_352_0
#print axioms conditional_352_0

theorem selected_352_4 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 4 [] ++ [352])) := by rfl

theorem source_352_4 (code : Nat) :
    edgeSource 4 352 code = 1049760+code/6 := by rfl

theorem target_352_4 (code : Nat) :
    edgeTarget 4 352 code = 388800+code%7776 := by rfl

theorem block_352_4 :
    savedBlockClass (75*352+4) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_4 (code : Nat) :
    weight completedCredit 4 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 4 352 [] 0 0
    (fun code => 0) selected_352_4 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_4 (code : Nat) :
    weight conditionalCredit 4 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 4 352 [] 0 16
    (fun code => 0) selected_352_4 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_4
#print axioms source_352_4
#print axioms target_352_4
#print axioms block_352_4
#print axioms completed_352_4
#print axioms conditional_352_4

theorem selected_352_9 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 9 [] ++ [352])) := by rfl

theorem source_352_9 (code : Nat) :
    edgeSource 9 352 code = 1088640+code/6 := by rfl

theorem target_352_9 (code : Nat) :
    edgeTarget 9 352 code = 388800+code%7776 := by rfl

theorem block_352_9 :
    savedBlockClass (75*352+9) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_9 (code : Nat) :
    weight completedCredit 9 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 9 352 [] 0 0
    (fun code => 0) selected_352_9 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_9 (code : Nat) :
    weight conditionalCredit 9 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 9 352 [] 0 16
    (fun code => 0) selected_352_9 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_9
#print axioms source_352_9
#print axioms target_352_9
#print axioms block_352_9
#print axioms completed_352_9
#print axioms conditional_352_9

theorem selected_352_16 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 16 [] ++ [352])) := by rfl

theorem source_352_16 (code : Nat) :
    edgeSource 16 352 code = 1143072+code/6 := by rfl

theorem target_352_16 (code : Nat) :
    edgeTarget 16 352 code = 388800+code%7776 := by rfl

theorem block_352_16 :
    savedBlockClass (75*352+16) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_16 (code : Nat) :
    weight completedCredit 16 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 16 352 [] 0 0
    (fun code => 0) selected_352_16 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_16 (code : Nat) :
    weight conditionalCredit 16 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 16 352 [] 0 16
    (fun code => 0) selected_352_16 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_16
#print axioms source_352_16
#print axioms target_352_16
#print axioms block_352_16
#print axioms completed_352_16
#print axioms conditional_352_16

theorem selected_352_28 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 28 [] ++ [352])) := by rfl

theorem source_352_28 (code : Nat) :
    edgeSource 28 352 code = 1236384+code/6 := by rfl

theorem target_352_28 (code : Nat) :
    edgeTarget 28 352 code = 1555200+code%7776 := by rfl

theorem block_352_28 :
    savedBlockClass (75*352+28) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_28 (code : Nat) :
    weight completedCredit 28 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 28 352 [] 0 0
    (fun code => 0) selected_352_28 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_28 (code : Nat) :
    weight conditionalCredit 28 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 28 352 [] 0 16
    (fun code => 0) selected_352_28 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_28
#print axioms source_352_28
#print axioms target_352_28
#print axioms block_352_28
#print axioms completed_352_28
#print axioms conditional_352_28

theorem selected_352_29 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 29 [] ++ [352])) := by rfl

theorem source_352_29 (code : Nat) :
    edgeSource 29 352 code = 1244160+code/6 := by rfl

theorem target_352_29 (code : Nat) :
    edgeTarget 29 352 code = 388800+code%7776 := by rfl

theorem block_352_29 :
    savedBlockClass (75*352+29) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_29 (code : Nat) :
    weight completedCredit 29 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 29 352 [] 0 0
    (fun code => 0) selected_352_29 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_29 (code : Nat) :
    weight conditionalCredit 29 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 29 352 [] 0 16
    (fun code => 0) selected_352_29 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_29
#print axioms source_352_29
#print axioms target_352_29
#print axioms block_352_29
#print axioms completed_352_29
#print axioms conditional_352_29

theorem selected_352_40 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 40 [] ++ [352])) := by rfl

theorem source_352_40 (code : Nat) :
    edgeSource 40 352 code = 1329696+code/6 := by rfl

theorem target_352_40 (code : Nat) :
    edgeTarget 40 352 code = 388800+code%7776 := by rfl

theorem block_352_40 :
    savedBlockClass (75*352+40) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_40 (code : Nat) :
    weight completedCredit 40 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 40 352 [] 0 0
    (fun code => 0) selected_352_40 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_40 (code : Nat) :
    weight conditionalCredit 40 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 40 352 [] 0 16
    (fun code => 0) selected_352_40 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_40
#print axioms source_352_40
#print axioms target_352_40
#print axioms block_352_40
#print axioms completed_352_40
#print axioms conditional_352_40

theorem selected_352_44 :
    [rule022] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 44 [] ++ [352])) := by rfl

theorem source_352_44 (code : Nat) :
    edgeSource 44 352 code = 1360800+code/6 := by rfl

theorem target_352_44 (code : Nat) :
    edgeTarget 44 352 code = 1555200+code%7776 := by rfl

theorem block_352_44 :
    savedBlockClass (75*352+44) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_44 (code : Nat) :
    weight completedCredit 44 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule022] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 44 352 [rule022] 0 0
    (fun code => 0) selected_352_44 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_44 (code : Nat) :
    weight conditionalCredit 44 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule022] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 44 352 [rule022] 0 16
    (fun code => 0) selected_352_44 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_44
#print axioms source_352_44
#print axioms target_352_44
#print axioms block_352_44
#print axioms completed_352_44
#print axioms conditional_352_44

theorem selected_352_50 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 50 [] ++ [352])) := by rfl

theorem source_352_50 (code : Nat) :
    edgeSource 50 352 code = 1407456+code/6 := by rfl

theorem target_352_50 (code : Nat) :
    edgeTarget 50 352 code = 388800+code%7776 := by rfl

theorem block_352_50 :
    savedBlockClass (75*352+50) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_50 (code : Nat) :
    weight completedCredit 50 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 50 352 [] 0 0
    (fun code => 0) selected_352_50 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_50 (code : Nat) :
    weight conditionalCredit 50 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 50 352 [] 0 16
    (fun code => 0) selected_352_50 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_50
#print axioms source_352_50
#print axioms target_352_50
#print axioms block_352_50
#print axioms completed_352_50
#print axioms conditional_352_50

theorem selected_352_55 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 55 [] ++ [352])) := by rfl

theorem source_352_55 (code : Nat) :
    edgeSource 55 352 code = 1446336+code/6 := by rfl

theorem target_352_55 (code : Nat) :
    edgeTarget 55 352 code = 1555200+code%7776 := by rfl

theorem block_352_55 :
    savedBlockClass (75*352+55) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_55 (code : Nat) :
    weight completedCredit 55 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 55 352 [] 0 0
    (fun code => 0) selected_352_55 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_55 (code : Nat) :
    weight conditionalCredit 55 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 55 352 [] 0 16
    (fun code => 0) selected_352_55 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_55
#print axioms source_352_55
#print axioms target_352_55
#print axioms block_352_55
#print axioms completed_352_55
#print axioms conditional_352_55

theorem selected_352_65 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 65 [] ++ [352])) := by rfl

theorem source_352_65 (code : Nat) :
    edgeSource 65 352 code = 1524096+code/6 := by rfl

theorem target_352_65 (code : Nat) :
    edgeTarget 65 352 code = 1555200+code%7776 := by rfl

theorem block_352_65 :
    savedBlockClass (75*352+65) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_65 (code : Nat) :
    weight completedCredit 65 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 65 352 [] 0 0
    (fun code => 0) selected_352_65 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_65 (code : Nat) :
    weight conditionalCredit 65 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 65 352 [] 0 16
    (fun code => 0) selected_352_65 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_65
#print axioms source_352_65
#print axioms target_352_65
#print axioms block_352_65
#print axioms completed_352_65
#print axioms conditional_352_65

theorem selected_352_74 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 74 [] ++ [352])) := by rfl

theorem source_352_74 (code : Nat) :
    edgeSource 74 352 code = 1594080+code/6 := by rfl

theorem target_352_74 (code : Nat) :
    edgeTarget 74 352 code = 1555200+code%7776 := by rfl

theorem block_352_74 :
    savedBlockClass (75*352+74) = some 124 ∧
    recordedClassRoot 124 = 3970 := by decide +kernel

theorem completed_352_74 (code : Nat) :
    weight completedCredit 74 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 74 352 [] 0 0
    (fun code => 0) selected_352_74 direction_352.1
    direction_352.2.1 conditioned_352 code

theorem conditional_352_74 (code : Nat) :
    weight conditionalCredit 74 352 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 74 352 [] 0 16
    (fun code => 0) selected_352_74 direction_352.1
    direction_352.2.2 conditioned_352 code
#print axioms selected_352_74
#print axioms source_352_74
#print axioms target_352_74
#print axioms block_352_74
#print axioms completed_352_74
#print axioms conditional_352_74

end Snake9.Context101
