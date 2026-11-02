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

theorem selected_482_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [482])) := by rfl

theorem source_482_0 (code : Nat) :
    edgeSource 0 482 code = 995328+code/6 := by rfl

theorem target_482_0 (code : Nat) :
    edgeTarget 0 482 code = 870912+code%7776 := by rfl

theorem block_482_0 :
    savedBlockClass (75*482+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_482_0 (code : Nat) :
    weight completedCredit 0 482 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 482 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_482_0 direction_482.1
    direction_482.2.1 conditioned_482 code

theorem conditional_482_0 (code : Nat) :
    weight conditionalCredit 0 482 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 482 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_482_0 direction_482.1
    direction_482.2.2 conditioned_482 code
#print axioms selected_482_0
#print axioms source_482_0
#print axioms target_482_0
#print axioms block_482_0
#print axioms completed_482_0
#print axioms conditional_482_0

theorem selected_483_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [483])) := by rfl

theorem source_483_0 (code : Nat) :
    edgeSource 0 483 code = 995328+code/6 := by rfl

theorem target_483_0 (code : Nat) :
    edgeTarget 0 483 code = 878688+code%7776 := by rfl

theorem block_483_0 :
    savedBlockClass (75*483+0) = some 29 ∧
    recordedClassRoot 29 = 2691 := by decide +kernel

theorem completed_483_0 (code : Nat) :
    weight completedCredit 0 483 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 483 [] 0 0
    (fun code => 0) selected_483_0 direction_483.1
    direction_483.2.1 conditioned_483 code

theorem conditional_483_0 (code : Nat) :
    weight conditionalCredit 0 483 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 483 [] 0 16
    (fun code => 0) selected_483_0 direction_483.1
    direction_483.2.2 conditioned_483 code
#print axioms selected_483_0
#print axioms source_483_0
#print axioms target_483_0
#print axioms block_483_0
#print axioms completed_483_0
#print axioms conditional_483_0

theorem selected_484_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [484])) := by rfl

theorem source_484_0 (code : Nat) :
    edgeSource 0 484 code = 995328+code/6 := by rfl

theorem target_484_0 (code : Nat) :
    edgeTarget 0 484 code = 886464+code%7776 := by rfl

theorem block_484_0 :
    savedBlockClass (75*484+0) = some 43 ∧
    recordedClassRoot 43 = 3318 := by decide +kernel

theorem completed_484_0 (code : Nat) :
    weight completedCredit 0 484 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 484 [] 0 16
    (fun code => 0) selected_484_0 direction_484.1
    direction_484.2.1 conditioned_484 code

theorem conditional_484_0 (code : Nat) :
    weight conditionalCredit 0 484 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 484 [] 0 16
    (fun code => 0) selected_484_0 direction_484.1
    direction_484.2.2 conditioned_484 code
#print axioms selected_484_0
#print axioms source_484_0
#print axioms target_484_0
#print axioms block_484_0
#print axioms completed_484_0
#print axioms conditional_484_0

theorem selected_485_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [485])) := by rfl

theorem source_485_0 (code : Nat) :
    edgeSource 0 485 code = 995328+code/6 := by rfl

theorem target_485_0 (code : Nat) :
    edgeTarget 0 485 code = 894240+code%7776 := by rfl

theorem block_485_0 :
    savedBlockClass (75*485+0) = some 112 ∧
    recordedClassRoot 112 = 3904 := by decide +kernel

theorem completed_485_0 (code : Nat) :
    weight completedCredit 0 485 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 485 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_485_0 direction_485.1
    direction_485.2.1 conditioned_485 code

theorem conditional_485_0 (code : Nat) :
    weight conditionalCredit 0 485 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 485 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_485_0 direction_485.1
    direction_485.2.2 conditioned_485 code
#print axioms selected_485_0
#print axioms source_485_0
#print axioms target_485_0
#print axioms block_485_0
#print axioms completed_485_0
#print axioms conditional_485_0

theorem selected_486_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [486])) := by rfl

theorem source_486_0 (code : Nat) :
    edgeSource 0 486 code = 995328+code/6 := by rfl

theorem target_486_0 (code : Nat) :
    edgeTarget 0 486 code = 902016+code%7776 := by rfl

theorem block_486_0 :
    savedBlockClass (75*486+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_486_0 (code : Nat) :
    weight completedCredit 0 486 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 486 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_486_0 direction_486.1
    direction_486.2.1 conditioned_486 code

theorem conditional_486_0 (code : Nat) :
    weight conditionalCredit 0 486 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 486 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_486_0 direction_486.1
    direction_486.2.2 conditioned_486 code
#print axioms selected_486_0
#print axioms source_486_0
#print axioms target_486_0
#print axioms block_486_0
#print axioms completed_486_0
#print axioms conditional_486_0

theorem selected_487_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [487])) := by rfl

theorem source_487_0 (code : Nat) :
    edgeSource 0 487 code = 1003104+code/6 := by rfl

theorem target_487_0 (code : Nat) :
    edgeTarget 0 487 code = 940896+code%7776 := by rfl

theorem block_487_0 :
    savedBlockClass (75*487+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_487_0 (code : Nat) :
    weight completedCredit 0 487 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 487 [] 18 16
    (fun code => 0) selected_487_0 direction_487.1
    direction_487.2.1 conditioned_487 code

theorem conditional_487_0 (code : Nat) :
    weight conditionalCredit 0 487 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 487 [] 18 16
    (fun code => 0) selected_487_0 direction_487.1
    direction_487.2.2 conditioned_487 code
#print axioms selected_487_0
#print axioms source_487_0
#print axioms target_487_0
#print axioms block_487_0
#print axioms completed_487_0
#print axioms conditional_487_0

theorem selected_488_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [488])) := by rfl

theorem source_488_0 (code : Nat) :
    edgeSource 0 488 code = 1003104+code/6 := by rfl

theorem target_488_0 (code : Nat) :
    edgeTarget 0 488 code = 909792+code%7776 := by rfl

theorem block_488_0 :
    savedBlockClass (75*488+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_488_0 (code : Nat) :
    weight completedCredit 0 488 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 488 [] 18 16
    (fun code => 0) selected_488_0 direction_488.1
    direction_488.2.1 conditioned_488 code

theorem conditional_488_0 (code : Nat) :
    weight conditionalCredit 0 488 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 488 [] 18 16
    (fun code => 0) selected_488_0 direction_488.1
    direction_488.2.2 conditioned_488 code
#print axioms selected_488_0
#print axioms source_488_0
#print axioms target_488_0
#print axioms block_488_0
#print axioms completed_488_0
#print axioms conditional_488_0

theorem selected_489_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [489])) := by rfl

theorem source_489_0 (code : Nat) :
    edgeSource 0 489 code = 1003104+code/6 := by rfl

theorem target_489_0 (code : Nat) :
    edgeTarget 0 489 code = 917568+code%7776 := by rfl

theorem block_489_0 :
    savedBlockClass (75*489+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_489_0 (code : Nat) :
    weight completedCredit 0 489 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 489 [] 18 16
    (fun code => 0) selected_489_0 direction_489.1
    direction_489.2.1 conditioned_489 code

theorem conditional_489_0 (code : Nat) :
    weight conditionalCredit 0 489 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 489 [] 18 16
    (fun code => 0) selected_489_0 direction_489.1
    direction_489.2.2 conditioned_489 code
#print axioms selected_489_0
#print axioms source_489_0
#print axioms target_489_0
#print axioms block_489_0
#print axioms completed_489_0
#print axioms conditional_489_0

theorem selected_490_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [490])) := by rfl

theorem source_490_0 (code : Nat) :
    edgeSource 0 490 code = 1003104+code/6 := by rfl

theorem target_490_0 (code : Nat) :
    edgeTarget 0 490 code = 925344+code%7776 := by rfl

theorem block_490_0 :
    savedBlockClass (75*490+0) = some 76 ∧
    recordedClassRoot 76 = 3519 := by decide +kernel

theorem completed_490_0 (code : Nat) :
    weight completedCredit 0 490 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 490 [] 6 0
    (fun code => 0) selected_490_0 direction_490.1
    direction_490.2.1 conditioned_490 code

theorem conditional_490_0 (code : Nat) :
    weight conditionalCredit 0 490 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 490 [] 6 16
    (fun code => 0) selected_490_0 direction_490.1
    direction_490.2.2 conditioned_490 code
#print axioms selected_490_0
#print axioms source_490_0
#print axioms target_490_0
#print axioms block_490_0
#print axioms completed_490_0
#print axioms conditional_490_0

theorem selected_491_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [491])) := by rfl

theorem source_491_0 (code : Nat) :
    edgeSource 0 491 code = 1003104+code/6 := by rfl

theorem target_491_0 (code : Nat) :
    edgeTarget 0 491 code = 933120+code%7776 := by rfl

theorem block_491_0 :
    savedBlockClass (75*491+0) = some 77 ∧
    recordedClassRoot 77 = 3522 := by decide +kernel

theorem completed_491_0 (code : Nat) :
    weight completedCredit 0 491 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 491 [] 12 16
    (fun code => 0) selected_491_0 direction_491.1
    direction_491.2.1 conditioned_491 code

theorem conditional_491_0 (code : Nat) :
    weight conditionalCredit 0 491 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 491 [] 12 16
    (fun code => 0) selected_491_0 direction_491.1
    direction_491.2.2 conditioned_491 code
#print axioms selected_491_0
#print axioms source_491_0
#print axioms target_491_0
#print axioms block_491_0
#print axioms completed_491_0
#print axioms conditional_491_0

theorem selected_492_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [492])) := by rfl

theorem source_492_0 (code : Nat) :
    edgeSource 0 492 code = 1003104+code/6 := by rfl

theorem target_492_0 (code : Nat) :
    edgeTarget 0 492 code = 940896+code%7776 := by rfl

theorem block_492_0 :
    savedBlockClass (75*492+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_492_0 (code : Nat) :
    weight completedCredit 0 492 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 492 [] 18 16
    (fun code => 0) selected_492_0 direction_492.1
    direction_492.2.1 conditioned_492 code

theorem conditional_492_0 (code : Nat) :
    weight conditionalCredit 0 492 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 492 [] 18 16
    (fun code => 0) selected_492_0 direction_492.1
    direction_492.2.2 conditioned_492 code
#print axioms selected_492_0
#print axioms source_492_0
#print axioms target_492_0
#print axioms block_492_0
#print axioms completed_492_0
#print axioms conditional_492_0

theorem selected_493_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [493])) := by rfl

theorem source_493_0 (code : Nat) :
    edgeSource 0 493 code = 1010880+code/6 := by rfl

theorem target_493_0 (code : Nat) :
    edgeTarget 0 493 code = 972000+code%7776 := by rfl

theorem block_493_0 :
    savedBlockClass (75*493+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_493_0 (code : Nat) :
    weight completedCredit 0 493 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 493 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_493_0 direction_493.1
    direction_493.2.1 conditioned_493 code

theorem conditional_493_0 (code : Nat) :
    weight conditionalCredit 0 493 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 493 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_493_0 direction_493.1
    direction_493.2.2 conditioned_493 code
#print axioms selected_493_0
#print axioms source_493_0
#print axioms target_493_0
#print axioms block_493_0
#print axioms completed_493_0
#print axioms conditional_493_0

theorem selected_494_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [494])) := by rfl

theorem source_494_0 (code : Nat) :
    edgeSource 0 494 code = 1010880+code/6 := by rfl

theorem target_494_0 (code : Nat) :
    edgeTarget 0 494 code = 948672+code%7776 := by rfl

theorem block_494_0 :
    savedBlockClass (75*494+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_494_0 (code : Nat) :
    weight completedCredit 0 494 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 494 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_494_0 direction_494.1
    direction_494.2.1 conditioned_494 code

theorem conditional_494_0 (code : Nat) :
    weight conditionalCredit 0 494 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 494 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_494_0 direction_494.1
    direction_494.2.2 conditioned_494 code
#print axioms selected_494_0
#print axioms source_494_0
#print axioms target_494_0
#print axioms block_494_0
#print axioms completed_494_0
#print axioms conditional_494_0

theorem selected_495_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [495])) := by rfl

theorem source_495_0 (code : Nat) :
    edgeSource 0 495 code = 1010880+code/6 := by rfl

theorem target_495_0 (code : Nat) :
    edgeTarget 0 495 code = 956448+code%7776 := by rfl

theorem block_495_0 :
    savedBlockClass (75*495+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_495_0 (code : Nat) :
    weight completedCredit 0 495 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 495 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_495_0 direction_495.1
    direction_495.2.1 conditioned_495 code

theorem conditional_495_0 (code : Nat) :
    weight conditionalCredit 0 495 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 495 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_495_0 direction_495.1
    direction_495.2.2 conditioned_495 code
#print axioms selected_495_0
#print axioms source_495_0
#print axioms target_495_0
#print axioms block_495_0
#print axioms completed_495_0
#print axioms conditional_495_0

theorem selected_496_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [496])) := by rfl

theorem source_496_0 (code : Nat) :
    edgeSource 0 496 code = 1010880+code/6 := by rfl

theorem target_496_0 (code : Nat) :
    edgeTarget 0 496 code = 1259712+code%7776 := by rfl

theorem block_496_0 :
    savedBlockClass (75*496+0) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_496_0 (code : Nat) :
    weight completedCredit 0 496 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 496 [] 0 12
    (fun code => 0) selected_496_0 direction_496.1
    direction_496.2.1 conditioned_496 code

theorem conditional_496_0 (code : Nat) :
    weight conditionalCredit 0 496 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 496 [] 0 12
    (fun code => 0) selected_496_0 direction_496.1
    direction_496.2.2 conditioned_496 code
#print axioms selected_496_0
#print axioms source_496_0
#print axioms target_496_0
#print axioms block_496_0
#print axioms completed_496_0
#print axioms conditional_496_0

theorem selected_497_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [497])) := by rfl

theorem source_497_0 (code : Nat) :
    edgeSource 0 497 code = 1010880+code/6 := by rfl

theorem target_497_0 (code : Nat) :
    edgeTarget 0 497 code = 972000+code%7776 := by rfl

theorem block_497_0 :
    savedBlockClass (75*497+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_497_0 (code : Nat) :
    weight completedCredit 0 497 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 497 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_497_0 direction_497.1
    direction_497.2.1 conditioned_497 code

theorem conditional_497_0 (code : Nat) :
    weight conditionalCredit 0 497 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 497 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_497_0 direction_497.1
    direction_497.2.2 conditioned_497 code
#print axioms selected_497_0
#print axioms source_497_0
#print axioms target_497_0
#print axioms block_497_0
#print axioms completed_497_0
#print axioms conditional_497_0

theorem selected_498_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [498])) := by rfl

theorem source_498_0 (code : Nat) :
    edgeSource 0 498 code = 1018656+code/6 := by rfl

theorem target_498_0 (code : Nat) :
    edgeTarget 0 498 code = 1018656+code%7776 := by rfl

theorem block_498_0 :
    savedBlockClass (75*498+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_498_0 (code : Nat) :
    weight completedCredit 0 498 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 498 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_498_0 direction_498.1
    direction_498.2.1 conditioned_498 code

theorem conditional_498_0 (code : Nat) :
    weight conditionalCredit 0 498 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 498 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_498_0 direction_498.1
    direction_498.2.2 conditioned_498 code
#print axioms selected_498_0
#print axioms source_498_0
#print axioms target_498_0
#print axioms block_498_0
#print axioms completed_498_0
#print axioms conditional_498_0

theorem selected_499_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [499])) := by rfl

theorem source_499_0 (code : Nat) :
    edgeSource 0 499 code = 1018656+code/6 := by rfl

theorem target_499_0 (code : Nat) :
    edgeTarget 0 499 code = 979776+code%7776 := by rfl

theorem block_499_0 :
    savedBlockClass (75*499+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_499_0 (code : Nat) :
    weight completedCredit 0 499 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 499 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_499_0 direction_499.1
    direction_499.2.1 conditioned_499 code

theorem conditional_499_0 (code : Nat) :
    weight conditionalCredit 0 499 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 499 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_499_0 direction_499.1
    direction_499.2.2 conditioned_499 code
#print axioms selected_499_0
#print axioms source_499_0
#print axioms target_499_0
#print axioms block_499_0
#print axioms completed_499_0
#print axioms conditional_499_0

theorem selected_500_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [500])) := by rfl

theorem source_500_0 (code : Nat) :
    edgeSource 0 500 code = 1018656+code/6 := by rfl

theorem target_500_0 (code : Nat) :
    edgeTarget 0 500 code = 987552+code%7776 := by rfl

theorem block_500_0 :
    savedBlockClass (75*500+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_500_0 (code : Nat) :
    weight completedCredit 0 500 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 500 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_500_0 direction_500.1
    direction_500.2.1 conditioned_500 code

theorem conditional_500_0 (code : Nat) :
    weight conditionalCredit 0 500 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 500 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_500_0 direction_500.1
    direction_500.2.2 conditioned_500 code
#print axioms selected_500_0
#print axioms source_500_0
#print axioms target_500_0
#print axioms block_500_0
#print axioms completed_500_0
#print axioms conditional_500_0

theorem selected_501_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [501])) := by rfl

theorem source_501_0 (code : Nat) :
    edgeSource 0 501 code = 1018656+code/6 := by rfl

theorem target_501_0 (code : Nat) :
    edgeTarget 0 501 code = 995328+code%7776 := by rfl

theorem block_501_0 :
    savedBlockClass (75*501+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_501_0 (code : Nat) :
    weight completedCredit 0 501 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 501 [] 0 0
    (fun code => 0) selected_501_0 direction_501.1
    direction_501.2.1 conditioned_501 code

theorem conditional_501_0 (code : Nat) :
    weight conditionalCredit 0 501 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 501 [] 0 16
    (fun code => 0) selected_501_0 direction_501.1
    direction_501.2.2 conditioned_501 code
#print axioms selected_501_0
#print axioms source_501_0
#print axioms target_501_0
#print axioms block_501_0
#print axioms completed_501_0
#print axioms conditional_501_0

theorem selected_502_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [502])) := by rfl

theorem source_502_0 (code : Nat) :
    edgeSource 0 502 code = 1018656+code/6 := by rfl

theorem target_502_0 (code : Nat) :
    edgeTarget 0 502 code = 1003104+code%7776 := by rfl

theorem block_502_0 :
    savedBlockClass (75*502+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_502_0 (code : Nat) :
    weight completedCredit 0 502 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 502 [] 0 16
    (fun code => 0) selected_502_0 direction_502.1
    direction_502.2.1 conditioned_502 code

theorem conditional_502_0 (code : Nat) :
    weight conditionalCredit 0 502 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 502 [] 0 16
    (fun code => 0) selected_502_0 direction_502.1
    direction_502.2.2 conditioned_502 code
#print axioms selected_502_0
#print axioms source_502_0
#print axioms target_502_0
#print axioms block_502_0
#print axioms completed_502_0
#print axioms conditional_502_0

theorem selected_503_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [503])) := by rfl

theorem source_503_0 (code : Nat) :
    edgeSource 0 503 code = 1018656+code/6 := by rfl

theorem target_503_0 (code : Nat) :
    edgeTarget 0 503 code = 1010880+code%7776 := by rfl

theorem block_503_0 :
    savedBlockClass (75*503+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_503_0 (code : Nat) :
    weight completedCredit 0 503 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 503 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_503_0 direction_503.1
    direction_503.2.1 conditioned_503 code

theorem conditional_503_0 (code : Nat) :
    weight conditionalCredit 0 503 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 503 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_503_0 direction_503.1
    direction_503.2.2 conditioned_503 code
#print axioms selected_503_0
#print axioms source_503_0
#print axioms target_503_0
#print axioms block_503_0
#print axioms completed_503_0
#print axioms conditional_503_0

theorem selected_504_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [504])) := by rfl

theorem source_504_0 (code : Nat) :
    edgeSource 0 504 code = 1018656+code/6 := by rfl

theorem target_504_0 (code : Nat) :
    edgeTarget 0 504 code = 1018656+code%7776 := by rfl

theorem block_504_0 :
    savedBlockClass (75*504+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_504_0 (code : Nat) :
    weight completedCredit 0 504 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 504 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_504_0 direction_504.1
    direction_504.2.1 conditioned_504 code

theorem conditional_504_0 (code : Nat) :
    weight conditionalCredit 0 504 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 504 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_504_0 direction_504.1
    direction_504.2.2 conditioned_504 code
#print axioms selected_504_0
#print axioms source_504_0
#print axioms target_504_0
#print axioms block_504_0
#print axioms completed_504_0
#print axioms conditional_504_0

end Snake9.Context101
