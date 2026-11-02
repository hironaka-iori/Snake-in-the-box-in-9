import Direction101Group01

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_80_34 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 34 [] ++ [80])) := by rfl

theorem source_80_34 (code : Nat) :
    edgeSource 34 80 code = 1283040+code/6 := by rfl

theorem target_80_34 (code : Nat) :
    edgeTarget 34 80 code = 948672+code%7776 := by rfl

theorem block_80_34 :
    savedBlockClass (75*80+34) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_80_34 (code : Nat) :
    weight completedCredit 34 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 34 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_34 direction_80.1
    direction_80.2.1 conditioned_80 code

theorem conditional_80_34 (code : Nat) :
    weight conditionalCredit 34 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 34 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_34 direction_80.1
    direction_80.2.2 conditioned_80 code
#print axioms selected_80_34
#print axioms source_80_34
#print axioms target_80_34
#print axioms block_80_34
#print axioms completed_80_34
#print axioms conditional_80_34

theorem selected_81_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [81])) := by rfl

theorem source_81_0 (code : Nat) :
    edgeSource 0 81 code = 178848+code/6 := by rfl

theorem target_81_0 (code : Nat) :
    edgeTarget 0 81 code = 956448+code%7776 := by rfl

theorem block_81_0 :
    savedBlockClass (75*81+0) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_81_0 (code : Nat) :
    weight completedCredit 0 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_0 direction_81.1
    direction_81.2.1 conditioned_81 code

theorem conditional_81_0 (code : Nat) :
    weight conditionalCredit 0 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_0 direction_81.1
    direction_81.2.2 conditioned_81 code
#print axioms selected_81_0
#print axioms source_81_0
#print axioms target_81_0
#print axioms block_81_0
#print axioms completed_81_0
#print axioms conditional_81_0

theorem selected_81_13 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 13 [] ++ [81])) := by rfl

theorem source_81_13 (code : Nat) :
    edgeSource 13 81 code = 1119744+code/6 := by rfl

theorem target_81_13 (code : Nat) :
    edgeTarget 13 81 code = 956448+code%7776 := by rfl

theorem block_81_13 :
    savedBlockClass (75*81+13) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_81_13 (code : Nat) :
    weight completedCredit 13 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 13 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_13 direction_81.1
    direction_81.2.1 conditioned_81 code

theorem conditional_81_13 (code : Nat) :
    weight conditionalCredit 13 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 13 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_13 direction_81.1
    direction_81.2.2 conditioned_81 code
#print axioms selected_81_13
#print axioms source_81_13
#print axioms target_81_13
#print axioms block_81_13
#print axioms completed_81_13
#print axioms conditional_81_13

theorem selected_81_15 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 15 [] ++ [81])) := by rfl

theorem source_81_15 (code : Nat) :
    edgeSource 15 81 code = 1135296+code/6 := by rfl

theorem target_81_15 (code : Nat) :
    edgeTarget 15 81 code = 956448+code%7776 := by rfl

theorem block_81_15 :
    savedBlockClass (75*81+15) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_81_15 (code : Nat) :
    weight completedCredit 15 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 15 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_15 direction_81.1
    direction_81.2.1 conditioned_81 code

theorem conditional_81_15 (code : Nat) :
    weight conditionalCredit 15 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 15 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_15 direction_81.1
    direction_81.2.2 conditioned_81 code
#print axioms selected_81_15
#print axioms source_81_15
#print axioms target_81_15
#print axioms block_81_15
#print axioms completed_81_15
#print axioms conditional_81_15

theorem selected_81_32 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 32 [] ++ [81])) := by rfl

theorem source_81_32 (code : Nat) :
    edgeSource 32 81 code = 1267488+code/6 := by rfl

theorem target_81_32 (code : Nat) :
    edgeTarget 32 81 code = 956448+code%7776 := by rfl

theorem block_81_32 :
    savedBlockClass (75*81+32) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_81_32 (code : Nat) :
    weight completedCredit 32 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 32 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_32 direction_81.1
    direction_81.2.1 conditioned_81 code

theorem conditional_81_32 (code : Nat) :
    weight conditionalCredit 32 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 32 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_32 direction_81.1
    direction_81.2.2 conditioned_81 code
#print axioms selected_81_32
#print axioms source_81_32
#print axioms target_81_32
#print axioms block_81_32
#print axioms completed_81_32
#print axioms conditional_81_32

theorem selected_81_34 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 34 [] ++ [81])) := by rfl

theorem source_81_34 (code : Nat) :
    edgeSource 34 81 code = 1283040+code/6 := by rfl

theorem target_81_34 (code : Nat) :
    edgeTarget 34 81 code = 956448+code%7776 := by rfl

theorem block_81_34 :
    savedBlockClass (75*81+34) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_81_34 (code : Nat) :
    weight completedCredit 34 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 34 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_34 direction_81.1
    direction_81.2.1 conditioned_81 code

theorem conditional_81_34 (code : Nat) :
    weight conditionalCredit 34 81 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 34 81 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_81_34 direction_81.1
    direction_81.2.2 conditioned_81 code
#print axioms selected_81_34
#print axioms source_81_34
#print axioms target_81_34
#print axioms block_81_34
#print axioms completed_81_34
#print axioms conditional_81_34

theorem selected_82_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [82])) := by rfl

theorem source_82_0 (code : Nat) :
    edgeSource 0 82 code = 178848+code/6 := by rfl

theorem target_82_0 (code : Nat) :
    edgeTarget 0 82 code = 972000+code%7776 := by rfl

theorem block_82_0 :
    savedBlockClass (75*82+0) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_82_0 (code : Nat) :
    weight completedCredit 0 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_0 direction_82.1
    direction_82.2.1 conditioned_82 code

theorem conditional_82_0 (code : Nat) :
    weight conditionalCredit 0 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_0 direction_82.1
    direction_82.2.2 conditioned_82 code
#print axioms selected_82_0
#print axioms source_82_0
#print axioms target_82_0
#print axioms block_82_0
#print axioms completed_82_0
#print axioms conditional_82_0

theorem selected_82_13 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 13 [] ++ [82])) := by rfl

theorem source_82_13 (code : Nat) :
    edgeSource 13 82 code = 1119744+code/6 := by rfl

theorem target_82_13 (code : Nat) :
    edgeTarget 13 82 code = 972000+code%7776 := by rfl

theorem block_82_13 :
    savedBlockClass (75*82+13) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_82_13 (code : Nat) :
    weight completedCredit 13 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 13 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_13 direction_82.1
    direction_82.2.1 conditioned_82 code

theorem conditional_82_13 (code : Nat) :
    weight conditionalCredit 13 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 13 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_13 direction_82.1
    direction_82.2.2 conditioned_82 code
#print axioms selected_82_13
#print axioms source_82_13
#print axioms target_82_13
#print axioms block_82_13
#print axioms completed_82_13
#print axioms conditional_82_13

theorem selected_82_15 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 15 [] ++ [82])) := by rfl

theorem source_82_15 (code : Nat) :
    edgeSource 15 82 code = 1135296+code/6 := by rfl

theorem target_82_15 (code : Nat) :
    edgeTarget 15 82 code = 972000+code%7776 := by rfl

theorem block_82_15 :
    savedBlockClass (75*82+15) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_82_15 (code : Nat) :
    weight completedCredit 15 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 15 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_15 direction_82.1
    direction_82.2.1 conditioned_82 code

theorem conditional_82_15 (code : Nat) :
    weight conditionalCredit 15 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 15 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_15 direction_82.1
    direction_82.2.2 conditioned_82 code
#print axioms selected_82_15
#print axioms source_82_15
#print axioms target_82_15
#print axioms block_82_15
#print axioms completed_82_15
#print axioms conditional_82_15

theorem selected_82_32 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 32 [] ++ [82])) := by rfl

theorem source_82_32 (code : Nat) :
    edgeSource 32 82 code = 1267488+code/6 := by rfl

theorem target_82_32 (code : Nat) :
    edgeTarget 32 82 code = 972000+code%7776 := by rfl

theorem block_82_32 :
    savedBlockClass (75*82+32) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_82_32 (code : Nat) :
    weight completedCredit 32 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 32 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_32 direction_82.1
    direction_82.2.1 conditioned_82 code

theorem conditional_82_32 (code : Nat) :
    weight conditionalCredit 32 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 32 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_32 direction_82.1
    direction_82.2.2 conditioned_82 code
#print axioms selected_82_32
#print axioms source_82_32
#print axioms target_82_32
#print axioms block_82_32
#print axioms completed_82_32
#print axioms conditional_82_32

theorem selected_82_34 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 34 [] ++ [82])) := by rfl

theorem source_82_34 (code : Nat) :
    edgeSource 34 82 code = 1283040+code/6 := by rfl

theorem target_82_34 (code : Nat) :
    edgeTarget 34 82 code = 972000+code%7776 := by rfl

theorem block_82_34 :
    savedBlockClass (75*82+34) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_82_34 (code : Nat) :
    weight completedCredit 34 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 34 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_34 direction_82.1
    direction_82.2.1 conditioned_82 code

theorem conditional_82_34 (code : Nat) :
    weight conditionalCredit 34 82 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 34 82 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_82_34 direction_82.1
    direction_82.2.2 conditioned_82 code
#print axioms selected_82_34
#print axioms source_82_34
#print axioms target_82_34
#print axioms block_82_34
#print axioms completed_82_34
#print axioms conditional_82_34

theorem selected_83_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [83])) := by rfl

theorem source_83_0 (code : Nat) :
    edgeSource 0 83 code = 186624+code/6 := by rfl

theorem target_83_0 (code : Nat) :
    edgeTarget 0 83 code = 995328+code%7776 := by rfl

theorem block_83_0 :
    savedBlockClass (75*83+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_83_0 (code : Nat) :
    weight completedCredit 0 83 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 83 [] 0 0
    (fun code => 0) selected_83_0 direction_83.1
    direction_83.2.1 conditioned_83 code

theorem conditional_83_0 (code : Nat) :
    weight conditionalCredit 0 83 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 83 [] 0 16
    (fun code => 0) selected_83_0 direction_83.1
    direction_83.2.2 conditioned_83 code
#print axioms selected_83_0
#print axioms source_83_0
#print axioms target_83_0
#print axioms block_83_0
#print axioms completed_83_0
#print axioms conditional_83_0

theorem selected_84_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [84])) := by rfl

theorem source_84_0 (code : Nat) :
    edgeSource 0 84 code = 186624+code/6 := by rfl

theorem target_84_0 (code : Nat) :
    edgeTarget 0 84 code = 979776+code%7776 := by rfl

theorem block_84_0 :
    savedBlockClass (75*84+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_84_0 (code : Nat) :
    weight completedCredit 0 84 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 84 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_84_0 direction_84.1
    direction_84.2.1 conditioned_84 code

theorem conditional_84_0 (code : Nat) :
    weight conditionalCredit 0 84 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 84 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_84_0 direction_84.1
    direction_84.2.2 conditioned_84 code
#print axioms selected_84_0
#print axioms source_84_0
#print axioms target_84_0
#print axioms block_84_0
#print axioms completed_84_0
#print axioms conditional_84_0

theorem selected_85_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [85])) := by rfl

theorem source_85_0 (code : Nat) :
    edgeSource 0 85 code = 186624+code/6 := by rfl

theorem target_85_0 (code : Nat) :
    edgeTarget 0 85 code = 987552+code%7776 := by rfl

theorem block_85_0 :
    savedBlockClass (75*85+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_85_0 (code : Nat) :
    weight completedCredit 0 85 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 85 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_85_0 direction_85.1
    direction_85.2.1 conditioned_85 code

theorem conditional_85_0 (code : Nat) :
    weight conditionalCredit 0 85 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 85 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_85_0 direction_85.1
    direction_85.2.2 conditioned_85 code
#print axioms selected_85_0
#print axioms source_85_0
#print axioms target_85_0
#print axioms block_85_0
#print axioms completed_85_0
#print axioms conditional_85_0

theorem selected_86_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [86])) := by rfl

theorem source_86_0 (code : Nat) :
    edgeSource 0 86 code = 186624+code/6 := by rfl

theorem target_86_0 (code : Nat) :
    edgeTarget 0 86 code = 1003104+code%7776 := by rfl

theorem block_86_0 :
    savedBlockClass (75*86+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_86_0 (code : Nat) :
    weight completedCredit 0 86 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 86 [] 0 16
    (fun code => 0) selected_86_0 direction_86.1
    direction_86.2.1 conditioned_86 code

theorem conditional_86_0 (code : Nat) :
    weight conditionalCredit 0 86 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 86 [] 0 16
    (fun code => 0) selected_86_0 direction_86.1
    direction_86.2.2 conditioned_86 code
#print axioms selected_86_0
#print axioms source_86_0
#print axioms target_86_0
#print axioms block_86_0
#print axioms completed_86_0
#print axioms conditional_86_0

theorem selected_87_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [87])) := by rfl

theorem source_87_0 (code : Nat) :
    edgeSource 0 87 code = 186624+code/6 := by rfl

theorem target_87_0 (code : Nat) :
    edgeTarget 0 87 code = 1010880+code%7776 := by rfl

theorem block_87_0 :
    savedBlockClass (75*87+0) = some 35 ∧
    recordedClassRoot 35 = 2722 := by decide +kernel

theorem completed_87_0 (code : Nat) :
    weight completedCredit 0 87 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 87 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_87_0 direction_87.1
    direction_87.2.1 conditioned_87 code

theorem conditional_87_0 (code : Nat) :
    weight conditionalCredit 0 87 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 87 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_87_0 direction_87.1
    direction_87.2.2 conditioned_87 code
#print axioms selected_87_0
#print axioms source_87_0
#print axioms target_87_0
#print axioms block_87_0
#print axioms completed_87_0
#print axioms conditional_87_0

theorem selected_88_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [88])) := by rfl

theorem source_88_0 (code : Nat) :
    edgeSource 0 88 code = 186624+code/6 := by rfl

theorem target_88_0 (code : Nat) :
    edgeTarget 0 88 code = 1018656+code%7776 := by rfl

theorem block_88_0 :
    savedBlockClass (75*88+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_88_0 (code : Nat) :
    weight completedCredit 0 88 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 88 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_88_0 direction_88.1
    direction_88.2.1 conditioned_88 code

theorem conditional_88_0 (code : Nat) :
    weight conditionalCredit 0 88 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 88 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_88_0 direction_88.1
    direction_88.2.2 conditioned_88 code
#print axioms selected_88_0
#print axioms source_88_0
#print axioms target_88_0
#print axioms block_88_0
#print axioms completed_88_0
#print axioms conditional_88_0

theorem selected_89_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [89])) := by rfl

theorem source_89_0 (code : Nat) :
    edgeSource 0 89 code = 194400+code/6 := by rfl

theorem target_89_0 (code : Nat) :
    edgeTarget 0 89 code = 318816+code%7776 := by rfl

theorem block_89_0 :
    savedBlockClass (75*89+0) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_89_0 (code : Nat) :
    weight completedCredit 0 89 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 89 [] 12 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_89_0 direction_89.1
    direction_89.2.1 conditioned_89 code

theorem conditional_89_0 (code : Nat) :
    weight conditionalCredit 0 89 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 89 [] 12 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_89_0 direction_89.1
    direction_89.2.2 conditioned_89 code
#print axioms selected_89_0
#print axioms source_89_0
#print axioms target_89_0
#print axioms block_89_0
#print axioms completed_89_0
#print axioms conditional_89_0

theorem selected_89_19 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 19 [] ++ [89])) := by rfl

theorem source_89_19 (code : Nat) :
    edgeSource 19 89 code = 1166400+code/6 := by rfl

theorem target_89_19 (code : Nat) :
    edgeTarget 19 89 code = 318816+code%7776 := by rfl

theorem block_89_19 :
    savedBlockClass (75*89+19) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_89_19 (code : Nat) :
    weight completedCredit 19 89 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 19 89 [] 12 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_89_19 direction_89.1
    direction_89.2.1 conditioned_89 code

theorem conditional_89_19 (code : Nat) :
    weight conditionalCredit 19 89 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 19 89 [] 12 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_89_19 direction_89.1
    direction_89.2.2 conditioned_89 code
#print axioms selected_89_19
#print axioms source_89_19
#print axioms target_89_19
#print axioms block_89_19
#print axioms completed_89_19
#print axioms conditional_89_19

theorem selected_89_67 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 67 [] ++ [89])) := by rfl

theorem source_89_67 (code : Nat) :
    edgeSource 67 89 code = 1539648+code/6 := by rfl

theorem target_89_67 (code : Nat) :
    edgeTarget 67 89 code = 318816+code%7776 := by rfl

theorem block_89_67 :
    savedBlockClass (75*89+67) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_89_67 (code : Nat) :
    weight completedCredit 67 89 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 67 89 [] 12 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_89_67 direction_89.1
    direction_89.2.1 conditioned_89 code

theorem conditional_89_67 (code : Nat) :
    weight conditionalCredit 67 89 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 67 89 [] 12 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_89_67 direction_89.1
    direction_89.2.2 conditioned_89 code
#print axioms selected_89_67
#print axioms source_89_67
#print axioms target_89_67
#print axioms block_89_67
#print axioms completed_89_67
#print axioms conditional_89_67

theorem selected_90_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [90])) := by rfl

theorem source_90_0 (code : Nat) :
    edgeSource 0 90 code = 194400+code/6 := by rfl

theorem target_90_0 (code : Nat) :
    edgeTarget 0 90 code = 1073088+code%7776 := by rfl

theorem block_90_0 :
    savedBlockClass (75*90+0) = some 9 ∧
    recordedClassRoot 9 = 1489 := by decide +kernel

theorem completed_90_0 (code : Nat) :
    weight completedCredit 0 90 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 90 [] 10 12
    (fun code => 0) selected_90_0 direction_90.1
    direction_90.2.1 conditioned_90 code

theorem conditional_90_0 (code : Nat) :
    weight conditionalCredit 0 90 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 90 [] 10 12
    (fun code => 0) selected_90_0 direction_90.1
    direction_90.2.2 conditioned_90 code
#print axioms selected_90_0
#print axioms source_90_0
#print axioms target_90_0
#print axioms block_90_0
#print axioms completed_90_0
#print axioms conditional_90_0

theorem selected_90_19 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 19 [] ++ [90])) := by rfl

theorem source_90_19 (code : Nat) :
    edgeSource 19 90 code = 1166400+code/6 := by rfl

theorem target_90_19 (code : Nat) :
    edgeTarget 19 90 code = 1454112+code%7776 := by rfl

theorem block_90_19 :
    savedBlockClass (75*90+19) = some 9 ∧
    recordedClassRoot 9 = 1489 := by decide +kernel

theorem completed_90_19 (code : Nat) :
    weight completedCredit 19 90 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 19 90 [] 10 12
    (fun code => 0) selected_90_19 direction_90.1
    direction_90.2.1 conditioned_90 code

theorem conditional_90_19 (code : Nat) :
    weight conditionalCredit 19 90 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 19 90 [] 10 12
    (fun code => 0) selected_90_19 direction_90.1
    direction_90.2.2 conditioned_90 code
#print axioms selected_90_19
#print axioms source_90_19
#print axioms target_90_19
#print axioms block_90_19
#print axioms completed_90_19
#print axioms conditional_90_19

theorem selected_90_67 :
    [rule044] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 67 [] ++ [90])) := by rfl

theorem source_90_67 (code : Nat) :
    edgeSource 67 90 code = 1539648+code/6 := by rfl

theorem target_90_67 (code : Nat) :
    edgeTarget 67 90 code = 1454112+code%7776 := by rfl

theorem block_90_67 :
    savedBlockClass (75*90+67) = some 9 ∧
    recordedClassRoot 9 = 1489 := by decide +kernel

theorem completed_90_67 (code : Nat) :
    weight completedCredit 67 90 code =
      120*(code%6+1)+max (max 10 (emittedCredit [rule044] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 67 90 [rule044] 10 12
    (fun code => 0) selected_90_67 direction_90.1
    direction_90.2.1 conditioned_90 code

theorem conditional_90_67 (code : Nat) :
    weight conditionalCredit 67 90 code =
      120*(code%6+1)+max (max 10 (emittedCredit [rule044] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 67 90 [rule044] 10 12
    (fun code => 0) selected_90_67 direction_90.1
    direction_90.2.2 conditioned_90 code
#print axioms selected_90_67
#print axioms source_90_67
#print axioms target_90_67
#print axioms block_90_67
#print axioms completed_90_67
#print axioms conditional_90_67

theorem selected_91_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [91])) := by rfl

theorem source_91_0 (code : Nat) :
    edgeSource 0 91 code = 194400+code/6 := by rfl

theorem target_91_0 (code : Nat) :
    edgeTarget 0 91 code = 334368+code%7776 := by rfl

theorem block_91_0 :
    savedBlockClass (75*91+0) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_91_0 (code : Nat) :
    weight completedCredit 0 91 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 91 [] 17 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_91_0 direction_91.1
    direction_91.2.1 conditioned_91 code

theorem conditional_91_0 (code : Nat) :
    weight conditionalCredit 0 91 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 91 [] 17 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_91_0 direction_91.1
    direction_91.2.2 conditioned_91 code
#print axioms selected_91_0
#print axioms source_91_0
#print axioms target_91_0
#print axioms block_91_0
#print axioms completed_91_0
#print axioms conditional_91_0

theorem selected_91_19 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 19 [] ++ [91])) := by rfl

theorem source_91_19 (code : Nat) :
    edgeSource 19 91 code = 1166400+code/6 := by rfl

theorem target_91_19 (code : Nat) :
    edgeTarget 19 91 code = 334368+code%7776 := by rfl

theorem block_91_19 :
    savedBlockClass (75*91+19) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_91_19 (code : Nat) :
    weight completedCredit 19 91 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 19 91 [] 17 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_91_19 direction_91.1
    direction_91.2.1 conditioned_91 code

theorem conditional_91_19 (code : Nat) :
    weight conditionalCredit 19 91 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 19 91 [] 17 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_91_19 direction_91.1
    direction_91.2.2 conditioned_91 code
#print axioms selected_91_19
#print axioms source_91_19
#print axioms target_91_19
#print axioms block_91_19
#print axioms completed_91_19
#print axioms conditional_91_19

theorem selected_91_67 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 67 [] ++ [91])) := by rfl

theorem source_91_67 (code : Nat) :
    edgeSource 67 91 code = 1539648+code/6 := by rfl

theorem target_91_67 (code : Nat) :
    edgeTarget 67 91 code = 334368+code%7776 := by rfl

theorem block_91_67 :
    savedBlockClass (75*91+67) = some 10 ∧
    recordedClassRoot 10 = 1609 := by decide +kernel

theorem completed_91_67 (code : Nat) :
    weight completedCredit 67 91 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 67 91 [] 17 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_91_67 direction_91.1
    direction_91.2.1 conditioned_91 code

theorem conditional_91_67 (code : Nat) :
    weight conditionalCredit 67 91 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 67 91 [] 17 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_91_67 direction_91.1
    direction_91.2.2 conditioned_91 code
#print axioms selected_91_67
#print axioms source_91_67
#print axioms target_91_67
#print axioms block_91_67
#print axioms completed_91_67
#print axioms conditional_91_67

theorem selected_92_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [92])) := by rfl

theorem source_92_0 (code : Nat) :
    edgeSource 0 92 code = 202176+code/6 := by rfl

theorem target_92_0 (code : Nat) :
    edgeTarget 0 92 code = 272160+code%7776 := by rfl

theorem block_92_0 :
    savedBlockClass (75*92+0) = some 43 ∧
    recordedClassRoot 43 = 3318 := by decide +kernel

theorem completed_92_0 (code : Nat) :
    weight completedCredit 0 92 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 92 [] 5 16
    (fun code => 0) selected_92_0 direction_92.1
    direction_92.2.1 conditioned_92 code

theorem conditional_92_0 (code : Nat) :
    weight conditionalCredit 0 92 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 92 [] 5 16
    (fun code => 0) selected_92_0 direction_92.1
    direction_92.2.2 conditioned_92 code
#print axioms selected_92_0
#print axioms source_92_0
#print axioms target_92_0
#print axioms block_92_0
#print axioms completed_92_0
#print axioms conditional_92_0

theorem selected_93_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [93])) := by rfl

theorem source_93_0 (code : Nat) :
    edgeSource 0 93 code = 202176+code/6 := by rfl

theorem target_93_0 (code : Nat) :
    edgeTarget 0 93 code = 256608+code%7776 := by rfl

theorem block_93_0 :
    savedBlockClass (75*93+0) = some 7 ∧
    recordedClassRoot 7 = 1278 := by decide +kernel

theorem completed_93_0 (code : Nat) :
    weight completedCredit 0 93 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 93 [] 13 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_93_0 direction_93.1
    direction_93.2.1 conditioned_93 code

theorem conditional_93_0 (code : Nat) :
    weight conditionalCredit 0 93 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 93 [] 13 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_93_0 direction_93.1
    direction_93.2.2 conditioned_93 code
#print axioms selected_93_0
#print axioms source_93_0
#print axioms target_93_0
#print axioms block_93_0
#print axioms completed_93_0
#print axioms conditional_93_0

theorem selected_94_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [94])) := by rfl

theorem source_94_0 (code : Nat) :
    edgeSource 0 94 code = 202176+code/6 := by rfl

theorem target_94_0 (code : Nat) :
    edgeTarget 0 94 code = 279936+code%7776 := by rfl

theorem block_94_0 :
    savedBlockClass (75*94+0) = some 8 ∧
    recordedClassRoot 8 = 1378 := by decide +kernel

theorem completed_94_0 (code : Nat) :
    weight completedCredit 0 94 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 94 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_94_0 direction_94.1
    direction_94.2.1 conditioned_94 code

theorem conditional_94_0 (code : Nat) :
    weight conditionalCredit 0 94 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 94 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_94_0 direction_94.1
    direction_94.2.2 conditioned_94 code
#print axioms selected_94_0
#print axioms source_94_0
#print axioms target_94_0
#print axioms block_94_0
#print axioms completed_94_0
#print axioms conditional_94_0

theorem selected_95_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [95])) := by rfl

theorem source_95_0 (code : Nat) :
    edgeSource 0 95 code = 209952+code/6 := by rfl

theorem target_95_0 (code : Nat) :
    edgeTarget 0 95 code = 303264+code%7776 := by rfl

theorem block_95_0 :
    savedBlockClass (75*95+0) = some 5 ∧
    recordedClassRoot 5 = 1008 := by decide +kernel

theorem completed_95_0 (code : Nat) :
    weight completedCredit 0 95 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 95 [] 11 0
    (fun code => 0) selected_95_0 direction_95.1
    direction_95.2.1 conditioned_95 code

theorem conditional_95_0 (code : Nat) :
    weight conditionalCredit 0 95 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 95 [] 11 16
    (fun code => 0) selected_95_0 direction_95.1
    direction_95.2.2 conditioned_95 code
#print axioms selected_95_0
#print axioms source_95_0
#print axioms target_95_0
#print axioms block_95_0
#print axioms completed_95_0
#print axioms conditional_95_0

theorem selected_96_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [96])) := by rfl

theorem source_96_0 (code : Nat) :
    edgeSource 0 96 code = 209952+code/6 := by rfl

theorem target_96_0 (code : Nat) :
    edgeTarget 0 96 code = 287712+code%7776 := by rfl

theorem block_96_0 :
    savedBlockClass (75*96+0) = some 3 ∧
    recordedClassRoot 3 = 669 := by decide +kernel

theorem completed_96_0 (code : Nat) :
    weight completedCredit 0 96 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 96 [] 22 16
    (fun code => 0) selected_96_0 direction_96.1
    direction_96.2.1 conditioned_96 code

theorem conditional_96_0 (code : Nat) :
    weight conditionalCredit 0 96 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 96 [] 22 16
    (fun code => 0) selected_96_0 direction_96.1
    direction_96.2.2 conditioned_96 code
#print axioms selected_96_0
#print axioms source_96_0
#print axioms target_96_0
#print axioms block_96_0
#print axioms completed_96_0
#print axioms conditional_96_0

theorem selected_97_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [97])) := by rfl

theorem source_97_0 (code : Nat) :
    edgeSource 0 97 code = 209952+code/6 := by rfl

theorem target_97_0 (code : Nat) :
    edgeTarget 0 97 code = 311040+code%7776 := by rfl

theorem block_97_0 :
    savedBlockClass (75*97+0) = some 4 ∧
    recordedClassRoot 4 = 846 := by decide +kernel

theorem completed_97_0 (code : Nat) :
    weight completedCredit 0 97 code =
      120*(code%6+1)+max (max 28 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 97 [] 28 16
    (fun code => 0) selected_97_0 direction_97.1
    direction_97.2.1 conditioned_97 code

theorem conditional_97_0 (code : Nat) :
    weight conditionalCredit 0 97 code =
      120*(code%6+1)+max (max 28 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 97 [] 28 16
    (fun code => 0) selected_97_0 direction_97.1
    direction_97.2.2 conditioned_97 code
#print axioms selected_97_0
#print axioms source_97_0
#print axioms target_97_0
#print axioms block_97_0
#print axioms completed_97_0
#print axioms conditional_97_0

theorem selected_98_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [98])) := by rfl

theorem source_98_0 (code : Nat) :
    edgeSource 0 98 code = 217728+code/6 := by rfl

theorem target_98_0 (code : Nat) :
    edgeTarget 0 98 code = 365472+code%7776 := by rfl

theorem block_98_0 :
    savedBlockClass (75*98+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_98_0 (code : Nat) :
    weight completedCredit 0 98 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 98 [] 5 16
    (fun code => 0) selected_98_0 direction_98.1
    direction_98.2.1 conditioned_98 code

theorem conditional_98_0 (code : Nat) :
    weight conditionalCredit 0 98 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 98 [] 5 16
    (fun code => 0) selected_98_0 direction_98.1
    direction_98.2.2 conditioned_98 code
#print axioms selected_98_0
#print axioms source_98_0
#print axioms target_98_0
#print axioms block_98_0
#print axioms completed_98_0
#print axioms conditional_98_0

theorem selected_98_20 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 20 [] ++ [98])) := by rfl

theorem source_98_20 (code : Nat) :
    edgeSource 20 98 code = 1174176+code/6 := by rfl

theorem target_98_20 (code : Nat) :
    edgeTarget 20 98 code = 365472+code%7776 := by rfl

theorem block_98_20 :
    savedBlockClass (75*98+20) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_98_20 (code : Nat) :
    weight completedCredit 20 98 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 20 98 [] 5 16
    (fun code => 0) selected_98_20 direction_98.1
    direction_98.2.1 conditioned_98 code

theorem conditional_98_20 (code : Nat) :
    weight conditionalCredit 20 98 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 20 98 [] 5 16
    (fun code => 0) selected_98_20 direction_98.1
    direction_98.2.2 conditioned_98 code
#print axioms selected_98_20
#print axioms source_98_20
#print axioms target_98_20
#print axioms block_98_20
#print axioms completed_98_20
#print axioms conditional_98_20

theorem selected_98_37 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 37 [] ++ [98])) := by rfl

theorem source_98_37 (code : Nat) :
    edgeSource 37 98 code = 1306368+code/6 := by rfl

theorem target_98_37 (code : Nat) :
    edgeTarget 37 98 code = 365472+code%7776 := by rfl

theorem block_98_37 :
    savedBlockClass (75*98+37) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_98_37 (code : Nat) :
    weight completedCredit 37 98 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 37 98 [] 5 16
    (fun code => 0) selected_98_37 direction_98.1
    direction_98.2.1 conditioned_98 code

theorem conditional_98_37 (code : Nat) :
    weight conditionalCredit 37 98 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 37 98 [] 5 16
    (fun code => 0) selected_98_37 direction_98.1
    direction_98.2.2 conditioned_98 code
#print axioms selected_98_37
#print axioms source_98_37
#print axioms target_98_37
#print axioms block_98_37
#print axioms completed_98_37
#print axioms conditional_98_37

theorem selected_99_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [99])) := by rfl

theorem source_99_0 (code : Nat) :
    edgeSource 0 99 code = 217728+code/6 := by rfl

theorem target_99_0 (code : Nat) :
    edgeTarget 0 99 code = 1080864+code%7776 := by rfl

theorem block_99_0 :
    savedBlockClass (75*99+0) = some 12 ∧
    recordedClassRoot 12 = 1807 := by decide +kernel

theorem completed_99_0 (code : Nat) :
    weight completedCredit 0 99 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 99 [] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_99_0 direction_99.1
    direction_99.2.1 conditioned_99 code

theorem conditional_99_0 (code : Nat) :
    weight conditionalCredit 0 99 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 99 [] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_99_0 direction_99.1
    direction_99.2.2 conditioned_99 code
#print axioms selected_99_0
#print axioms source_99_0
#print axioms target_99_0
#print axioms block_99_0
#print axioms completed_99_0
#print axioms conditional_99_0

theorem selected_99_20 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 20 [] ++ [99])) := by rfl

theorem source_99_20 (code : Nat) :
    edgeSource 20 99 code = 1174176+code/6 := by rfl

theorem target_99_20 (code : Nat) :
    edgeTarget 20 99 code = 1461888+code%7776 := by rfl

theorem block_99_20 :
    savedBlockClass (75*99+20) = some 12 ∧
    recordedClassRoot 12 = 1807 := by decide +kernel

theorem completed_99_20 (code : Nat) :
    weight completedCredit 20 99 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 20 99 [] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_99_20 direction_99.1
    direction_99.2.1 conditioned_99 code

theorem conditional_99_20 (code : Nat) :
    weight conditionalCredit 20 99 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 20 99 [] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_99_20 direction_99.1
    direction_99.2.2 conditioned_99 code
#print axioms selected_99_20
#print axioms source_99_20
#print axioms target_99_20
#print axioms block_99_20
#print axioms completed_99_20
#print axioms conditional_99_20

theorem selected_99_37 :
    [rule000] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 37 [] ++ [99])) := by rfl

theorem source_99_37 (code : Nat) :
    edgeSource 37 99 code = 1306368+code/6 := by rfl

theorem target_99_37 (code : Nat) :
    edgeTarget 37 99 code = 1080864+code%7776 := by rfl

theorem block_99_37 :
    savedBlockClass (75*99+37) = some 12 ∧
    recordedClassRoot 12 = 1807 := by decide +kernel

theorem completed_99_37 (code : Nat) :
    weight completedCredit 37 99 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule000] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 37 99 [rule000] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_99_37 direction_99.1
    direction_99.2.1 conditioned_99 code

theorem conditional_99_37 (code : Nat) :
    weight conditionalCredit 37 99 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule000] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 37 99 [rule000] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_99_37 direction_99.1
    direction_99.2.2 conditioned_99 code
#print axioms selected_99_37
#print axioms source_99_37
#print axioms target_99_37
#print axioms block_99_37
#print axioms completed_99_37
#print axioms conditional_99_37

theorem selected_100_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [100])) := by rfl

theorem source_100_0 (code : Nat) :
    edgeSource 0 100 code = 217728+code/6 := by rfl

theorem target_100_0 (code : Nat) :
    edgeTarget 0 100 code = 349920+code%7776 := by rfl

theorem block_100_0 :
    savedBlockClass (75*100+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_100_0 (code : Nat) :
    weight completedCredit 0 100 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 100 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_100_0 direction_100.1
    direction_100.2.1 conditioned_100 code

theorem conditional_100_0 (code : Nat) :
    weight conditionalCredit 0 100 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 100 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_100_0 direction_100.1
    direction_100.2.2 conditioned_100 code
#print axioms selected_100_0
#print axioms source_100_0
#print axioms target_100_0
#print axioms block_100_0
#print axioms completed_100_0
#print axioms conditional_100_0

theorem selected_100_20 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 20 [] ++ [100])) := by rfl

theorem source_100_20 (code : Nat) :
    edgeSource 20 100 code = 1174176+code/6 := by rfl

theorem target_100_20 (code : Nat) :
    edgeTarget 20 100 code = 349920+code%7776 := by rfl

theorem block_100_20 :
    savedBlockClass (75*100+20) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_100_20 (code : Nat) :
    weight completedCredit 20 100 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 20 100 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_100_20 direction_100.1
    direction_100.2.1 conditioned_100 code

theorem conditional_100_20 (code : Nat) :
    weight conditionalCredit 20 100 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 20 100 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_100_20 direction_100.1
    direction_100.2.2 conditioned_100 code
#print axioms selected_100_20
#print axioms source_100_20
#print axioms target_100_20
#print axioms block_100_20
#print axioms completed_100_20
#print axioms conditional_100_20

theorem selected_100_37 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 37 [] ++ [100])) := by rfl

theorem source_100_37 (code : Nat) :
    edgeSource 37 100 code = 1306368+code/6 := by rfl

theorem target_100_37 (code : Nat) :
    edgeTarget 37 100 code = 349920+code%7776 := by rfl

theorem block_100_37 :
    savedBlockClass (75*100+37) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_100_37 (code : Nat) :
    weight completedCredit 37 100 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 37 100 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_100_37 direction_100.1
    direction_100.2.1 conditioned_100 code

theorem conditional_100_37 (code : Nat) :
    weight conditionalCredit 37 100 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 37 100 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_100_37 direction_100.1
    direction_100.2.2 conditioned_100 code
#print axioms selected_100_37
#print axioms source_100_37
#print axioms target_100_37
#print axioms block_100_37
#print axioms completed_100_37
#print axioms conditional_100_37

theorem selected_101_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [101])) := by rfl

theorem source_101_0 (code : Nat) :
    edgeSource 0 101 code = 217728+code/6 := by rfl

theorem target_101_0 (code : Nat) :
    edgeTarget 0 101 code = 357696+code%7776 := by rfl

theorem block_101_0 :
    savedBlockClass (75*101+0) = some 11 ∧
    recordedClassRoot 11 = 1698 := by decide +kernel

theorem completed_101_0 (code : Nat) :
    weight completedCredit 0 101 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 101 [] 5 0
    (fun code => 0) selected_101_0 direction_101.1
    direction_101.2.1 conditioned_101 code

theorem conditional_101_0 (code : Nat) :
    weight conditionalCredit 0 101 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 101 [] 5 16
    (fun code => 0) selected_101_0 direction_101.1
    direction_101.2.2 conditioned_101 code
#print axioms selected_101_0
#print axioms source_101_0
#print axioms target_101_0
#print axioms block_101_0
#print axioms completed_101_0
#print axioms conditional_101_0

theorem selected_101_20 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 20 [] ++ [101])) := by rfl

theorem source_101_20 (code : Nat) :
    edgeSource 20 101 code = 1174176+code/6 := by rfl

theorem target_101_20 (code : Nat) :
    edgeTarget 20 101 code = 357696+code%7776 := by rfl

theorem block_101_20 :
    savedBlockClass (75*101+20) = some 11 ∧
    recordedClassRoot 11 = 1698 := by decide +kernel

theorem completed_101_20 (code : Nat) :
    weight completedCredit 20 101 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 20 101 [] 5 0
    (fun code => 0) selected_101_20 direction_101.1
    direction_101.2.1 conditioned_101 code

theorem conditional_101_20 (code : Nat) :
    weight conditionalCredit 20 101 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 20 101 [] 5 16
    (fun code => 0) selected_101_20 direction_101.1
    direction_101.2.2 conditioned_101 code
#print axioms selected_101_20
#print axioms source_101_20
#print axioms target_101_20
#print axioms block_101_20
#print axioms completed_101_20
#print axioms conditional_101_20

theorem selected_101_37 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 37 [] ++ [101])) := by rfl

theorem source_101_37 (code : Nat) :
    edgeSource 37 101 code = 1306368+code/6 := by rfl

theorem target_101_37 (code : Nat) :
    edgeTarget 37 101 code = 357696+code%7776 := by rfl

theorem block_101_37 :
    savedBlockClass (75*101+37) = some 11 ∧
    recordedClassRoot 11 = 1698 := by decide +kernel

theorem completed_101_37 (code : Nat) :
    weight completedCredit 37 101 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 37 101 [] 5 0
    (fun code => 0) selected_101_37 direction_101.1
    direction_101.2.1 conditioned_101 code

theorem conditional_101_37 (code : Nat) :
    weight conditionalCredit 37 101 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 37 101 [] 5 16
    (fun code => 0) selected_101_37 direction_101.1
    direction_101.2.2 conditioned_101 code
#print axioms selected_101_37
#print axioms source_101_37
#print axioms target_101_37
#print axioms block_101_37
#print axioms completed_101_37
#print axioms conditional_101_37

theorem selected_102_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [102])) := by rfl

theorem source_102_0 (code : Nat) :
    edgeSource 0 102 code = 217728+code/6 := by rfl

theorem target_102_0 (code : Nat) :
    edgeTarget 0 102 code = 373248+code%7776 := by rfl

theorem block_102_0 :
    savedBlockClass (75*102+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_102_0 (code : Nat) :
    weight completedCredit 0 102 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 102 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_102_0 direction_102.1
    direction_102.2.1 conditioned_102 code

theorem conditional_102_0 (code : Nat) :
    weight conditionalCredit 0 102 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 102 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_102_0 direction_102.1
    direction_102.2.2 conditioned_102 code
#print axioms selected_102_0
#print axioms source_102_0
#print axioms target_102_0
#print axioms block_102_0
#print axioms completed_102_0
#print axioms conditional_102_0

theorem selected_102_20 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 20 [] ++ [102])) := by rfl

theorem source_102_20 (code : Nat) :
    edgeSource 20 102 code = 1174176+code/6 := by rfl

theorem target_102_20 (code : Nat) :
    edgeTarget 20 102 code = 373248+code%7776 := by rfl

theorem block_102_20 :
    savedBlockClass (75*102+20) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_102_20 (code : Nat) :
    weight completedCredit 20 102 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 20 102 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_102_20 direction_102.1
    direction_102.2.1 conditioned_102 code

theorem conditional_102_20 (code : Nat) :
    weight conditionalCredit 20 102 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 20 102 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_102_20 direction_102.1
    direction_102.2.2 conditioned_102 code
#print axioms selected_102_20
#print axioms source_102_20
#print axioms target_102_20
#print axioms block_102_20
#print axioms completed_102_20
#print axioms conditional_102_20

theorem selected_102_37 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 37 [] ++ [102])) := by rfl

theorem source_102_37 (code : Nat) :
    edgeSource 37 102 code = 1306368+code/6 := by rfl

theorem target_102_37 (code : Nat) :
    edgeTarget 37 102 code = 373248+code%7776 := by rfl

theorem block_102_37 :
    savedBlockClass (75*102+37) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_102_37 (code : Nat) :
    weight completedCredit 37 102 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 37 102 [] 5 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_102_37 direction_102.1
    direction_102.2.1 conditioned_102 code

theorem conditional_102_37 (code : Nat) :
    weight conditionalCredit 37 102 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 37 102 [] 5 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_102_37 direction_102.1
    direction_102.2.2 conditioned_102 code
#print axioms selected_102_37
#print axioms source_102_37
#print axioms target_102_37
#print axioms block_102_37
#print axioms completed_102_37
#print axioms conditional_102_37

theorem selected_103_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [103])) := by rfl

theorem source_103_0 (code : Nat) :
    edgeSource 0 103 code = 225504+code/6 := by rfl

theorem target_103_0 (code : Nat) :
    edgeTarget 0 103 code = 466560+code%7776 := by rfl

theorem block_103_0 :
    savedBlockClass (75*103+0) = some 45 ∧
    recordedClassRoot 45 = 3369 := by decide +kernel

theorem completed_103_0 (code : Nat) :
    weight completedCredit 0 103 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 103 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_103_0 direction_103.1
    direction_103.2.1 conditioned_103 code

theorem conditional_103_0 (code : Nat) :
    weight conditionalCredit 0 103 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 103 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_103_0 direction_103.1
    direction_103.2.2 conditioned_103 code
#print axioms selected_103_0
#print axioms source_103_0
#print axioms target_103_0
#print axioms block_103_0
#print axioms completed_103_0
#print axioms conditional_103_0

theorem selected_104_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [104])) := by rfl

theorem source_104_0 (code : Nat) :
    edgeSource 0 104 code = 225504+code/6 := by rfl

theorem target_104_0 (code : Nat) :
    edgeTarget 0 104 code = 474336+code%7776 := by rfl

theorem block_104_0 :
    savedBlockClass (75*104+0) = some 45 ∧
    recordedClassRoot 45 = 3369 := by decide +kernel

theorem completed_104_0 (code : Nat) :
    weight completedCredit 0 104 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 104 [] 10 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_104_0 direction_104.1
    direction_104.2.1 conditioned_104 code

theorem conditional_104_0 (code : Nat) :
    weight conditionalCredit 0 104 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 104 [] 10 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_104_0 direction_104.1
    direction_104.2.2 conditioned_104 code
#print axioms selected_104_0
#print axioms source_104_0
#print axioms target_104_0
#print axioms block_104_0
#print axioms completed_104_0
#print axioms conditional_104_0

theorem selected_105_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [105])) := by rfl

theorem source_105_0 (code : Nat) :
    edgeSource 0 105 code = 233280+code/6 := by rfl

theorem target_105_0 (code : Nat) :
    edgeTarget 0 105 code = 427680+code%7776 := by rfl

theorem block_105_0 :
    savedBlockClass (75*105+0) = some 46 ∧
    recordedClassRoot 46 = 3372 := by decide +kernel

theorem completed_105_0 (code : Nat) :
    weight completedCredit 0 105 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 105 [] 13 16
    (fun code => 0) selected_105_0 direction_105.1
    direction_105.2.1 conditioned_105 code

theorem conditional_105_0 (code : Nat) :
    weight conditionalCredit 0 105 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 105 [] 13 16
    (fun code => 0) selected_105_0 direction_105.1
    direction_105.2.2 conditioned_105 code
#print axioms selected_105_0
#print axioms source_105_0
#print axioms target_105_0
#print axioms block_105_0
#print axioms completed_105_0
#print axioms conditional_105_0

theorem selected_106_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [106])) := by rfl

theorem source_106_0 (code : Nat) :
    edgeSource 0 106 code = 233280+code/6 := by rfl

theorem target_106_0 (code : Nat) :
    edgeTarget 0 106 code = 412128+code%7776 := by rfl

theorem block_106_0 :
    savedBlockClass (75*106+0) = some 47 ∧
    recordedClassRoot 47 = 3375 := by decide +kernel

theorem completed_106_0 (code : Nat) :
    weight completedCredit 0 106 code =
      120*(code%6+1)+max (max 23 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 106 [] 23 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_106_0 direction_106.1
    direction_106.2.1 conditioned_106 code

theorem conditional_106_0 (code : Nat) :
    weight conditionalCredit 0 106 code =
      120*(code%6+1)+max (max 23 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 106 [] 23 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_106_0 direction_106.1
    direction_106.2.2 conditioned_106 code
#print axioms selected_106_0
#print axioms source_106_0
#print axioms target_106_0
#print axioms block_106_0
#print axioms completed_106_0
#print axioms conditional_106_0

theorem selected_107_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [107])) := by rfl

theorem source_107_0 (code : Nat) :
    edgeSource 0 107 code = 233280+code/6 := by rfl

theorem target_107_0 (code : Nat) :
    edgeTarget 0 107 code = 435456+code%7776 := by rfl

theorem block_107_0 :
    savedBlockClass (75*107+0) = some 48 ∧
    recordedClassRoot 48 = 3378 := by decide +kernel

theorem completed_107_0 (code : Nat) :
    weight completedCredit 0 107 code =
      120*(code%6+1)+max (max 24 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 107 [] 24 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_107_0 direction_107.1
    direction_107.2.1 conditioned_107 code

theorem conditional_107_0 (code : Nat) :
    weight conditionalCredit 0 107 code =
      120*(code%6+1)+max (max 24 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 107 [] 24 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_107_0 direction_107.1
    direction_107.2.2 conditioned_107 code
#print axioms selected_107_0
#print axioms source_107_0
#print axioms target_107_0
#print axioms block_107_0
#print axioms completed_107_0
#print axioms conditional_107_0

theorem selected_108_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [108])) := by rfl

theorem source_108_0 (code : Nat) :
    edgeSource 0 108 code = 241056+code/6 := by rfl

theorem target_108_0 (code : Nat) :
    edgeTarget 0 108 code = 451008+code%7776 := by rfl

theorem block_108_0 :
    savedBlockClass (75*108+0) = some 49 ∧
    recordedClassRoot 49 = 3380 := by decide +kernel

theorem completed_108_0 (code : Nat) :
    weight completedCredit 0 108 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 108 [] 11 16
    (fun code => 0) selected_108_0 direction_108.1
    direction_108.2.1 conditioned_108 code

theorem conditional_108_0 (code : Nat) :
    weight conditionalCredit 0 108 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 108 [] 11 16
    (fun code => 0) selected_108_0 direction_108.1
    direction_108.2.2 conditioned_108 code
#print axioms selected_108_0
#print axioms source_108_0
#print axioms target_108_0
#print axioms block_108_0
#print axioms completed_108_0
#print axioms conditional_108_0

theorem selected_109_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [109])) := by rfl

theorem source_109_0 (code : Nat) :
    edgeSource 0 109 code = 241056+code/6 := by rfl

theorem target_109_0 (code : Nat) :
    edgeTarget 0 109 code = 458784+code%7776 := by rfl

theorem block_109_0 :
    savedBlockClass (75*109+0) = some 50 ∧
    recordedClassRoot 50 = 3382 := by decide +kernel

theorem completed_109_0 (code : Nat) :
    weight completedCredit 0 109 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 109 [] 17 16
    (fun code => 0) selected_109_0 direction_109.1
    direction_109.2.1 conditioned_109 code

theorem conditional_109_0 (code : Nat) :
    weight conditionalCredit 0 109 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 109 [] 17 16
    (fun code => 0) selected_109_0 direction_109.1
    direction_109.2.2 conditioned_109 code
#print axioms selected_109_0
#print axioms source_109_0
#print axioms target_109_0
#print axioms block_109_0
#print axioms completed_109_0
#print axioms conditional_109_0

theorem selected_110_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [110])) := by rfl

theorem source_110_0 (code : Nat) :
    edgeSource 0 110 code = 248832+code/6 := by rfl

theorem target_110_0 (code : Nat) :
    edgeTarget 0 110 code = 505440+code%7776 := by rfl

theorem block_110_0 :
    savedBlockClass (75*110+0) = some 46 ∧
    recordedClassRoot 46 = 3372 := by decide +kernel

theorem completed_110_0 (code : Nat) :
    weight completedCredit 0 110 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 110 [] 9 16
    (fun code => 0) selected_110_0 direction_110.1
    direction_110.2.1 conditioned_110 code

theorem conditional_110_0 (code : Nat) :
    weight conditionalCredit 0 110 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 110 [] 9 16
    (fun code => 0) selected_110_0 direction_110.1
    direction_110.2.2 conditioned_110 code
#print axioms selected_110_0
#print axioms source_110_0
#print axioms target_110_0
#print axioms block_110_0
#print axioms completed_110_0
#print axioms conditional_110_0

theorem selected_111_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [111])) := by rfl

theorem source_111_0 (code : Nat) :
    edgeSource 0 111 code = 248832+code/6 := by rfl

theorem target_111_0 (code : Nat) :
    edgeTarget 0 111 code = 482112+code%7776 := by rfl

theorem block_111_0 :
    savedBlockClass (75*111+0) = some 48 ∧
    recordedClassRoot 48 = 3378 := by decide +kernel

theorem completed_111_0 (code : Nat) :
    weight completedCredit 0 111 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 111 [] 9 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_111_0 direction_111.1
    direction_111.2.1 conditioned_111 code

theorem conditional_111_0 (code : Nat) :
    weight conditionalCredit 0 111 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 111 [] 9 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_111_0 direction_111.1
    direction_111.2.2 conditioned_111 code
#print axioms selected_111_0
#print axioms source_111_0
#print axioms target_111_0
#print axioms block_111_0
#print axioms completed_111_0
#print axioms conditional_111_0

theorem selected_112_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [112])) := by rfl

theorem source_112_0 (code : Nat) :
    edgeSource 0 112 code = 248832+code/6 := by rfl

theorem target_112_0 (code : Nat) :
    edgeTarget 0 112 code = 489888+code%7776 := by rfl

theorem block_112_0 :
    savedBlockClass (75*112+0) = some 47 ∧
    recordedClassRoot 47 = 3375 := by decide +kernel

theorem completed_112_0 (code : Nat) :
    weight completedCredit 0 112 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 112 [] 9 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_112_0 direction_112.1
    direction_112.2.1 conditioned_112 code

theorem conditional_112_0 (code : Nat) :
    weight conditionalCredit 0 112 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 112 [] 9 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_112_0 direction_112.1
    direction_112.2.2 conditioned_112 code
#print axioms selected_112_0
#print axioms source_112_0
#print axioms target_112_0
#print axioms block_112_0
#print axioms completed_112_0
#print axioms conditional_112_0

theorem selected_113_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [113])) := by rfl

theorem source_113_0 (code : Nat) :
    edgeSource 0 113 code = 248832+code/6 := by rfl

theorem target_113_0 (code : Nat) :
    edgeTarget 0 113 code = 497664+code%7776 := by rfl

theorem block_113_0 :
    savedBlockClass (75*113+0) = some 51 ∧
    recordedClassRoot 51 = 3384 := by decide +kernel

theorem completed_113_0 (code : Nat) :
    weight completedCredit 0 113 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 113 [] 9 0
    (fun code => 0) selected_113_0 direction_113.1
    direction_113.2.1 conditioned_113 code

theorem conditional_113_0 (code : Nat) :
    weight conditionalCredit 0 113 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 113 [] 9 16
    (fun code => 0) selected_113_0 direction_113.1
    direction_113.2.2 conditioned_113 code
#print axioms selected_113_0
#print axioms source_113_0
#print axioms target_113_0
#print axioms block_113_0
#print axioms completed_113_0
#print axioms conditional_113_0

theorem selected_114_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [114])) := by rfl

theorem source_114_0 (code : Nat) :
    edgeSource 0 114 code = 248832+code/6 := by rfl

theorem target_114_0 (code : Nat) :
    edgeTarget 0 114 code = 513216+code%7776 := by rfl

theorem block_114_0 :
    savedBlockClass (75*114+0) = some 48 ∧
    recordedClassRoot 48 = 3378 := by decide +kernel

theorem completed_114_0 (code : Nat) :
    weight completedCredit 0 114 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 114 [] 9 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_114_0 direction_114.1
    direction_114.2.1 conditioned_114 code

theorem conditional_114_0 (code : Nat) :
    weight conditionalCredit 0 114 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 114 [] 9 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_114_0 direction_114.1
    direction_114.2.2 conditioned_114 code
#print axioms selected_114_0
#print axioms source_114_0
#print axioms target_114_0
#print axioms block_114_0
#print axioms completed_114_0
#print axioms conditional_114_0

theorem selected_115_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [115])) := by rfl

theorem source_115_0 (code : Nat) :
    edgeSource 0 115 code = 256608+code/6 := by rfl

theorem target_115_0 (code : Nat) :
    edgeTarget 0 115 code = 583200+code%7776 := by rfl

theorem block_115_0 :
    savedBlockClass (75*115+0) = some 52 ∧
    recordedClassRoot 52 = 3415 := by decide +kernel

theorem completed_115_0 (code : Nat) :
    weight completedCredit 0 115 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 115 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_115_0 direction_115.1
    direction_115.2.1 conditioned_115 code

theorem conditional_115_0 (code : Nat) :
    weight conditionalCredit 0 115 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 115 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_115_0 direction_115.1
    direction_115.2.2 conditioned_115 code
#print axioms selected_115_0
#print axioms source_115_0
#print axioms target_115_0
#print axioms block_115_0
#print axioms completed_115_0
#print axioms conditional_115_0

theorem selected_116_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [116])) := by rfl

theorem source_116_0 (code : Nat) :
    edgeSource 0 116 code = 256608+code/6 := by rfl

theorem target_116_0 (code : Nat) :
    edgeTarget 0 116 code = 590976+code%7776 := by rfl

theorem block_116_0 :
    savedBlockClass (75*116+0) = some 53 ∧
    recordedClassRoot 53 = 3444 := by decide +kernel

theorem completed_116_0 (code : Nat) :
    weight completedCredit 0 116 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 116 [] 0 12
    (fun code => 0) selected_116_0 direction_116.1
    direction_116.2.1 conditioned_116 code

theorem conditional_116_0 (code : Nat) :
    weight conditionalCredit 0 116 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 116 [] 0 12
    (fun code => 0) selected_116_0 direction_116.1
    direction_116.2.2 conditioned_116 code
#print axioms selected_116_0
#print axioms source_116_0
#print axioms target_116_0
#print axioms block_116_0
#print axioms completed_116_0
#print axioms conditional_116_0

theorem selected_117_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [117])) := by rfl

theorem source_117_0 (code : Nat) :
    edgeSource 0 117 code = 256608+code/6 := by rfl

theorem target_117_0 (code : Nat) :
    edgeTarget 0 117 code = 598752+code%7776 := by rfl

theorem block_117_0 :
    savedBlockClass (75*117+0) = some 52 ∧
    recordedClassRoot 52 = 3415 := by decide +kernel

theorem completed_117_0 (code : Nat) :
    weight completedCredit 0 117 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 117 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_117_0 direction_117.1
    direction_117.2.1 conditioned_117 code

theorem conditional_117_0 (code : Nat) :
    weight conditionalCredit 0 117 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 117 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_117_0 direction_117.1
    direction_117.2.2 conditioned_117 code
#print axioms selected_117_0
#print axioms source_117_0
#print axioms target_117_0
#print axioms block_117_0
#print axioms completed_117_0
#print axioms conditional_117_0

theorem selected_118_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [118])) := by rfl

theorem source_118_0 (code : Nat) :
    edgeSource 0 118 code = 264384+code/6 := by rfl

theorem target_118_0 (code : Nat) :
    edgeTarget 0 118 code = 528768+code%7776 := by rfl

theorem block_118_0 :
    savedBlockClass (75*118+0) = some 54 ∧
    recordedClassRoot 54 = 3447 := by decide +kernel

theorem completed_118_0 (code : Nat) :
    weight completedCredit 0 118 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 118 [] 11 16
    (fun code => 0) selected_118_0 direction_118.1
    direction_118.2.1 conditioned_118 code

theorem conditional_118_0 (code : Nat) :
    weight conditionalCredit 0 118 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 118 [] 11 16
    (fun code => 0) selected_118_0 direction_118.1
    direction_118.2.2 conditioned_118 code
#print axioms selected_118_0
#print axioms source_118_0
#print axioms target_118_0
#print axioms block_118_0
#print axioms completed_118_0
#print axioms conditional_118_0

theorem selected_119_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [119])) := by rfl

theorem source_119_0 (code : Nat) :
    edgeSource 0 119 code = 264384+code/6 := by rfl

theorem target_119_0 (code : Nat) :
    edgeTarget 0 119 code = 544320+code%7776 := by rfl

theorem block_119_0 :
    savedBlockClass (75*119+0) = some 55 ∧
    recordedClassRoot 55 = 3450 := by decide +kernel

theorem completed_119_0 (code : Nat) :
    weight completedCredit 0 119 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 119 [] 17 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_119_0 direction_119.1
    direction_119.2.1 conditioned_119 code

theorem conditional_119_0 (code : Nat) :
    weight conditionalCredit 0 119 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 119 [] 17 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_119_0 direction_119.1
    direction_119.2.2 conditioned_119 code
#print axioms selected_119_0
#print axioms source_119_0
#print axioms target_119_0
#print axioms block_119_0
#print axioms completed_119_0
#print axioms conditional_119_0

end Snake9.Context101
