import Direction101Group05
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

theorem selected_353_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [353])) := by rfl

theorem source_353_0 (code : Nat) :
    edgeSource 0 353 code = 785376+code/6 := by rfl

theorem target_353_0 (code : Nat) :
    edgeTarget 0 353 code = 1197504+code%7776 := by rfl

theorem block_353_0 :
    savedBlockClass (75*353+0) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_0 (code : Nat) :
    weight completedCredit 0 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 353 [] 0 16
    (fun code => 0) selected_353_0 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_0 (code : Nat) :
    weight conditionalCredit 0 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 353 [] 0 16
    (fun code => 0) selected_353_0 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_0
#print axioms source_353_0
#print axioms target_353_0
#print axioms block_353_0
#print axioms completed_353_0
#print axioms conditional_353_0

theorem selected_353_4 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 4 [] ++ [353])) := by rfl

theorem source_353_4 (code : Nat) :
    edgeSource 4 353 code = 1049760+code/6 := by rfl

theorem target_353_4 (code : Nat) :
    edgeTarget 4 353 code = 1197504+code%7776 := by rfl

theorem block_353_4 :
    savedBlockClass (75*353+4) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_4 (code : Nat) :
    weight completedCredit 4 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 4 353 [] 0 16
    (fun code => 0) selected_353_4 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_4 (code : Nat) :
    weight conditionalCredit 4 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 4 353 [] 0 16
    (fun code => 0) selected_353_4 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_4
#print axioms source_353_4
#print axioms target_353_4
#print axioms block_353_4
#print axioms completed_353_4
#print axioms conditional_353_4

theorem selected_353_9 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 9 [] ++ [353])) := by rfl

theorem source_353_9 (code : Nat) :
    edgeSource 9 353 code = 1088640+code/6 := by rfl

theorem target_353_9 (code : Nat) :
    edgeTarget 9 353 code = 1353024+code%7776 := by rfl

theorem block_353_9 :
    savedBlockClass (75*353+9) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_9 (code : Nat) :
    weight completedCredit 9 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 9 353 [] 0 16
    (fun code => 0) selected_353_9 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_9 (code : Nat) :
    weight conditionalCredit 9 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 9 353 [] 0 16
    (fun code => 0) selected_353_9 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_9
#print axioms source_353_9
#print axioms target_353_9
#print axioms block_353_9
#print axioms completed_353_9
#print axioms conditional_353_9

theorem selected_353_16 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 16 [] ++ [353])) := by rfl

theorem source_353_16 (code : Nat) :
    edgeSource 16 353 code = 1143072+code/6 := by rfl

theorem target_353_16 (code : Nat) :
    edgeTarget 16 353 code = 1197504+code%7776 := by rfl

theorem block_353_16 :
    savedBlockClass (75*353+16) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_16 (code : Nat) :
    weight completedCredit 16 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 16 353 [] 0 16
    (fun code => 0) selected_353_16 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_16 (code : Nat) :
    weight conditionalCredit 16 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 16 353 [] 0 16
    (fun code => 0) selected_353_16 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_16
#print axioms source_353_16
#print axioms target_353_16
#print axioms block_353_16
#print axioms completed_353_16
#print axioms conditional_353_16

theorem selected_353_28 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 28 [] ++ [353])) := by rfl

theorem source_353_28 (code : Nat) :
    edgeSource 28 353 code = 1236384+code/6 := by rfl

theorem target_353_28 (code : Nat) :
    edgeTarget 28 353 code = 1562976+code%7776 := by rfl

theorem block_353_28 :
    savedBlockClass (75*353+28) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_28 (code : Nat) :
    weight completedCredit 28 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 28 353 [] 0 16
    (fun code => 0) selected_353_28 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_28 (code : Nat) :
    weight conditionalCredit 28 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 28 353 [] 0 16
    (fun code => 0) selected_353_28 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_28
#print axioms source_353_28
#print axioms target_353_28
#print axioms block_353_28
#print axioms completed_353_28
#print axioms conditional_353_28

theorem selected_353_29 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 29 [] ++ [353])) := by rfl

theorem source_353_29 (code : Nat) :
    edgeSource 29 353 code = 1244160+code/6 := by rfl

theorem target_353_29 (code : Nat) :
    edgeTarget 29 353 code = 1578528+code%7776 := by rfl

theorem block_353_29 :
    savedBlockClass (75*353+29) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_29 (code : Nat) :
    weight completedCredit 29 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 29 353 [] 0 16
    (fun code => 0) selected_353_29 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_29 (code : Nat) :
    weight conditionalCredit 29 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 29 353 [] 0 16
    (fun code => 0) selected_353_29 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_29
#print axioms source_353_29
#print axioms target_353_29
#print axioms block_353_29
#print axioms completed_353_29
#print axioms conditional_353_29

theorem selected_353_40 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 40 [] ++ [353])) := by rfl

theorem source_353_40 (code : Nat) :
    edgeSource 40 353 code = 1329696+code/6 := by rfl

theorem target_353_40 (code : Nat) :
    edgeTarget 40 353 code = 1353024+code%7776 := by rfl

theorem block_353_40 :
    savedBlockClass (75*353+40) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_40 (code : Nat) :
    weight completedCredit 40 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 40 353 [] 0 16
    (fun code => 0) selected_353_40 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_40 (code : Nat) :
    weight conditionalCredit 40 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 40 353 [] 0 16
    (fun code => 0) selected_353_40 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_40
#print axioms source_353_40
#print axioms target_353_40
#print axioms block_353_40
#print axioms completed_353_40
#print axioms conditional_353_40

theorem selected_353_44 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 44 [] ++ [353])) := by rfl

theorem source_353_44 (code : Nat) :
    edgeSource 44 353 code = 1360800+code/6 := by rfl

theorem target_353_44 (code : Nat) :
    edgeTarget 44 353 code = 1562976+code%7776 := by rfl

theorem block_353_44 :
    savedBlockClass (75*353+44) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_44 (code : Nat) :
    weight completedCredit 44 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 44 353 [] 0 16
    (fun code => 0) selected_353_44 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_44 (code : Nat) :
    weight conditionalCredit 44 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 44 353 [] 0 16
    (fun code => 0) selected_353_44 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_44
#print axioms source_353_44
#print axioms target_353_44
#print axioms block_353_44
#print axioms completed_353_44
#print axioms conditional_353_44

theorem selected_353_50 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 50 [] ++ [353])) := by rfl

theorem source_353_50 (code : Nat) :
    edgeSource 50 353 code = 1407456+code/6 := by rfl

theorem target_353_50 (code : Nat) :
    edgeTarget 50 353 code = 1197504+code%7776 := by rfl

theorem block_353_50 :
    savedBlockClass (75*353+50) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_50 (code : Nat) :
    weight completedCredit 50 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 50 353 [] 0 16
    (fun code => 0) selected_353_50 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_50 (code : Nat) :
    weight conditionalCredit 50 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 50 353 [] 0 16
    (fun code => 0) selected_353_50 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_50
#print axioms source_353_50
#print axioms target_353_50
#print axioms block_353_50
#print axioms completed_353_50
#print axioms conditional_353_50

theorem selected_353_55 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 55 [] ++ [353])) := by rfl

theorem source_353_55 (code : Nat) :
    edgeSource 55 353 code = 1446336+code/6 := by rfl

theorem target_353_55 (code : Nat) :
    edgeTarget 55 353 code = 1562976+code%7776 := by rfl

theorem block_353_55 :
    savedBlockClass (75*353+55) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_55 (code : Nat) :
    weight completedCredit 55 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 55 353 [] 0 16
    (fun code => 0) selected_353_55 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_55 (code : Nat) :
    weight conditionalCredit 55 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 55 353 [] 0 16
    (fun code => 0) selected_353_55 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_55
#print axioms source_353_55
#print axioms target_353_55
#print axioms block_353_55
#print axioms completed_353_55
#print axioms conditional_353_55

theorem selected_353_65 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 65 [] ++ [353])) := by rfl

theorem source_353_65 (code : Nat) :
    edgeSource 65 353 code = 1524096+code/6 := by rfl

theorem target_353_65 (code : Nat) :
    edgeTarget 65 353 code = 1562976+code%7776 := by rfl

theorem block_353_65 :
    savedBlockClass (75*353+65) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_65 (code : Nat) :
    weight completedCredit 65 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 65 353 [] 0 16
    (fun code => 0) selected_353_65 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_65 (code : Nat) :
    weight conditionalCredit 65 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 65 353 [] 0 16
    (fun code => 0) selected_353_65 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_65
#print axioms source_353_65
#print axioms target_353_65
#print axioms block_353_65
#print axioms completed_353_65
#print axioms conditional_353_65

theorem selected_353_74 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 74 [] ++ [353])) := by rfl

theorem source_353_74 (code : Nat) :
    edgeSource 74 353 code = 1594080+code/6 := by rfl

theorem target_353_74 (code : Nat) :
    edgeTarget 74 353 code = 1562976+code%7776 := by rfl

theorem block_353_74 :
    savedBlockClass (75*353+74) = some 125 ∧
    recordedClassRoot 125 = 3980 := by decide +kernel

theorem completed_353_74 (code : Nat) :
    weight completedCredit 74 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 74 353 [] 0 16
    (fun code => 0) selected_353_74 direction_353.1
    direction_353.2.1 conditioned_353 code

theorem conditional_353_74 (code : Nat) :
    weight conditionalCredit 74 353 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 74 353 [] 0 16
    (fun code => 0) selected_353_74 direction_353.1
    direction_353.2.2 conditioned_353 code
#print axioms selected_353_74
#print axioms source_353_74
#print axioms target_353_74
#print axioms block_353_74
#print axioms completed_353_74
#print axioms conditional_353_74

theorem selected_354_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [354])) := by rfl

theorem source_354_0 (code : Nat) :
    edgeSource 0 354 code = 785376+code/6 := by rfl

theorem target_354_0 (code : Nat) :
    edgeTarget 0 354 code = 1205280+code%7776 := by rfl

theorem block_354_0 :
    savedBlockClass (75*354+0) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_0 (code : Nat) :
    weight completedCredit 0 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 354 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_0 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_0 (code : Nat) :
    weight conditionalCredit 0 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 354 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_0 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_0
#print axioms source_354_0
#print axioms target_354_0
#print axioms block_354_0
#print axioms completed_354_0
#print axioms conditional_354_0

theorem selected_354_4 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 4 [] ++ [354])) := by rfl

theorem source_354_4 (code : Nat) :
    edgeSource 4 354 code = 1049760+code/6 := by rfl

theorem target_354_4 (code : Nat) :
    edgeTarget 4 354 code = 1205280+code%7776 := by rfl

theorem block_354_4 :
    savedBlockClass (75*354+4) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_4 (code : Nat) :
    weight completedCredit 4 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 4 354 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_4 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_4 (code : Nat) :
    weight conditionalCredit 4 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 4 354 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_4 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_4
#print axioms source_354_4
#print axioms target_354_4
#print axioms block_354_4
#print axioms completed_354_4
#print axioms conditional_354_4

theorem selected_354_9 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 9 [] ++ [354])) := by rfl

theorem source_354_9 (code : Nat) :
    edgeSource 9 354 code = 1088640+code/6 := by rfl

theorem target_354_9 (code : Nat) :
    edgeTarget 9 354 code = 1205280+code%7776 := by rfl

theorem block_354_9 :
    savedBlockClass (75*354+9) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_9 (code : Nat) :
    weight completedCredit 9 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 9 354 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_9 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_9 (code : Nat) :
    weight conditionalCredit 9 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 9 354 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_9 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_9
#print axioms source_354_9
#print axioms target_354_9
#print axioms block_354_9
#print axioms completed_354_9
#print axioms conditional_354_9

theorem selected_354_16 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 16 [] ++ [354])) := by rfl

theorem source_354_16 (code : Nat) :
    edgeSource 16 354 code = 1143072+code/6 := by rfl

theorem target_354_16 (code : Nat) :
    edgeTarget 16 354 code = 1430784+code%7776 := by rfl

theorem block_354_16 :
    savedBlockClass (75*354+16) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_16 (code : Nat) :
    weight completedCredit 16 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 16 354 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_16 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_16 (code : Nat) :
    weight conditionalCredit 16 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 16 354 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_16 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_16
#print axioms source_354_16
#print axioms target_354_16
#print axioms block_354_16
#print axioms completed_354_16
#print axioms conditional_354_16

theorem selected_354_28 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 28 [] ++ [354])) := by rfl

theorem source_354_28 (code : Nat) :
    edgeSource 28 354 code = 1236384+code/6 := by rfl

theorem target_354_28 (code : Nat) :
    edgeTarget 28 354 code = 1205280+code%7776 := by rfl

theorem block_354_28 :
    savedBlockClass (75*354+28) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_28 (code : Nat) :
    weight completedCredit 28 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 28 354 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_28 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_28 (code : Nat) :
    weight conditionalCredit 28 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 28 354 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_28 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_28
#print axioms source_354_28
#print axioms target_354_28
#print axioms block_354_28
#print axioms completed_354_28
#print axioms conditional_354_28

theorem selected_354_29 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 29 [] ++ [354])) := by rfl

theorem source_354_29 (code : Nat) :
    edgeSource 29 354 code = 1244160+code/6 := by rfl

theorem target_354_29 (code : Nat) :
    edgeTarget 29 354 code = 1205280+code%7776 := by rfl

theorem block_354_29 :
    savedBlockClass (75*354+29) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_29 (code : Nat) :
    weight completedCredit 29 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 29 354 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_29 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_29 (code : Nat) :
    weight conditionalCredit 29 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 29 354 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_29 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_29
#print axioms source_354_29
#print axioms target_354_29
#print axioms block_354_29
#print axioms completed_354_29
#print axioms conditional_354_29

theorem selected_354_40 :
    [rule015] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 40 [] ++ [354])) := by rfl

theorem source_354_40 (code : Nat) :
    edgeSource 40 354 code = 1329696+code/6 := by rfl

theorem target_354_40 (code : Nat) :
    edgeTarget 40 354 code = 1205280+code%7776 := by rfl

theorem block_354_40 :
    savedBlockClass (75*354+40) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_40 (code : Nat) :
    weight completedCredit 40 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule015] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 40 354 [rule015] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_40 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_40 (code : Nat) :
    weight conditionalCredit 40 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule015] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 40 354 [rule015] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_40 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_40
#print axioms source_354_40
#print axioms target_354_40
#print axioms block_354_40
#print axioms completed_354_40
#print axioms conditional_354_40

theorem selected_354_44 :
    [rule023] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 44 [] ++ [354])) := by rfl

theorem source_354_44 (code : Nat) :
    edgeSource 44 354 code = 1360800+code/6 := by rfl

theorem target_354_44 (code : Nat) :
    edgeTarget 44 354 code = 1205280+code%7776 := by rfl

theorem block_354_44 :
    savedBlockClass (75*354+44) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_44 (code : Nat) :
    weight completedCredit 44 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule023] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 44 354 [rule023] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_44 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_44 (code : Nat) :
    weight conditionalCredit 44 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule023] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 44 354 [rule023] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_44 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_44
#print axioms source_354_44
#print axioms target_354_44
#print axioms block_354_44
#print axioms completed_354_44
#print axioms conditional_354_44

theorem selected_354_50 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 50 [] ++ [354])) := by rfl

theorem source_354_50 (code : Nat) :
    edgeSource 50 354 code = 1407456+code/6 := by rfl

theorem target_354_50 (code : Nat) :
    edgeTarget 50 354 code = 1205280+code%7776 := by rfl

theorem block_354_50 :
    savedBlockClass (75*354+50) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_50 (code : Nat) :
    weight completedCredit 50 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 50 354 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_50 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_50 (code : Nat) :
    weight conditionalCredit 50 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 50 354 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_50 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_50
#print axioms source_354_50
#print axioms target_354_50
#print axioms block_354_50
#print axioms completed_354_50
#print axioms conditional_354_50

theorem selected_354_55 :
    [rule032] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 55 [] ++ [354])) := by rfl

theorem source_354_55 (code : Nat) :
    edgeSource 55 354 code = 1446336+code/6 := by rfl

theorem target_354_55 (code : Nat) :
    edgeTarget 55 354 code = 1205280+code%7776 := by rfl

theorem block_354_55 :
    savedBlockClass (75*354+55) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_55 (code : Nat) :
    weight completedCredit 55 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule032] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 55 354 [rule032] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_55 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_55 (code : Nat) :
    weight conditionalCredit 55 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule032] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 55 354 [rule032] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_55 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_55
#print axioms source_354_55
#print axioms target_354_55
#print axioms block_354_55
#print axioms completed_354_55
#print axioms conditional_354_55

theorem selected_354_65 :
    [rule041] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 65 [] ++ [354])) := by rfl

theorem source_354_65 (code : Nat) :
    edgeSource 65 354 code = 1524096+code/6 := by rfl

theorem target_354_65 (code : Nat) :
    edgeTarget 65 354 code = 1205280+code%7776 := by rfl

theorem block_354_65 :
    savedBlockClass (75*354+65) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_65 (code : Nat) :
    weight completedCredit 65 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule041] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 65 354 [rule041] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_65 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_65 (code : Nat) :
    weight conditionalCredit 65 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule041] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 65 354 [rule041] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_65 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_65
#print axioms source_354_65
#print axioms target_354_65
#print axioms block_354_65
#print axioms completed_354_65
#print axioms conditional_354_65

theorem selected_354_74 :
    [rule054] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 74 [] ++ [354])) := by rfl

theorem source_354_74 (code : Nat) :
    edgeSource 74 354 code = 1594080+code/6 := by rfl

theorem target_354_74 (code : Nat) :
    edgeTarget 74 354 code = 1205280+code%7776 := by rfl

theorem block_354_74 :
    savedBlockClass (75*354+74) = some 123 ∧
    recordedClassRoot 123 = 3960 := by decide +kernel

theorem completed_354_74 (code : Nat) :
    weight completedCredit 74 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule054] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 74 354 [rule054] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_74 direction_354.1
    direction_354.2.1 conditioned_354 code

theorem conditional_354_74 (code : Nat) :
    weight conditionalCredit 74 354 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule054] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 74 354 [rule054] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_354_74 direction_354.1
    direction_354.2.2 conditioned_354 code
#print axioms selected_354_74
#print axioms source_354_74
#print axioms target_354_74
#print axioms block_354_74
#print axioms completed_354_74
#print axioms conditional_354_74

theorem selected_355_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [355])) := by rfl

theorem source_355_0 (code : Nat) :
    edgeSource 0 355 code = 793152+code/6 := by rfl

theorem target_355_0 (code : Nat) :
    edgeTarget 0 355 code = 482112+code%7776 := by rfl

theorem block_355_0 :
    savedBlockClass (75*355+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_355_0 (code : Nat) :
    weight completedCredit 0 355 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 355 [] 9 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_355_0 direction_355.1
    direction_355.2.1 conditioned_355 code

theorem conditional_355_0 (code : Nat) :
    weight conditionalCredit 0 355 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 355 [] 9 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_355_0 direction_355.1
    direction_355.2.2 conditioned_355 code
#print axioms selected_355_0
#print axioms source_355_0
#print axioms target_355_0
#print axioms block_355_0
#print axioms completed_355_0
#print axioms conditional_355_0

theorem selected_356_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [356])) := by rfl

theorem source_356_0 (code : Nat) :
    edgeSource 0 356 code = 793152+code/6 := by rfl

theorem target_356_0 (code : Nat) :
    edgeTarget 0 356 code = 489888+code%7776 := by rfl

theorem block_356_0 :
    savedBlockClass (75*356+0) = some 18 ∧
    recordedClassRoot 18 = 2297 := by decide +kernel

theorem completed_356_0 (code : Nat) :
    weight completedCredit 0 356 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 356 [] 9 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_356_0 direction_356.1
    direction_356.2.1 conditioned_356 code

theorem conditional_356_0 (code : Nat) :
    weight conditionalCredit 0 356 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 356 [] 9 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_356_0 direction_356.1
    direction_356.2.2 conditioned_356 code
#print axioms selected_356_0
#print axioms source_356_0
#print axioms target_356_0
#print axioms block_356_0
#print axioms completed_356_0
#print axioms conditional_356_0

theorem selected_357_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [357])) := by rfl

theorem source_357_0 (code : Nat) :
    edgeSource 0 357 code = 793152+code/6 := by rfl

theorem target_357_0 (code : Nat) :
    edgeTarget 0 357 code = 497664+code%7776 := by rfl

theorem block_357_0 :
    savedBlockClass (75*357+0) = some 17 ∧
    recordedClassRoot 17 = 2231 := by decide +kernel

theorem completed_357_0 (code : Nat) :
    weight completedCredit 0 357 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 357 [] 9 0
    (fun code => 0) selected_357_0 direction_357.1
    direction_357.2.1 conditioned_357 code

theorem conditional_357_0 (code : Nat) :
    weight conditionalCredit 0 357 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 357 [] 9 16
    (fun code => 0) selected_357_0 direction_357.1
    direction_357.2.2 conditioned_357 code
#print axioms selected_357_0
#print axioms source_357_0
#print axioms target_357_0
#print axioms block_357_0
#print axioms completed_357_0
#print axioms conditional_357_0

theorem selected_358_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [358])) := by rfl

theorem source_358_0 (code : Nat) :
    edgeSource 0 358 code = 793152+code/6 := by rfl

theorem target_358_0 (code : Nat) :
    edgeTarget 0 358 code = 505440+code%7776 := by rfl

theorem block_358_0 :
    savedBlockClass (75*358+0) = some 21 ∧
    recordedClassRoot 21 = 2479 := by decide +kernel

theorem completed_358_0 (code : Nat) :
    weight completedCredit 0 358 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 358 [] 9 16
    (fun code => 0) selected_358_0 direction_358.1
    direction_358.2.1 conditioned_358 code

theorem conditional_358_0 (code : Nat) :
    weight conditionalCredit 0 358 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 358 [] 9 16
    (fun code => 0) selected_358_0 direction_358.1
    direction_358.2.2 conditioned_358 code
#print axioms selected_358_0
#print axioms source_358_0
#print axioms target_358_0
#print axioms block_358_0
#print axioms completed_358_0
#print axioms conditional_358_0

theorem selected_359_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [359])) := by rfl

theorem source_359_0 (code : Nat) :
    edgeSource 0 359 code = 793152+code/6 := by rfl

theorem target_359_0 (code : Nat) :
    edgeTarget 0 359 code = 513216+code%7776 := by rfl

theorem block_359_0 :
    savedBlockClass (75*359+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_359_0 (code : Nat) :
    weight completedCredit 0 359 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 359 [] 9 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_359_0 direction_359.1
    direction_359.2.1 conditioned_359 code

theorem conditional_359_0 (code : Nat) :
    weight conditionalCredit 0 359 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 359 [] 9 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_359_0 direction_359.1
    direction_359.2.2 conditioned_359 code
#print axioms selected_359_0
#print axioms source_359_0
#print axioms target_359_0
#print axioms block_359_0
#print axioms completed_359_0
#print axioms conditional_359_0

theorem selected_360_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [360])) := by rfl

theorem source_360_0 (code : Nat) :
    edgeSource 0 360 code = 800928+code/6 := by rfl

theorem target_360_0 (code : Nat) :
    edgeTarget 0 360 code = 435456+code%7776 := by rfl

theorem block_360_0 :
    savedBlockClass (75*360+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_360_0 (code : Nat) :
    weight completedCredit 0 360 code =
      120*(code%6+1)+max (max 33 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 360 [] 33 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_360_0 direction_360.1
    direction_360.2.1 conditioned_360 code

theorem conditional_360_0 (code : Nat) :
    weight conditionalCredit 0 360 code =
      120*(code%6+1)+max (max 33 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 360 [] 33 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_360_0 direction_360.1
    direction_360.2.2 conditioned_360 code
#print axioms selected_360_0
#print axioms source_360_0
#print axioms target_360_0
#print axioms block_360_0
#print axioms completed_360_0
#print axioms conditional_360_0

theorem selected_361_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [361])) := by rfl

theorem source_361_0 (code : Nat) :
    edgeSource 0 361 code = 800928+code/6 := by rfl

theorem target_361_0 (code : Nat) :
    edgeTarget 0 361 code = 412128+code%7776 := by rfl

theorem block_361_0 :
    savedBlockClass (75*361+0) = some 18 ∧
    recordedClassRoot 18 = 2297 := by decide +kernel

theorem completed_361_0 (code : Nat) :
    weight completedCredit 0 361 code =
      120*(code%6+1)+max (max 32 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 361 [] 32 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_361_0 direction_361.1
    direction_361.2.1 conditioned_361 code

theorem conditional_361_0 (code : Nat) :
    weight conditionalCredit 0 361 code =
      120*(code%6+1)+max (max 32 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 361 [] 32 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_361_0 direction_361.1
    direction_361.2.2 conditioned_361 code
#print axioms selected_361_0
#print axioms source_361_0
#print axioms target_361_0
#print axioms block_361_0
#print axioms completed_361_0
#print axioms conditional_361_0

theorem selected_362_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [362])) := by rfl

theorem source_362_0 (code : Nat) :
    edgeSource 0 362 code = 800928+code/6 := by rfl

theorem target_362_0 (code : Nat) :
    edgeTarget 0 362 code = 419904+code%7776 := by rfl

theorem block_362_0 :
    savedBlockClass (75*362+0) = some 17 ∧
    recordedClassRoot 17 = 2231 := by decide +kernel

theorem completed_362_0 (code : Nat) :
    weight completedCredit 0 362 code =
      120*(code%6+1)+max (max 23 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 362 [] 23 0
    (fun code => 0) selected_362_0 direction_362.1
    direction_362.2.1 conditioned_362 code

theorem conditional_362_0 (code : Nat) :
    weight conditionalCredit 0 362 code =
      120*(code%6+1)+max (max 23 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 362 [] 23 16
    (fun code => 0) selected_362_0 direction_362.1
    direction_362.2.2 conditioned_362 code
#print axioms selected_362_0
#print axioms source_362_0
#print axioms target_362_0
#print axioms block_362_0
#print axioms completed_362_0
#print axioms conditional_362_0

theorem selected_363_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [363])) := by rfl

theorem source_363_0 (code : Nat) :
    edgeSource 0 363 code = 800928+code/6 := by rfl

theorem target_363_0 (code : Nat) :
    edgeTarget 0 363 code = 427680+code%7776 := by rfl

theorem block_363_0 :
    savedBlockClass (75*363+0) = some 21 ∧
    recordedClassRoot 21 = 2479 := by decide +kernel

theorem completed_363_0 (code : Nat) :
    weight completedCredit 0 363 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 363 [] 22 16
    (fun code => 0) selected_363_0 direction_363.1
    direction_363.2.1 conditioned_363 code

theorem conditional_363_0 (code : Nat) :
    weight conditionalCredit 0 363 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 363 [] 22 16
    (fun code => 0) selected_363_0 direction_363.1
    direction_363.2.2 conditioned_363 code
#print axioms selected_363_0
#print axioms source_363_0
#print axioms target_363_0
#print axioms block_363_0
#print axioms completed_363_0
#print axioms conditional_363_0

theorem selected_364_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [364])) := by rfl

theorem source_364_0 (code : Nat) :
    edgeSource 0 364 code = 800928+code/6 := by rfl

theorem target_364_0 (code : Nat) :
    edgeTarget 0 364 code = 435456+code%7776 := by rfl

theorem block_364_0 :
    savedBlockClass (75*364+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_364_0 (code : Nat) :
    weight completedCredit 0 364 code =
      120*(code%6+1)+max (max 33 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 364 [] 33 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_364_0 direction_364.1
    direction_364.2.1 conditioned_364 code

theorem conditional_364_0 (code : Nat) :
    weight conditionalCredit 0 364 code =
      120*(code%6+1)+max (max 33 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 364 [] 33 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_364_0 direction_364.1
    direction_364.2.2 conditioned_364 code
#print axioms selected_364_0
#print axioms source_364_0
#print axioms target_364_0
#print axioms block_364_0
#print axioms completed_364_0
#print axioms conditional_364_0

theorem selected_365_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [365])) := by rfl

theorem source_365_0 (code : Nat) :
    edgeSource 0 365 code = 808704+code/6 := by rfl

theorem target_365_0 (code : Nat) :
    edgeTarget 0 365 code = 458784+code%7776 := by rfl

theorem block_365_0 :
    savedBlockClass (75*365+0) = some 15 ∧
    recordedClassRoot 15 = 2085 := by decide +kernel

theorem completed_365_0 (code : Nat) :
    weight completedCredit 0 365 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 365 [] 22 16
    (fun code => 0) selected_365_0 direction_365.1
    direction_365.2.1 conditioned_365 code

theorem conditional_365_0 (code : Nat) :
    weight conditionalCredit 0 365 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 365 [] 22 16
    (fun code => 0) selected_365_0 direction_365.1
    direction_365.2.2 conditioned_365 code
#print axioms selected_365_0
#print axioms source_365_0
#print axioms target_365_0
#print axioms block_365_0
#print axioms completed_365_0
#print axioms conditional_365_0

theorem selected_366_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [366])) := by rfl

theorem source_366_0 (code : Nat) :
    edgeSource 0 366 code = 808704+code/6 := by rfl

theorem target_366_0 (code : Nat) :
    edgeTarget 0 366 code = 443232+code%7776 := by rfl

theorem block_366_0 :
    savedBlockClass (75*366+0) = some 15 ∧
    recordedClassRoot 15 = 2085 := by decide +kernel

theorem completed_366_0 (code : Nat) :
    weight completedCredit 0 366 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 366 [] 17 16
    (fun code => 0) selected_366_0 direction_366.1
    direction_366.2.1 conditioned_366 code

theorem conditional_366_0 (code : Nat) :
    weight conditionalCredit 0 366 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 366 [] 17 16
    (fun code => 0) selected_366_0 direction_366.1
    direction_366.2.2 conditioned_366 code
#print axioms selected_366_0
#print axioms source_366_0
#print axioms target_366_0
#print axioms block_366_0
#print axioms completed_366_0
#print axioms conditional_366_0

theorem selected_367_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [367])) := by rfl

theorem source_367_0 (code : Nat) :
    edgeSource 0 367 code = 808704+code/6 := by rfl

theorem target_367_0 (code : Nat) :
    edgeTarget 0 367 code = 451008+code%7776 := by rfl

theorem block_367_0 :
    savedBlockClass (75*367+0) = some 16 ∧
    recordedClassRoot 16 = 2162 := by decide +kernel

theorem completed_367_0 (code : Nat) :
    weight completedCredit 0 367 code =
      120*(code%6+1)+max (max 16 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 367 [] 16 16
    (fun code => 0) selected_367_0 direction_367.1
    direction_367.2.1 conditioned_367 code

theorem conditional_367_0 (code : Nat) :
    weight conditionalCredit 0 367 code =
      120*(code%6+1)+max (max 16 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 367 [] 16 16
    (fun code => 0) selected_367_0 direction_367.1
    direction_367.2.2 conditioned_367 code
#print axioms selected_367_0
#print axioms source_367_0
#print axioms target_367_0
#print axioms block_367_0
#print axioms completed_367_0
#print axioms conditional_367_0

theorem selected_368_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [368])) := by rfl

theorem source_368_0 (code : Nat) :
    edgeSource 0 368 code = 808704+code/6 := by rfl

theorem target_368_0 (code : Nat) :
    edgeTarget 0 368 code = 458784+code%7776 := by rfl

theorem block_368_0 :
    savedBlockClass (75*368+0) = some 15 ∧
    recordedClassRoot 15 = 2085 := by decide +kernel

theorem completed_368_0 (code : Nat) :
    weight completedCredit 0 368 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 368 [] 22 16
    (fun code => 0) selected_368_0 direction_368.1
    direction_368.2.1 conditioned_368 code

theorem conditional_368_0 (code : Nat) :
    weight conditionalCredit 0 368 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 368 [] 22 16
    (fun code => 0) selected_368_0 direction_368.1
    direction_368.2.2 conditioned_368 code
#print axioms selected_368_0
#print axioms source_368_0
#print axioms target_368_0
#print axioms block_368_0
#print axioms completed_368_0
#print axioms conditional_368_0

theorem selected_369_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [369])) := by rfl

theorem source_369_0 (code : Nat) :
    edgeSource 0 369 code = 816480+code/6 := by rfl

theorem target_369_0 (code : Nat) :
    edgeTarget 0 369 code = 474336+code%7776 := by rfl

theorem block_369_0 :
    savedBlockClass (75*369+0) = some 20 ∧
    recordedClassRoot 20 = 2418 := by decide +kernel

theorem completed_369_0 (code : Nat) :
    weight completedCredit 0 369 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 369 [] 10 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_369_0 direction_369.1
    direction_369.2.1 conditioned_369 code

theorem conditional_369_0 (code : Nat) :
    weight conditionalCredit 0 369 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 369 [] 10 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_369_0 direction_369.1
    direction_369.2.2 conditioned_369 code
#print axioms selected_369_0
#print axioms source_369_0
#print axioms target_369_0
#print axioms block_369_0
#print axioms completed_369_0
#print axioms conditional_369_0

theorem selected_370_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [370])) := by rfl

theorem source_370_0 (code : Nat) :
    edgeSource 0 370 code = 816480+code/6 := by rfl

theorem target_370_0 (code : Nat) :
    edgeTarget 0 370 code = 466560+code%7776 := by rfl

theorem block_370_0 :
    savedBlockClass (75*370+0) = some 20 ∧
    recordedClassRoot 20 = 2418 := by decide +kernel

theorem completed_370_0 (code : Nat) :
    weight completedCredit 0 370 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 370 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_370_0 direction_370.1
    direction_370.2.1 conditioned_370 code

theorem conditional_370_0 (code : Nat) :
    weight conditionalCredit 0 370 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 370 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_370_0 direction_370.1
    direction_370.2.2 conditioned_370 code
#print axioms selected_370_0
#print axioms source_370_0
#print axioms target_370_0
#print axioms block_370_0
#print axioms completed_370_0
#print axioms conditional_370_0

theorem selected_371_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [371])) := by rfl

theorem source_371_0 (code : Nat) :
    edgeSource 0 371 code = 816480+code/6 := by rfl

theorem target_371_0 (code : Nat) :
    edgeTarget 0 371 code = 474336+code%7776 := by rfl

theorem block_371_0 :
    savedBlockClass (75*371+0) = some 20 ∧
    recordedClassRoot 20 = 2418 := by decide +kernel

theorem completed_371_0 (code : Nat) :
    weight completedCredit 0 371 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 371 [] 10 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_371_0 direction_371.1
    direction_371.2.1 conditioned_371 code

theorem conditional_371_0 (code : Nat) :
    weight conditionalCredit 0 371 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 371 [] 10 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_371_0 direction_371.1
    direction_371.2.2 conditioned_371 code
#print axioms selected_371_0
#print axioms source_371_0
#print axioms target_371_0
#print axioms block_371_0
#print axioms completed_371_0
#print axioms conditional_371_0

theorem selected_372_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [372])) := by rfl

theorem source_372_0 (code : Nat) :
    edgeSource 0 372 code = 824256+code/6 := by rfl

theorem target_372_0 (code : Nat) :
    edgeTarget 0 372 code = 513216+code%7776 := by rfl

theorem block_372_0 :
    savedBlockClass (75*372+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_372_0 (code : Nat) :
    weight completedCredit 0 372 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 372 [] 9 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_372_0 direction_372.1
    direction_372.2.1 conditioned_372 code

theorem conditional_372_0 (code : Nat) :
    weight conditionalCredit 0 372 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 372 [] 9 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_372_0 direction_372.1
    direction_372.2.2 conditioned_372 code
#print axioms selected_372_0
#print axioms source_372_0
#print axioms target_372_0
#print axioms block_372_0
#print axioms completed_372_0
#print axioms conditional_372_0

theorem selected_373_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [373])) := by rfl

theorem source_373_0 (code : Nat) :
    edgeSource 0 373 code = 824256+code/6 := by rfl

theorem target_373_0 (code : Nat) :
    edgeTarget 0 373 code = 482112+code%7776 := by rfl

theorem block_373_0 :
    savedBlockClass (75*373+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_373_0 (code : Nat) :
    weight completedCredit 0 373 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 373 [] 9 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_373_0 direction_373.1
    direction_373.2.1 conditioned_373 code

theorem conditional_373_0 (code : Nat) :
    weight conditionalCredit 0 373 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 373 [] 9 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_373_0 direction_373.1
    direction_373.2.2 conditioned_373 code
#print axioms selected_373_0
#print axioms source_373_0
#print axioms target_373_0
#print axioms block_373_0
#print axioms completed_373_0
#print axioms conditional_373_0

theorem selected_374_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [374])) := by rfl

theorem source_374_0 (code : Nat) :
    edgeSource 0 374 code = 824256+code/6 := by rfl

theorem target_374_0 (code : Nat) :
    edgeTarget 0 374 code = 489888+code%7776 := by rfl

theorem block_374_0 :
    savedBlockClass (75*374+0) = some 18 ∧
    recordedClassRoot 18 = 2297 := by decide +kernel

theorem completed_374_0 (code : Nat) :
    weight completedCredit 0 374 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 374 [] 9 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_374_0 direction_374.1
    direction_374.2.1 conditioned_374 code

theorem conditional_374_0 (code : Nat) :
    weight conditionalCredit 0 374 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 374 [] 9 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_374_0 direction_374.1
    direction_374.2.2 conditioned_374 code
#print axioms selected_374_0
#print axioms source_374_0
#print axioms target_374_0
#print axioms block_374_0
#print axioms completed_374_0
#print axioms conditional_374_0

theorem selected_375_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [375])) := by rfl

theorem source_375_0 (code : Nat) :
    edgeSource 0 375 code = 824256+code/6 := by rfl

theorem target_375_0 (code : Nat) :
    edgeTarget 0 375 code = 497664+code%7776 := by rfl

theorem block_375_0 :
    savedBlockClass (75*375+0) = some 17 ∧
    recordedClassRoot 17 = 2231 := by decide +kernel

theorem completed_375_0 (code : Nat) :
    weight completedCredit 0 375 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 375 [] 9 0
    (fun code => 0) selected_375_0 direction_375.1
    direction_375.2.1 conditioned_375 code

theorem conditional_375_0 (code : Nat) :
    weight conditionalCredit 0 375 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 375 [] 9 16
    (fun code => 0) selected_375_0 direction_375.1
    direction_375.2.2 conditioned_375 code
#print axioms selected_375_0
#print axioms source_375_0
#print axioms target_375_0
#print axioms block_375_0
#print axioms completed_375_0
#print axioms conditional_375_0

theorem selected_376_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [376])) := by rfl

theorem source_376_0 (code : Nat) :
    edgeSource 0 376 code = 824256+code/6 := by rfl

theorem target_376_0 (code : Nat) :
    edgeTarget 0 376 code = 505440+code%7776 := by rfl

theorem block_376_0 :
    savedBlockClass (75*376+0) = some 21 ∧
    recordedClassRoot 21 = 2479 := by decide +kernel

theorem completed_376_0 (code : Nat) :
    weight completedCredit 0 376 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 376 [] 9 16
    (fun code => 0) selected_376_0 direction_376.1
    direction_376.2.1 conditioned_376 code

theorem conditional_376_0 (code : Nat) :
    weight conditionalCredit 0 376 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 376 [] 9 16
    (fun code => 0) selected_376_0 direction_376.1
    direction_376.2.2 conditioned_376 code
#print axioms selected_376_0
#print axioms source_376_0
#print axioms target_376_0
#print axioms block_376_0
#print axioms completed_376_0
#print axioms conditional_376_0

theorem selected_377_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [377])) := by rfl

theorem source_377_0 (code : Nat) :
    edgeSource 0 377 code = 824256+code/6 := by rfl

theorem target_377_0 (code : Nat) :
    edgeTarget 0 377 code = 513216+code%7776 := by rfl

theorem block_377_0 :
    savedBlockClass (75*377+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_377_0 (code : Nat) :
    weight completedCredit 0 377 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 377 [] 9 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_377_0 direction_377.1
    direction_377.2.1 conditioned_377 code

theorem conditional_377_0 (code : Nat) :
    weight conditionalCredit 0 377 code =
      120*(code%6+1)+max (max 9 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 377 [] 9 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_377_0 direction_377.1
    direction_377.2.2 conditioned_377 code
#print axioms selected_377_0
#print axioms source_377_0
#print axioms target_377_0
#print axioms block_377_0
#print axioms completed_377_0
#print axioms conditional_377_0

theorem selected_378_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [378])) := by rfl

theorem source_378_0 (code : Nat) :
    edgeSource 0 378 code = 832032+code/6 := by rfl

theorem target_378_0 (code : Nat) :
    edgeTarget 0 378 code = 832032+code%7776 := by rfl

theorem block_378_0 :
    savedBlockClass (75*378+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_378_0 (code : Nat) :
    weight completedCredit 0 378 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 378 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_378_0 direction_378.1
    direction_378.2.1 conditioned_378 code

theorem conditional_378_0 (code : Nat) :
    weight conditionalCredit 0 378 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 378 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_378_0 direction_378.1
    direction_378.2.2 conditioned_378 code
#print axioms selected_378_0
#print axioms source_378_0
#print axioms target_378_0
#print axioms block_378_0
#print axioms completed_378_0
#print axioms conditional_378_0

theorem selected_379_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [379])) := by rfl

theorem source_379_0 (code : Nat) :
    edgeSource 0 379 code = 832032+code/6 := by rfl

theorem target_379_0 (code : Nat) :
    edgeTarget 0 379 code = 839808+code%7776 := by rfl

theorem block_379_0 :
    savedBlockClass (75*379+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_379_0 (code : Nat) :
    weight completedCredit 0 379 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 379 [] 0 0
    (fun code => 0) selected_379_0 direction_379.1
    direction_379.2.1 conditioned_379 code

theorem conditional_379_0 (code : Nat) :
    weight conditionalCredit 0 379 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 379 [] 0 16
    (fun code => 0) selected_379_0 direction_379.1
    direction_379.2.2 conditioned_379 code
#print axioms selected_379_0
#print axioms source_379_0
#print axioms target_379_0
#print axioms block_379_0
#print axioms completed_379_0
#print axioms conditional_379_0

theorem selected_380_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [380])) := by rfl

theorem source_380_0 (code : Nat) :
    edgeSource 0 380 code = 832032+code/6 := by rfl

theorem target_380_0 (code : Nat) :
    edgeTarget 0 380 code = 847584+code%7776 := by rfl

theorem block_380_0 :
    savedBlockClass (75*380+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_380_0 (code : Nat) :
    weight completedCredit 0 380 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 380 [] 0 16
    (fun code => 0) selected_380_0 direction_380.1
    direction_380.2.1 conditioned_380 code

theorem conditional_380_0 (code : Nat) :
    weight conditionalCredit 0 380 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 380 [] 0 16
    (fun code => 0) selected_380_0 direction_380.1
    direction_380.2.2 conditioned_380 code
#print axioms selected_380_0
#print axioms source_380_0
#print axioms target_380_0
#print axioms block_380_0
#print axioms completed_380_0
#print axioms conditional_380_0

theorem selected_381_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [381])) := by rfl

theorem source_381_0 (code : Nat) :
    edgeSource 0 381 code = 832032+code/6 := by rfl

theorem target_381_0 (code : Nat) :
    edgeTarget 0 381 code = 855360+code%7776 := by rfl

theorem block_381_0 :
    savedBlockClass (75*381+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_381_0 (code : Nat) :
    weight completedCredit 0 381 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 381 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_381_0 direction_381.1
    direction_381.2.1 conditioned_381 code

theorem conditional_381_0 (code : Nat) :
    weight conditionalCredit 0 381 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 381 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_381_0 direction_381.1
    direction_381.2.2 conditioned_381 code
#print axioms selected_381_0
#print axioms source_381_0
#print axioms target_381_0
#print axioms block_381_0
#print axioms completed_381_0
#print axioms conditional_381_0

theorem selected_382_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [382])) := by rfl

theorem source_382_0 (code : Nat) :
    edgeSource 0 382 code = 832032+code/6 := by rfl

theorem target_382_0 (code : Nat) :
    edgeTarget 0 382 code = 863136+code%7776 := by rfl

theorem block_382_0 :
    savedBlockClass (75*382+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_382_0 (code : Nat) :
    weight completedCredit 0 382 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 382 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_382_0 direction_382.1
    direction_382.2.1 conditioned_382 code

theorem conditional_382_0 (code : Nat) :
    weight conditionalCredit 0 382 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 382 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_382_0 direction_382.1
    direction_382.2.2 conditioned_382 code
#print axioms selected_382_0
#print axioms source_382_0
#print axioms target_382_0
#print axioms block_382_0
#print axioms completed_382_0
#print axioms conditional_382_0

theorem selected_383_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [383])) := by rfl

theorem source_383_0 (code : Nat) :
    edgeSource 0 383 code = 839808+code/6 := by rfl

theorem target_383_0 (code : Nat) :
    edgeTarget 0 383 code = 870912+code%7776 := by rfl

theorem block_383_0 :
    savedBlockClass (75*383+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_383_0 (code : Nat) :
    weight completedCredit 0 383 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 383 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_383_0 direction_383.1
    direction_383.2.1 conditioned_383 code

theorem conditional_383_0 (code : Nat) :
    weight conditionalCredit 0 383 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 383 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_383_0 direction_383.1
    direction_383.2.2 conditioned_383 code
#print axioms selected_383_0
#print axioms source_383_0
#print axioms target_383_0
#print axioms block_383_0
#print axioms completed_383_0
#print axioms conditional_383_0

theorem selected_384_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [384])) := by rfl

theorem source_384_0 (code : Nat) :
    edgeSource 0 384 code = 839808+code/6 := by rfl

theorem target_384_0 (code : Nat) :
    edgeTarget 0 384 code = 878688+code%7776 := by rfl

theorem block_384_0 :
    savedBlockClass (75*384+0) = some 29 ∧
    recordedClassRoot 29 = 2691 := by decide +kernel

theorem completed_384_0 (code : Nat) :
    weight completedCredit 0 384 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 384 [] 0 0
    (fun code => 0) selected_384_0 direction_384.1
    direction_384.2.1 conditioned_384 code

theorem conditional_384_0 (code : Nat) :
    weight conditionalCredit 0 384 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 384 [] 0 16
    (fun code => 0) selected_384_0 direction_384.1
    direction_384.2.2 conditioned_384 code
#print axioms selected_384_0
#print axioms source_384_0
#print axioms target_384_0
#print axioms block_384_0
#print axioms completed_384_0
#print axioms conditional_384_0

theorem selected_385_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [385])) := by rfl

theorem source_385_0 (code : Nat) :
    edgeSource 0 385 code = 839808+code/6 := by rfl

theorem target_385_0 (code : Nat) :
    edgeTarget 0 385 code = 886464+code%7776 := by rfl

theorem block_385_0 :
    savedBlockClass (75*385+0) = some 43 ∧
    recordedClassRoot 43 = 3318 := by decide +kernel

theorem completed_385_0 (code : Nat) :
    weight completedCredit 0 385 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 385 [] 0 16
    (fun code => 0) selected_385_0 direction_385.1
    direction_385.2.1 conditioned_385 code

theorem conditional_385_0 (code : Nat) :
    weight conditionalCredit 0 385 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 385 [] 0 16
    (fun code => 0) selected_385_0 direction_385.1
    direction_385.2.2 conditioned_385 code
#print axioms selected_385_0
#print axioms source_385_0
#print axioms target_385_0
#print axioms block_385_0
#print axioms completed_385_0
#print axioms conditional_385_0

theorem selected_386_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [386])) := by rfl

theorem source_386_0 (code : Nat) :
    edgeSource 0 386 code = 839808+code/6 := by rfl

theorem target_386_0 (code : Nat) :
    edgeTarget 0 386 code = 894240+code%7776 := by rfl

theorem block_386_0 :
    savedBlockClass (75*386+0) = some 112 ∧
    recordedClassRoot 112 = 3904 := by decide +kernel

theorem completed_386_0 (code : Nat) :
    weight completedCredit 0 386 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 386 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_386_0 direction_386.1
    direction_386.2.1 conditioned_386 code

theorem conditional_386_0 (code : Nat) :
    weight conditionalCredit 0 386 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 386 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_386_0 direction_386.1
    direction_386.2.2 conditioned_386 code
#print axioms selected_386_0
#print axioms source_386_0
#print axioms target_386_0
#print axioms block_386_0
#print axioms completed_386_0
#print axioms conditional_386_0

theorem selected_387_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [387])) := by rfl

theorem source_387_0 (code : Nat) :
    edgeSource 0 387 code = 839808+code/6 := by rfl

theorem target_387_0 (code : Nat) :
    edgeTarget 0 387 code = 902016+code%7776 := by rfl

theorem block_387_0 :
    savedBlockClass (75*387+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_387_0 (code : Nat) :
    weight completedCredit 0 387 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 387 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_387_0 direction_387.1
    direction_387.2.1 conditioned_387 code

theorem conditional_387_0 (code : Nat) :
    weight conditionalCredit 0 387 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 387 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_387_0 direction_387.1
    direction_387.2.2 conditioned_387 code
#print axioms selected_387_0
#print axioms source_387_0
#print axioms target_387_0
#print axioms block_387_0
#print axioms completed_387_0
#print axioms conditional_387_0

theorem selected_388_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [388])) := by rfl

theorem source_388_0 (code : Nat) :
    edgeSource 0 388 code = 847584+code/6 := by rfl

theorem target_388_0 (code : Nat) :
    edgeTarget 0 388 code = 909792+code%7776 := by rfl

theorem block_388_0 :
    savedBlockClass (75*388+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_388_0 (code : Nat) :
    weight completedCredit 0 388 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 388 [] 18 16
    (fun code => 0) selected_388_0 direction_388.1
    direction_388.2.1 conditioned_388 code

theorem conditional_388_0 (code : Nat) :
    weight conditionalCredit 0 388 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 388 [] 18 16
    (fun code => 0) selected_388_0 direction_388.1
    direction_388.2.2 conditioned_388 code
#print axioms selected_388_0
#print axioms source_388_0
#print axioms target_388_0
#print axioms block_388_0
#print axioms completed_388_0
#print axioms conditional_388_0

theorem selected_389_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [389])) := by rfl

theorem source_389_0 (code : Nat) :
    edgeSource 0 389 code = 847584+code/6 := by rfl

theorem target_389_0 (code : Nat) :
    edgeTarget 0 389 code = 917568+code%7776 := by rfl

theorem block_389_0 :
    savedBlockClass (75*389+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_389_0 (code : Nat) :
    weight completedCredit 0 389 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 389 [] 18 16
    (fun code => 0) selected_389_0 direction_389.1
    direction_389.2.1 conditioned_389 code

theorem conditional_389_0 (code : Nat) :
    weight conditionalCredit 0 389 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 389 [] 18 16
    (fun code => 0) selected_389_0 direction_389.1
    direction_389.2.2 conditioned_389 code
#print axioms selected_389_0
#print axioms source_389_0
#print axioms target_389_0
#print axioms block_389_0
#print axioms completed_389_0
#print axioms conditional_389_0

theorem selected_390_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [390])) := by rfl

theorem source_390_0 (code : Nat) :
    edgeSource 0 390 code = 847584+code/6 := by rfl

theorem target_390_0 (code : Nat) :
    edgeTarget 0 390 code = 925344+code%7776 := by rfl

theorem block_390_0 :
    savedBlockClass (75*390+0) = some 76 ∧
    recordedClassRoot 76 = 3519 := by decide +kernel

theorem completed_390_0 (code : Nat) :
    weight completedCredit 0 390 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 390 [] 6 0
    (fun code => 0) selected_390_0 direction_390.1
    direction_390.2.1 conditioned_390 code

theorem conditional_390_0 (code : Nat) :
    weight conditionalCredit 0 390 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 390 [] 6 16
    (fun code => 0) selected_390_0 direction_390.1
    direction_390.2.2 conditioned_390 code
#print axioms selected_390_0
#print axioms source_390_0
#print axioms target_390_0
#print axioms block_390_0
#print axioms completed_390_0
#print axioms conditional_390_0

theorem selected_391_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [391])) := by rfl

theorem source_391_0 (code : Nat) :
    edgeSource 0 391 code = 847584+code/6 := by rfl

theorem target_391_0 (code : Nat) :
    edgeTarget 0 391 code = 933120+code%7776 := by rfl

theorem block_391_0 :
    savedBlockClass (75*391+0) = some 77 ∧
    recordedClassRoot 77 = 3522 := by decide +kernel

theorem completed_391_0 (code : Nat) :
    weight completedCredit 0 391 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 391 [] 12 16
    (fun code => 0) selected_391_0 direction_391.1
    direction_391.2.1 conditioned_391 code

theorem conditional_391_0 (code : Nat) :
    weight conditionalCredit 0 391 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 391 [] 12 16
    (fun code => 0) selected_391_0 direction_391.1
    direction_391.2.2 conditioned_391 code
#print axioms selected_391_0
#print axioms source_391_0
#print axioms target_391_0
#print axioms block_391_0
#print axioms completed_391_0
#print axioms conditional_391_0

theorem selected_392_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [392])) := by rfl

theorem source_392_0 (code : Nat) :
    edgeSource 0 392 code = 847584+code/6 := by rfl

theorem target_392_0 (code : Nat) :
    edgeTarget 0 392 code = 940896+code%7776 := by rfl

theorem block_392_0 :
    savedBlockClass (75*392+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_392_0 (code : Nat) :
    weight completedCredit 0 392 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 392 [] 18 16
    (fun code => 0) selected_392_0 direction_392.1
    direction_392.2.1 conditioned_392 code

theorem conditional_392_0 (code : Nat) :
    weight conditionalCredit 0 392 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 392 [] 18 16
    (fun code => 0) selected_392_0 direction_392.1
    direction_392.2.2 conditioned_392 code
#print axioms selected_392_0
#print axioms source_392_0
#print axioms target_392_0
#print axioms block_392_0
#print axioms completed_392_0
#print axioms conditional_392_0

theorem selected_393_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [393])) := by rfl

theorem source_393_0 (code : Nat) :
    edgeSource 0 393 code = 855360+code/6 := by rfl

theorem target_393_0 (code : Nat) :
    edgeTarget 0 393 code = 948672+code%7776 := by rfl

theorem block_393_0 :
    savedBlockClass (75*393+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_393_0 (code : Nat) :
    weight completedCredit 0 393 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 393 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_393_0 direction_393.1
    direction_393.2.1 conditioned_393 code

theorem conditional_393_0 (code : Nat) :
    weight conditionalCredit 0 393 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 393 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_393_0 direction_393.1
    direction_393.2.2 conditioned_393 code
#print axioms selected_393_0
#print axioms source_393_0
#print axioms target_393_0
#print axioms block_393_0
#print axioms completed_393_0
#print axioms conditional_393_0

theorem selected_393_17 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 17 [] ++ [393])) := by rfl

theorem source_393_17 (code : Nat) :
    edgeSource 17 393 code = 1150848+code/6 := by rfl

theorem target_393_17 (code : Nat) :
    edgeTarget 17 393 code = 948672+code%7776 := by rfl

theorem block_393_17 :
    savedBlockClass (75*393+17) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_393_17 (code : Nat) :
    weight completedCredit 17 393 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 17 393 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_393_17 direction_393.1
    direction_393.2.1 conditioned_393 code

theorem conditional_393_17 (code : Nat) :
    weight conditionalCredit 17 393 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 17 393 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_393_17 direction_393.1
    direction_393.2.2 conditioned_393 code
#print axioms selected_393_17
#print axioms source_393_17
#print axioms target_393_17
#print axioms block_393_17
#print axioms completed_393_17
#print axioms conditional_393_17

end Snake9.Context101
