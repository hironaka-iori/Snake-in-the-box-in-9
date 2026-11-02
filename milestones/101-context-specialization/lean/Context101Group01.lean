import Direction101Group00
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

theorem selected_51_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [51])) := by rfl

theorem source_51_0 (code : Nat) :
    edgeSource 0 51 code = 116640+code/6 := by rfl

theorem target_51_0 (code : Nat) :
    edgeTarget 0 51 code = 622080+code%7776 := by rfl

theorem block_51_0 :
    savedBlockClass (75*51+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_51_0 (code : Nat) :
    weight completedCredit 0 51 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 51 [] 0 16
    (fun code => 0) selected_51_0 direction_51.1
    direction_51.2.1 conditioned_51 code

theorem conditional_51_0 (code : Nat) :
    weight conditionalCredit 0 51 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 51 [] 0 16
    (fun code => 0) selected_51_0 direction_51.1
    direction_51.2.2 conditioned_51 code
#print axioms selected_51_0
#print axioms source_51_0
#print axioms target_51_0
#print axioms block_51_0
#print axioms completed_51_0
#print axioms conditional_51_0

theorem selected_51_11 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 11 [] ++ [51])) := by rfl

theorem source_51_11 (code : Nat) :
    edgeSource 11 51 code = 1104192+code/6 := by rfl

theorem target_51_11 (code : Nat) :
    edgeTarget 11 51 code = 622080+code%7776 := by rfl

theorem block_51_11 :
    savedBlockClass (75*51+11) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_51_11 (code : Nat) :
    weight completedCredit 11 51 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 11 51 [] 0 16
    (fun code => 0) selected_51_11 direction_51.1
    direction_51.2.1 conditioned_51 code

theorem conditional_51_11 (code : Nat) :
    weight conditionalCredit 11 51 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 11 51 [] 0 16
    (fun code => 0) selected_51_11 direction_51.1
    direction_51.2.2 conditioned_51 code
#print axioms selected_51_11
#print axioms source_51_11
#print axioms target_51_11
#print axioms block_51_11
#print axioms completed_51_11
#print axioms conditional_51_11

theorem selected_52_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [52])) := by rfl

theorem source_52_0 (code : Nat) :
    edgeSource 0 52 code = 116640+code/6 := by rfl

theorem target_52_0 (code : Nat) :
    edgeTarget 0 52 code = 629856+code%7776 := by rfl

theorem block_52_0 :
    savedBlockClass (75*52+0) = some 35 ∧
    recordedClassRoot 35 = 2722 := by decide +kernel

theorem completed_52_0 (code : Nat) :
    weight completedCredit 0 52 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 52 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_52_0 direction_52.1
    direction_52.2.1 conditioned_52 code

theorem conditional_52_0 (code : Nat) :
    weight conditionalCredit 0 52 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 52 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_52_0 direction_52.1
    direction_52.2.2 conditioned_52 code
#print axioms selected_52_0
#print axioms source_52_0
#print axioms target_52_0
#print axioms block_52_0
#print axioms completed_52_0
#print axioms conditional_52_0

theorem selected_52_11 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 11 [] ++ [52])) := by rfl

theorem source_52_11 (code : Nat) :
    edgeSource 11 52 code = 1104192+code/6 := by rfl

theorem target_52_11 (code : Nat) :
    edgeTarget 11 52 code = 629856+code%7776 := by rfl

theorem block_52_11 :
    savedBlockClass (75*52+11) = some 35 ∧
    recordedClassRoot 35 = 2722 := by decide +kernel

theorem completed_52_11 (code : Nat) :
    weight completedCredit 11 52 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 11 52 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_52_11 direction_52.1
    direction_52.2.1 conditioned_52 code

theorem conditional_52_11 (code : Nat) :
    weight conditionalCredit 11 52 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 11 52 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_52_11 direction_52.1
    direction_52.2.2 conditioned_52 code
#print axioms selected_52_11
#print axioms source_52_11
#print axioms target_52_11
#print axioms block_52_11
#print axioms completed_52_11
#print axioms conditional_52_11

theorem selected_53_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [53])) := by rfl

theorem source_53_0 (code : Nat) :
    edgeSource 0 53 code = 116640+code/6 := by rfl

theorem target_53_0 (code : Nat) :
    edgeTarget 0 53 code = 637632+code%7776 := by rfl

theorem block_53_0 :
    savedBlockClass (75*53+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_53_0 (code : Nat) :
    weight completedCredit 0 53 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 53 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_53_0 direction_53.1
    direction_53.2.1 conditioned_53 code

theorem conditional_53_0 (code : Nat) :
    weight conditionalCredit 0 53 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 53 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_53_0 direction_53.1
    direction_53.2.2 conditioned_53 code
#print axioms selected_53_0
#print axioms source_53_0
#print axioms target_53_0
#print axioms block_53_0
#print axioms completed_53_0
#print axioms conditional_53_0

theorem selected_53_11 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 11 [] ++ [53])) := by rfl

theorem source_53_11 (code : Nat) :
    edgeSource 11 53 code = 1104192+code/6 := by rfl

theorem target_53_11 (code : Nat) :
    edgeTarget 11 53 code = 637632+code%7776 := by rfl

theorem block_53_11 :
    savedBlockClass (75*53+11) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_53_11 (code : Nat) :
    weight completedCredit 11 53 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 11 53 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_53_11 direction_53.1
    direction_53.2.1 conditioned_53 code

theorem conditional_53_11 (code : Nat) :
    weight conditionalCredit 11 53 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 11 53 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_53_11 direction_53.1
    direction_53.2.2 conditioned_53 code
#print axioms selected_53_11
#print axioms source_53_11
#print axioms target_53_11
#print axioms block_53_11
#print axioms completed_53_11
#print axioms conditional_53_11

theorem selected_54_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [54])) := by rfl

theorem source_54_0 (code : Nat) :
    edgeSource 0 54 code = 124416+code/6 := by rfl

theorem target_54_0 (code : Nat) :
    edgeTarget 0 54 code = 1057536+code%7776 := by rfl

theorem block_54_0 :
    savedBlockClass (75*54+0) = some 36 ∧
    recordedClassRoot 36 = 2814 := by decide +kernel

theorem completed_54_0 (code : Nat) :
    weight completedCredit 0 54 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 54 [] 6 16
    (fun code => 0) selected_54_0 direction_54.1
    direction_54.2.1 conditioned_54 code

theorem conditional_54_0 (code : Nat) :
    weight conditionalCredit 0 54 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 54 [] 6 16
    (fun code => 0) selected_54_0 direction_54.1
    direction_54.2.2 conditioned_54 code
#print axioms selected_54_0
#print axioms source_54_0
#print axioms target_54_0
#print axioms block_54_0
#print axioms completed_54_0
#print axioms conditional_54_0

theorem selected_54_12 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 12 [] ++ [54])) := by rfl

theorem source_54_12 (code : Nat) :
    edgeSource 12 54 code = 1111968+code/6 := by rfl

theorem target_54_12 (code : Nat) :
    edgeTarget 12 54 code = 1376352+code%7776 := by rfl

theorem block_54_12 :
    savedBlockClass (75*54+12) = some 36 ∧
    recordedClassRoot 36 = 2814 := by decide +kernel

theorem completed_54_12 (code : Nat) :
    weight completedCredit 12 54 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 12 54 [] 6 16
    (fun code => 0) selected_54_12 direction_54.1
    direction_54.2.1 conditioned_54 code

theorem conditional_54_12 (code : Nat) :
    weight conditionalCredit 12 54 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 12 54 [] 6 16
    (fun code => 0) selected_54_12 direction_54.1
    direction_54.2.2 conditioned_54 code
#print axioms selected_54_12
#print axioms source_54_12
#print axioms target_54_12
#print axioms block_54_12
#print axioms completed_54_12
#print axioms conditional_54_12

theorem selected_54_62 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 62 [] ++ [54])) := by rfl

theorem source_54_62 (code : Nat) :
    edgeSource 62 54 code = 1500768+code/6 := by rfl

theorem target_54_62 (code : Nat) :
    edgeTarget 62 54 code = 1376352+code%7776 := by rfl

theorem block_54_62 :
    savedBlockClass (75*54+62) = some 36 ∧
    recordedClassRoot 36 = 2814 := by decide +kernel

theorem completed_54_62 (code : Nat) :
    weight completedCredit 62 54 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 62 54 [] 6 16
    (fun code => 0) selected_54_62 direction_54.1
    direction_54.2.1 conditioned_54 code

theorem conditional_54_62 (code : Nat) :
    weight conditionalCredit 62 54 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 62 54 [] 6 16
    (fun code => 0) selected_54_62 direction_54.1
    direction_54.2.2 conditioned_54 code
#print axioms selected_54_62
#print axioms source_54_62
#print axioms target_54_62
#print axioms block_54_62
#print axioms completed_54_62
#print axioms conditional_54_62

theorem selected_55_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [55])) := by rfl

theorem source_55_0 (code : Nat) :
    edgeSource 0 55 code = 124416+code/6 := by rfl

theorem target_55_0 (code : Nat) :
    edgeTarget 0 55 code = 684288+code%7776 := by rfl

theorem block_55_0 :
    savedBlockClass (75*55+0) = some 36 ∧
    recordedClassRoot 36 = 2814 := by decide +kernel

theorem completed_55_0 (code : Nat) :
    weight completedCredit 0 55 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 55 [] 6 16
    (fun code => 0) selected_55_0 direction_55.1
    direction_55.2.1 conditioned_55 code

theorem conditional_55_0 (code : Nat) :
    weight conditionalCredit 0 55 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 55 [] 6 16
    (fun code => 0) selected_55_0 direction_55.1
    direction_55.2.2 conditioned_55 code
#print axioms selected_55_0
#print axioms source_55_0
#print axioms target_55_0
#print axioms block_55_0
#print axioms completed_55_0
#print axioms conditional_55_0

theorem selected_55_12 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 12 [] ++ [55])) := by rfl

theorem source_55_12 (code : Nat) :
    edgeSource 12 55 code = 1111968+code/6 := by rfl

theorem target_55_12 (code : Nat) :
    edgeTarget 12 55 code = 1384128+code%7776 := by rfl

theorem block_55_12 :
    savedBlockClass (75*55+12) = some 36 ∧
    recordedClassRoot 36 = 2814 := by decide +kernel

theorem completed_55_12 (code : Nat) :
    weight completedCredit 12 55 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 12 55 [] 6 16
    (fun code => 0) selected_55_12 direction_55.1
    direction_55.2.1 conditioned_55 code

theorem conditional_55_12 (code : Nat) :
    weight conditionalCredit 12 55 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 12 55 [] 6 16
    (fun code => 0) selected_55_12 direction_55.1
    direction_55.2.2 conditioned_55 code
#print axioms selected_55_12
#print axioms source_55_12
#print axioms target_55_12
#print axioms block_55_12
#print axioms completed_55_12
#print axioms conditional_55_12

theorem selected_55_62 :
    [rule038] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 62 [] ++ [55])) := by rfl

theorem source_55_62 (code : Nat) :
    edgeSource 62 55 code = 1500768+code/6 := by rfl

theorem target_55_62 (code : Nat) :
    edgeTarget 62 55 code = 1384128+code%7776 := by rfl

theorem block_55_62 :
    savedBlockClass (75*55+62) = some 36 ∧
    recordedClassRoot 36 = 2814 := by decide +kernel

theorem completed_55_62 (code : Nat) :
    weight completedCredit 62 55 code =
      120*(code%6+1)+max (max 6 (emittedCredit [rule038] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 62 55 [rule038] 6 16
    (fun code => 0) selected_55_62 direction_55.1
    direction_55.2.1 conditioned_55 code

theorem conditional_55_62 (code : Nat) :
    weight conditionalCredit 62 55 code =
      120*(code%6+1)+max (max 6 (emittedCredit [rule038] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 62 55 [rule038] 6 16
    (fun code => 0) selected_55_62 direction_55.1
    direction_55.2.2 conditioned_55 code
#print axioms selected_55_62
#print axioms source_55_62
#print axioms target_55_62
#print axioms block_55_62
#print axioms completed_55_62
#print axioms conditional_55_62

theorem selected_56_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [56])) := by rfl

theorem source_56_0 (code : Nat) :
    edgeSource 0 56 code = 132192+code/6 := by rfl

theorem target_56_0 (code : Nat) :
    edgeTarget 0 56 code = 645408+code%7776 := by rfl

theorem block_56_0 :
    savedBlockClass (75*56+0) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_56_0 (code : Nat) :
    weight completedCredit 0 56 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 56 [] 22 0
    (fun code => 0) selected_56_0 direction_56.1
    direction_56.2.1 conditioned_56 code

theorem conditional_56_0 (code : Nat) :
    weight conditionalCredit 0 56 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 56 [] 22 16
    (fun code => 0) selected_56_0 direction_56.1
    direction_56.2.2 conditioned_56 code
#print axioms selected_56_0
#print axioms source_56_0
#print axioms target_56_0
#print axioms block_56_0
#print axioms completed_56_0
#print axioms conditional_56_0

theorem selected_57_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [57])) := by rfl

theorem source_57_0 (code : Nat) :
    edgeSource 0 57 code = 132192+code/6 := by rfl

theorem target_57_0 (code : Nat) :
    edgeTarget 0 57 code = 668736+code%7776 := by rfl

theorem block_57_0 :
    savedBlockClass (75*57+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_57_0 (code : Nat) :
    weight completedCredit 0 57 code =
      120*(code%6+1)+max (max 31 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 57 [] 31 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_57_0 direction_57.1
    direction_57.2.1 conditioned_57 code

theorem conditional_57_0 (code : Nat) :
    weight conditionalCredit 0 57 code =
      120*(code%6+1)+max (max 31 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 57 [] 31 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_57_0 direction_57.1
    direction_57.2.2 conditioned_57 code
#print axioms selected_57_0
#print axioms source_57_0
#print axioms target_57_0
#print axioms block_57_0
#print axioms completed_57_0
#print axioms conditional_57_0

theorem selected_58_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [58])) := by rfl

theorem source_58_0 (code : Nat) :
    edgeSource 0 58 code = 139968+code/6 := by rfl

theorem target_58_0 (code : Nat) :
    edgeTarget 0 58 code = 699840+code%7776 := by rfl

theorem block_58_0 :
    savedBlockClass (75*58+0) = some 39 ∧
    recordedClassRoot 39 = 3055 := by decide +kernel

theorem completed_58_0 (code : Nat) :
    weight completedCredit 0 58 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 58 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_58_0 direction_58.1
    direction_58.2.1 conditioned_58 code

theorem conditional_58_0 (code : Nat) :
    weight conditionalCredit 0 58 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 58 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_58_0 direction_58.1
    direction_58.2.2 conditioned_58 code
#print axioms selected_58_0
#print axioms source_58_0
#print axioms target_58_0
#print axioms block_58_0
#print axioms completed_58_0
#print axioms conditional_58_0

theorem selected_59_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [59])) := by rfl

theorem source_59_0 (code : Nat) :
    edgeSource 0 59 code = 147744+code/6 := by rfl

theorem target_59_0 (code : Nat) :
    edgeTarget 0 59 code = 715392+code%7776 := by rfl

theorem block_59_0 :
    savedBlockClass (75*59+0) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_59_0 (code : Nat) :
    weight completedCredit 0 59 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 59 [] 13 0
    (fun code => 0) selected_59_0 direction_59.1
    direction_59.2.1 conditioned_59 code

theorem conditional_59_0 (code : Nat) :
    weight conditionalCredit 0 59 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 59 [] 13 16
    (fun code => 0) selected_59_0 direction_59.1
    direction_59.2.2 conditioned_59 code
#print axioms selected_59_0
#print axioms source_59_0
#print axioms target_59_0
#print axioms block_59_0
#print axioms completed_59_0
#print axioms conditional_59_0

theorem selected_60_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [60])) := by rfl

theorem source_60_0 (code : Nat) :
    edgeSource 0 60 code = 147744+code/6 := by rfl

theorem target_60_0 (code : Nat) :
    edgeTarget 0 60 code = 707616+code%7776 := by rfl

theorem block_60_0 :
    savedBlockClass (75*60+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_60_0 (code : Nat) :
    weight completedCredit 0 60 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 60 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_60_0 direction_60.1
    direction_60.2.1 conditioned_60 code

theorem conditional_60_0 (code : Nat) :
    weight conditionalCredit 0 60 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 60 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_60_0 direction_60.1
    direction_60.2.2 conditioned_60 code
#print axioms selected_60_0
#print axioms source_60_0
#print axioms target_60_0
#print axioms block_60_0
#print axioms completed_60_0
#print axioms conditional_60_0

theorem selected_61_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [61])) := by rfl

theorem source_61_0 (code : Nat) :
    edgeSource 0 61 code = 147744+code/6 := by rfl

theorem target_61_0 (code : Nat) :
    edgeTarget 0 61 code = 723168+code%7776 := by rfl

theorem block_61_0 :
    savedBlockClass (75*61+0) = some 40 ∧
    recordedClassRoot 40 = 3139 := by decide +kernel

theorem completed_61_0 (code : Nat) :
    weight completedCredit 0 61 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 61 [] 13 16
    (fun code => 0) selected_61_0 direction_61.1
    direction_61.2.1 conditioned_61 code

theorem conditional_61_0 (code : Nat) :
    weight conditionalCredit 0 61 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 61 [] 13 16
    (fun code => 0) selected_61_0 direction_61.1
    direction_61.2.2 conditioned_61 code
#print axioms selected_61_0
#print axioms source_61_0
#print axioms target_61_0
#print axioms block_61_0
#print axioms completed_61_0
#print axioms conditional_61_0

theorem selected_62_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [62])) := by rfl

theorem source_62_0 (code : Nat) :
    edgeSource 0 62 code = 147744+code/6 := by rfl

theorem target_62_0 (code : Nat) :
    edgeTarget 0 62 code = 730944+code%7776 := by rfl

theorem block_62_0 :
    savedBlockClass (75*62+0) = some 41 ∧
    recordedClassRoot 41 = 3215 := by decide +kernel

theorem completed_62_0 (code : Nat) :
    weight completedCredit 0 62 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 62 [] 13 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_62_0 direction_62.1
    direction_62.2.1 conditioned_62 code

theorem conditional_62_0 (code : Nat) :
    weight conditionalCredit 0 62 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 62 [] 13 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_62_0 direction_62.1
    direction_62.2.2 conditioned_62 code
#print axioms selected_62_0
#print axioms source_62_0
#print axioms target_62_0
#print axioms block_62_0
#print axioms completed_62_0
#print axioms conditional_62_0

theorem selected_63_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [63])) := by rfl

theorem source_63_0 (code : Nat) :
    edgeSource 0 63 code = 147744+code/6 := by rfl

theorem target_63_0 (code : Nat) :
    edgeTarget 0 63 code = 738720+code%7776 := by rfl

theorem block_63_0 :
    savedBlockClass (75*63+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_63_0 (code : Nat) :
    weight completedCredit 0 63 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 63 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_63_0 direction_63.1
    direction_63.2.1 conditioned_63 code

theorem conditional_63_0 (code : Nat) :
    weight conditionalCredit 0 63 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 63 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_63_0 direction_63.1
    direction_63.2.2 conditioned_63 code
#print axioms selected_63_0
#print axioms source_63_0
#print axioms target_63_0
#print axioms block_63_0
#print axioms completed_63_0
#print axioms conditional_63_0

theorem selected_64_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [64])) := by rfl

theorem source_64_0 (code : Nat) :
    edgeSource 0 64 code = 155520+code/6 := by rfl

theorem target_64_0 (code : Nat) :
    edgeTarget 0 64 code = 909792+code%7776 := by rfl

theorem block_64_0 :
    savedBlockClass (75*64+0) = some 26 ∧
    recordedClassRoot 26 = 2626 := by decide +kernel

theorem completed_64_0 (code : Nat) :
    weight completedCredit 0 64 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 64 [] 18 16
    (fun code => 0) selected_64_0 direction_64.1
    direction_64.2.1 conditioned_64 code

theorem conditional_64_0 (code : Nat) :
    weight conditionalCredit 0 64 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 64 [] 18 16
    (fun code => 0) selected_64_0 direction_64.1
    direction_64.2.2 conditioned_64 code
#print axioms selected_64_0
#print axioms source_64_0
#print axioms target_64_0
#print axioms block_64_0
#print axioms completed_64_0
#print axioms conditional_64_0

theorem selected_65_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [65])) := by rfl

theorem source_65_0 (code : Nat) :
    edgeSource 0 65 code = 155520+code/6 := by rfl

theorem target_65_0 (code : Nat) :
    edgeTarget 0 65 code = 917568+code%7776 := by rfl

theorem block_65_0 :
    savedBlockClass (75*65+0) = some 26 ∧
    recordedClassRoot 26 = 2626 := by decide +kernel

theorem completed_65_0 (code : Nat) :
    weight completedCredit 0 65 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 65 [] 18 16
    (fun code => 0) selected_65_0 direction_65.1
    direction_65.2.1 conditioned_65 code

theorem conditional_65_0 (code : Nat) :
    weight conditionalCredit 0 65 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 65 [] 18 16
    (fun code => 0) selected_65_0 direction_65.1
    direction_65.2.2 conditioned_65 code
#print axioms selected_65_0
#print axioms source_65_0
#print axioms target_65_0
#print axioms block_65_0
#print axioms completed_65_0
#print axioms conditional_65_0

theorem selected_66_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [66])) := by rfl

theorem source_66_0 (code : Nat) :
    edgeSource 0 66 code = 155520+code/6 := by rfl

theorem target_66_0 (code : Nat) :
    edgeTarget 0 66 code = 1065312+code%7776 := by rfl

theorem block_66_0 :
    savedBlockClass (75*66+0) = some 42 ∧
    recordedClassRoot 42 = 3221 := by decide +kernel

theorem completed_66_0 (code : Nat) :
    weight completedCredit 0 66 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 66 [] 6 0
    (fun code => 0) selected_66_0 direction_66.1
    direction_66.2.1 conditioned_66 code

theorem conditional_66_0 (code : Nat) :
    weight conditionalCredit 0 66 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 66 [] 6 16
    (fun code => 0) selected_66_0 direction_66.1
    direction_66.2.2 conditioned_66 code
#print axioms selected_66_0
#print axioms source_66_0
#print axioms target_66_0
#print axioms block_66_0
#print axioms completed_66_0
#print axioms conditional_66_0

theorem selected_67_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [67])) := by rfl

theorem source_67_0 (code : Nat) :
    edgeSource 0 67 code = 155520+code/6 := by rfl

theorem target_67_0 (code : Nat) :
    edgeTarget 0 67 code = 933120+code%7776 := by rfl

theorem block_67_0 :
    savedBlockClass (75*67+0) = some 28 ∧
    recordedClassRoot 28 = 2684 := by decide +kernel

theorem completed_67_0 (code : Nat) :
    weight completedCredit 0 67 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 67 [] 12 16
    (fun code => 0) selected_67_0 direction_67.1
    direction_67.2.1 conditioned_67 code

theorem conditional_67_0 (code : Nat) :
    weight conditionalCredit 0 67 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 67 [] 12 16
    (fun code => 0) selected_67_0 direction_67.1
    direction_67.2.2 conditioned_67 code
#print axioms selected_67_0
#print axioms source_67_0
#print axioms target_67_0
#print axioms block_67_0
#print axioms completed_67_0
#print axioms conditional_67_0

theorem selected_68_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [68])) := by rfl

theorem source_68_0 (code : Nat) :
    edgeSource 0 68 code = 155520+code/6 := by rfl

theorem target_68_0 (code : Nat) :
    edgeTarget 0 68 code = 940896+code%7776 := by rfl

theorem block_68_0 :
    savedBlockClass (75*68+0) = some 26 ∧
    recordedClassRoot 26 = 2626 := by decide +kernel

theorem completed_68_0 (code : Nat) :
    weight completedCredit 0 68 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 68 [] 18 16
    (fun code => 0) selected_68_0 direction_68.1
    direction_68.2.1 conditioned_68 code

theorem conditional_68_0 (code : Nat) :
    weight conditionalCredit 0 68 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 68 [] 18 16
    (fun code => 0) selected_68_0 direction_68.1
    direction_68.2.2 conditioned_68 code
#print axioms selected_68_0
#print axioms source_68_0
#print axioms target_68_0
#print axioms block_68_0
#print axioms completed_68_0
#print axioms conditional_68_0

theorem selected_69_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [69])) := by rfl

theorem source_69_0 (code : Nat) :
    edgeSource 0 69 code = 163296+code/6 := by rfl

theorem target_69_0 (code : Nat) :
    edgeTarget 0 69 code = 839808+code%7776 := by rfl

theorem block_69_0 :
    savedBlockClass (75*69+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_69_0 (code : Nat) :
    weight completedCredit 0 69 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 69 [] 0 0
    (fun code => 0) selected_69_0 direction_69.1
    direction_69.2.1 conditioned_69 code

theorem conditional_69_0 (code : Nat) :
    weight conditionalCredit 0 69 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 69 [] 0 16
    (fun code => 0) selected_69_0 direction_69.1
    direction_69.2.2 conditioned_69 code
#print axioms selected_69_0
#print axioms source_69_0
#print axioms target_69_0
#print axioms block_69_0
#print axioms completed_69_0
#print axioms conditional_69_0

theorem selected_69_58 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 58 [] ++ [69])) := by rfl

theorem source_69_58 (code : Nat) :
    edgeSource 58 69 code = 1469664+code/6 := by rfl

theorem target_69_58 (code : Nat) :
    edgeTarget 58 69 code = 839808+code%7776 := by rfl

theorem block_69_58 :
    savedBlockClass (75*69+58) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_69_58 (code : Nat) :
    weight completedCredit 58 69 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 58 69 [] 0 0
    (fun code => 0) selected_69_58 direction_69.1
    direction_69.2.1 conditioned_69 code

theorem conditional_69_58 (code : Nat) :
    weight conditionalCredit 58 69 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 58 69 [] 0 16
    (fun code => 0) selected_69_58 direction_69.1
    direction_69.2.2 conditioned_69 code
#print axioms selected_69_58
#print axioms source_69_58
#print axioms target_69_58
#print axioms block_69_58
#print axioms completed_69_58
#print axioms conditional_69_58

theorem selected_69_63 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 63 [] ++ [69])) := by rfl

theorem source_69_63 (code : Nat) :
    edgeSource 63 69 code = 1508544+code/6 := by rfl

theorem target_69_63 (code : Nat) :
    edgeTarget 63 69 code = 839808+code%7776 := by rfl

theorem block_69_63 :
    savedBlockClass (75*69+63) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_69_63 (code : Nat) :
    weight completedCredit 63 69 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 63 69 [] 0 0
    (fun code => 0) selected_69_63 direction_69.1
    direction_69.2.1 conditioned_69 code

theorem conditional_69_63 (code : Nat) :
    weight conditionalCredit 63 69 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 63 69 [] 0 16
    (fun code => 0) selected_69_63 direction_69.1
    direction_69.2.2 conditioned_69 code
#print axioms selected_69_63
#print axioms source_69_63
#print axioms target_69_63
#print axioms block_69_63
#print axioms completed_69_63
#print axioms conditional_69_63

theorem selected_70_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [70])) := by rfl

theorem source_70_0 (code : Nat) :
    edgeSource 0 70 code = 163296+code/6 := by rfl

theorem target_70_0 (code : Nat) :
    edgeTarget 0 70 code = 832032+code%7776 := by rfl

theorem block_70_0 :
    savedBlockClass (75*70+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_70_0 (code : Nat) :
    weight completedCredit 0 70 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 70 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_70_0 direction_70.1
    direction_70.2.1 conditioned_70 code

theorem conditional_70_0 (code : Nat) :
    weight conditionalCredit 0 70 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 70 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_70_0 direction_70.1
    direction_70.2.2 conditioned_70 code
#print axioms selected_70_0
#print axioms source_70_0
#print axioms target_70_0
#print axioms block_70_0
#print axioms completed_70_0
#print axioms conditional_70_0

theorem selected_70_58 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 58 [] ++ [70])) := by rfl

theorem source_70_58 (code : Nat) :
    edgeSource 58 70 code = 1469664+code/6 := by rfl

theorem target_70_58 (code : Nat) :
    edgeTarget 58 70 code = 832032+code%7776 := by rfl

theorem block_70_58 :
    savedBlockClass (75*70+58) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_70_58 (code : Nat) :
    weight completedCredit 58 70 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 58 70 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_70_58 direction_70.1
    direction_70.2.1 conditioned_70 code

theorem conditional_70_58 (code : Nat) :
    weight conditionalCredit 58 70 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 58 70 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_70_58 direction_70.1
    direction_70.2.2 conditioned_70 code
#print axioms selected_70_58
#print axioms source_70_58
#print axioms target_70_58
#print axioms block_70_58
#print axioms completed_70_58
#print axioms conditional_70_58

theorem selected_70_63 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 63 [] ++ [70])) := by rfl

theorem source_70_63 (code : Nat) :
    edgeSource 63 70 code = 1508544+code/6 := by rfl

theorem target_70_63 (code : Nat) :
    edgeTarget 63 70 code = 832032+code%7776 := by rfl

theorem block_70_63 :
    savedBlockClass (75*70+63) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_70_63 (code : Nat) :
    weight completedCredit 63 70 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 63 70 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_70_63 direction_70.1
    direction_70.2.1 conditioned_70 code

theorem conditional_70_63 (code : Nat) :
    weight conditionalCredit 63 70 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 63 70 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_70_63 direction_70.1
    direction_70.2.2 conditioned_70 code
#print axioms selected_70_63
#print axioms source_70_63
#print axioms target_70_63
#print axioms block_70_63
#print axioms completed_70_63
#print axioms conditional_70_63

theorem selected_71_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [71])) := by rfl

theorem source_71_0 (code : Nat) :
    edgeSource 0 71 code = 163296+code/6 := by rfl

theorem target_71_0 (code : Nat) :
    edgeTarget 0 71 code = 847584+code%7776 := by rfl

theorem block_71_0 :
    savedBlockClass (75*71+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_71_0 (code : Nat) :
    weight completedCredit 0 71 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 71 [] 0 16
    (fun code => 0) selected_71_0 direction_71.1
    direction_71.2.1 conditioned_71 code

theorem conditional_71_0 (code : Nat) :
    weight conditionalCredit 0 71 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 71 [] 0 16
    (fun code => 0) selected_71_0 direction_71.1
    direction_71.2.2 conditioned_71 code
#print axioms selected_71_0
#print axioms source_71_0
#print axioms target_71_0
#print axioms block_71_0
#print axioms completed_71_0
#print axioms conditional_71_0

theorem selected_71_58 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 58 [] ++ [71])) := by rfl

theorem source_71_58 (code : Nat) :
    edgeSource 58 71 code = 1469664+code/6 := by rfl

theorem target_71_58 (code : Nat) :
    edgeTarget 58 71 code = 847584+code%7776 := by rfl

theorem block_71_58 :
    savedBlockClass (75*71+58) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_71_58 (code : Nat) :
    weight completedCredit 58 71 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 58 71 [] 0 16
    (fun code => 0) selected_71_58 direction_71.1
    direction_71.2.1 conditioned_71 code

theorem conditional_71_58 (code : Nat) :
    weight conditionalCredit 58 71 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 58 71 [] 0 16
    (fun code => 0) selected_71_58 direction_71.1
    direction_71.2.2 conditioned_71 code
#print axioms selected_71_58
#print axioms source_71_58
#print axioms target_71_58
#print axioms block_71_58
#print axioms completed_71_58
#print axioms conditional_71_58

theorem selected_71_63 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 63 [] ++ [71])) := by rfl

theorem source_71_63 (code : Nat) :
    edgeSource 63 71 code = 1508544+code/6 := by rfl

theorem target_71_63 (code : Nat) :
    edgeTarget 63 71 code = 847584+code%7776 := by rfl

theorem block_71_63 :
    savedBlockClass (75*71+63) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_71_63 (code : Nat) :
    weight completedCredit 63 71 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 63 71 [] 0 16
    (fun code => 0) selected_71_63 direction_71.1
    direction_71.2.1 conditioned_71 code

theorem conditional_71_63 (code : Nat) :
    weight conditionalCredit 63 71 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 63 71 [] 0 16
    (fun code => 0) selected_71_63 direction_71.1
    direction_71.2.2 conditioned_71 code
#print axioms selected_71_63
#print axioms source_71_63
#print axioms target_71_63
#print axioms block_71_63
#print axioms completed_71_63
#print axioms conditional_71_63

theorem selected_72_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [72])) := by rfl

theorem source_72_0 (code : Nat) :
    edgeSource 0 72 code = 163296+code/6 := by rfl

theorem target_72_0 (code : Nat) :
    edgeTarget 0 72 code = 855360+code%7776 := by rfl

theorem block_72_0 :
    savedBlockClass (75*72+0) = some 35 ∧
    recordedClassRoot 35 = 2722 := by decide +kernel

theorem completed_72_0 (code : Nat) :
    weight completedCredit 0 72 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 72 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_72_0 direction_72.1
    direction_72.2.1 conditioned_72 code

theorem conditional_72_0 (code : Nat) :
    weight conditionalCredit 0 72 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 72 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_72_0 direction_72.1
    direction_72.2.2 conditioned_72 code
#print axioms selected_72_0
#print axioms source_72_0
#print axioms target_72_0
#print axioms block_72_0
#print axioms completed_72_0
#print axioms conditional_72_0

theorem selected_72_58 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 58 [] ++ [72])) := by rfl

theorem source_72_58 (code : Nat) :
    edgeSource 58 72 code = 1469664+code/6 := by rfl

theorem target_72_58 (code : Nat) :
    edgeTarget 58 72 code = 855360+code%7776 := by rfl

theorem block_72_58 :
    savedBlockClass (75*72+58) = some 35 ∧
    recordedClassRoot 35 = 2722 := by decide +kernel

theorem completed_72_58 (code : Nat) :
    weight completedCredit 58 72 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 58 72 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_72_58 direction_72.1
    direction_72.2.1 conditioned_72 code

theorem conditional_72_58 (code : Nat) :
    weight conditionalCredit 58 72 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 58 72 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_72_58 direction_72.1
    direction_72.2.2 conditioned_72 code
#print axioms selected_72_58
#print axioms source_72_58
#print axioms target_72_58
#print axioms block_72_58
#print axioms completed_72_58
#print axioms conditional_72_58

theorem selected_72_63 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 63 [] ++ [72])) := by rfl

theorem source_72_63 (code : Nat) :
    edgeSource 63 72 code = 1508544+code/6 := by rfl

theorem target_72_63 (code : Nat) :
    edgeTarget 63 72 code = 855360+code%7776 := by rfl

theorem block_72_63 :
    savedBlockClass (75*72+63) = some 35 ∧
    recordedClassRoot 35 = 2722 := by decide +kernel

theorem completed_72_63 (code : Nat) :
    weight completedCredit 63 72 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 63 72 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_72_63 direction_72.1
    direction_72.2.1 conditioned_72 code

theorem conditional_72_63 (code : Nat) :
    weight conditionalCredit 63 72 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 63 72 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_72_63 direction_72.1
    direction_72.2.2 conditioned_72 code
#print axioms selected_72_63
#print axioms source_72_63
#print axioms target_72_63
#print axioms block_72_63
#print axioms completed_72_63
#print axioms conditional_72_63

theorem selected_73_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [73])) := by rfl

theorem source_73_0 (code : Nat) :
    edgeSource 0 73 code = 163296+code/6 := by rfl

theorem target_73_0 (code : Nat) :
    edgeTarget 0 73 code = 863136+code%7776 := by rfl

theorem block_73_0 :
    savedBlockClass (75*73+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_73_0 (code : Nat) :
    weight completedCredit 0 73 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 73 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_73_0 direction_73.1
    direction_73.2.1 conditioned_73 code

theorem conditional_73_0 (code : Nat) :
    weight conditionalCredit 0 73 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 73 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_73_0 direction_73.1
    direction_73.2.2 conditioned_73 code
#print axioms selected_73_0
#print axioms source_73_0
#print axioms target_73_0
#print axioms block_73_0
#print axioms completed_73_0
#print axioms conditional_73_0

theorem selected_73_58 :
    [rule007] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 58 [] ++ [73])) := by rfl

theorem source_73_58 (code : Nat) :
    edgeSource 58 73 code = 1469664+code/6 := by rfl

theorem target_73_58 (code : Nat) :
    edgeTarget 58 73 code = 863136+code%7776 := by rfl

theorem block_73_58 :
    savedBlockClass (75*73+58) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_73_58 (code : Nat) :
    weight completedCredit 58 73 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule007] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 58 73 [rule007] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_73_58 direction_73.1
    direction_73.2.1 conditioned_73 code

theorem conditional_73_58 (code : Nat) :
    weight conditionalCredit 58 73 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule007] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 58 73 [rule007] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_73_58 direction_73.1
    direction_73.2.2 conditioned_73 code
#print axioms selected_73_58
#print axioms source_73_58
#print axioms target_73_58
#print axioms block_73_58
#print axioms completed_73_58
#print axioms conditional_73_58

theorem selected_73_63 :
    [rule039] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 63 [] ++ [73])) := by rfl

theorem source_73_63 (code : Nat) :
    edgeSource 63 73 code = 1508544+code/6 := by rfl

theorem target_73_63 (code : Nat) :
    edgeTarget 63 73 code = 863136+code%7776 := by rfl

theorem block_73_63 :
    savedBlockClass (75*73+63) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_73_63 (code : Nat) :
    weight completedCredit 63 73 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule039] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 63 73 [rule039] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_73_63 direction_73.1
    direction_73.2.1 conditioned_73 code

theorem conditional_73_63 (code : Nat) :
    weight conditionalCredit 63 73 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule039] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 63 73 [rule039] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_73_63 direction_73.1
    direction_73.2.2 conditioned_73 code
#print axioms selected_73_63
#print axioms source_73_63
#print axioms target_73_63
#print axioms block_73_63
#print axioms completed_73_63
#print axioms conditional_73_63

theorem selected_74_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [74])) := by rfl

theorem source_74_0 (code : Nat) :
    edgeSource 0 74 code = 171072+code/6 := by rfl

theorem target_74_0 (code : Nat) :
    edgeTarget 0 74 code = 878688+code%7776 := by rfl

theorem block_74_0 :
    savedBlockClass (75*74+0) = some 29 ∧
    recordedClassRoot 29 = 2691 := by decide +kernel

theorem completed_74_0 (code : Nat) :
    weight completedCredit 0 74 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 74 [] 0 0
    (fun code => 0) selected_74_0 direction_74.1
    direction_74.2.1 conditioned_74 code

theorem conditional_74_0 (code : Nat) :
    weight conditionalCredit 0 74 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 74 [] 0 16
    (fun code => 0) selected_74_0 direction_74.1
    direction_74.2.2 conditioned_74 code
#print axioms selected_74_0
#print axioms source_74_0
#print axioms target_74_0
#print axioms block_74_0
#print axioms completed_74_0
#print axioms conditional_74_0

theorem selected_74_59 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 59 [] ++ [74])) := by rfl

theorem source_74_59 (code : Nat) :
    edgeSource 59 74 code = 1477440+code/6 := by rfl

theorem target_74_59 (code : Nat) :
    edgeTarget 59 74 code = 878688+code%7776 := by rfl

theorem block_74_59 :
    savedBlockClass (75*74+59) = some 29 ∧
    recordedClassRoot 29 = 2691 := by decide +kernel

theorem completed_74_59 (code : Nat) :
    weight completedCredit 59 74 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 59 74 [] 0 0
    (fun code => 0) selected_74_59 direction_74.1
    direction_74.2.1 conditioned_74 code

theorem conditional_74_59 (code : Nat) :
    weight conditionalCredit 59 74 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 59 74 [] 0 16
    (fun code => 0) selected_74_59 direction_74.1
    direction_74.2.2 conditioned_74 code
#print axioms selected_74_59
#print axioms source_74_59
#print axioms target_74_59
#print axioms block_74_59
#print axioms completed_74_59
#print axioms conditional_74_59

theorem selected_74_64 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 64 [] ++ [74])) := by rfl

theorem source_74_64 (code : Nat) :
    edgeSource 64 74 code = 1516320+code/6 := by rfl

theorem target_74_64 (code : Nat) :
    edgeTarget 64 74 code = 878688+code%7776 := by rfl

theorem block_74_64 :
    savedBlockClass (75*74+64) = some 29 ∧
    recordedClassRoot 29 = 2691 := by decide +kernel

theorem completed_74_64 (code : Nat) :
    weight completedCredit 64 74 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 64 74 [] 0 0
    (fun code => 0) selected_74_64 direction_74.1
    direction_74.2.1 conditioned_74 code

theorem conditional_74_64 (code : Nat) :
    weight conditionalCredit 64 74 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 64 74 [] 0 16
    (fun code => 0) selected_74_64 direction_74.1
    direction_74.2.2 conditioned_74 code
#print axioms selected_74_64
#print axioms source_74_64
#print axioms target_74_64
#print axioms block_74_64
#print axioms completed_74_64
#print axioms conditional_74_64

theorem selected_75_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [75])) := by rfl

theorem source_75_0 (code : Nat) :
    edgeSource 0 75 code = 171072+code/6 := by rfl

theorem target_75_0 (code : Nat) :
    edgeTarget 0 75 code = 870912+code%7776 := by rfl

theorem block_75_0 :
    savedBlockClass (75*75+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_75_0 (code : Nat) :
    weight completedCredit 0 75 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 75 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_75_0 direction_75.1
    direction_75.2.1 conditioned_75 code

theorem conditional_75_0 (code : Nat) :
    weight conditionalCredit 0 75 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 75 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_75_0 direction_75.1
    direction_75.2.2 conditioned_75 code
#print axioms selected_75_0
#print axioms source_75_0
#print axioms target_75_0
#print axioms block_75_0
#print axioms completed_75_0
#print axioms conditional_75_0

theorem selected_75_59 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 59 [] ++ [75])) := by rfl

theorem source_75_59 (code : Nat) :
    edgeSource 59 75 code = 1477440+code/6 := by rfl

theorem target_75_59 (code : Nat) :
    edgeTarget 59 75 code = 870912+code%7776 := by rfl

theorem block_75_59 :
    savedBlockClass (75*75+59) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_75_59 (code : Nat) :
    weight completedCredit 59 75 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 59 75 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_75_59 direction_75.1
    direction_75.2.1 conditioned_75 code

theorem conditional_75_59 (code : Nat) :
    weight conditionalCredit 59 75 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 59 75 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_75_59 direction_75.1
    direction_75.2.2 conditioned_75 code
#print axioms selected_75_59
#print axioms source_75_59
#print axioms target_75_59
#print axioms block_75_59
#print axioms completed_75_59
#print axioms conditional_75_59

theorem selected_75_64 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 64 [] ++ [75])) := by rfl

theorem source_75_64 (code : Nat) :
    edgeSource 64 75 code = 1516320+code/6 := by rfl

theorem target_75_64 (code : Nat) :
    edgeTarget 64 75 code = 870912+code%7776 := by rfl

theorem block_75_64 :
    savedBlockClass (75*75+64) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_75_64 (code : Nat) :
    weight completedCredit 64 75 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 64 75 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_75_64 direction_75.1
    direction_75.2.1 conditioned_75 code

theorem conditional_75_64 (code : Nat) :
    weight conditionalCredit 64 75 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 64 75 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_75_64 direction_75.1
    direction_75.2.2 conditioned_75 code
#print axioms selected_75_64
#print axioms source_75_64
#print axioms target_75_64
#print axioms block_75_64
#print axioms completed_75_64
#print axioms conditional_75_64

theorem selected_76_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [76])) := by rfl

theorem source_76_0 (code : Nat) :
    edgeSource 0 76 code = 171072+code/6 := by rfl

theorem target_76_0 (code : Nat) :
    edgeTarget 0 76 code = 886464+code%7776 := by rfl

theorem block_76_0 :
    savedBlockClass (75*76+0) = some 43 ∧
    recordedClassRoot 43 = 3318 := by decide +kernel

theorem completed_76_0 (code : Nat) :
    weight completedCredit 0 76 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 76 [] 0 16
    (fun code => 0) selected_76_0 direction_76.1
    direction_76.2.1 conditioned_76 code

theorem conditional_76_0 (code : Nat) :
    weight conditionalCredit 0 76 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 76 [] 0 16
    (fun code => 0) selected_76_0 direction_76.1
    direction_76.2.2 conditioned_76 code
#print axioms selected_76_0
#print axioms source_76_0
#print axioms target_76_0
#print axioms block_76_0
#print axioms completed_76_0
#print axioms conditional_76_0

theorem selected_76_59 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 59 [] ++ [76])) := by rfl

theorem source_76_59 (code : Nat) :
    edgeSource 59 76 code = 1477440+code/6 := by rfl

theorem target_76_59 (code : Nat) :
    edgeTarget 59 76 code = 886464+code%7776 := by rfl

theorem block_76_59 :
    savedBlockClass (75*76+59) = some 43 ∧
    recordedClassRoot 43 = 3318 := by decide +kernel

theorem completed_76_59 (code : Nat) :
    weight completedCredit 59 76 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 59 76 [] 0 16
    (fun code => 0) selected_76_59 direction_76.1
    direction_76.2.1 conditioned_76 code

theorem conditional_76_59 (code : Nat) :
    weight conditionalCredit 59 76 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 59 76 [] 0 16
    (fun code => 0) selected_76_59 direction_76.1
    direction_76.2.2 conditioned_76 code
#print axioms selected_76_59
#print axioms source_76_59
#print axioms target_76_59
#print axioms block_76_59
#print axioms completed_76_59
#print axioms conditional_76_59

theorem selected_76_64 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 64 [] ++ [76])) := by rfl

theorem source_76_64 (code : Nat) :
    edgeSource 64 76 code = 1516320+code/6 := by rfl

theorem target_76_64 (code : Nat) :
    edgeTarget 64 76 code = 886464+code%7776 := by rfl

theorem block_76_64 :
    savedBlockClass (75*76+64) = some 43 ∧
    recordedClassRoot 43 = 3318 := by decide +kernel

theorem completed_76_64 (code : Nat) :
    weight completedCredit 64 76 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 64 76 [] 0 16
    (fun code => 0) selected_76_64 direction_76.1
    direction_76.2.1 conditioned_76 code

theorem conditional_76_64 (code : Nat) :
    weight conditionalCredit 64 76 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 64 76 [] 0 16
    (fun code => 0) selected_76_64 direction_76.1
    direction_76.2.2 conditioned_76 code
#print axioms selected_76_64
#print axioms source_76_64
#print axioms target_76_64
#print axioms block_76_64
#print axioms completed_76_64
#print axioms conditional_76_64

theorem selected_77_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [77])) := by rfl

theorem source_77_0 (code : Nat) :
    edgeSource 0 77 code = 171072+code/6 := by rfl

theorem target_77_0 (code : Nat) :
    edgeTarget 0 77 code = 894240+code%7776 := by rfl

theorem block_77_0 :
    savedBlockClass (75*77+0) = some 44 ∧
    recordedClassRoot 44 = 3365 := by decide +kernel

theorem completed_77_0 (code : Nat) :
    weight completedCredit 0 77 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 77 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_77_0 direction_77.1
    direction_77.2.1 conditioned_77 code

theorem conditional_77_0 (code : Nat) :
    weight conditionalCredit 0 77 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 77 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_77_0 direction_77.1
    direction_77.2.2 conditioned_77 code
#print axioms selected_77_0
#print axioms source_77_0
#print axioms target_77_0
#print axioms block_77_0
#print axioms completed_77_0
#print axioms conditional_77_0

theorem selected_77_59 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 59 [] ++ [77])) := by rfl

theorem source_77_59 (code : Nat) :
    edgeSource 59 77 code = 1477440+code/6 := by rfl

theorem target_77_59 (code : Nat) :
    edgeTarget 59 77 code = 894240+code%7776 := by rfl

theorem block_77_59 :
    savedBlockClass (75*77+59) = some 44 ∧
    recordedClassRoot 44 = 3365 := by decide +kernel

theorem completed_77_59 (code : Nat) :
    weight completedCredit 59 77 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 59 77 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_77_59 direction_77.1
    direction_77.2.1 conditioned_77 code

theorem conditional_77_59 (code : Nat) :
    weight conditionalCredit 59 77 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 59 77 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_77_59 direction_77.1
    direction_77.2.2 conditioned_77 code
#print axioms selected_77_59
#print axioms source_77_59
#print axioms target_77_59
#print axioms block_77_59
#print axioms completed_77_59
#print axioms conditional_77_59

theorem selected_77_64 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 64 [] ++ [77])) := by rfl

theorem source_77_64 (code : Nat) :
    edgeSource 64 77 code = 1516320+code/6 := by rfl

theorem target_77_64 (code : Nat) :
    edgeTarget 64 77 code = 894240+code%7776 := by rfl

theorem block_77_64 :
    savedBlockClass (75*77+64) = some 44 ∧
    recordedClassRoot 44 = 3365 := by decide +kernel

theorem completed_77_64 (code : Nat) :
    weight completedCredit 64 77 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 64 77 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_77_64 direction_77.1
    direction_77.2.1 conditioned_77 code

theorem conditional_77_64 (code : Nat) :
    weight conditionalCredit 64 77 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 64 77 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_77_64 direction_77.1
    direction_77.2.2 conditioned_77 code
#print axioms selected_77_64
#print axioms source_77_64
#print axioms target_77_64
#print axioms block_77_64
#print axioms completed_77_64
#print axioms conditional_77_64

theorem selected_78_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [78])) := by rfl

theorem source_78_0 (code : Nat) :
    edgeSource 0 78 code = 171072+code/6 := by rfl

theorem target_78_0 (code : Nat) :
    edgeTarget 0 78 code = 902016+code%7776 := by rfl

theorem block_78_0 :
    savedBlockClass (75*78+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_78_0 (code : Nat) :
    weight completedCredit 0 78 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 78 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_78_0 direction_78.1
    direction_78.2.1 conditioned_78 code

theorem conditional_78_0 (code : Nat) :
    weight conditionalCredit 0 78 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 78 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_78_0 direction_78.1
    direction_78.2.2 conditioned_78 code
#print axioms selected_78_0
#print axioms source_78_0
#print axioms target_78_0
#print axioms block_78_0
#print axioms completed_78_0
#print axioms conditional_78_0

theorem selected_78_59 :
    [rule035] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 59 [] ++ [78])) := by rfl

theorem source_78_59 (code : Nat) :
    edgeSource 59 78 code = 1477440+code/6 := by rfl

theorem target_78_59 (code : Nat) :
    edgeTarget 59 78 code = 902016+code%7776 := by rfl

theorem block_78_59 :
    savedBlockClass (75*78+59) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_78_59 (code : Nat) :
    weight completedCredit 59 78 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule035] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 59 78 [rule035] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_78_59 direction_78.1
    direction_78.2.1 conditioned_78 code

theorem conditional_78_59 (code : Nat) :
    weight conditionalCredit 59 78 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule035] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 59 78 [rule035] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_78_59 direction_78.1
    direction_78.2.2 conditioned_78 code
#print axioms selected_78_59
#print axioms source_78_59
#print axioms target_78_59
#print axioms block_78_59
#print axioms completed_78_59
#print axioms conditional_78_59

theorem selected_78_64 :
    [rule040] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 64 [] ++ [78])) := by rfl

theorem source_78_64 (code : Nat) :
    edgeSource 64 78 code = 1516320+code/6 := by rfl

theorem target_78_64 (code : Nat) :
    edgeTarget 64 78 code = 902016+code%7776 := by rfl

theorem block_78_64 :
    savedBlockClass (75*78+64) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_78_64 (code : Nat) :
    weight completedCredit 64 78 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule040] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 64 78 [rule040] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_78_64 direction_78.1
    direction_78.2.1 conditioned_78 code

theorem conditional_78_64 (code : Nat) :
    weight conditionalCredit 64 78 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule040] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 64 78 [rule040] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_78_64 direction_78.1
    direction_78.2.2 conditioned_78 code
#print axioms selected_78_64
#print axioms source_78_64
#print axioms target_78_64
#print axioms block_78_64
#print axioms completed_78_64
#print axioms conditional_78_64

theorem selected_79_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [79])) := by rfl

theorem source_79_0 (code : Nat) :
    edgeSource 0 79 code = 178848+code/6 := by rfl

theorem target_79_0 (code : Nat) :
    edgeTarget 0 79 code = 964224+code%7776 := by rfl

theorem block_79_0 :
    savedBlockClass (75*79+0) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_79_0 (code : Nat) :
    weight completedCredit 0 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 79 [] 0 12
    (fun code => 0) selected_79_0 direction_79.1
    direction_79.2.1 conditioned_79 code

theorem conditional_79_0 (code : Nat) :
    weight conditionalCredit 0 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 79 [] 0 12
    (fun code => 0) selected_79_0 direction_79.1
    direction_79.2.2 conditioned_79 code
#print axioms selected_79_0
#print axioms source_79_0
#print axioms target_79_0
#print axioms block_79_0
#print axioms completed_79_0
#print axioms conditional_79_0

theorem selected_79_13 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 13 [] ++ [79])) := by rfl

theorem source_79_13 (code : Nat) :
    edgeSource 13 79 code = 1119744+code/6 := by rfl

theorem target_79_13 (code : Nat) :
    edgeTarget 13 79 code = 1391904+code%7776 := by rfl

theorem block_79_13 :
    savedBlockClass (75*79+13) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_79_13 (code : Nat) :
    weight completedCredit 13 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 13 79 [] 0 12
    (fun code => 0) selected_79_13 direction_79.1
    direction_79.2.1 conditioned_79 code

theorem conditional_79_13 (code : Nat) :
    weight conditionalCredit 13 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 13 79 [] 0 12
    (fun code => 0) selected_79_13 direction_79.1
    direction_79.2.2 conditioned_79 code
#print axioms selected_79_13
#print axioms source_79_13
#print axioms target_79_13
#print axioms block_79_13
#print axioms completed_79_13
#print axioms conditional_79_13

theorem selected_79_15 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 15 [] ++ [79])) := by rfl

theorem source_79_15 (code : Nat) :
    edgeSource 15 79 code = 1135296+code/6 := by rfl

theorem target_79_15 (code : Nat) :
    edgeTarget 15 79 code = 1415232+code%7776 := by rfl

theorem block_79_15 :
    savedBlockClass (75*79+15) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_79_15 (code : Nat) :
    weight completedCredit 15 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 15 79 [] 0 12
    (fun code => 0) selected_79_15 direction_79.1
    direction_79.2.1 conditioned_79 code

theorem conditional_79_15 (code : Nat) :
    weight conditionalCredit 15 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 15 79 [] 0 12
    (fun code => 0) selected_79_15 direction_79.1
    direction_79.2.2 conditioned_79 code
#print axioms selected_79_15
#print axioms source_79_15
#print axioms target_79_15
#print axioms block_79_15
#print axioms completed_79_15
#print axioms conditional_79_15

theorem selected_79_32 :
    [rule008] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 32 [] ++ [79])) := by rfl

theorem source_79_32 (code : Nat) :
    edgeSource 32 79 code = 1267488+code/6 := by rfl

theorem target_79_32 (code : Nat) :
    edgeTarget 32 79 code = 1391904+code%7776 := by rfl

theorem block_79_32 :
    savedBlockClass (75*79+32) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_79_32 (code : Nat) :
    weight completedCredit 32 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule008] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 32 79 [rule008] 0 12
    (fun code => 0) selected_79_32 direction_79.1
    direction_79.2.1 conditioned_79 code

theorem conditional_79_32 (code : Nat) :
    weight conditionalCredit 32 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule008] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 32 79 [rule008] 0 12
    (fun code => 0) selected_79_32 direction_79.1
    direction_79.2.2 conditioned_79 code
#print axioms selected_79_32
#print axioms source_79_32
#print axioms target_79_32
#print axioms block_79_32
#print axioms completed_79_32
#print axioms conditional_79_32

theorem selected_79_34 :
    [rule011] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 34 [] ++ [79])) := by rfl

theorem source_79_34 (code : Nat) :
    edgeSource 34 79 code = 1283040+code/6 := by rfl

theorem target_79_34 (code : Nat) :
    edgeTarget 34 79 code = 1415232+code%7776 := by rfl

theorem block_79_34 :
    savedBlockClass (75*79+34) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_79_34 (code : Nat) :
    weight completedCredit 34 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule011] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 34 79 [rule011] 0 12
    (fun code => 0) selected_79_34 direction_79.1
    direction_79.2.1 conditioned_79 code

theorem conditional_79_34 (code : Nat) :
    weight conditionalCredit 34 79 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule011] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 34 79 [rule011] 0 12
    (fun code => 0) selected_79_34 direction_79.1
    direction_79.2.2 conditioned_79 code
#print axioms selected_79_34
#print axioms source_79_34
#print axioms target_79_34
#print axioms block_79_34
#print axioms completed_79_34
#print axioms conditional_79_34

theorem selected_80_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [80])) := by rfl

theorem source_80_0 (code : Nat) :
    edgeSource 0 80 code = 178848+code/6 := by rfl

theorem target_80_0 (code : Nat) :
    edgeTarget 0 80 code = 948672+code%7776 := by rfl

theorem block_80_0 :
    savedBlockClass (75*80+0) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_80_0 (code : Nat) :
    weight completedCredit 0 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_0 direction_80.1
    direction_80.2.1 conditioned_80 code

theorem conditional_80_0 (code : Nat) :
    weight conditionalCredit 0 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_0 direction_80.1
    direction_80.2.2 conditioned_80 code
#print axioms selected_80_0
#print axioms source_80_0
#print axioms target_80_0
#print axioms block_80_0
#print axioms completed_80_0
#print axioms conditional_80_0

theorem selected_80_13 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 13 [] ++ [80])) := by rfl

theorem source_80_13 (code : Nat) :
    edgeSource 13 80 code = 1119744+code/6 := by rfl

theorem target_80_13 (code : Nat) :
    edgeTarget 13 80 code = 948672+code%7776 := by rfl

theorem block_80_13 :
    savedBlockClass (75*80+13) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_80_13 (code : Nat) :
    weight completedCredit 13 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 13 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_13 direction_80.1
    direction_80.2.1 conditioned_80 code

theorem conditional_80_13 (code : Nat) :
    weight conditionalCredit 13 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 13 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_13 direction_80.1
    direction_80.2.2 conditioned_80 code
#print axioms selected_80_13
#print axioms source_80_13
#print axioms target_80_13
#print axioms block_80_13
#print axioms completed_80_13
#print axioms conditional_80_13

theorem selected_80_15 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 15 [] ++ [80])) := by rfl

theorem source_80_15 (code : Nat) :
    edgeSource 15 80 code = 1135296+code/6 := by rfl

theorem target_80_15 (code : Nat) :
    edgeTarget 15 80 code = 948672+code%7776 := by rfl

theorem block_80_15 :
    savedBlockClass (75*80+15) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_80_15 (code : Nat) :
    weight completedCredit 15 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 15 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_15 direction_80.1
    direction_80.2.1 conditioned_80 code

theorem conditional_80_15 (code : Nat) :
    weight conditionalCredit 15 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 15 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_15 direction_80.1
    direction_80.2.2 conditioned_80 code
#print axioms selected_80_15
#print axioms source_80_15
#print axioms target_80_15
#print axioms block_80_15
#print axioms completed_80_15
#print axioms conditional_80_15

theorem selected_80_32 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 32 [] ++ [80])) := by rfl

theorem source_80_32 (code : Nat) :
    edgeSource 32 80 code = 1267488+code/6 := by rfl

theorem target_80_32 (code : Nat) :
    edgeTarget 32 80 code = 948672+code%7776 := by rfl

theorem block_80_32 :
    savedBlockClass (75*80+32) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_80_32 (code : Nat) :
    weight completedCredit 32 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 32 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_32 direction_80.1
    direction_80.2.1 conditioned_80 code

theorem conditional_80_32 (code : Nat) :
    weight conditionalCredit 32 80 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 32 80 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_80_32 direction_80.1
    direction_80.2.2 conditioned_80 code
#print axioms selected_80_32
#print axioms source_80_32
#print axioms target_80_32
#print axioms block_80_32
#print axioms completed_80_32
#print axioms conditional_80_32

end Snake9.Context101
