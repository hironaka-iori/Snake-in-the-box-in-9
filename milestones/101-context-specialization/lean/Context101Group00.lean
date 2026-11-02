import ContextPilot101
import EmittingPilot101
import Direction101Group00

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_2_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [2])) := by rfl

theorem source_2_0 (code : Nat) :
    edgeSource 0 2 code = 0+code/6 := by rfl

theorem target_2_0 (code : Nat) :
    edgeTarget 0 2 code = 241056+code%7776 := by rfl

theorem block_2_0 :
    savedBlockClass (75*2+0) = some 2 ∧
    recordedClassRoot 2 = 521 := by decide +kernel

theorem completed_2_0 (code : Nat) :
    weight completedCredit 0 2 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 2 [] 10 16
    (fun code => 0) selected_2_0 direction_2.1
    direction_2.2.1 conditioned_2 code

theorem conditional_2_0 (code : Nat) :
    weight conditionalCredit 0 2 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 2 [] 10 16
    (fun code => 0) selected_2_0 direction_2.1
    direction_2.2.2 conditioned_2 code
#print axioms selected_2_0
#print axioms source_2_0
#print axioms target_2_0
#print axioms block_2_0
#print axioms completed_2_0
#print axioms conditional_2_0

theorem selected_3_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [3])) := by rfl

theorem source_3_0 (code : Nat) :
    edgeSource 0 3 code = 0+code/6 := by rfl

theorem target_3_0 (code : Nat) :
    edgeTarget 0 3 code = 248832+code%7776 := by rfl

theorem block_3_0 :
    savedBlockClass (75*3+0) = some 1 ∧
    recordedClassRoot 1 = 379 := by decide +kernel

theorem completed_3_0 (code : Nat) :
    weight completedCredit 0 3 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 3 [] 12 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_3_0 direction_3.1
    direction_3.2.1 conditioned_3 code

theorem conditional_3_0 (code : Nat) :
    weight conditionalCredit 0 3 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 3 [] 12 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_3_0 direction_3.1
    direction_3.2.2 conditioned_3 code
#print axioms selected_3_0
#print axioms source_3_0
#print axioms target_3_0
#print axioms block_3_0
#print axioms completed_3_0
#print axioms conditional_3_0

theorem selected_4_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [4])) := by rfl

theorem source_4_0 (code : Nat) :
    edgeSource 0 4 code = 7776+code/6 := by rfl

theorem target_4_0 (code : Nat) :
    edgeTarget 0 4 code = 287712+code%7776 := by rfl

theorem block_4_0 :
    savedBlockClass (75*4+0) = some 3 ∧
    recordedClassRoot 3 = 669 := by decide +kernel

theorem completed_4_0 (code : Nat) :
    weight completedCredit 0 4 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 4 [] 29 16
    (fun code => 0) selected_4_0 direction_4.1
    direction_4.2.1 conditioned_4 code

theorem conditional_4_0 (code : Nat) :
    weight conditionalCredit 0 4 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 4 [] 29 16
    (fun code => 0) selected_4_0 direction_4.1
    direction_4.2.2 conditioned_4 code
#print axioms selected_4_0
#print axioms source_4_0
#print axioms target_4_0
#print axioms block_4_0
#print axioms completed_4_0
#print axioms conditional_4_0

theorem selected_5_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [5])) := by rfl

theorem source_5_0 (code : Nat) :
    edgeSource 0 5 code = 7776+code/6 := by rfl

theorem target_5_0 (code : Nat) :
    edgeTarget 0 5 code = 295488+code%7776 := by rfl

theorem block_5_0 :
    savedBlockClass (75*5+0) = some 4 ∧
    recordedClassRoot 4 = 846 := by decide +kernel

theorem completed_5_0 (code : Nat) :
    weight completedCredit 0 5 code =
      120*(code%6+1)+max (max 31 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 5 [] 31 16
    (fun code => 0) selected_5_0 direction_5.1
    direction_5.2.1 conditioned_5 code

theorem conditional_5_0 (code : Nat) :
    weight conditionalCredit 0 5 code =
      120*(code%6+1)+max (max 31 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 5 [] 31 16
    (fun code => 0) selected_5_0 direction_5.1
    direction_5.2.2 conditioned_5 code
#print axioms selected_5_0
#print axioms source_5_0
#print axioms target_5_0
#print axioms block_5_0
#print axioms completed_5_0
#print axioms conditional_5_0

theorem selected_6_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [6])) := by rfl

theorem source_6_0 (code : Nat) :
    edgeSource 0 6 code = 7776+code/6 := by rfl

theorem target_6_0 (code : Nat) :
    edgeTarget 0 6 code = 303264+code%7776 := by rfl

theorem block_6_0 :
    savedBlockClass (75*6+0) = some 5 ∧
    recordedClassRoot 5 = 1008 := by decide +kernel

theorem completed_6_0 (code : Nat) :
    weight completedCredit 0 6 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 6 [] 21 0
    (fun code => 0) selected_6_0 direction_6.1
    direction_6.2.1 conditioned_6 code

theorem conditional_6_0 (code : Nat) :
    weight conditionalCredit 0 6 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 6 [] 21 16
    (fun code => 0) selected_6_0 direction_6.1
    direction_6.2.2 conditioned_6 code
#print axioms selected_6_0
#print axioms source_6_0
#print axioms target_6_0
#print axioms block_6_0
#print axioms completed_6_0
#print axioms conditional_6_0

theorem selected_7_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [7])) := by rfl

theorem source_7_0 (code : Nat) :
    edgeSource 0 7 code = 7776+code/6 := by rfl

theorem target_7_0 (code : Nat) :
    edgeTarget 0 7 code = 311040+code%7776 := by rfl

theorem block_7_0 :
    savedBlockClass (75*7+0) = some 4 ∧
    recordedClassRoot 4 = 846 := by decide +kernel

theorem completed_7_0 (code : Nat) :
    weight completedCredit 0 7 code =
      120*(code%6+1)+max (max 36 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 7 [] 36 16
    (fun code => 0) selected_7_0 direction_7.1
    direction_7.2.1 conditioned_7 code

theorem conditional_7_0 (code : Nat) :
    weight conditionalCredit 0 7 code =
      120*(code%6+1)+max (max 36 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 7 [] 36 16
    (fun code => 0) selected_7_0 direction_7.1
    direction_7.2.2 conditioned_7 code
#print axioms selected_7_0
#print axioms source_7_0
#print axioms target_7_0
#print axioms block_7_0
#print axioms completed_7_0
#print axioms conditional_7_0

theorem selected_8_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [8])) := by rfl

theorem source_8_0 (code : Nat) :
    edgeSource 0 8 code = 15552+code/6 := by rfl

theorem target_8_0 (code : Nat) :
    edgeTarget 0 8 code = 264384+code%7776 := by rfl

theorem block_8_0 :
    savedBlockClass (75*8+0) = some 6 ∧
    recordedClassRoot 6 = 1150 := by decide +kernel

theorem completed_8_0 (code : Nat) :
    weight completedCredit 0 8 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 8 [] 7 0
    (fun code => 0) selected_8_0 direction_8.1
    direction_8.2.1 conditioned_8 code

theorem conditional_8_0 (code : Nat) :
    weight conditionalCredit 0 8 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 8 [] 7 16
    (fun code => 0) selected_8_0 direction_8.1
    direction_8.2.2 conditioned_8 code
#print axioms selected_8_0
#print axioms source_8_0
#print axioms target_8_0
#print axioms block_8_0
#print axioms completed_8_0
#print axioms conditional_8_0

theorem selected_11_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [11])) := by rfl

theorem source_11_0 (code : Nat) :
    edgeSource 0 11 code = 23328+code/6 := by rfl

theorem target_11_0 (code : Nat) :
    edgeTarget 0 11 code = 326592+code%7776 := by rfl

theorem block_11_0 :
    savedBlockClass (75*11+0) = some 9 ∧
    recordedClassRoot 9 = 1489 := by decide +kernel

theorem completed_11_0 (code : Nat) :
    weight completedCredit 0 11 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 11 [] 7 12
    (fun code => 0) selected_11_0 direction_11.1
    direction_11.2.1 conditioned_11 code

theorem conditional_11_0 (code : Nat) :
    weight conditionalCredit 0 11 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 11 [] 7 12
    (fun code => 0) selected_11_0 direction_11.1
    direction_11.2.2 conditioned_11 code
#print axioms selected_11_0
#print axioms source_11_0
#print axioms target_11_0
#print axioms block_11_0
#print axioms completed_11_0
#print axioms conditional_11_0

theorem selected_13_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [13])) := by rfl

theorem source_13_0 (code : Nat) :
    edgeSource 0 13 code = 31104+code/6 := by rfl

theorem target_13_0 (code : Nat) :
    edgeTarget 0 13 code = 357696+code%7776 := by rfl

theorem block_13_0 :
    savedBlockClass (75*13+0) = some 11 ∧
    recordedClassRoot 11 = 1698 := by decide +kernel

theorem completed_13_0 (code : Nat) :
    weight completedCredit 0 13 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 13 [] 7 0
    (fun code => 0) selected_13_0 direction_13.1
    direction_13.2.1 conditioned_13 code

theorem conditional_13_0 (code : Nat) :
    weight conditionalCredit 0 13 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 13 [] 7 16
    (fun code => 0) selected_13_0 direction_13.1
    direction_13.2.2 conditioned_13 code
#print axioms selected_13_0
#print axioms source_13_0
#print axioms target_13_0
#print axioms block_13_0
#print axioms completed_13_0
#print axioms conditional_13_0

theorem selected_14_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [14])) := by rfl

theorem source_14_0 (code : Nat) :
    edgeSource 0 14 code = 31104+code/6 := by rfl

theorem target_14_0 (code : Nat) :
    edgeTarget 0 14 code = 342144+code%7776 := by rfl

theorem block_14_0 :
    savedBlockClass (75*14+0) = some 12 ∧
    recordedClassRoot 12 = 1807 := by decide +kernel

theorem completed_14_0 (code : Nat) :
    weight completedCredit 0 14 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 14 [] 7 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_14_0 direction_14.1
    direction_14.2.1 conditioned_14 code

theorem conditional_14_0 (code : Nat) :
    weight conditionalCredit 0 14 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 14 [] 7 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_14_0 direction_14.1
    direction_14.2.2 conditioned_14 code
#print axioms selected_14_0
#print axioms source_14_0
#print axioms target_14_0
#print axioms block_14_0
#print axioms completed_14_0
#print axioms conditional_14_0

theorem selected_15_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [15])) := by rfl

theorem source_15_0 (code : Nat) :
    edgeSource 0 15 code = 31104+code/6 := by rfl

theorem target_15_0 (code : Nat) :
    edgeTarget 0 15 code = 349920+code%7776 := by rfl

theorem block_15_0 :
    savedBlockClass (75*15+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_15_0 (code : Nat) :
    weight completedCredit 0 15 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 15 [] 7 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_15_0 direction_15.1
    direction_15.2.1 conditioned_15 code

theorem conditional_15_0 (code : Nat) :
    weight conditionalCredit 0 15 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 15 [] 7 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_15_0 direction_15.1
    direction_15.2.2 conditioned_15 code
#print axioms selected_15_0
#print axioms source_15_0
#print axioms target_15_0
#print axioms block_15_0
#print axioms completed_15_0
#print axioms conditional_15_0

theorem selected_16_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [16])) := by rfl

theorem source_16_0 (code : Nat) :
    edgeSource 0 16 code = 31104+code/6 := by rfl

theorem target_16_0 (code : Nat) :
    edgeTarget 0 16 code = 365472+code%7776 := by rfl

theorem block_16_0 :
    savedBlockClass (75*16+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_16_0 (code : Nat) :
    weight completedCredit 0 16 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 16 [] 7 16
    (fun code => 0) selected_16_0 direction_16.1
    direction_16.2.1 conditioned_16 code

theorem conditional_16_0 (code : Nat) :
    weight conditionalCredit 0 16 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 16 [] 7 16
    (fun code => 0) selected_16_0 direction_16.1
    direction_16.2.2 conditioned_16 code
#print axioms selected_16_0
#print axioms source_16_0
#print axioms target_16_0
#print axioms block_16_0
#print axioms completed_16_0
#print axioms conditional_16_0

theorem selected_17_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [17])) := by rfl

theorem source_17_0 (code : Nat) :
    edgeSource 0 17 code = 31104+code/6 := by rfl

theorem target_17_0 (code : Nat) :
    edgeTarget 0 17 code = 373248+code%7776 := by rfl

theorem block_17_0 :
    savedBlockClass (75*17+0) = some 13 ∧
    recordedClassRoot 13 = 1878 := by decide +kernel

theorem completed_17_0 (code : Nat) :
    weight completedCredit 0 17 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 17 [] 7 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_17_0 direction_17.1
    direction_17.2.1 conditioned_17 code

theorem conditional_17_0 (code : Nat) :
    weight conditionalCredit 0 17 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 17 [] 7 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_17_0 direction_17.1
    direction_17.2.2 conditioned_17 code
#print axioms selected_17_0
#print axioms source_17_0
#print axioms target_17_0
#print axioms block_17_0
#print axioms completed_17_0
#print axioms conditional_17_0

theorem selected_18_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [18])) := by rfl

theorem source_18_0 (code : Nat) :
    edgeSource 0 18 code = 38880+code/6 := by rfl

theorem target_18_0 (code : Nat) :
    edgeTarget 0 18 code = 443232+code%7776 := by rfl

theorem block_18_0 :
    savedBlockClass (75*18+0) = some 15 ∧
    recordedClassRoot 15 = 2085 := by decide +kernel

theorem completed_18_0 (code : Nat) :
    weight completedCredit 0 18 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 18 [] 12 16
    (fun code => 0) selected_18_0 direction_18.1
    direction_18.2.1 conditioned_18 code

theorem conditional_18_0 (code : Nat) :
    weight conditionalCredit 0 18 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 18 [] 12 16
    (fun code => 0) selected_18_0 direction_18.1
    direction_18.2.2 conditioned_18 code
#print axioms selected_18_0
#print axioms source_18_0
#print axioms target_18_0
#print axioms block_18_0
#print axioms completed_18_0
#print axioms conditional_18_0

theorem selected_19_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [19])) := by rfl

theorem source_19_0 (code : Nat) :
    edgeSource 0 19 code = 38880+code/6 := by rfl

theorem target_19_0 (code : Nat) :
    edgeTarget 0 19 code = 451008+code%7776 := by rfl

theorem block_19_0 :
    savedBlockClass (75*19+0) = some 16 ∧
    recordedClassRoot 16 = 2162 := by decide +kernel

theorem completed_19_0 (code : Nat) :
    weight completedCredit 0 19 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 19 [] 11 16
    (fun code => 0) selected_19_0 direction_19.1
    direction_19.2.1 conditioned_19 code

theorem conditional_19_0 (code : Nat) :
    weight conditionalCredit 0 19 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 19 [] 11 16
    (fun code => 0) selected_19_0 direction_19.1
    direction_19.2.2 conditioned_19 code
#print axioms selected_19_0
#print axioms source_19_0
#print axioms target_19_0
#print axioms block_19_0
#print axioms completed_19_0
#print axioms conditional_19_0

theorem selected_20_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [20])) := by rfl

theorem source_20_0 (code : Nat) :
    edgeSource 0 20 code = 38880+code/6 := by rfl

theorem target_20_0 (code : Nat) :
    edgeTarget 0 20 code = 458784+code%7776 := by rfl

theorem block_20_0 :
    savedBlockClass (75*20+0) = some 15 ∧
    recordedClassRoot 15 = 2085 := by decide +kernel

theorem completed_20_0 (code : Nat) :
    weight completedCredit 0 20 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 20 [] 17 16
    (fun code => 0) selected_20_0 direction_20.1
    direction_20.2.1 conditioned_20 code

theorem conditional_20_0 (code : Nat) :
    weight conditionalCredit 0 20 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 20 [] 17 16
    (fun code => 0) selected_20_0 direction_20.1
    direction_20.2.2 conditioned_20 code
#print axioms selected_20_0
#print axioms source_20_0
#print axioms target_20_0
#print axioms block_20_0
#print axioms completed_20_0
#print axioms conditional_20_0

theorem selected_21_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [21])) := by rfl

theorem source_21_0 (code : Nat) :
    edgeSource 0 21 code = 46656+code/6 := by rfl

theorem target_21_0 (code : Nat) :
    edgeTarget 0 21 code = 419904+code%7776 := by rfl

theorem block_21_0 :
    savedBlockClass (75*21+0) = some 17 ∧
    recordedClassRoot 17 = 2231 := by decide +kernel

theorem completed_21_0 (code : Nat) :
    weight completedCredit 0 21 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 21 [] 7 0
    (fun code => 0) selected_21_0 direction_21.1
    direction_21.2.1 conditioned_21 code

theorem conditional_21_0 (code : Nat) :
    weight conditionalCredit 0 21 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 21 [] 7 16
    (fun code => 0) selected_21_0 direction_21.1
    direction_21.2.2 conditioned_21 code
#print axioms selected_21_0
#print axioms source_21_0
#print axioms target_21_0
#print axioms block_21_0
#print axioms completed_21_0
#print axioms conditional_21_0

theorem selected_22_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [22])) := by rfl

theorem source_22_0 (code : Nat) :
    edgeSource 0 22 code = 46656+code/6 := by rfl

theorem target_22_0 (code : Nat) :
    edgeTarget 0 22 code = 412128+code%7776 := by rfl

theorem block_22_0 :
    savedBlockClass (75*22+0) = some 18 ∧
    recordedClassRoot 18 = 2297 := by decide +kernel

theorem completed_22_0 (code : Nat) :
    weight completedCredit 0 22 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 22 [] 17 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_22_0 direction_22.1
    direction_22.2.1 conditioned_22 code

theorem conditional_22_0 (code : Nat) :
    weight conditionalCredit 0 22 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 22 [] 17 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_22_0 direction_22.1
    direction_22.2.2 conditioned_22 code
#print axioms selected_22_0
#print axioms source_22_0
#print axioms target_22_0
#print axioms block_22_0
#print axioms completed_22_0
#print axioms conditional_22_0

theorem selected_23_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [23])) := by rfl

theorem source_23_0 (code : Nat) :
    edgeSource 0 23 code = 46656+code/6 := by rfl

theorem target_23_0 (code : Nat) :
    edgeTarget 0 23 code = 435456+code%7776 := by rfl

theorem block_23_0 :
    savedBlockClass (75*23+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_23_0 (code : Nat) :
    weight completedCredit 0 23 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 23 [] 17 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_23_0 direction_23.1
    direction_23.2.1 conditioned_23 code

theorem conditional_23_0 (code : Nat) :
    weight conditionalCredit 0 23 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 23 [] 17 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_23_0 direction_23.1
    direction_23.2.2 conditioned_23 code
#print axioms selected_23_0
#print axioms source_23_0
#print axioms target_23_0
#print axioms block_23_0
#print axioms completed_23_0
#print axioms conditional_23_0

theorem selected_24_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [24])) := by rfl

theorem source_24_0 (code : Nat) :
    edgeSource 0 24 code = 54432+code/6 := by rfl

theorem target_24_0 (code : Nat) :
    edgeTarget 0 24 code = 474336+code%7776 := by rfl

theorem block_24_0 :
    savedBlockClass (75*24+0) = some 20 ∧
    recordedClassRoot 20 = 2418 := by decide +kernel

theorem completed_24_0 (code : Nat) :
    weight completedCredit 0 24 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 24 [] 0 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_24_0 direction_24.1
    direction_24.2.1 conditioned_24 code

theorem conditional_24_0 (code : Nat) :
    weight conditionalCredit 0 24 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 24 [] 0 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_24_0 direction_24.1
    direction_24.2.2 conditioned_24 code
#print axioms selected_24_0
#print axioms source_24_0
#print axioms target_24_0
#print axioms block_24_0
#print axioms completed_24_0
#print axioms conditional_24_0

theorem selected_25_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [25])) := by rfl

theorem source_25_0 (code : Nat) :
    edgeSource 0 25 code = 62208+code/6 := by rfl

theorem target_25_0 (code : Nat) :
    edgeTarget 0 25 code = 497664+code%7776 := by rfl

theorem block_25_0 :
    savedBlockClass (75*25+0) = some 17 ∧
    recordedClassRoot 17 = 2231 := by decide +kernel

theorem completed_25_0 (code : Nat) :
    weight completedCredit 0 25 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 25 [] 4 0
    (fun code => 0) selected_25_0 direction_25.1
    direction_25.2.1 conditioned_25 code

theorem conditional_25_0 (code : Nat) :
    weight conditionalCredit 0 25 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 25 [] 4 16
    (fun code => 0) selected_25_0 direction_25.1
    direction_25.2.2 conditioned_25 code
#print axioms selected_25_0
#print axioms source_25_0
#print axioms target_25_0
#print axioms block_25_0
#print axioms completed_25_0
#print axioms conditional_25_0

theorem selected_26_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [26])) := by rfl

theorem source_26_0 (code : Nat) :
    edgeSource 0 26 code = 62208+code/6 := by rfl

theorem target_26_0 (code : Nat) :
    edgeTarget 0 26 code = 1026432+code%7776 := by rfl

theorem block_26_0 :
    savedBlockClass (75*26+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_26_0 (code : Nat) :
    weight completedCredit 0 26 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 26 [] 4 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_26_0 direction_26.1
    direction_26.2.1 conditioned_26 code

theorem conditional_26_0 (code : Nat) :
    weight conditionalCredit 0 26 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 26 [] 4 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_26_0 direction_26.1
    direction_26.2.2 conditioned_26 code
#print axioms selected_26_0
#print axioms source_26_0
#print axioms target_26_0
#print axioms block_26_0
#print axioms completed_26_0
#print axioms conditional_26_0

theorem selected_27_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [27])) := by rfl

theorem source_27_0 (code : Nat) :
    edgeSource 0 27 code = 62208+code/6 := by rfl

theorem target_27_0 (code : Nat) :
    edgeTarget 0 27 code = 1034208+code%7776 := by rfl

theorem block_27_0 :
    savedBlockClass (75*27+0) = some 18 ∧
    recordedClassRoot 18 = 2297 := by decide +kernel

theorem completed_27_0 (code : Nat) :
    weight completedCredit 0 27 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 27 [] 4 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_27_0 direction_27.1
    direction_27.2.1 conditioned_27 code

theorem conditional_27_0 (code : Nat) :
    weight conditionalCredit 0 27 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 27 [] 4 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_27_0 direction_27.1
    direction_27.2.2 conditioned_27 code
#print axioms selected_27_0
#print axioms source_27_0
#print axioms target_27_0
#print axioms block_27_0
#print axioms completed_27_0
#print axioms conditional_27_0

theorem selected_28_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [28])) := by rfl

theorem source_28_0 (code : Nat) :
    edgeSource 0 28 code = 62208+code/6 := by rfl

theorem target_28_0 (code : Nat) :
    edgeTarget 0 28 code = 505440+code%7776 := by rfl

theorem block_28_0 :
    savedBlockClass (75*28+0) = some 21 ∧
    recordedClassRoot 21 = 2479 := by decide +kernel

theorem completed_28_0 (code : Nat) :
    weight completedCredit 0 28 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 28 [] 4 16
    (fun code => 0) selected_28_0 direction_28.1
    direction_28.2.1 conditioned_28 code

theorem conditional_28_0 (code : Nat) :
    weight conditionalCredit 0 28 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 28 [] 4 16
    (fun code => 0) selected_28_0 direction_28.1
    direction_28.2.2 conditioned_28 code
#print axioms selected_28_0
#print axioms source_28_0
#print axioms target_28_0
#print axioms block_28_0
#print axioms completed_28_0
#print axioms conditional_28_0

theorem selected_29_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [29])) := by rfl

theorem source_29_0 (code : Nat) :
    edgeSource 0 29 code = 62208+code/6 := by rfl

theorem target_29_0 (code : Nat) :
    edgeTarget 0 29 code = 1041984+code%7776 := by rfl

theorem block_29_0 :
    savedBlockClass (75*29+0) = some 19 ∧
    recordedClassRoot 19 = 2355 := by decide +kernel

theorem completed_29_0 (code : Nat) :
    weight completedCredit 0 29 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 29 [] 4 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_29_0 direction_29.1
    direction_29.2.1 conditioned_29 code

theorem conditional_29_0 (code : Nat) :
    weight conditionalCredit 0 29 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 29 [] 4 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_29_0 direction_29.1
    direction_29.2.2 conditioned_29 code
#print axioms selected_29_0
#print axioms source_29_0
#print axioms target_29_0
#print axioms block_29_0
#print axioms completed_29_0
#print axioms conditional_29_0

theorem selected_30_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [30])) := by rfl

theorem source_30_0 (code : Nat) :
    edgeSource 0 30 code = 69984+code/6 := by rfl

theorem target_30_0 (code : Nat) :
    edgeTarget 0 30 code = 746496+code%7776 := by rfl

theorem block_30_0 :
    savedBlockClass (75*30+0) = some 22 ∧
    recordedClassRoot 22 = 2490 := by decide +kernel

theorem completed_30_0 (code : Nat) :
    weight completedCredit 0 30 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 30 [] 18 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_30_0 direction_30.1
    direction_30.2.1 conditioned_30 code

theorem conditional_30_0 (code : Nat) :
    weight conditionalCredit 0 30 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 30 [] 18 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_30_0 direction_30.1
    direction_30.2.2 conditioned_30 code
#print axioms selected_30_0
#print axioms source_30_0
#print axioms target_30_0
#print axioms block_30_0
#print axioms completed_30_0
#print axioms conditional_30_0

theorem selected_31_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [31])) := by rfl

theorem source_31_0 (code : Nat) :
    edgeSource 0 31 code = 69984+code/6 := by rfl

theorem target_31_0 (code : Nat) :
    edgeTarget 0 31 code = 754272+code%7776 := by rfl

theorem block_31_0 :
    savedBlockClass (75*31+0) = some 23 ∧
    recordedClassRoot 23 = 2559 := by decide +kernel

theorem completed_31_0 (code : Nat) :
    weight completedCredit 0 31 code =
      120*(code%6+1)+max (max 23 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 31 [] 23 16
    (fun code => 0) selected_31_0 direction_31.1
    direction_31.2.1 conditioned_31 code

theorem conditional_31_0 (code : Nat) :
    weight conditionalCredit 0 31 code =
      120*(code%6+1)+max (max 23 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 31 [] 23 16
    (fun code => 0) selected_31_0 direction_31.1
    direction_31.2.2 conditioned_31 code
#print axioms selected_31_0
#print axioms source_31_0
#print axioms target_31_0
#print axioms block_31_0
#print axioms completed_31_0
#print axioms conditional_31_0

theorem selected_32_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [32])) := by rfl

theorem source_32_0 (code : Nat) :
    edgeSource 0 32 code = 69984+code/6 := by rfl

theorem target_32_0 (code : Nat) :
    edgeTarget 0 32 code = 762048+code%7776 := by rfl

theorem block_32_0 :
    savedBlockClass (75*32+0) = some 24 ∧
    recordedClassRoot 24 = 2570 := by decide +kernel

theorem completed_32_0 (code : Nat) :
    weight completedCredit 0 32 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 32 [] 18 0
    (fun code => 0) selected_32_0 direction_32.1
    direction_32.2.1 conditioned_32 code

theorem conditional_32_0 (code : Nat) :
    weight conditionalCredit 0 32 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 32 [] 18 16
    (fun code => 0) selected_32_0 direction_32.1
    direction_32.2.2 conditioned_32 code
#print axioms selected_32_0
#print axioms source_32_0
#print axioms target_32_0
#print axioms block_32_0
#print axioms completed_32_0
#print axioms conditional_32_0

theorem selected_33_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [33])) := by rfl

theorem source_33_0 (code : Nat) :
    edgeSource 0 33 code = 69984+code/6 := by rfl

theorem target_33_0 (code : Nat) :
    edgeTarget 0 33 code = 769824+code%7776 := by rfl

theorem block_33_0 :
    savedBlockClass (75*33+0) = some 22 ∧
    recordedClassRoot 22 = 2490 := by decide +kernel

theorem completed_33_0 (code : Nat) :
    weight completedCredit 0 33 code =
      120*(code%6+1)+max (max 27 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 33 [] 27 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_33_0 direction_33.1
    direction_33.2.1 conditioned_33 code

theorem conditional_33_0 (code : Nat) :
    weight conditionalCredit 0 33 code =
      120*(code%6+1)+max (max 27 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 33 [] 27 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_33_0 direction_33.1
    direction_33.2.2 conditioned_33 code
#print axioms selected_33_0
#print axioms source_33_0
#print axioms target_33_0
#print axioms block_33_0
#print axioms completed_33_0
#print axioms conditional_33_0

theorem selected_34_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [34])) := by rfl

theorem source_34_0 (code : Nat) :
    edgeSource 0 34 code = 77760+code/6 := by rfl

theorem target_34_0 (code : Nat) :
    edgeTarget 0 34 code = 777600+code%7776 := by rfl

theorem block_34_0 :
    savedBlockClass (75*34+0) = some 25 ∧
    recordedClassRoot 25 = 2620 := by decide +kernel

theorem completed_34_0 (code : Nat) :
    weight completedCredit 0 34 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 34 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_34_0 direction_34.1
    direction_34.2.1 conditioned_34 code

theorem conditional_34_0 (code : Nat) :
    weight conditionalCredit 0 34 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 34 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_34_0 direction_34.1
    direction_34.2.2 conditioned_34 code
#print axioms selected_34_0
#print axioms source_34_0
#print axioms target_34_0
#print axioms block_34_0
#print axioms completed_34_0
#print axioms conditional_34_0

theorem selected_34_14 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 14 [] ++ [34])) := by rfl

theorem source_34_14 (code : Nat) :
    edgeSource 14 34 code = 1127520+code/6 := by rfl

theorem target_34_14 (code : Nat) :
    edgeTarget 14 34 code = 1399680+code%7776 := by rfl

theorem block_34_14 :
    savedBlockClass (75*34+14) = some 25 ∧
    recordedClassRoot 25 = 2620 := by decide +kernel

theorem completed_34_14 (code : Nat) :
    weight completedCredit 14 34 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 14 34 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_34_14 direction_34.1
    direction_34.2.1 conditioned_34 code

theorem conditional_34_14 (code : Nat) :
    weight conditionalCredit 14 34 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 14 34 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_34_14 direction_34.1
    direction_34.2.2 conditioned_34 code
#print axioms selected_34_14
#print axioms source_34_14
#print axioms target_34_14
#print axioms block_34_14
#print axioms completed_34_14
#print axioms conditional_34_14

theorem selected_34_60 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 60 [] ++ [34])) := by rfl

theorem source_34_60 (code : Nat) :
    edgeSource 60 34 code = 1485216+code/6 := by rfl

theorem target_34_60 (code : Nat) :
    edgeTarget 60 34 code = 777600+code%7776 := by rfl

theorem block_34_60 :
    savedBlockClass (75*34+60) = some 25 ∧
    recordedClassRoot 25 = 2620 := by decide +kernel

theorem completed_34_60 (code : Nat) :
    weight completedCredit 60 34 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 60 34 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_34_60 direction_34.1
    direction_34.2.1 conditioned_34 code

theorem conditional_34_60 (code : Nat) :
    weight conditionalCredit 60 34 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 60 34 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_34_60 direction_34.1
    direction_34.2.2 conditioned_34 code
#print axioms selected_34_60
#print axioms source_34_60
#print axioms target_34_60
#print axioms block_34_60
#print axioms completed_34_60
#print axioms conditional_34_60

theorem selected_35_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [35])) := by rfl

theorem source_35_0 (code : Nat) :
    edgeSource 0 35 code = 77760+code/6 := by rfl

theorem target_35_0 (code : Nat) :
    edgeTarget 0 35 code = 1049760+code%7776 := by rfl

theorem block_35_0 :
    savedBlockClass (75*35+0) = some 25 ∧
    recordedClassRoot 25 = 2620 := by decide +kernel

theorem completed_35_0 (code : Nat) :
    weight completedCredit 0 35 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 35 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_35_0 direction_35.1
    direction_35.2.1 conditioned_35 code

theorem conditional_35_0 (code : Nat) :
    weight conditionalCredit 0 35 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 35 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_35_0 direction_35.1
    direction_35.2.2 conditioned_35 code
#print axioms selected_35_0
#print axioms source_35_0
#print axioms target_35_0
#print axioms block_35_0
#print axioms completed_35_0
#print axioms conditional_35_0

theorem selected_35_14 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 14 [] ++ [35])) := by rfl

theorem source_35_14 (code : Nat) :
    edgeSource 14 35 code = 1127520+code/6 := by rfl

theorem target_35_14 (code : Nat) :
    edgeTarget 14 35 code = 1407456+code%7776 := by rfl

theorem block_35_14 :
    savedBlockClass (75*35+14) = some 25 ∧
    recordedClassRoot 25 = 2620 := by decide +kernel

theorem completed_35_14 (code : Nat) :
    weight completedCredit 14 35 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 14 35 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_35_14 direction_35.1
    direction_35.2.1 conditioned_35 code

theorem conditional_35_14 (code : Nat) :
    weight conditionalCredit 14 35 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 14 35 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_35_14 direction_35.1
    direction_35.2.2 conditioned_35 code
#print axioms selected_35_14
#print axioms source_35_14
#print axioms target_35_14
#print axioms block_35_14
#print axioms completed_35_14
#print axioms conditional_35_14

theorem selected_35_33 :
    [rule010] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 33 [] ++ [35])) := by rfl

theorem source_35_33 (code : Nat) :
    edgeSource 33 35 code = 1275264+code/6 := by rfl

theorem target_35_33 (code : Nat) :
    edgeTarget 33 35 code = 1407456+code%7776 := by rfl

theorem block_35_33 :
    savedBlockClass (75*35+33) = some 25 ∧
    recordedClassRoot 25 = 2620 := by decide +kernel

theorem completed_35_33 (code : Nat) :
    weight completedCredit 33 35 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule010] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 33 35 [rule010] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_35_33 direction_35.1
    direction_35.2.1 conditioned_35 code

theorem conditional_35_33 (code : Nat) :
    weight conditionalCredit 33 35 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule010] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 33 35 [rule010] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_35_33 direction_35.1
    direction_35.2.2 conditioned_35 code
#print axioms selected_35_33
#print axioms source_35_33
#print axioms target_35_33
#print axioms block_35_33
#print axioms completed_35_33
#print axioms conditional_35_33

theorem selected_35_60 :
    [rule036] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 60 [] ++ [35])) := by rfl

theorem source_35_60 (code : Nat) :
    edgeSource 60 35 code = 1485216+code/6 := by rfl

theorem target_35_60 (code : Nat) :
    edgeTarget 60 35 code = 1049760+code%7776 := by rfl

theorem block_35_60 :
    savedBlockClass (75*35+60) = some 25 ∧
    recordedClassRoot 25 = 2620 := by decide +kernel

theorem completed_35_60 (code : Nat) :
    weight completedCredit 60 35 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule036] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 60 35 [rule036] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_35_60 direction_35.1
    direction_35.2.1 conditioned_35 code

theorem conditional_35_60 (code : Nat) :
    weight conditionalCredit 60 35 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule036] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 60 35 [rule036] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_35_60 direction_35.1
    direction_35.2.2 conditioned_35 code
#print axioms selected_35_60
#print axioms source_35_60
#print axioms target_35_60
#print axioms block_35_60
#print axioms completed_35_60
#print axioms conditional_35_60

theorem selected_36_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [36])) := by rfl

theorem source_36_0 (code : Nat) :
    edgeSource 0 36 code = 85536+code/6 := by rfl

theorem target_36_0 (code : Nat) :
    edgeTarget 0 36 code = 793152+code%7776 := by rfl

theorem block_36_0 :
    savedBlockClass (75*36+0) = some 22 ∧
    recordedClassRoot 22 = 2490 := by decide +kernel

theorem completed_36_0 (code : Nat) :
    weight completedCredit 0 36 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 36 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_36_0 direction_36.1
    direction_36.2.1 conditioned_36 code

theorem conditional_36_0 (code : Nat) :
    weight conditionalCredit 0 36 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 36 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_36_0 direction_36.1
    direction_36.2.2 conditioned_36 code
#print axioms selected_36_0
#print axioms source_36_0
#print axioms target_36_0
#print axioms block_36_0
#print axioms completed_36_0
#print axioms conditional_36_0

theorem selected_36_61 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 61 [] ++ [36])) := by rfl

theorem source_36_61 (code : Nat) :
    edgeSource 61 36 code = 1492992+code/6 := by rfl

theorem target_36_61 (code : Nat) :
    edgeTarget 61 36 code = 793152+code%7776 := by rfl

theorem block_36_61 :
    savedBlockClass (75*36+61) = some 22 ∧
    recordedClassRoot 22 = 2490 := by decide +kernel

theorem completed_36_61 (code : Nat) :
    weight completedCredit 61 36 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 61 36 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_36_61 direction_36.1
    direction_36.2.1 conditioned_36 code

theorem conditional_36_61 (code : Nat) :
    weight conditionalCredit 61 36 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 61 36 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_36_61 direction_36.1
    direction_36.2.2 conditioned_36 code
#print axioms selected_36_61
#print axioms source_36_61
#print axioms target_36_61
#print axioms block_36_61
#print axioms completed_36_61
#print axioms conditional_36_61

theorem selected_37_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [37])) := by rfl

theorem source_37_0 (code : Nat) :
    edgeSource 0 37 code = 85536+code/6 := by rfl

theorem target_37_0 (code : Nat) :
    edgeTarget 0 37 code = 800928+code%7776 := by rfl

theorem block_37_0 :
    savedBlockClass (75*37+0) = some 22 ∧
    recordedClassRoot 22 = 2490 := by decide +kernel

theorem completed_37_0 (code : Nat) :
    weight completedCredit 0 37 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 37 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_37_0 direction_37.1
    direction_37.2.1 conditioned_37 code

theorem conditional_37_0 (code : Nat) :
    weight conditionalCredit 0 37 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 37 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_37_0 direction_37.1
    direction_37.2.2 conditioned_37 code
#print axioms selected_37_0
#print axioms source_37_0
#print axioms target_37_0
#print axioms block_37_0
#print axioms completed_37_0
#print axioms conditional_37_0

theorem selected_37_61 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 61 [] ++ [37])) := by rfl

theorem source_37_61 (code : Nat) :
    edgeSource 61 37 code = 1492992+code/6 := by rfl

theorem target_37_61 (code : Nat) :
    edgeTarget 61 37 code = 800928+code%7776 := by rfl

theorem block_37_61 :
    savedBlockClass (75*37+61) = some 22 ∧
    recordedClassRoot 22 = 2490 := by decide +kernel

theorem completed_37_61 (code : Nat) :
    weight completedCredit 61 37 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 61 37 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_37_61 direction_37.1
    direction_37.2.1 conditioned_37 code

theorem conditional_37_61 (code : Nat) :
    weight conditionalCredit 61 37 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 61 37 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_37_61 direction_37.1
    direction_37.2.2 conditioned_37 code
#print axioms selected_37_61
#print axioms source_37_61
#print axioms target_37_61
#print axioms block_37_61
#print axioms completed_37_61
#print axioms conditional_37_61

theorem selected_38_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [38])) := by rfl

theorem source_38_0 (code : Nat) :
    edgeSource 0 38 code = 85536+code/6 := by rfl

theorem target_38_0 (code : Nat) :
    edgeTarget 0 38 code = 808704+code%7776 := by rfl

theorem block_38_0 :
    savedBlockClass (75*38+0) = some 23 ∧
    recordedClassRoot 23 = 2559 := by decide +kernel

theorem completed_38_0 (code : Nat) :
    weight completedCredit 0 38 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 38 [] 10 16
    (fun code => 0) selected_38_0 direction_38.1
    direction_38.2.1 conditioned_38 code

theorem conditional_38_0 (code : Nat) :
    weight conditionalCredit 0 38 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 38 [] 10 16
    (fun code => 0) selected_38_0 direction_38.1
    direction_38.2.2 conditioned_38 code
#print axioms selected_38_0
#print axioms source_38_0
#print axioms target_38_0
#print axioms block_38_0
#print axioms completed_38_0
#print axioms conditional_38_0

theorem selected_38_61 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 61 [] ++ [38])) := by rfl

theorem source_38_61 (code : Nat) :
    edgeSource 61 38 code = 1492992+code/6 := by rfl

theorem target_38_61 (code : Nat) :
    edgeTarget 61 38 code = 808704+code%7776 := by rfl

theorem block_38_61 :
    savedBlockClass (75*38+61) = some 23 ∧
    recordedClassRoot 23 = 2559 := by decide +kernel

theorem completed_38_61 (code : Nat) :
    weight completedCredit 61 38 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 61 38 [] 10 16
    (fun code => 0) selected_38_61 direction_38.1
    direction_38.2.1 conditioned_38 code

theorem conditional_38_61 (code : Nat) :
    weight conditionalCredit 61 38 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 61 38 [] 10 16
    (fun code => 0) selected_38_61 direction_38.1
    direction_38.2.2 conditioned_38 code
#print axioms selected_38_61
#print axioms source_38_61
#print axioms target_38_61
#print axioms block_38_61
#print axioms completed_38_61
#print axioms conditional_38_61

theorem selected_39_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [39])) := by rfl

theorem source_39_0 (code : Nat) :
    edgeSource 0 39 code = 85536+code/6 := by rfl

theorem target_39_0 (code : Nat) :
    edgeTarget 0 39 code = 816480+code%7776 := by rfl

theorem block_39_0 :
    savedBlockClass (75*39+0) = some 24 ∧
    recordedClassRoot 24 = 2570 := by decide +kernel

theorem completed_39_0 (code : Nat) :
    weight completedCredit 0 39 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 39 [] 5 0
    (fun code => 0) selected_39_0 direction_39.1
    direction_39.2.1 conditioned_39 code

theorem conditional_39_0 (code : Nat) :
    weight conditionalCredit 0 39 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 39 [] 5 16
    (fun code => 0) selected_39_0 direction_39.1
    direction_39.2.2 conditioned_39 code
#print axioms selected_39_0
#print axioms source_39_0
#print axioms target_39_0
#print axioms block_39_0
#print axioms completed_39_0
#print axioms conditional_39_0

theorem selected_39_61 :
    [rule037] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 61 [] ++ [39])) := by rfl

theorem source_39_61 (code : Nat) :
    edgeSource 61 39 code = 1492992+code/6 := by rfl

theorem target_39_61 (code : Nat) :
    edgeTarget 61 39 code = 816480+code%7776 := by rfl

theorem block_39_61 :
    savedBlockClass (75*39+61) = some 24 ∧
    recordedClassRoot 24 = 2570 := by decide +kernel

theorem completed_39_61 (code : Nat) :
    weight completedCredit 61 39 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule037] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 61 39 [rule037] 5 0
    (fun code => 0) selected_39_61 direction_39.1
    direction_39.2.1 conditioned_39 code

theorem conditional_39_61 (code : Nat) :
    weight conditionalCredit 61 39 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule037] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 61 39 [rule037] 5 16
    (fun code => 0) selected_39_61 direction_39.1
    direction_39.2.2 conditioned_39 code
#print axioms selected_39_61
#print axioms source_39_61
#print axioms target_39_61
#print axioms block_39_61
#print axioms completed_39_61
#print axioms conditional_39_61

theorem selected_40_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [40])) := by rfl

theorem source_40_0 (code : Nat) :
    edgeSource 0 40 code = 85536+code/6 := by rfl

theorem target_40_0 (code : Nat) :
    edgeTarget 0 40 code = 824256+code%7776 := by rfl

theorem block_40_0 :
    savedBlockClass (75*40+0) = some 22 ∧
    recordedClassRoot 22 = 2490 := by decide +kernel

theorem completed_40_0 (code : Nat) :
    weight completedCredit 0 40 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 40 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_40_0 direction_40.1
    direction_40.2.1 conditioned_40 code

theorem conditional_40_0 (code : Nat) :
    weight conditionalCredit 0 40 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 40 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_40_0 direction_40.1
    direction_40.2.2 conditioned_40 code
#print axioms selected_40_0
#print axioms source_40_0
#print axioms target_40_0
#print axioms block_40_0
#print axioms completed_40_0
#print axioms conditional_40_0

theorem selected_40_61 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 61 [] ++ [40])) := by rfl

theorem source_40_61 (code : Nat) :
    edgeSource 61 40 code = 1492992+code/6 := by rfl

theorem target_40_61 (code : Nat) :
    edgeTarget 61 40 code = 824256+code%7776 := by rfl

theorem block_40_61 :
    savedBlockClass (75*40+61) = some 22 ∧
    recordedClassRoot 22 = 2490 := by decide +kernel

theorem completed_40_61 (code : Nat) :
    weight completedCredit 61 40 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 61 40 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_40_61 direction_40.1
    direction_40.2.1 conditioned_40 code

theorem conditional_40_61 (code : Nat) :
    weight conditionalCredit 61 40 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 61 40 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_40_61 direction_40.1
    direction_40.2.2 conditioned_40 code
#print axioms selected_40_61
#print axioms source_40_61
#print axioms target_40_61
#print axioms block_40_61
#print axioms completed_40_61
#print axioms conditional_40_61

theorem selected_41_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [41])) := by rfl

theorem source_41_0 (code : Nat) :
    edgeSource 0 41 code = 93312+code/6 := by rfl

theorem target_41_0 (code : Nat) :
    edgeTarget 0 41 code = 552096+code%7776 := by rfl

theorem block_41_0 :
    savedBlockClass (75*41+0) = some 26 ∧
    recordedClassRoot 26 = 2626 := by decide +kernel

theorem completed_41_0 (code : Nat) :
    weight completedCredit 0 41 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 41 [] 25 16
    (fun code => 0) selected_41_0 direction_41.1
    direction_41.2.1 conditioned_41 code

theorem conditional_41_0 (code : Nat) :
    weight conditionalCredit 0 41 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 41 [] 25 16
    (fun code => 0) selected_41_0 direction_41.1
    direction_41.2.2 conditioned_41 code
#print axioms selected_41_0
#print axioms source_41_0
#print axioms target_41_0
#print axioms block_41_0
#print axioms completed_41_0
#print axioms conditional_41_0

theorem selected_42_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [42])) := by rfl

theorem source_42_0 (code : Nat) :
    edgeSource 0 42 code = 93312+code/6 := by rfl

theorem target_42_0 (code : Nat) :
    edgeTarget 0 42 code = 559872+code%7776 := by rfl

theorem block_42_0 :
    savedBlockClass (75*42+0) = some 27 ∧
    recordedClassRoot 27 = 2676 := by decide +kernel

theorem completed_42_0 (code : Nat) :
    weight completedCredit 0 42 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 42 [] 10 0
    (fun code => 0) selected_42_0 direction_42.1
    direction_42.2.1 conditioned_42 code

theorem conditional_42_0 (code : Nat) :
    weight conditionalCredit 0 42 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 42 [] 10 16
    (fun code => 0) selected_42_0 direction_42.1
    direction_42.2.2 conditioned_42 code
#print axioms selected_42_0
#print axioms source_42_0
#print axioms target_42_0
#print axioms block_42_0
#print axioms completed_42_0
#print axioms conditional_42_0

theorem selected_43_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [43])) := by rfl

theorem source_43_0 (code : Nat) :
    edgeSource 0 43 code = 93312+code/6 := by rfl

theorem target_43_0 (code : Nat) :
    edgeTarget 0 43 code = 567648+code%7776 := by rfl

theorem block_43_0 :
    savedBlockClass (75*43+0) = some 28 ∧
    recordedClassRoot 28 = 2684 := by decide +kernel

theorem completed_43_0 (code : Nat) :
    weight completedCredit 0 43 code =
      120*(code%6+1)+max (max 15 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 43 [] 15 16
    (fun code => 0) selected_43_0 direction_43.1
    direction_43.2.1 conditioned_43 code

theorem conditional_43_0 (code : Nat) :
    weight conditionalCredit 0 43 code =
      120*(code%6+1)+max (max 15 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 43 [] 15 16
    (fun code => 0) selected_43_0 direction_43.1
    direction_43.2.2 conditioned_43 code
#print axioms selected_43_0
#print axioms source_43_0
#print axioms target_43_0
#print axioms block_43_0
#print axioms completed_43_0
#print axioms conditional_43_0

theorem selected_44_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [44])) := by rfl

theorem source_44_0 (code : Nat) :
    edgeSource 0 44 code = 93312+code/6 := by rfl

theorem target_44_0 (code : Nat) :
    edgeTarget 0 44 code = 575424+code%7776 := by rfl

theorem block_44_0 :
    savedBlockClass (75*44+0) = some 26 ∧
    recordedClassRoot 26 = 2626 := by decide +kernel

theorem completed_44_0 (code : Nat) :
    weight completedCredit 0 44 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 44 [] 25 16
    (fun code => 0) selected_44_0 direction_44.1
    direction_44.2.1 conditioned_44 code

theorem conditional_44_0 (code : Nat) :
    weight conditionalCredit 0 44 code =
      120*(code%6+1)+max (max 25 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 44 [] 25 16
    (fun code => 0) selected_44_0 direction_44.1
    direction_44.2.2 conditioned_44 code
#print axioms selected_44_0
#print axioms source_44_0
#print axioms target_44_0
#print axioms block_44_0
#print axioms completed_44_0
#print axioms conditional_44_0

theorem selected_45_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [45])) := by rfl

theorem source_45_0 (code : Nat) :
    edgeSource 0 45 code = 101088+code/6 := by rfl

theorem target_45_0 (code : Nat) :
    edgeTarget 0 45 code = 520992+code%7776 := by rfl

theorem block_45_0 :
    savedBlockClass (75*45+0) = some 29 ∧
    recordedClassRoot 29 = 2691 := by decide +kernel

theorem completed_45_0 (code : Nat) :
    weight completedCredit 0 45 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 45 [] 4 0
    (fun code => 0) selected_45_0 direction_45.1
    direction_45.2.1 conditioned_45 code

theorem conditional_45_0 (code : Nat) :
    weight conditionalCredit 0 45 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 45 [] 4 16
    (fun code => 0) selected_45_0 direction_45.1
    direction_45.2.2 conditioned_45 code
#print axioms selected_45_0
#print axioms source_45_0
#print axioms target_45_0
#print axioms block_45_0
#print axioms completed_45_0
#print axioms conditional_45_0

theorem selected_46_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [46])) := by rfl

theorem source_46_0 (code : Nat) :
    edgeSource 0 46 code = 101088+code/6 := by rfl

theorem target_46_0 (code : Nat) :
    edgeTarget 0 46 code = 544320+code%7776 := by rfl

theorem block_46_0 :
    savedBlockClass (75*46+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_46_0 (code : Nat) :
    weight completedCredit 0 46 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 46 [] 4 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_46_0 direction_46.1
    direction_46.2.1 conditioned_46 code

theorem conditional_46_0 (code : Nat) :
    weight conditionalCredit 0 46 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 46 [] 4 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_46_0 direction_46.1
    direction_46.2.2 conditioned_46 code
#print axioms selected_46_0
#print axioms source_46_0
#print axioms target_46_0
#print axioms block_46_0
#print axioms completed_46_0
#print axioms conditional_46_0

theorem selected_47_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [47])) := by rfl

theorem source_47_0 (code : Nat) :
    edgeSource 0 47 code = 108864+code/6 := by rfl

theorem target_47_0 (code : Nat) :
    edgeTarget 0 47 code = 590976+code%7776 := by rfl

theorem block_47_0 :
    savedBlockClass (75*47+0) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_47_0 (code : Nat) :
    weight completedCredit 0 47 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 47 [] 0 12
    (fun code => 0) selected_47_0 direction_47.1
    direction_47.2.1 conditioned_47 code

theorem conditional_47_0 (code : Nat) :
    weight conditionalCredit 0 47 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 47 [] 0 12
    (fun code => 0) selected_47_0 direction_47.1
    direction_47.2.2 conditioned_47 code
#print axioms selected_47_0
#print axioms source_47_0
#print axioms target_47_0
#print axioms block_47_0
#print axioms completed_47_0
#print axioms conditional_47_0

theorem selected_48_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [48])) := by rfl

theorem source_48_0 (code : Nat) :
    edgeSource 0 48 code = 108864+code/6 := by rfl

theorem target_48_0 (code : Nat) :
    edgeTarget 0 48 code = 598752+code%7776 := by rfl

theorem block_48_0 :
    savedBlockClass (75*48+0) = some 32 ∧
    recordedClassRoot 32 = 2707 := by decide +kernel

theorem completed_48_0 (code : Nat) :
    weight completedCredit 0 48 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 48 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_48_0 direction_48.1
    direction_48.2.1 conditioned_48 code

theorem conditional_48_0 (code : Nat) :
    weight conditionalCredit 0 48 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 48 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_48_0 direction_48.1
    direction_48.2.2 conditioned_48 code
#print axioms selected_48_0
#print axioms source_48_0
#print axioms target_48_0
#print axioms block_48_0
#print axioms completed_48_0
#print axioms conditional_48_0

theorem selected_49_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [49])) := by rfl

theorem source_49_0 (code : Nat) :
    edgeSource 0 49 code = 116640+code/6 := by rfl

theorem target_49_0 (code : Nat) :
    edgeTarget 0 49 code = 614304+code%7776 := by rfl

theorem block_49_0 :
    savedBlockClass (75*49+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_49_0 (code : Nat) :
    weight completedCredit 0 49 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 49 [] 0 0
    (fun code => 0) selected_49_0 direction_49.1
    direction_49.2.1 conditioned_49 code

theorem conditional_49_0 (code : Nat) :
    weight conditionalCredit 0 49 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 49 [] 0 16
    (fun code => 0) selected_49_0 direction_49.1
    direction_49.2.2 conditioned_49 code
#print axioms selected_49_0
#print axioms source_49_0
#print axioms target_49_0
#print axioms block_49_0
#print axioms completed_49_0
#print axioms conditional_49_0

theorem selected_49_11 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 11 [] ++ [49])) := by rfl

theorem source_49_11 (code : Nat) :
    edgeSource 11 49 code = 1104192+code/6 := by rfl

theorem target_49_11 (code : Nat) :
    edgeTarget 11 49 code = 614304+code%7776 := by rfl

theorem block_49_11 :
    savedBlockClass (75*49+11) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_49_11 (code : Nat) :
    weight completedCredit 11 49 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 11 49 [] 0 0
    (fun code => 0) selected_49_11 direction_49.1
    direction_49.2.1 conditioned_49 code

theorem conditional_49_11 (code : Nat) :
    weight conditionalCredit 11 49 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 11 49 [] 0 16
    (fun code => 0) selected_49_11 direction_49.1
    direction_49.2.2 conditioned_49 code
#print axioms selected_49_11
#print axioms source_49_11
#print axioms target_49_11
#print axioms block_49_11
#print axioms completed_49_11
#print axioms conditional_49_11

theorem selected_50_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [50])) := by rfl

theorem source_50_0 (code : Nat) :
    edgeSource 0 50 code = 116640+code/6 := by rfl

theorem target_50_0 (code : Nat) :
    edgeTarget 0 50 code = 606528+code%7776 := by rfl

theorem block_50_0 :
    savedBlockClass (75*50+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_50_0 (code : Nat) :
    weight completedCredit 0 50 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 50 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_50_0 direction_50.1
    direction_50.2.1 conditioned_50 code

theorem conditional_50_0 (code : Nat) :
    weight conditionalCredit 0 50 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 50 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_50_0 direction_50.1
    direction_50.2.2 conditioned_50 code
#print axioms selected_50_0
#print axioms source_50_0
#print axioms target_50_0
#print axioms block_50_0
#print axioms completed_50_0
#print axioms conditional_50_0

theorem selected_50_11 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 11 [] ++ [50])) := by rfl

theorem source_50_11 (code : Nat) :
    edgeSource 11 50 code = 1104192+code/6 := by rfl

theorem target_50_11 (code : Nat) :
    edgeTarget 11 50 code = 1368576+code%7776 := by rfl

theorem block_50_11 :
    savedBlockClass (75*50+11) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_50_11 (code : Nat) :
    weight completedCredit 11 50 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 11 50 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_50_11 direction_50.1
    direction_50.2.1 conditioned_50 code

theorem conditional_50_11 (code : Nat) :
    weight conditionalCredit 11 50 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 11 50 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_50_11 direction_50.1
    direction_50.2.2 conditioned_50 code
#print axioms selected_50_11
#print axioms source_50_11
#print axioms target_50_11
#print axioms block_50_11
#print axioms completed_50_11
#print axioms conditional_50_11

end Snake9.Context101
