import DirectionPilot101
import Direction101Batch02
import ContextWeights101
import StateWalk
import DefinedProofGraph

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem direction_2 :
    10 = geometricCredits.getD 2 0 ∧
    16 = completedCredit 2 ∧
    16 = conditionalCredit 2 := by decide +kernel

theorem conditioned_2 (code : Nat) :
    conditionedCredit 2 code = 0 := by
  have hf : canon ((extensions.getD 2 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 2 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_2
#print axioms conditioned_2

theorem direction_3 :
    12 = geometricCredits.getD 3 0 ∧
    0 = completedCredit 3 ∧
    18 = conditionalCredit 3 := by decide +kernel

theorem conditioned_3 (code : Nat) :
    conditionedCredit 3 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 3 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 3 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_3
#print axioms conditioned_3

theorem direction_4 :
    29 = geometricCredits.getD 4 0 ∧
    16 = completedCredit 4 ∧
    16 = conditionalCredit 4 := by decide +kernel

theorem conditioned_4 (code : Nat) :
    conditionedCredit 4 code = 0 := by
  have hf : canon ((extensions.getD 4 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 4 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_4
#print axioms conditioned_4

theorem direction_5 :
    31 = geometricCredits.getD 5 0 ∧
    16 = completedCredit 5 ∧
    16 = conditionalCredit 5 := by decide +kernel

theorem conditioned_5 (code : Nat) :
    conditionedCredit 5 code = 0 := by
  have hf : canon ((extensions.getD 5 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 5 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_5
#print axioms conditioned_5

theorem direction_6 :
    21 = geometricCredits.getD 6 0 ∧
    0 = completedCredit 6 ∧
    16 = conditionalCredit 6 := by decide +kernel

theorem conditioned_6 (code : Nat) :
    conditionedCredit 6 code = 0 := by
  have hf : canon ((extensions.getD 6 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 6 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_6
#print axioms conditioned_6

theorem direction_7 :
    36 = geometricCredits.getD 7 0 ∧
    16 = completedCredit 7 ∧
    16 = conditionalCredit 7 := by decide +kernel

theorem conditioned_7 (code : Nat) :
    conditionedCredit 7 code = 0 := by
  have hf : canon ((extensions.getD 7 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 7 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_7
#print axioms conditioned_7

theorem direction_8 :
    7 = geometricCredits.getD 8 0 ∧
    0 = completedCredit 8 ∧
    16 = conditionalCredit 8 := by decide +kernel

theorem conditioned_8 (code : Nat) :
    conditionedCredit 8 code = 0 := by
  have hf : canon ((extensions.getD 8 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 8 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_8
#print axioms conditioned_8

theorem direction_11 :
    7 = geometricCredits.getD 11 0 ∧
    12 = completedCredit 11 ∧
    12 = conditionalCredit 11 := by decide +kernel

theorem conditioned_11 (code : Nat) :
    conditionedCredit 11 code = 0 := by
  have hf : canon ((extensions.getD 11 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 11 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_11
#print axioms conditioned_11

theorem direction_13 :
    7 = geometricCredits.getD 13 0 ∧
    0 = completedCredit 13 ∧
    16 = conditionalCredit 13 := by decide +kernel

theorem conditioned_13 (code : Nat) :
    conditionedCredit 13 code = 0 := by
  have hf : canon ((extensions.getD 13 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 13 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_13
#print axioms conditioned_13

theorem direction_14 :
    7 = geometricCredits.getD 14 0 ∧
    0 = completedCredit 14 ∧
    18 = conditionalCredit 14 := by decide +kernel

theorem conditioned_14 (code : Nat) :
    conditionedCredit 14 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 14 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 14 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_14
#print axioms conditioned_14

theorem direction_15 :
    7 = geometricCredits.getD 15 0 ∧
    12 = completedCredit 15 ∧
    16 = conditionalCredit 15 := by decide +kernel

theorem conditioned_15 (code : Nat) :
    conditionedCredit 15 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 15 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 15 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_15
#print axioms conditioned_15

theorem direction_16 :
    7 = geometricCredits.getD 16 0 ∧
    16 = completedCredit 16 ∧
    16 = conditionalCredit 16 := by decide +kernel

theorem conditioned_16 (code : Nat) :
    conditionedCredit 16 code = 0 := by
  have hf : canon ((extensions.getD 16 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 16 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_16
#print axioms conditioned_16

theorem direction_17 :
    7 = geometricCredits.getD 17 0 ∧
    12 = completedCredit 17 ∧
    16 = conditionalCredit 17 := by decide +kernel

theorem conditioned_17 (code : Nat) :
    conditionedCredit 17 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 17 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 17 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_17
#print axioms conditioned_17

theorem direction_18 :
    12 = geometricCredits.getD 18 0 ∧
    16 = completedCredit 18 ∧
    16 = conditionalCredit 18 := by decide +kernel

theorem conditioned_18 (code : Nat) :
    conditionedCredit 18 code = 0 := by
  have hf : canon ((extensions.getD 18 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 18 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_18
#print axioms conditioned_18

theorem direction_19 :
    11 = geometricCredits.getD 19 0 ∧
    16 = completedCredit 19 ∧
    16 = conditionalCredit 19 := by decide +kernel

theorem conditioned_19 (code : Nat) :
    conditionedCredit 19 code = 0 := by
  have hf : canon ((extensions.getD 19 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 19 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_19
#print axioms conditioned_19

theorem direction_20 :
    17 = geometricCredits.getD 20 0 ∧
    16 = completedCredit 20 ∧
    16 = conditionalCredit 20 := by decide +kernel

theorem conditioned_20 (code : Nat) :
    conditionedCredit 20 code = 0 := by
  have hf : canon ((extensions.getD 20 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 20 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_20
#print axioms conditioned_20

theorem direction_21 :
    7 = geometricCredits.getD 21 0 ∧
    0 = completedCredit 21 ∧
    16 = conditionalCredit 21 := by decide +kernel

theorem conditioned_21 (code : Nat) :
    conditionedCredit 21 code = 0 := by
  have hf : canon ((extensions.getD 21 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 21 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_21
#print axioms conditioned_21

theorem direction_22 :
    17 = geometricCredits.getD 22 0 ∧
    0 = completedCredit 22 ∧
    18 = conditionalCredit 22 := by decide +kernel

theorem conditioned_22 (code : Nat) :
    conditionedCredit 22 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 22 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 22 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_22
#print axioms conditioned_22

theorem direction_23 :
    17 = geometricCredits.getD 23 0 ∧
    12 = completedCredit 23 ∧
    16 = conditionalCredit 23 := by decide +kernel

theorem conditioned_23 (code : Nat) :
    conditionedCredit 23 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 23 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 23 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_23
#print axioms conditioned_23

theorem direction_24 :
    0 = geometricCredits.getD 24 0 ∧
    16 = completedCredit 24 ∧
    16 = conditionalCredit 24 := by decide +kernel

theorem conditioned_24 (code : Nat) :
    conditionedCredit 24 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 24 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 24 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_24
#print axioms conditioned_24

theorem direction_25 :
    4 = geometricCredits.getD 25 0 ∧
    0 = completedCredit 25 ∧
    16 = conditionalCredit 25 := by decide +kernel

theorem conditioned_25 (code : Nat) :
    conditionedCredit 25 code = 0 := by
  have hf : canon ((extensions.getD 25 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 25 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_25
#print axioms conditioned_25

theorem direction_26 :
    4 = geometricCredits.getD 26 0 ∧
    12 = completedCredit 26 ∧
    16 = conditionalCredit 26 := by decide +kernel

theorem conditioned_26 (code : Nat) :
    conditionedCredit 26 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 26 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 26 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_26
#print axioms conditioned_26

theorem direction_27 :
    4 = geometricCredits.getD 27 0 ∧
    0 = completedCredit 27 ∧
    18 = conditionalCredit 27 := by decide +kernel

theorem conditioned_27 (code : Nat) :
    conditionedCredit 27 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 27 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 27 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_27
#print axioms conditioned_27

theorem direction_28 :
    4 = geometricCredits.getD 28 0 ∧
    16 = completedCredit 28 ∧
    16 = conditionalCredit 28 := by decide +kernel

theorem conditioned_28 (code : Nat) :
    conditionedCredit 28 code = 0 := by
  have hf : canon ((extensions.getD 28 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 28 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_28
#print axioms conditioned_28

theorem direction_29 :
    4 = geometricCredits.getD 29 0 ∧
    12 = completedCredit 29 ∧
    16 = conditionalCredit 29 := by decide +kernel

theorem conditioned_29 (code : Nat) :
    conditionedCredit 29 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 29 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 29 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_29
#print axioms conditioned_29

theorem direction_30 :
    18 = geometricCredits.getD 30 0 ∧
    0 = completedCredit 30 ∧
    18 = conditionalCredit 30 := by decide +kernel

theorem conditioned_30 (code : Nat) :
    conditionedCredit 30 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 30 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 30 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_30
#print axioms conditioned_30

theorem direction_31 :
    23 = geometricCredits.getD 31 0 ∧
    16 = completedCredit 31 ∧
    16 = conditionalCredit 31 := by decide +kernel

theorem conditioned_31 (code : Nat) :
    conditionedCredit 31 code = 0 := by
  have hf : canon ((extensions.getD 31 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 31 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_31
#print axioms conditioned_31

theorem direction_48 :
    7 = geometricCredits.getD 48 0 ∧
    16 = completedCredit 48 ∧
    16 = conditionalCredit 48 := by decide +kernel

theorem conditioned_48 (code : Nat) :
    conditionedCredit 48 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 48 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 48 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_48
#print axioms conditioned_48

theorem direction_49 :
    0 = geometricCredits.getD 49 0 ∧
    0 = completedCredit 49 ∧
    16 = conditionalCredit 49 := by decide +kernel

theorem conditioned_49 (code : Nat) :
    conditionedCredit 49 code = 0 := by
  have hf : canon ((extensions.getD 49 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 49 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_49
#print axioms conditioned_49

theorem direction_50 :
    0 = geometricCredits.getD 50 0 ∧
    12 = completedCredit 50 ∧
    16 = conditionalCredit 50 := by decide +kernel

theorem conditioned_50 (code : Nat) :
    conditionedCredit 50 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 50 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 50 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_50
#print axioms conditioned_50

theorem direction_51 :
    0 = geometricCredits.getD 51 0 ∧
    16 = completedCredit 51 ∧
    16 = conditionalCredit 51 := by decide +kernel

theorem conditioned_51 (code : Nat) :
    conditionedCredit 51 code = 0 := by
  have hf : canon ((extensions.getD 51 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 51 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_51
#print axioms conditioned_51

theorem direction_52 :
    0 = geometricCredits.getD 52 0 ∧
    0 = completedCredit 52 ∧
    18 = conditionalCredit 52 := by decide +kernel

theorem conditioned_52 (code : Nat) :
    conditionedCredit 52 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 52 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 52 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_52
#print axioms conditioned_52

theorem direction_53 :
    0 = geometricCredits.getD 53 0 ∧
    12 = completedCredit 53 ∧
    16 = conditionalCredit 53 := by decide +kernel

theorem conditioned_53 (code : Nat) :
    conditionedCredit 53 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 53 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 53 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_53
#print axioms conditioned_53

theorem direction_54 :
    6 = geometricCredits.getD 54 0 ∧
    16 = completedCredit 54 ∧
    16 = conditionalCredit 54 := by decide +kernel

theorem conditioned_54 (code : Nat) :
    conditionedCredit 54 code = 0 := by
  have hf : canon ((extensions.getD 54 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 54 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_54
#print axioms conditioned_54

theorem direction_55 :
    6 = geometricCredits.getD 55 0 ∧
    16 = completedCredit 55 ∧
    16 = conditionalCredit 55 := by decide +kernel

theorem conditioned_55 (code : Nat) :
    conditionedCredit 55 code = 0 := by
  have hf : canon ((extensions.getD 55 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 55 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_55
#print axioms conditioned_55

theorem direction_56 :
    22 = geometricCredits.getD 56 0 ∧
    0 = completedCredit 56 ∧
    16 = conditionalCredit 56 := by decide +kernel

theorem conditioned_56 (code : Nat) :
    conditionedCredit 56 code = 0 := by
  have hf : canon ((extensions.getD 56 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 56 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_56
#print axioms conditioned_56

theorem direction_57 :
    31 = geometricCredits.getD 57 0 ∧
    12 = completedCredit 57 ∧
    16 = conditionalCredit 57 := by decide +kernel

theorem conditioned_57 (code : Nat) :
    conditionedCredit 57 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 57 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 57 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_57
#print axioms conditioned_57

theorem direction_58 :
    11 = geometricCredits.getD 58 0 ∧
    16 = completedCredit 58 ∧
    16 = conditionalCredit 58 := by decide +kernel

theorem conditioned_58 (code : Nat) :
    conditionedCredit 58 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 58 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 58 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_58
#print axioms conditioned_58

theorem direction_59 :
    13 = geometricCredits.getD 59 0 ∧
    0 = completedCredit 59 ∧
    16 = conditionalCredit 59 := by decide +kernel

theorem conditioned_59 (code : Nat) :
    conditionedCredit 59 code = 0 := by
  have hf : canon ((extensions.getD 59 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 59 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_59
#print axioms conditioned_59

theorem direction_60 :
    13 = geometricCredits.getD 60 0 ∧
    12 = completedCredit 60 ∧
    16 = conditionalCredit 60 := by decide +kernel

theorem conditioned_60 (code : Nat) :
    conditionedCredit 60 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 60 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 60 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_60
#print axioms conditioned_60

theorem direction_61 :
    13 = geometricCredits.getD 61 0 ∧
    16 = completedCredit 61 ∧
    16 = conditionalCredit 61 := by decide +kernel

theorem conditioned_61 (code : Nat) :
    conditionedCredit 61 code = 0 := by
  have hf : canon ((extensions.getD 61 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 61 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_61
#print axioms conditioned_61

theorem direction_62 :
    13 = geometricCredits.getD 62 0 ∧
    0 = completedCredit 62 ∧
    18 = conditionalCredit 62 := by decide +kernel

theorem conditioned_62 (code : Nat) :
    conditionedCredit 62 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 62 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 62 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_62
#print axioms conditioned_62

theorem direction_63 :
    13 = geometricCredits.getD 63 0 ∧
    12 = completedCredit 63 ∧
    16 = conditionalCredit 63 := by decide +kernel

theorem conditioned_63 (code : Nat) :
    conditionedCredit 63 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 63 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 63 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_63
#print axioms conditioned_63

end Snake9.Context101
