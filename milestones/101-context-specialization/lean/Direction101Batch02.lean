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

theorem direction_32 :
    18 = geometricCredits.getD 32 0 ∧
    0 = completedCredit 32 ∧
    16 = conditionalCredit 32 := by decide +kernel

theorem conditioned_32 (code : Nat) :
    conditionedCredit 32 code = 0 := by
  have hf : canon ((extensions.getD 32 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 32 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_32
#print axioms conditioned_32

theorem direction_33 :
    27 = geometricCredits.getD 33 0 ∧
    0 = completedCredit 33 ∧
    18 = conditionalCredit 33 := by decide +kernel

theorem conditioned_33 (code : Nat) :
    conditionedCredit 33 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 33 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 33 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_33
#print axioms conditioned_33

theorem direction_34 :
    0 = geometricCredits.getD 34 0 ∧
    0 = completedCredit 34 ∧
    18 = conditionalCredit 34 := by decide +kernel

theorem conditioned_34 (code : Nat) :
    conditionedCredit 34 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 34 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 34 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_34
#print axioms conditioned_34

theorem direction_35 :
    0 = geometricCredits.getD 35 0 ∧
    0 = completedCredit 35 ∧
    18 = conditionalCredit 35 := by decide +kernel

theorem conditioned_35 (code : Nat) :
    conditionedCredit 35 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 35 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 35 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_35
#print axioms conditioned_35

theorem direction_36 :
    10 = geometricCredits.getD 36 0 ∧
    0 = completedCredit 36 ∧
    18 = conditionalCredit 36 := by decide +kernel

theorem conditioned_36 (code : Nat) :
    conditionedCredit 36 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 36 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 36 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_36
#print axioms conditioned_36

theorem direction_37 :
    10 = geometricCredits.getD 37 0 ∧
    0 = completedCredit 37 ∧
    18 = conditionalCredit 37 := by decide +kernel

theorem conditioned_37 (code : Nat) :
    conditionedCredit 37 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 37 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 37 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_37
#print axioms conditioned_37

theorem direction_38 :
    10 = geometricCredits.getD 38 0 ∧
    16 = completedCredit 38 ∧
    16 = conditionalCredit 38 := by decide +kernel

theorem conditioned_38 (code : Nat) :
    conditionedCredit 38 code = 0 := by
  have hf : canon ((extensions.getD 38 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 38 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_38
#print axioms conditioned_38

theorem direction_39 :
    5 = geometricCredits.getD 39 0 ∧
    0 = completedCredit 39 ∧
    16 = conditionalCredit 39 := by decide +kernel

theorem conditioned_39 (code : Nat) :
    conditionedCredit 39 code = 0 := by
  have hf : canon ((extensions.getD 39 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 39 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_39
#print axioms conditioned_39

theorem direction_40 :
    10 = geometricCredits.getD 40 0 ∧
    0 = completedCredit 40 ∧
    18 = conditionalCredit 40 := by decide +kernel

theorem conditioned_40 (code : Nat) :
    conditionedCredit 40 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 40 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 40 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_40
#print axioms conditioned_40

theorem direction_41 :
    25 = geometricCredits.getD 41 0 ∧
    16 = completedCredit 41 ∧
    16 = conditionalCredit 41 := by decide +kernel

theorem conditioned_41 (code : Nat) :
    conditionedCredit 41 code = 0 := by
  have hf : canon ((extensions.getD 41 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 41 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_41
#print axioms conditioned_41

theorem direction_42 :
    10 = geometricCredits.getD 42 0 ∧
    0 = completedCredit 42 ∧
    16 = conditionalCredit 42 := by decide +kernel

theorem conditioned_42 (code : Nat) :
    conditionedCredit 42 code = 0 := by
  have hf : canon ((extensions.getD 42 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 42 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_42
#print axioms conditioned_42

theorem direction_43 :
    15 = geometricCredits.getD 43 0 ∧
    16 = completedCredit 43 ∧
    16 = conditionalCredit 43 := by decide +kernel

theorem conditioned_43 (code : Nat) :
    conditionedCredit 43 code = 0 := by
  have hf : canon ((extensions.getD 43 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 43 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_43
#print axioms conditioned_43

theorem direction_44 :
    25 = geometricCredits.getD 44 0 ∧
    16 = completedCredit 44 ∧
    16 = conditionalCredit 44 := by decide +kernel

theorem conditioned_44 (code : Nat) :
    conditionedCredit 44 code = 0 := by
  have hf : canon ((extensions.getD 44 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 44 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_44
#print axioms conditioned_44

theorem direction_45 :
    4 = geometricCredits.getD 45 0 ∧
    0 = completedCredit 45 ∧
    16 = conditionalCredit 45 := by decide +kernel

theorem conditioned_45 (code : Nat) :
    conditionedCredit 45 code = 0 := by
  have hf : canon ((extensions.getD 45 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 45 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_45
#print axioms conditioned_45

theorem direction_46 :
    4 = geometricCredits.getD 46 0 ∧
    12 = completedCredit 46 ∧
    16 = conditionalCredit 46 := by decide +kernel

theorem conditioned_46 (code : Nat) :
    conditionedCredit 46 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 46 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 46 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_46
#print axioms conditioned_46

theorem direction_47 :
    0 = geometricCredits.getD 47 0 ∧
    12 = completedCredit 47 ∧
    12 = conditionalCredit 47 := by decide +kernel

theorem conditioned_47 (code : Nat) :
    conditionedCredit 47 code = 0 := by
  have hf : canon ((extensions.getD 47 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 47 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_47
#print axioms conditioned_47

end Snake9.Context101
