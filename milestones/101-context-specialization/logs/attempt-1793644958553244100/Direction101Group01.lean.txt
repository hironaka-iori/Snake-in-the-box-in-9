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

theorem direction_64 :
    18 = geometricCredits.getD 64 0 ∧
    16 = completedCredit 64 ∧
    16 = conditionalCredit 64 := by decide +kernel

theorem conditioned_64 (code : Nat) :
    conditionedCredit 64 code = 0 := by
  have hf : canon ((extensions.getD 64 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 64 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_64
#print axioms conditioned_64

theorem direction_65 :
    18 = geometricCredits.getD 65 0 ∧
    16 = completedCredit 65 ∧
    16 = conditionalCredit 65 := by decide +kernel

theorem conditioned_65 (code : Nat) :
    conditionedCredit 65 code = 0 := by
  have hf : canon ((extensions.getD 65 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 65 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_65
#print axioms conditioned_65

theorem direction_66 :
    6 = geometricCredits.getD 66 0 ∧
    0 = completedCredit 66 ∧
    16 = conditionalCredit 66 := by decide +kernel

theorem conditioned_66 (code : Nat) :
    conditionedCredit 66 code = 0 := by
  have hf : canon ((extensions.getD 66 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 66 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_66
#print axioms conditioned_66

theorem direction_67 :
    12 = geometricCredits.getD 67 0 ∧
    16 = completedCredit 67 ∧
    16 = conditionalCredit 67 := by decide +kernel

theorem conditioned_67 (code : Nat) :
    conditionedCredit 67 code = 0 := by
  have hf : canon ((extensions.getD 67 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 67 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_67
#print axioms conditioned_67

theorem direction_68 :
    18 = geometricCredits.getD 68 0 ∧
    16 = completedCredit 68 ∧
    16 = conditionalCredit 68 := by decide +kernel

theorem conditioned_68 (code : Nat) :
    conditionedCredit 68 code = 0 := by
  have hf : canon ((extensions.getD 68 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 68 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_68
#print axioms conditioned_68

theorem direction_69 :
    0 = geometricCredits.getD 69 0 ∧
    0 = completedCredit 69 ∧
    16 = conditionalCredit 69 := by decide +kernel

theorem conditioned_69 (code : Nat) :
    conditionedCredit 69 code = 0 := by
  have hf : canon ((extensions.getD 69 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 69 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_69
#print axioms conditioned_69

theorem direction_70 :
    0 = geometricCredits.getD 70 0 ∧
    12 = completedCredit 70 ∧
    16 = conditionalCredit 70 := by decide +kernel

theorem conditioned_70 (code : Nat) :
    conditionedCredit 70 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 70 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 70 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_70
#print axioms conditioned_70

theorem direction_71 :
    0 = geometricCredits.getD 71 0 ∧
    16 = completedCredit 71 ∧
    16 = conditionalCredit 71 := by decide +kernel

theorem conditioned_71 (code : Nat) :
    conditionedCredit 71 code = 0 := by
  have hf : canon ((extensions.getD 71 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 71 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_71
#print axioms conditioned_71

theorem direction_72 :
    0 = geometricCredits.getD 72 0 ∧
    0 = completedCredit 72 ∧
    18 = conditionalCredit 72 := by decide +kernel

theorem conditioned_72 (code : Nat) :
    conditionedCredit 72 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 72 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 72 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_72
#print axioms conditioned_72

theorem direction_73 :
    0 = geometricCredits.getD 73 0 ∧
    12 = completedCredit 73 ∧
    16 = conditionalCredit 73 := by decide +kernel

theorem conditioned_73 (code : Nat) :
    conditionedCredit 73 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 73 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 73 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_73
#print axioms conditioned_73

theorem direction_74 :
    0 = geometricCredits.getD 74 0 ∧
    0 = completedCredit 74 ∧
    16 = conditionalCredit 74 := by decide +kernel

theorem conditioned_74 (code : Nat) :
    conditionedCredit 74 code = 0 := by
  have hf : canon ((extensions.getD 74 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 74 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_74
#print axioms conditioned_74

theorem direction_75 :
    0 = geometricCredits.getD 75 0 ∧
    12 = completedCredit 75 ∧
    16 = conditionalCredit 75 := by decide +kernel

theorem conditioned_75 (code : Nat) :
    conditionedCredit 75 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 75 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 75 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_75
#print axioms conditioned_75

theorem direction_76 :
    0 = geometricCredits.getD 76 0 ∧
    16 = completedCredit 76 ∧
    16 = conditionalCredit 76 := by decide +kernel

theorem conditioned_76 (code : Nat) :
    conditionedCredit 76 code = 0 := by
  have hf : canon ((extensions.getD 76 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 76 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_76
#print axioms conditioned_76

theorem direction_77 :
    0 = geometricCredits.getD 77 0 ∧
    0 = completedCredit 77 ∧
    18 = conditionalCredit 77 := by decide +kernel

theorem conditioned_77 (code : Nat) :
    conditionedCredit 77 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 77 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 77 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_77
#print axioms conditioned_77

theorem direction_78 :
    0 = geometricCredits.getD 78 0 ∧
    12 = completedCredit 78 ∧
    16 = conditionalCredit 78 := by decide +kernel

theorem conditioned_78 (code : Nat) :
    conditionedCredit 78 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 78 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 78 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_78
#print axioms conditioned_78

theorem direction_79 :
    0 = geometricCredits.getD 79 0 ∧
    12 = completedCredit 79 ∧
    12 = conditionalCredit 79 := by decide +kernel

theorem conditioned_79 (code : Nat) :
    conditionedCredit 79 code = 0 := by
  have hf : canon ((extensions.getD 79 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 79 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_79
#print axioms conditioned_79

theorem direction_80 :
    5 = geometricCredits.getD 80 0 ∧
    16 = completedCredit 80 ∧
    16 = conditionalCredit 80 := by decide +kernel

theorem conditioned_80 (code : Nat) :
    conditionedCredit 80 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 80 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 80 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_80
#print axioms conditioned_80

theorem direction_81 :
    5 = geometricCredits.getD 81 0 ∧
    16 = completedCredit 81 ∧
    16 = conditionalCredit 81 := by decide +kernel

theorem conditioned_81 (code : Nat) :
    conditionedCredit 81 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 81 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 81 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_81
#print axioms conditioned_81

theorem direction_82 :
    5 = geometricCredits.getD 82 0 ∧
    16 = completedCredit 82 ∧
    16 = conditionalCredit 82 := by decide +kernel

theorem conditioned_82 (code : Nat) :
    conditionedCredit 82 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 82 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 82 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_82
#print axioms conditioned_82

theorem direction_83 :
    0 = geometricCredits.getD 83 0 ∧
    0 = completedCredit 83 ∧
    16 = conditionalCredit 83 := by decide +kernel

theorem conditioned_83 (code : Nat) :
    conditionedCredit 83 code = 0 := by
  have hf : canon ((extensions.getD 83 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 83 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_83
#print axioms conditioned_83

theorem direction_84 :
    0 = geometricCredits.getD 84 0 ∧
    12 = completedCredit 84 ∧
    16 = conditionalCredit 84 := by decide +kernel

theorem conditioned_84 (code : Nat) :
    conditionedCredit 84 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 84 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 84 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_84
#print axioms conditioned_84

theorem direction_85 :
    0 = geometricCredits.getD 85 0 ∧
    12 = completedCredit 85 ∧
    16 = conditionalCredit 85 := by decide +kernel

theorem conditioned_85 (code : Nat) :
    conditionedCredit 85 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 85 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 85 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_85
#print axioms conditioned_85

theorem direction_86 :
    0 = geometricCredits.getD 86 0 ∧
    16 = completedCredit 86 ∧
    16 = conditionalCredit 86 := by decide +kernel

theorem conditioned_86 (code : Nat) :
    conditionedCredit 86 code = 0 := by
  have hf : canon ((extensions.getD 86 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 86 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_86
#print axioms conditioned_86

theorem direction_87 :
    0 = geometricCredits.getD 87 0 ∧
    0 = completedCredit 87 ∧
    18 = conditionalCredit 87 := by decide +kernel

theorem conditioned_87 (code : Nat) :
    conditionedCredit 87 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 87 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 87 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_87
#print axioms conditioned_87

theorem direction_88 :
    0 = geometricCredits.getD 88 0 ∧
    12 = completedCredit 88 ∧
    16 = conditionalCredit 88 := by decide +kernel

theorem conditioned_88 (code : Nat) :
    conditionedCredit 88 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 88 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 88 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_88
#print axioms conditioned_88

theorem direction_89 :
    12 = geometricCredits.getD 89 0 ∧
    16 = completedCredit 89 ∧
    16 = conditionalCredit 89 := by decide +kernel

theorem conditioned_89 (code : Nat) :
    conditionedCredit 89 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 89 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 89 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_89
#print axioms conditioned_89

theorem direction_90 :
    10 = geometricCredits.getD 90 0 ∧
    12 = completedCredit 90 ∧
    12 = conditionalCredit 90 := by decide +kernel

theorem conditioned_90 (code : Nat) :
    conditionedCredit 90 code = 0 := by
  have hf : canon ((extensions.getD 90 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 90 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_90
#print axioms conditioned_90

theorem direction_91 :
    17 = geometricCredits.getD 91 0 ∧
    16 = completedCredit 91 ∧
    16 = conditionalCredit 91 := by decide +kernel

theorem conditioned_91 (code : Nat) :
    conditionedCredit 91 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 91 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 91 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_91
#print axioms conditioned_91

theorem direction_92 :
    5 = geometricCredits.getD 92 0 ∧
    16 = completedCredit 92 ∧
    16 = conditionalCredit 92 := by decide +kernel

theorem conditioned_92 (code : Nat) :
    conditionedCredit 92 code = 0 := by
  have hf : canon ((extensions.getD 92 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 92 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_92
#print axioms conditioned_92

theorem direction_93 :
    13 = geometricCredits.getD 93 0 ∧
    0 = completedCredit 93 ∧
    18 = conditionalCredit 93 := by decide +kernel

theorem conditioned_93 (code : Nat) :
    conditionedCredit 93 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 93 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 93 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_93
#print axioms conditioned_93

theorem direction_94 :
    13 = geometricCredits.getD 94 0 ∧
    12 = completedCredit 94 ∧
    16 = conditionalCredit 94 := by decide +kernel

theorem conditioned_94 (code : Nat) :
    conditionedCredit 94 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 94 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 94 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_94
#print axioms conditioned_94

theorem direction_95 :
    11 = geometricCredits.getD 95 0 ∧
    0 = completedCredit 95 ∧
    16 = conditionalCredit 95 := by decide +kernel

theorem conditioned_95 (code : Nat) :
    conditionedCredit 95 code = 0 := by
  have hf : canon ((extensions.getD 95 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 95 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_95
#print axioms conditioned_95

theorem direction_96 :
    22 = geometricCredits.getD 96 0 ∧
    16 = completedCredit 96 ∧
    16 = conditionalCredit 96 := by decide +kernel

theorem conditioned_96 (code : Nat) :
    conditionedCredit 96 code = 0 := by
  have hf : canon ((extensions.getD 96 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 96 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_96
#print axioms conditioned_96

theorem direction_97 :
    28 = geometricCredits.getD 97 0 ∧
    16 = completedCredit 97 ∧
    16 = conditionalCredit 97 := by decide +kernel

theorem conditioned_97 (code : Nat) :
    conditionedCredit 97 code = 0 := by
  have hf : canon ((extensions.getD 97 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 97 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_97
#print axioms conditioned_97

theorem direction_98 :
    5 = geometricCredits.getD 98 0 ∧
    16 = completedCredit 98 ∧
    16 = conditionalCredit 98 := by decide +kernel

theorem conditioned_98 (code : Nat) :
    conditionedCredit 98 code = 0 := by
  have hf : canon ((extensions.getD 98 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 98 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_98
#print axioms conditioned_98

theorem direction_99 :
    5 = geometricCredits.getD 99 0 ∧
    0 = completedCredit 99 ∧
    18 = conditionalCredit 99 := by decide +kernel

theorem conditioned_99 (code : Nat) :
    conditionedCredit 99 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 99 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 99 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_99
#print axioms conditioned_99

theorem direction_100 :
    5 = geometricCredits.getD 100 0 ∧
    12 = completedCredit 100 ∧
    16 = conditionalCredit 100 := by decide +kernel

theorem conditioned_100 (code : Nat) :
    conditionedCredit 100 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 100 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 100 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_100
#print axioms conditioned_100

theorem direction_101 :
    5 = geometricCredits.getD 101 0 ∧
    0 = completedCredit 101 ∧
    16 = conditionalCredit 101 := by decide +kernel

theorem conditioned_101 (code : Nat) :
    conditionedCredit 101 code = 0 := by
  have hf : canon ((extensions.getD 101 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 101 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_101
#print axioms conditioned_101

theorem direction_102 :
    5 = geometricCredits.getD 102 0 ∧
    12 = completedCredit 102 ∧
    16 = conditionalCredit 102 := by decide +kernel

theorem conditioned_102 (code : Nat) :
    conditionedCredit 102 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 102 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 102 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_102
#print axioms conditioned_102

theorem direction_103 :
    5 = geometricCredits.getD 103 0 ∧
    16 = completedCredit 103 ∧
    16 = conditionalCredit 103 := by decide +kernel

theorem conditioned_103 (code : Nat) :
    conditionedCredit 103 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 103 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 103 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_103
#print axioms conditioned_103

theorem direction_104 :
    10 = geometricCredits.getD 104 0 ∧
    16 = completedCredit 104 ∧
    16 = conditionalCredit 104 := by decide +kernel

theorem conditioned_104 (code : Nat) :
    conditionedCredit 104 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 104 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 104 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_104
#print axioms conditioned_104

theorem direction_105 :
    13 = geometricCredits.getD 105 0 ∧
    16 = completedCredit 105 ∧
    16 = conditionalCredit 105 := by decide +kernel

theorem conditioned_105 (code : Nat) :
    conditionedCredit 105 code = 0 := by
  have hf : canon ((extensions.getD 105 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 105 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_105
#print axioms conditioned_105

theorem direction_106 :
    23 = geometricCredits.getD 106 0 ∧
    0 = completedCredit 106 ∧
    18 = conditionalCredit 106 := by decide +kernel

theorem conditioned_106 (code : Nat) :
    conditionedCredit 106 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 106 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 106 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_106
#print axioms conditioned_106

theorem direction_107 :
    24 = geometricCredits.getD 107 0 ∧
    12 = completedCredit 107 ∧
    16 = conditionalCredit 107 := by decide +kernel

theorem conditioned_107 (code : Nat) :
    conditionedCredit 107 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 107 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 107 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_107
#print axioms conditioned_107

theorem direction_108 :
    11 = geometricCredits.getD 108 0 ∧
    16 = completedCredit 108 ∧
    16 = conditionalCredit 108 := by decide +kernel

theorem conditioned_108 (code : Nat) :
    conditionedCredit 108 code = 0 := by
  have hf : canon ((extensions.getD 108 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 108 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_108
#print axioms conditioned_108

theorem direction_109 :
    17 = geometricCredits.getD 109 0 ∧
    16 = completedCredit 109 ∧
    16 = conditionalCredit 109 := by decide +kernel

theorem conditioned_109 (code : Nat) :
    conditionedCredit 109 code = 0 := by
  have hf : canon ((extensions.getD 109 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 109 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_109
#print axioms conditioned_109

theorem direction_110 :
    9 = geometricCredits.getD 110 0 ∧
    16 = completedCredit 110 ∧
    16 = conditionalCredit 110 := by decide +kernel

theorem conditioned_110 (code : Nat) :
    conditionedCredit 110 code = 0 := by
  have hf : canon ((extensions.getD 110 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 110 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_110
#print axioms conditioned_110

theorem direction_111 :
    9 = geometricCredits.getD 111 0 ∧
    12 = completedCredit 111 ∧
    16 = conditionalCredit 111 := by decide +kernel

theorem conditioned_111 (code : Nat) :
    conditionedCredit 111 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 111 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 111 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_111
#print axioms conditioned_111

theorem direction_112 :
    9 = geometricCredits.getD 112 0 ∧
    0 = completedCredit 112 ∧
    18 = conditionalCredit 112 := by decide +kernel

theorem conditioned_112 (code : Nat) :
    conditionedCredit 112 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 112 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 112 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_112
#print axioms conditioned_112

theorem direction_113 :
    9 = geometricCredits.getD 113 0 ∧
    0 = completedCredit 113 ∧
    16 = conditionalCredit 113 := by decide +kernel

theorem conditioned_113 (code : Nat) :
    conditionedCredit 113 code = 0 := by
  have hf : canon ((extensions.getD 113 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 113 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_113
#print axioms conditioned_113

theorem direction_114 :
    9 = geometricCredits.getD 114 0 ∧
    12 = completedCredit 114 ∧
    16 = conditionalCredit 114 := by decide +kernel

theorem conditioned_114 (code : Nat) :
    conditionedCredit 114 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 114 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 114 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_114
#print axioms conditioned_114

theorem direction_115 :
    7 = geometricCredits.getD 115 0 ∧
    16 = completedCredit 115 ∧
    16 = conditionalCredit 115 := by decide +kernel

theorem conditioned_115 (code : Nat) :
    conditionedCredit 115 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 115 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 115 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_115
#print axioms conditioned_115

theorem direction_116 :
    0 = geometricCredits.getD 116 0 ∧
    12 = completedCredit 116 ∧
    12 = conditionalCredit 116 := by decide +kernel

theorem conditioned_116 (code : Nat) :
    conditionedCredit 116 code = 0 := by
  have hf : canon ((extensions.getD 116 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 116 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_116
#print axioms conditioned_116

theorem direction_117 :
    7 = geometricCredits.getD 117 0 ∧
    16 = completedCredit 117 ∧
    16 = conditionalCredit 117 := by decide +kernel

theorem conditioned_117 (code : Nat) :
    conditionedCredit 117 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 117 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 117 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_117
#print axioms conditioned_117

theorem direction_118 :
    11 = geometricCredits.getD 118 0 ∧
    16 = completedCredit 118 ∧
    16 = conditionalCredit 118 := by decide +kernel

theorem conditioned_118 (code : Nat) :
    conditionedCredit 118 code = 0 := by
  have hf : canon ((extensions.getD 118 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 118 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_118
#print axioms conditioned_118

theorem direction_119 :
    17 = geometricCredits.getD 119 0 ∧
    12 = completedCredit 119 ∧
    16 = conditionalCredit 119 := by decide +kernel

theorem conditioned_119 (code : Nat) :
    conditionedCredit 119 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 119 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 119 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_119
#print axioms conditioned_119

theorem direction_120 :
    6 = geometricCredits.getD 120 0 ∧
    0 = completedCredit 120 ∧
    16 = conditionalCredit 120 := by decide +kernel

theorem conditioned_120 (code : Nat) :
    conditionedCredit 120 code = 0 := by
  have hf : canon ((extensions.getD 120 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 120 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_120
#print axioms conditioned_120

theorem direction_121 :
    21 = geometricCredits.getD 121 0 ∧
    16 = completedCredit 121 ∧
    16 = conditionalCredit 121 := by decide +kernel

theorem conditioned_121 (code : Nat) :
    conditionedCredit 121 code = 0 := by
  have hf : canon ((extensions.getD 121 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 121 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_121
#print axioms conditioned_121

theorem direction_122 :
    0 = geometricCredits.getD 122 0 ∧
    16 = completedCredit 122 ∧
    16 = conditionalCredit 122 := by decide +kernel

theorem conditioned_122 (code : Nat) :
    conditionedCredit 122 code = 0 := by
  have hf : canon ((extensions.getD 122 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 122 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_122
#print axioms conditioned_122

theorem direction_123 :
    0 = geometricCredits.getD 123 0 ∧
    12 = completedCredit 123 ∧
    16 = conditionalCredit 123 := by decide +kernel

theorem conditioned_123 (code : Nat) :
    conditionedCredit 123 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 123 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 123 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_123
#print axioms conditioned_123

theorem direction_124 :
    0 = geometricCredits.getD 124 0 ∧
    0 = completedCredit 124 ∧
    16 = conditionalCredit 124 := by decide +kernel

theorem conditioned_124 (code : Nat) :
    conditionedCredit 124 code = 0 := by
  have hf : canon ((extensions.getD 124 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 124 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_124
#print axioms conditioned_124

theorem direction_125 :
    0 = geometricCredits.getD 125 0 ∧
    0 = completedCredit 125 ∧
    18 = conditionalCredit 125 := by decide +kernel

theorem conditioned_125 (code : Nat) :
    conditionedCredit 125 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 125 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 125 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_125
#print axioms conditioned_125

theorem direction_126 :
    0 = geometricCredits.getD 126 0 ∧
    12 = completedCredit 126 ∧
    16 = conditionalCredit 126 := by decide +kernel

theorem conditioned_126 (code : Nat) :
    conditionedCredit 126 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 126 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 126 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_126
#print axioms conditioned_126

theorem direction_127 :
    11 = geometricCredits.getD 127 0 ∧
    16 = completedCredit 127 ∧
    16 = conditionalCredit 127 := by decide +kernel

theorem conditioned_127 (code : Nat) :
    conditionedCredit 127 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 127 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 127 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_127
#print axioms conditioned_127

end Snake9.Context101
