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

theorem direction_128 :
    11 = geometricCredits.getD 128 0 ∧
    16 = completedCredit 128 ∧
    16 = conditionalCredit 128 := by decide +kernel

theorem conditioned_128 (code : Nat) :
    conditionedCredit 128 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 128 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 128 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_128
#print axioms conditioned_128

theorem direction_129 :
    31 = geometricCredits.getD 129 0 ∧
    16 = completedCredit 129 ∧
    16 = conditionalCredit 129 := by decide +kernel

theorem conditioned_129 (code : Nat) :
    conditionedCredit 129 code = 0 := by
  have hf : canon ((extensions.getD 129 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 129 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_129
#print axioms conditioned_129

theorem direction_130 :
    42 = geometricCredits.getD 130 0 ∧
    12 = completedCredit 130 ∧
    16 = conditionalCredit 130 := by decide +kernel

theorem conditioned_130 (code : Nat) :
    conditionedCredit 130 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 130 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 130 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_130
#print axioms conditioned_130

theorem direction_131 :
    6 = geometricCredits.getD 131 0 ∧
    16 = completedCredit 131 ∧
    16 = conditionalCredit 131 := by decide +kernel

theorem conditioned_131 (code : Nat) :
    conditionedCredit 131 code = 0 := by
  have hf : canon ((extensions.getD 131 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 131 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_131
#print axioms conditioned_131

theorem direction_132 :
    13 = geometricCredits.getD 132 0 ∧
    16 = completedCredit 132 ∧
    16 = conditionalCredit 132 := by decide +kernel

theorem conditioned_132 (code : Nat) :
    conditionedCredit 132 code = 0 := by
  have hf : canon ((extensions.getD 132 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 132 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_132
#print axioms conditioned_132

theorem direction_133 :
    13 = geometricCredits.getD 133 0 ∧
    12 = completedCredit 133 ∧
    16 = conditionalCredit 133 := by decide +kernel

theorem conditioned_133 (code : Nat) :
    conditionedCredit 133 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 133 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 133 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_133
#print axioms conditioned_133

theorem direction_134 :
    13 = geometricCredits.getD 134 0 ∧
    0 = completedCredit 134 ∧
    16 = conditionalCredit 134 := by decide +kernel

theorem conditioned_134 (code : Nat) :
    conditionedCredit 134 code = 0 := by
  have hf : canon ((extensions.getD 134 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 134 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_134
#print axioms conditioned_134

theorem direction_135 :
    13 = geometricCredits.getD 135 0 ∧
    0 = completedCredit 135 ∧
    18 = conditionalCredit 135 := by decide +kernel

theorem conditioned_135 (code : Nat) :
    conditionedCredit 135 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 135 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 135 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_135
#print axioms conditioned_135

theorem direction_136 :
    13 = geometricCredits.getD 136 0 ∧
    12 = completedCredit 136 ∧
    16 = conditionalCredit 136 := by decide +kernel

theorem conditioned_136 (code : Nat) :
    conditionedCredit 136 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 136 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 136 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_136
#print axioms conditioned_136

theorem direction_137 :
    14 = geometricCredits.getD 137 0 ∧
    16 = completedCredit 137 ∧
    16 = conditionalCredit 137 := by decide +kernel

theorem conditioned_137 (code : Nat) :
    conditionedCredit 137 code = 0 := by
  have hf : canon ((extensions.getD 137 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 137 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_137
#print axioms conditioned_137

theorem direction_138 :
    18 = geometricCredits.getD 138 0 ∧
    0 = completedCredit 138 ∧
    18 = conditionalCredit 138 := by decide +kernel

theorem conditioned_138 (code : Nat) :
    conditionedCredit 138 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 138 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 138 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_138
#print axioms conditioned_138

theorem direction_139 :
    0 = geometricCredits.getD 139 0 ∧
    0 = completedCredit 139 ∧
    18 = conditionalCredit 139 := by decide +kernel

theorem conditioned_139 (code : Nat) :
    conditionedCredit 139 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 139 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 139 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_139
#print axioms conditioned_139

theorem direction_140 :
    10 = geometricCredits.getD 140 0 ∧
    16 = completedCredit 140 ∧
    16 = conditionalCredit 140 := by decide +kernel

theorem conditioned_140 (code : Nat) :
    conditionedCredit 140 code = 0 := by
  have hf : canon ((extensions.getD 140 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 140 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_140
#print axioms conditioned_140

theorem direction_141 :
    10 = geometricCredits.getD 141 0 ∧
    0 = completedCredit 141 ∧
    18 = conditionalCredit 141 := by decide +kernel

theorem conditioned_141 (code : Nat) :
    conditionedCredit 141 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 141 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 141 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_141
#print axioms conditioned_141

theorem direction_142 :
    10 = geometricCredits.getD 142 0 ∧
    0 = completedCredit 142 ∧
    18 = conditionalCredit 142 := by decide +kernel

theorem conditioned_142 (code : Nat) :
    conditionedCredit 142 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 142 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 142 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_142
#print axioms conditioned_142

theorem direction_143 :
    5 = geometricCredits.getD 143 0 ∧
    0 = completedCredit 143 ∧
    16 = conditionalCredit 143 := by decide +kernel

theorem conditioned_143 (code : Nat) :
    conditionedCredit 143 code = 0 := by
  have hf : canon ((extensions.getD 143 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 143 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_143
#print axioms conditioned_143

theorem direction_144 :
    10 = geometricCredits.getD 144 0 ∧
    0 = completedCredit 144 ∧
    18 = conditionalCredit 144 := by decide +kernel

theorem conditioned_144 (code : Nat) :
    conditionedCredit 144 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 144 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 144 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_144
#print axioms conditioned_144

theorem direction_145 :
    5 = geometricCredits.getD 145 0 ∧
    16 = completedCredit 145 ∧
    16 = conditionalCredit 145 := by decide +kernel

theorem conditioned_145 (code : Nat) :
    conditionedCredit 145 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 145 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 145 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_145
#print axioms conditioned_145

theorem direction_146 :
    5 = geometricCredits.getD 146 0 ∧
    16 = completedCredit 146 ∧
    16 = conditionalCredit 146 := by decide +kernel

theorem conditioned_146 (code : Nat) :
    conditionedCredit 146 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 146 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 146 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_146
#print axioms conditioned_146

theorem direction_147 :
    0 = geometricCredits.getD 147 0 ∧
    12 = completedCredit 147 ∧
    12 = conditionalCredit 147 := by decide +kernel

theorem conditioned_147 (code : Nat) :
    conditionedCredit 147 code = 0 := by
  have hf : canon ((extensions.getD 147 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 147 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_147
#print axioms conditioned_147

theorem direction_148 :
    5 = geometricCredits.getD 148 0 ∧
    16 = completedCredit 148 ∧
    16 = conditionalCredit 148 := by decide +kernel

theorem conditioned_148 (code : Nat) :
    conditionedCredit 148 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 148 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 148 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_148
#print axioms conditioned_148

theorem direction_149 :
    0 = geometricCredits.getD 149 0 ∧
    16 = completedCredit 149 ∧
    16 = conditionalCredit 149 := by decide +kernel

theorem conditioned_149 (code : Nat) :
    conditionedCredit 149 code = 0 := by
  have hf : canon ((extensions.getD 149 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 149 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_149
#print axioms conditioned_149

theorem direction_150 :
    0 = geometricCredits.getD 150 0 ∧
    12 = completedCredit 150 ∧
    16 = conditionalCredit 150 := by decide +kernel

theorem conditioned_150 (code : Nat) :
    conditionedCredit 150 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 150 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 150 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_150
#print axioms conditioned_150

theorem direction_151 :
    0 = geometricCredits.getD 151 0 ∧
    0 = completedCredit 151 ∧
    16 = conditionalCredit 151 := by decide +kernel

theorem conditioned_151 (code : Nat) :
    conditionedCredit 151 code = 0 := by
  have hf : canon ((extensions.getD 151 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 151 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_151
#print axioms conditioned_151

theorem direction_152 :
    0 = geometricCredits.getD 152 0 ∧
    0 = completedCredit 152 ∧
    18 = conditionalCredit 152 := by decide +kernel

theorem conditioned_152 (code : Nat) :
    conditionedCredit 152 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 152 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 152 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_152
#print axioms conditioned_152

theorem direction_153 :
    0 = geometricCredits.getD 153 0 ∧
    12 = completedCredit 153 ∧
    16 = conditionalCredit 153 := by decide +kernel

theorem conditioned_153 (code : Nat) :
    conditionedCredit 153 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 153 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 153 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_153
#print axioms conditioned_153

theorem direction_154 :
    0 = geometricCredits.getD 154 0 ∧
    16 = completedCredit 154 ∧
    16 = conditionalCredit 154 := by decide +kernel

theorem conditioned_154 (code : Nat) :
    conditionedCredit 154 code = 0 := by
  have hf : canon ((extensions.getD 154 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 154 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_154
#print axioms conditioned_154

theorem direction_155 :
    0 = geometricCredits.getD 155 0 ∧
    12 = completedCredit 155 ∧
    16 = conditionalCredit 155 := by decide +kernel

theorem conditioned_155 (code : Nat) :
    conditionedCredit 155 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 155 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 155 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_155
#print axioms conditioned_155

theorem direction_156 :
    0 = geometricCredits.getD 156 0 ∧
    0 = completedCredit 156 ∧
    16 = conditionalCredit 156 := by decide +kernel

theorem conditioned_156 (code : Nat) :
    conditionedCredit 156 code = 0 := by
  have hf : canon ((extensions.getD 156 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 156 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_156
#print axioms conditioned_156

theorem direction_157 :
    0 = geometricCredits.getD 157 0 ∧
    0 = completedCredit 157 ∧
    18 = conditionalCredit 157 := by decide +kernel

theorem conditioned_157 (code : Nat) :
    conditionedCredit 157 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 157 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 157 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_157
#print axioms conditioned_157

theorem direction_158 :
    0 = geometricCredits.getD 158 0 ∧
    12 = completedCredit 158 ∧
    16 = conditionalCredit 158 := by decide +kernel

theorem conditioned_158 (code : Nat) :
    conditionedCredit 158 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 158 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 158 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_158
#print axioms conditioned_158

theorem direction_159 :
    6 = geometricCredits.getD 159 0 ∧
    0 = completedCredit 159 ∧
    16 = conditionalCredit 159 := by decide +kernel

theorem conditioned_159 (code : Nat) :
    conditionedCredit 159 code = 0 := by
  have hf : canon ((extensions.getD 159 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 159 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_159
#print axioms conditioned_159

theorem direction_160 :
    18 = geometricCredits.getD 160 0 ∧
    16 = completedCredit 160 ∧
    16 = conditionalCredit 160 := by decide +kernel

theorem conditioned_160 (code : Nat) :
    conditionedCredit 160 code = 0 := by
  have hf : canon ((extensions.getD 160 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 160 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_160
#print axioms conditioned_160

theorem direction_161 :
    18 = geometricCredits.getD 161 0 ∧
    16 = completedCredit 161 ∧
    16 = conditionalCredit 161 := by decide +kernel

theorem conditioned_161 (code : Nat) :
    conditionedCredit 161 code = 0 := by
  have hf : canon ((extensions.getD 161 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 161 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_161
#print axioms conditioned_161

theorem direction_162 :
    12 = geometricCredits.getD 162 0 ∧
    16 = completedCredit 162 ∧
    16 = conditionalCredit 162 := by decide +kernel

theorem conditioned_162 (code : Nat) :
    conditionedCredit 162 code = 0 := by
  have hf : canon ((extensions.getD 162 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 162 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_162
#print axioms conditioned_162

theorem direction_163 :
    18 = geometricCredits.getD 163 0 ∧
    16 = completedCredit 163 ∧
    16 = conditionalCredit 163 := by decide +kernel

theorem conditioned_163 (code : Nat) :
    conditionedCredit 163 code = 0 := by
  have hf : canon ((extensions.getD 163 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 163 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_163
#print axioms conditioned_163

theorem direction_164 :
    0 = geometricCredits.getD 164 0 ∧
    16 = completedCredit 164 ∧
    16 = conditionalCredit 164 := by decide +kernel

theorem conditioned_164 (code : Nat) :
    conditionedCredit 164 code = 0 := by
  have hf : canon ((extensions.getD 164 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 164 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_164
#print axioms conditioned_164

theorem direction_165 :
    0 = geometricCredits.getD 165 0 ∧
    12 = completedCredit 165 ∧
    16 = conditionalCredit 165 := by decide +kernel

theorem conditioned_165 (code : Nat) :
    conditionedCredit 165 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 165 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 165 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_165
#print axioms conditioned_165

theorem direction_166 :
    0 = geometricCredits.getD 166 0 ∧
    12 = completedCredit 166 ∧
    16 = conditionalCredit 166 := by decide +kernel

theorem conditioned_166 (code : Nat) :
    conditionedCredit 166 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 166 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 166 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_166
#print axioms conditioned_166

theorem direction_167 :
    0 = geometricCredits.getD 167 0 ∧
    0 = completedCredit 167 ∧
    16 = conditionalCredit 167 := by decide +kernel

theorem conditioned_167 (code : Nat) :
    conditionedCredit 167 code = 0 := by
  have hf : canon ((extensions.getD 167 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 167 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_167
#print axioms conditioned_167

theorem direction_168 :
    0 = geometricCredits.getD 168 0 ∧
    0 = completedCredit 168 ∧
    18 = conditionalCredit 168 := by decide +kernel

theorem conditioned_168 (code : Nat) :
    conditionedCredit 168 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 168 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 168 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_168
#print axioms conditioned_168

theorem direction_169 :
    0 = geometricCredits.getD 169 0 ∧
    12 = completedCredit 169 ∧
    16 = conditionalCredit 169 := by decide +kernel

theorem conditioned_169 (code : Nat) :
    conditionedCredit 169 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 169 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 169 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_169
#print axioms conditioned_169

theorem direction_170 :
    5 = geometricCredits.getD 170 0 ∧
    16 = completedCredit 170 ∧
    16 = conditionalCredit 170 := by decide +kernel

theorem conditioned_170 (code : Nat) :
    conditionedCredit 170 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 170 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 170 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_170
#print axioms conditioned_170

theorem direction_171 :
    0 = geometricCredits.getD 171 0 ∧
    12 = completedCredit 171 ∧
    12 = conditionalCredit 171 := by decide +kernel

theorem conditioned_171 (code : Nat) :
    conditionedCredit 171 code = 0 := by
  have hf : canon ((extensions.getD 171 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 171 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_171
#print axioms conditioned_171

theorem direction_172 :
    5 = geometricCredits.getD 172 0 ∧
    16 = completedCredit 172 ∧
    16 = conditionalCredit 172 := by decide +kernel

theorem conditioned_172 (code : Nat) :
    conditionedCredit 172 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 172 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 172 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_172
#print axioms conditioned_172

theorem direction_173 :
    0 = geometricCredits.getD 173 0 ∧
    0 = completedCredit 173 ∧
    18 = conditionalCredit 173 := by decide +kernel

theorem conditioned_173 (code : Nat) :
    conditionedCredit 173 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 173 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 173 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_173
#print axioms conditioned_173

theorem direction_174 :
    0 = geometricCredits.getD 174 0 ∧
    16 = completedCredit 174 ∧
    16 = conditionalCredit 174 := by decide +kernel

theorem conditioned_174 (code : Nat) :
    conditionedCredit 174 code = 0 := by
  have hf : canon ((extensions.getD 174 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 174 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_174
#print axioms conditioned_174

theorem direction_175 :
    0 = geometricCredits.getD 175 0 ∧
    12 = completedCredit 175 ∧
    16 = conditionalCredit 175 := by decide +kernel

theorem conditioned_175 (code : Nat) :
    conditionedCredit 175 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 175 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 175 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_175
#print axioms conditioned_175

theorem direction_176 :
    12 = geometricCredits.getD 176 0 ∧
    16 = completedCredit 176 ∧
    16 = conditionalCredit 176 := by decide +kernel

theorem conditioned_176 (code : Nat) :
    conditionedCredit 176 code = 0 := by
  have hf : canon ((extensions.getD 176 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 176 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_176
#print axioms conditioned_176

theorem direction_177 :
    8 = geometricCredits.getD 177 0 ∧
    0 = completedCredit 177 ∧
    16 = conditionalCredit 177 := by decide +kernel

theorem conditioned_177 (code : Nat) :
    conditionedCredit 177 code = 0 := by
  have hf : canon ((extensions.getD 177 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 177 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_177
#print axioms conditioned_177

theorem direction_178 :
    20 = geometricCredits.getD 178 0 ∧
    16 = completedCredit 178 ∧
    16 = conditionalCredit 178 := by decide +kernel

theorem conditioned_178 (code : Nat) :
    conditionedCredit 178 code = 0 := by
  have hf : canon ((extensions.getD 178 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 178 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_178
#print axioms conditioned_178

theorem direction_179 :
    0 = geometricCredits.getD 179 0 ∧
    0 = completedCredit 179 ∧
    18 = conditionalCredit 179 := by decide +kernel

theorem conditioned_179 (code : Nat) :
    conditionedCredit 179 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 179 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 179 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_179
#print axioms conditioned_179

theorem direction_180 :
    0 = geometricCredits.getD 180 0 ∧
    16 = completedCredit 180 ∧
    16 = conditionalCredit 180 := by decide +kernel

theorem conditioned_180 (code : Nat) :
    conditionedCredit 180 code = 0 := by
  have hf : canon ((extensions.getD 180 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 180 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_180
#print axioms conditioned_180

theorem direction_181 :
    0 = geometricCredits.getD 181 0 ∧
    12 = completedCredit 181 ∧
    16 = conditionalCredit 181 := by decide +kernel

theorem conditioned_181 (code : Nat) :
    conditionedCredit 181 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 181 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 181 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_181
#print axioms conditioned_181

theorem direction_182 :
    0 = geometricCredits.getD 182 0 ∧
    0 = completedCredit 182 ∧
    16 = conditionalCredit 182 := by decide +kernel

theorem conditioned_182 (code : Nat) :
    conditionedCredit 182 code = 0 := by
  have hf : canon ((extensions.getD 182 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 182 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_182
#print axioms conditioned_182

theorem direction_183 :
    0 = geometricCredits.getD 183 0 ∧
    12 = completedCredit 183 ∧
    16 = conditionalCredit 183 := by decide +kernel

theorem conditioned_183 (code : Nat) :
    conditionedCredit 183 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 183 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 183 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_183
#print axioms conditioned_183

theorem direction_184 :
    7 = geometricCredits.getD 184 0 ∧
    16 = completedCredit 184 ∧
    16 = conditionalCredit 184 := by decide +kernel

theorem conditioned_184 (code : Nat) :
    conditionedCredit 184 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 184 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 184 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_184
#print axioms conditioned_184

theorem direction_185 :
    2 = geometricCredits.getD 185 0 ∧
    12 = completedCredit 185 ∧
    12 = conditionalCredit 185 := by decide +kernel

theorem conditioned_185 (code : Nat) :
    conditionedCredit 185 code = 0 := by
  have hf : canon ((extensions.getD 185 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 185 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_185
#print axioms conditioned_185

theorem direction_186 :
    7 = geometricCredits.getD 186 0 ∧
    16 = completedCredit 186 ∧
    16 = conditionalCredit 186 := by decide +kernel

theorem conditioned_186 (code : Nat) :
    conditionedCredit 186 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 186 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 186 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_186
#print axioms conditioned_186

theorem direction_187 :
    6 = geometricCredits.getD 187 0 ∧
    16 = completedCredit 187 ∧
    16 = conditionalCredit 187 := by decide +kernel

theorem conditioned_187 (code : Nat) :
    conditionedCredit 187 code = 0 := by
  have hf : canon ((extensions.getD 187 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 187 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_187
#print axioms conditioned_187

theorem direction_188 :
    6 = geometricCredits.getD 188 0 ∧
    12 = completedCredit 188 ∧
    16 = conditionalCredit 188 := by decide +kernel

theorem conditioned_188 (code : Nat) :
    conditionedCredit 188 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 188 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 188 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_188
#print axioms conditioned_188

theorem direction_189 :
    14 = geometricCredits.getD 189 0 ∧
    0 = completedCredit 189 ∧
    16 = conditionalCredit 189 := by decide +kernel

theorem conditioned_189 (code : Nat) :
    conditionedCredit 189 code = 0 := by
  have hf : canon ((extensions.getD 189 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 189 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_189
#print axioms conditioned_189

theorem direction_190 :
    26 = geometricCredits.getD 190 0 ∧
    16 = completedCredit 190 ∧
    16 = conditionalCredit 190 := by decide +kernel

theorem conditioned_190 (code : Nat) :
    conditionedCredit 190 code = 0 := by
  have hf : canon ((extensions.getD 190 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 190 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_190
#print axioms conditioned_190

theorem direction_191 :
    2 = geometricCredits.getD 191 0 ∧
    16 = completedCredit 191 ∧
    16 = conditionalCredit 191 := by decide +kernel

theorem conditioned_191 (code : Nat) :
    conditionedCredit 191 code = 0 := by
  have hf : canon ((extensions.getD 191 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 191 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_191
#print axioms conditioned_191

end Snake9.Context101
