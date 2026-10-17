import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 476 = false := by
  rw [value476]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count475 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true ∨ valuation q 237 = true ∨ valuation q 238 = true ∨ valuation q 239 = true ∨ valuation q 240 = true := by
  rw [value121, value122, value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236, value237, value238, value239, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 829 = true := by
  have hs : count829 q = (countLit q [-16]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (829)) (countLit q [-16]) (countLit q [-17]) (count829 q) 1 (meaningNeg16 q) (meaning829 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 829 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 829 = false ∨ valuationOf q 832 = true := by
  have hs : count831 q = (countLit q [-14]) + (countLit q [-16, -17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -17])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (829)) (literal (valuationOf q) (832)) (countLit q [-14]) (countLit q [-16, -17]) (count831 q) 1 1 (meaningNeg14 q) (meaning829 q) (meaning832 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 829 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 829 = false ∨ valuation q 832 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 843 = true := by
  have hs : count842 q = (countLit q [-14, -16, -17]) + (countLit q [-19, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -17]) (l₂ := [-19, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (832)) (literal (valuationOf q) (843)) (countLit q [-14, -16, -17]) (countLit q [-19, -23, -25, -27]) (count842 q) 2 (meaning832 q) (meaning843 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 843 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 850 = true := by
  have hs : count849 q = (countLit q [-1, -4, -7, -8, -9, -10, -11]) + (countLit q [-14, -16, -17, -19, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -8, -9, -10, -11]) (l₂ := [-14, -16, -17, -19, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (843)) (literal (valuationOf q) (850)) (countLit q [-1, -4, -7, -8, -9, -10, -11]) (countLit q [-14, -16, -17, -19, -23, -25, -27]) (count849 q) 2 (meaning843 q) (meaning850 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 850 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 870 = true := by
  have hs : count870 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (870)) (countLit q [-39]) (countLit q [-41]) (count870 q) 1 (meaningNeg41 q) (meaning870 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 870 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 872 = true := by
  have hs : count872 q = (countLit q [-34, -37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-34, -37]) (l₂ := [-39, -41])
  have hm := merge_right (literal (valuationOf q) (870)) (literal (valuationOf q) (872)) (countLit q [-34, -37]) (countLit q [-39, -41]) (count872 q) 1 (meaning870 q) (meaning872 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 872 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count876 q = (countLit q [-29, -31, -33]) + (countLit q [-34, -37, -39, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33]) (l₂ := [-34, -37, -39, -41])
  have hm := merge_right (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-29, -31, -33]) (countLit q [-34, -37, -39, -41]) (count876 q) 1 (meaning872 q) (meaning876 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 876 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (883)) (countLit q [-43]) (countLit q [-45]) (count883 q) 1 (meaningNeg43 q) (meaning883 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 883 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 885 = true := by
  have hs : count885 q = (countLit q [-47]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (885)) (countLit q [-47]) (countLit q [-49]) (count885 q) 1 (meaningNeg49 q) (meaning885 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 885 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 885 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-43, -45]) + (countLit q [-47, -49]) := List.countP_append (p := literal q) (l₁ := [-43, -45]) (l₂ := [-47, -49])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (885)) (literal (valuationOf q) (888)) (countLit q [-43, -45]) (countLit q [-47, -49]) (count887 q) 1 1 (meaning883 q) (meaning885 q) (meaning888 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 885 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 885 = false ∨ valuation q 888 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 891 = true := by
  have hs : count891 q = (countLit q [-50]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (891)) (countLit q [-50]) (countLit q [-54]) (count891 q) 1 (meaningNeg50 q) (meaning891 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 891 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-50, -54]) + (countLit q [-55, -57]) := List.countP_append (p := literal q) (l₁ := [-50, -54]) (l₂ := [-55, -57])
  have hm := merge_left (literal (valuationOf q) (891)) (literal (valuationOf q) (895)) (countLit q [-50, -54]) (countLit q [-55, -57]) (count895 q) 1 (meaning891 q) (meaning895 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 895 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 895 = false ∨ valuationOf q 901 = true := by
  have hs : count899 q = (countLit q [-43, -45, -47, -49]) + (countLit q [-50, -54, -55, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -49]) (l₂ := [-50, -54, -55, -57])
  have hm := merge_two (literal (valuationOf q) (888)) (literal (valuationOf q) (895)) (literal (valuationOf q) (901)) (countLit q [-43, -45, -47, -49]) (countLit q [-50, -54, -55, -57]) (count899 q) 2 1 (meaning888 q) (meaning895 q) (meaning901 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 895 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 895 = false ∨ valuation q 901 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 901 = false ∨ valuationOf q 910 = true := by
  have hs : count907 q = (countLit q [-29, -31, -33, -34, -37, -39, -41]) + (countLit q [-43, -45, -47, -49, -50, -54, -55, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33, -34, -37, -39, -41]) (l₂ := [-43, -45, -47, -49, -50, -54, -55, -57])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (901)) (literal (valuationOf q) (910)) (countLit q [-29, -31, -33, -34, -37, -39, -41]) (countLit q [-43, -45, -47, -49, -50, -54, -55, -57]) (count907 q) 1 3 (meaning876 q) (meaning901 q) (meaning910 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 901 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 901 = false ∨ valuation q 910 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 910 = false ∨ valuationOf q 927 = true := by
  have hs : count922 q = (countLit q [-1, -4, -7, -8, -9, -10, -11, -14, -16, -17, -19, -23, -25, -27]) + (countLit q [-29, -31, -33, -34, -37, -39, -41, -43, -45, -47, -49, -50, -54, -55, -57]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -8, -9, -10, -11, -14, -16, -17, -19, -23, -25, -27]) (l₂ := [-29, -31, -33, -34, -37, -39, -41, -43, -45, -47, -49, -50, -54, -55, -57])
  have hm := merge_two (literal (valuationOf q) (850)) (literal (valuationOf q) (910)) (literal (valuationOf q) (927)) (countLit q [-1, -4, -7, -8, -9, -10, -11, -14, -16, -17, -19, -23, -25, -27]) (countLit q [-29, -31, -33, -34, -37, -39, -41, -43, -45, -47, -49, -50, -54, -55, -57]) (count922 q) 2 4 (meaning850 q) (meaning910 q) (meaning927 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 910 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 910 = false ∨ valuation q 927 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 941 = true := by
  have hs : count941 q = (countLit q [-63]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65])
  have hm := merge_right (literal (valuationOf q) (-65)) (literal (valuationOf q) (941)) (countLit q [-63]) (countLit q [-65]) (count941 q) 1 (meaningNeg65 q) (meaning941 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 941 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 941 = false ∨ valuationOf q 944 = true := by
  have hs : count943 q = (countLit q [-58]) + (countLit q [-63, -65]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-63, -65])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (941)) (literal (valuationOf q) (944)) (countLit q [-58]) (countLit q [-63, -65]) (count943 q) 1 1 (meaningNeg58 q) (meaning941 q) (meaning944 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 941 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 941 = false ∨ valuation q 944 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 946 = true := by
  have hs : count946 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (946)) (countLit q [-66]) (countLit q [-68]) (count946 q) 1 (meaningNeg68 q) (meaning946 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 946 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 948 = true := by
  have hs : count948 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (948)) (countLit q [-69]) (countLit q [-72]) (count948 q) 1 (meaningNeg72 q) (meaning948 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 948 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 948 = false ∨ valuationOf q 951 = true := by
  have hs : count950 q = (countLit q [-66, -68]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -72])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (948)) (literal (valuationOf q) (951)) (countLit q [-66, -68]) (countLit q [-69, -72]) (count950 q) 1 1 (meaning946 q) (meaning948 q) (meaning951 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 948 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 948 = false ∨ valuation q 951 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 951 = false ∨ valuationOf q 957 = true := by
  have hs : count954 q = (countLit q [-58, -63, -65]) + (countLit q [-66, -68, -69, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -63, -65]) (l₂ := [-66, -68, -69, -72])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (951)) (literal (valuationOf q) (957)) (countLit q [-58, -63, -65]) (countLit q [-66, -68, -69, -72]) (count954 q) 2 2 (meaning944 q) (meaning951 q) (meaning957 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 951 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 951 = false ∨ valuation q 957 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 85 = true ∨ valuationOf q 970 = true := by
  have hs : count969 q = (countLit q [-81]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (970)) (countLit q [-81]) (countLit q [-85]) (count969 q) 1 1 (meaningNeg81 q) (meaningNeg85 q) (meaning970 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 970 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 970 = false ∨ valuationOf q 974 = true := by
  have hs : count973 q = (countLit q [-81, -85]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -85]) (l₂ := [-88, -89])
  have hm := merge_left (literal (valuationOf q) (970)) (literal (valuationOf q) (974)) (countLit q [-81, -85]) (countLit q [-88, -89]) (count973 q) 2 (meaning970 q) (meaning974 q) hs
  change valuationOf q 970 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 970 = false ∨ valuation q 974 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 978 = true := by
  have hs : count977 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -88, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -88, -89])
  have hm := merge_right (literal (valuationOf q) (974)) (literal (valuationOf q) (978)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -88, -89]) (count977 q) 2 (meaning974 q) (meaning978 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 978 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 978 = false ∨ valuationOf q 990 = true := by
  have hs : count985 q = (countLit q [-58, -63, -65, -66, -68, -69, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -88, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -63, -65, -66, -68, -69, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -88, -89])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (978)) (literal (valuationOf q) (990)) (countLit q [-58, -63, -65, -66, -68, -69, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -88, -89]) (count985 q) 4 2 (meaning957 q) (meaning978 q) (meaning990 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 978 = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 978 = false ∨ valuation q 990 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1002 = true := by
  have hs : count1002 q = (countLit q [-92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -94])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1002)) (countLit q [-92]) (countLit q [-93, -94]) (count1002 q) 1 (meaningNeg92 q) (meaning1002 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1002 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1005 = true := by
  have hs : count1005 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1005)) (countLit q [-95]) (countLit q [-96]) (count1005 q) 1 (meaningNeg95 q) (meaning1005 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1005 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1008 = true := by
  have hs : count1007 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1008)) (countLit q [-99]) (countLit q [-100]) (count1007 q) 1 1 (meaningNeg99 q) (meaningNeg100 q) (meaning1008 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 1008 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1011 = true := by
  have hs : count1009 q = (countLit q [-95, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1008)) (literal (valuationOf q) (1011)) (countLit q [-95, -96]) (countLit q [-99, -100]) (count1009 q) 1 2 (meaning1005 q) (meaning1008 q) (meaning1011 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1008 = false ∨ valuation q 1011 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1016 = true := by
  have hs : count1013 q = (countLit q [-92, -93, -94]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1016)) (countLit q [-92, -93, -94]) (countLit q [-95, -96, -99, -100]) (count1013 q) 1 3 (meaning1002 q) (meaning1011 q) (meaning1016 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1011 = false ∨ valuation q 1016 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E004.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112004
