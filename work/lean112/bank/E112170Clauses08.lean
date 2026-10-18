import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 1151 = false ∨ valuationOf q 1157 = false ∨ valuationOf q 1161 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1151)) (literal (valuationOf q) (1157)) (literal (valuationOf q) (1161)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11]) (count1159 q) 1 2 (meaning1151 q) (meaning1157 q) (meaning1161 q) hs
  change valuationOf q 1151 = false ∨ valuationOf q 1157 = false ∨ valuationOf q 1161 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 1151 = false ∨ valuation q 1157 = false ∨ valuation q 1161 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 1151 = false ∨ valuationOf q 1158 = false ∨ valuationOf q 1162 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1151)) (literal (valuationOf q) (1158)) (literal (valuationOf q) (1162)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11]) (count1159 q) 1 3 (meaning1151 q) (meaning1158 q) (meaning1162 q) hs
  change valuationOf q 1151 = false ∨ valuationOf q 1158 = false ∨ valuationOf q 1162 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 1151 = false ∨ valuation q 1158 = false ∨ valuation q 1162 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 1152 = false ∨ valuationOf q 1160 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11])
  have hm := merge_left (literal (valuationOf q) (1152)) (literal (valuationOf q) (1160)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11]) (count1159 q) 2 (meaning1152 q) (meaning1160 q) hs
  change valuationOf q 1152 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 1152 = false ∨ valuation q 1160 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 1153 = false ∨ valuationOf q 1161 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11])
  have hm := merge_left (literal (valuationOf q) (1153)) (literal (valuationOf q) (1161)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11]) (count1159 q) 3 (meaning1153 q) (meaning1161 q) hs
  change valuationOf q 1153 = false ∨ valuationOf q 1161 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 1153 = false ∨ valuation q 1161 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 1153 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1162 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1153)) (literal (valuationOf q) (1156)) (literal (valuationOf q) (1162)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11]) (count1159 q) 3 1 (meaning1153 q) (meaning1156 q) (meaning1162 q) hs
  change valuationOf q 1153 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1162 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 1153 = false ∨ valuation q 1156 = false ∨ valuation q 1162 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1170 = true := by
  have hs : count1170 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1170)) (countLit q [-22]) (countLit q [-23]) (count1170 q) 1 (meaningNeg23 q) (meaning1170 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1170 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1170 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1170 = true := by
  have hs : count1170 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1170)) (countLit q [-22]) (countLit q [-23]) (count1170 q) 1 (meaningNeg22 q) (meaning1170 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1170 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1170 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1171 = true := by
  have hs : count1170 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1171)) (countLit q [-22]) (countLit q [-23]) (count1170 q) 1 1 (meaningNeg22 q) (meaningNeg23 q) (meaning1171 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1171 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 1171 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 1170 = false ∨ valuationOf q 1172 = true := by
  have hs : count1172 q = (countLit q [-19]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-22, -23])
  have hm := merge_right (literal (valuationOf q) (1170)) (literal (valuationOf q) (1172)) (countLit q [-19]) (countLit q [-22, -23]) (count1172 q) 1 (meaning1170 q) (meaning1172 q) hs
  change valuationOf q 1170 = false ∨ valuationOf q 1172 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 1170 = false ∨ valuation q 1172 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 1171 = false ∨ valuationOf q 1173 = true := by
  have hs : count1172 q = (countLit q [-19]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-22, -23])
  have hm := merge_right (literal (valuationOf q) (1171)) (literal (valuationOf q) (1173)) (countLit q [-19]) (countLit q [-22, -23]) (count1172 q) 2 (meaning1171 q) (meaning1173 q) hs
  change valuationOf q 1171 = false ∨ valuationOf q 1173 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 1171 = false ∨ valuation q 1173 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 1172 = false ∨ valuationOf q 1175 = true := by
  have hs : count1175 q = (countLit q [-14, -16, -17]) + (countLit q [-19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -17]) (l₂ := [-19, -22, -23])
  have hm := merge_right (literal (valuationOf q) (1172)) (literal (valuationOf q) (1175)) (countLit q [-14, -16, -17]) (countLit q [-19, -22, -23]) (count1175 q) 1 (meaning1172 q) (meaning1175 q) hs
  change valuationOf q 1172 = false ∨ valuationOf q 1175 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 1172 = false ∨ valuation q 1175 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 1173 = false ∨ valuationOf q 1176 = true := by
  have hs : count1175 q = (countLit q [-14, -16, -17]) + (countLit q [-19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -17]) (l₂ := [-19, -22, -23])
  have hm := merge_right (literal (valuationOf q) (1173)) (literal (valuationOf q) (1176)) (countLit q [-14, -16, -17]) (countLit q [-19, -22, -23]) (count1175 q) 2 (meaning1173 q) (meaning1176 q) hs
  change valuationOf q 1173 = false ∨ valuationOf q 1176 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 1173 = false ∨ valuation q 1176 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 1159 = false ∨ valuationOf q 1181 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -5, -8, -10, -11]) + (countLit q [-14, -16, -17, -19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11]) (l₂ := [-14, -16, -17, -19, -22, -23])
  have hm := merge_left (literal (valuationOf q) (1159)) (literal (valuationOf q) (1181)) (countLit q [-2, -3, -5, -8, -10, -11]) (countLit q [-14, -16, -17, -19, -22, -23]) (count1181 q) 1 (meaning1159 q) (meaning1181 q) hs
  change valuationOf q 1159 = false ∨ valuationOf q 1181 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 1159 = false ∨ valuation q 1181 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 1159 = false ∨ valuationOf q 1175 = false ∨ valuationOf q 1182 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -5, -8, -10, -11]) + (countLit q [-14, -16, -17, -19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11]) (l₂ := [-14, -16, -17, -19, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1159)) (literal (valuationOf q) (1175)) (literal (valuationOf q) (1182)) (countLit q [-2, -3, -5, -8, -10, -11]) (countLit q [-14, -16, -17, -19, -22, -23]) (count1181 q) 1 1 (meaning1159 q) (meaning1175 q) (meaning1182 q) hs
  change valuationOf q 1159 = false ∨ valuationOf q 1175 = false ∨ valuationOf q 1182 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 1159 = false ∨ valuation q 1175 = false ∨ valuation q 1182 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 1159 = false ∨ valuationOf q 1176 = false ∨ valuationOf q 1183 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -5, -8, -10, -11]) + (countLit q [-14, -16, -17, -19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11]) (l₂ := [-14, -16, -17, -19, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1159)) (literal (valuationOf q) (1176)) (literal (valuationOf q) (1183)) (countLit q [-2, -3, -5, -8, -10, -11]) (countLit q [-14, -16, -17, -19, -22, -23]) (count1181 q) 1 2 (meaning1159 q) (meaning1176 q) (meaning1183 q) hs
  change valuationOf q 1159 = false ∨ valuationOf q 1176 = false ∨ valuationOf q 1183 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 1159 = false ∨ valuation q 1176 = false ∨ valuation q 1183 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 1160 = false ∨ valuationOf q 1182 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -5, -8, -10, -11]) + (countLit q [-14, -16, -17, -19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11]) (l₂ := [-14, -16, -17, -19, -22, -23])
  have hm := merge_left (literal (valuationOf q) (1160)) (literal (valuationOf q) (1182)) (countLit q [-2, -3, -5, -8, -10, -11]) (countLit q [-14, -16, -17, -19, -22, -23]) (count1181 q) 2 (meaning1160 q) (meaning1182 q) hs
  change valuationOf q 1160 = false ∨ valuationOf q 1182 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 1160 = false ∨ valuation q 1182 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 1160 = false ∨ valuationOf q 1175 = false ∨ valuationOf q 1183 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -5, -8, -10, -11]) + (countLit q [-14, -16, -17, -19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11]) (l₂ := [-14, -16, -17, -19, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1160)) (literal (valuationOf q) (1175)) (literal (valuationOf q) (1183)) (countLit q [-2, -3, -5, -8, -10, -11]) (countLit q [-14, -16, -17, -19, -22, -23]) (count1181 q) 2 1 (meaning1160 q) (meaning1175 q) (meaning1183 q) hs
  change valuationOf q 1160 = false ∨ valuationOf q 1175 = false ∨ valuationOf q 1183 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 1160 = false ∨ valuation q 1175 = false ∨ valuation q 1183 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 1161 = false ∨ valuationOf q 1183 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -5, -8, -10, -11]) + (countLit q [-14, -16, -17, -19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11]) (l₂ := [-14, -16, -17, -19, -22, -23])
  have hm := merge_left (literal (valuationOf q) (1161)) (literal (valuationOf q) (1183)) (countLit q [-2, -3, -5, -8, -10, -11]) (countLit q [-14, -16, -17, -19, -22, -23]) (count1181 q) 3 (meaning1161 q) (meaning1183 q) hs
  change valuationOf q 1161 = false ∨ valuationOf q 1183 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 1161 = false ∨ valuation q 1183 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 1161 = false ∨ valuationOf q 1175 = false ∨ valuationOf q 1184 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -5, -8, -10, -11]) + (countLit q [-14, -16, -17, -19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11]) (l₂ := [-14, -16, -17, -19, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1161)) (literal (valuationOf q) (1175)) (literal (valuationOf q) (1184)) (countLit q [-2, -3, -5, -8, -10, -11]) (countLit q [-14, -16, -17, -19, -22, -23]) (count1181 q) 3 1 (meaning1161 q) (meaning1175 q) (meaning1184 q) hs
  change valuationOf q 1161 = false ∨ valuationOf q 1175 = false ∨ valuationOf q 1184 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 1161 = false ∨ valuation q 1175 = false ∨ valuation q 1184 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 1162 = false ∨ valuationOf q 1184 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -5, -8, -10, -11]) + (countLit q [-14, -16, -17, -19, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11]) (l₂ := [-14, -16, -17, -19, -22, -23])
  have hm := merge_left (literal (valuationOf q) (1162)) (literal (valuationOf q) (1184)) (countLit q [-2, -3, -5, -8, -10, -11]) (countLit q [-14, -16, -17, -19, -22, -23]) (count1181 q) 4 (meaning1162 q) (meaning1184 q) hs
  change valuationOf q 1162 = false ∨ valuationOf q 1184 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 1162 = false ∨ valuation q 1184 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1190)) (countLit q [-27]) (countLit q [-29]) (count1190 q) 1 (meaningNeg29 q) (meaning1190 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1190 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1190)) (countLit q [-27]) (countLit q [-29]) (count1190 q) 1 (meaningNeg27 q) (meaning1190 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1190 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 29 = true ∨ valuationOf q 1191 = true := by
  have hs : count1190 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (1191)) (countLit q [-27]) (countLit q [-29]) (count1190 q) 1 1 (meaningNeg27 q) (meaningNeg29 q) (meaning1191 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 1191 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 1191 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 1190 = false ∨ valuationOf q 1192 = true := by
  have hs : count1192 q = (countLit q [-26]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1190)) (literal (valuationOf q) (1192)) (countLit q [-26]) (countLit q [-27, -29]) (count1192 q) 1 (meaning1190 q) (meaning1192 q) hs
  change valuationOf q 1190 = false ∨ valuationOf q 1192 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 1190 = false ∨ valuation q 1192 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 1191 = false ∨ valuationOf q 1193 = true := by
  have hs : count1192 q = (countLit q [-26]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1191)) (literal (valuationOf q) (1193)) (countLit q [-26]) (countLit q [-27, -29]) (count1192 q) 2 (meaning1191 q) (meaning1193 q) hs
  change valuationOf q 1191 = false ∨ valuationOf q 1193 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 1191 = false ∨ valuation q 1193 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1192 = true := by
  have hs : count1192 q = (countLit q [-26]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1192)) (countLit q [-26]) (countLit q [-27, -29]) (count1192 q) 1 (meaningNeg26 q) (meaning1192 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1192 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1192 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1190 = false ∨ valuationOf q 1193 = true := by
  have hs : count1192 q = (countLit q [-26]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (1190)) (literal (valuationOf q) (1193)) (countLit q [-26]) (countLit q [-27, -29]) (count1192 q) 1 1 (meaningNeg26 q) (meaning1190 q) (meaning1193 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1190 = false ∨ valuationOf q 1193 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1190 = false ∨ valuation q 1193 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1191 = false ∨ valuationOf q 1194 = true := by
  have hs : count1192 q = (countLit q [-26]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (1191)) (literal (valuationOf q) (1194)) (countLit q [-26]) (countLit q [-27, -29]) (count1192 q) 1 2 (meaningNeg26 q) (meaning1191 q) (meaning1194 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1191 = false ∨ valuationOf q 1194 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1191 = false ∨ valuation q 1194 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1195)) (countLit q [-33]) (countLit q [-35]) (count1195 q) 1 (meaningNeg35 q) (meaning1195 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1195 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1195)) (countLit q [-33]) (countLit q [-35]) (count1195 q) 1 (meaningNeg33 q) (meaning1195 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1195 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1196 = true := by
  have hs : count1195 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1196)) (countLit q [-33]) (countLit q [-35]) (count1195 q) 1 1 (meaningNeg33 q) (meaningNeg35 q) (meaning1196 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1196 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 1196 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 1195 = false ∨ valuationOf q 1197 = true := by
  have hs : count1197 q = (countLit q [-32]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (1195)) (literal (valuationOf q) (1197)) (countLit q [-32]) (countLit q [-33, -35]) (count1197 q) 1 (meaning1195 q) (meaning1197 q) hs
  change valuationOf q 1195 = false ∨ valuationOf q 1197 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 1195 = false ∨ valuation q 1197 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E170.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112170
