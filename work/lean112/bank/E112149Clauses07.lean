import E112149Semantics
import B112E149Inputs
namespace Snake9.Regrowth.E112149
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 1152 = false ∨ valuationOf q 1160 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -6]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6]) (l₂ := [-8, -9, -10])
  have hm := merge_left (literal (valuationOf q) (1152)) (literal (valuationOf q) (1160)) (countLit q [-2, -3, -6]) (countLit q [-8, -9, -10]) (count1159 q) 2 (meaning1152 q) (meaning1160 q) hs
  change valuationOf q 1152 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 1152 = false ∨ valuation q 1160 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1165 = true := by
  have hs : count1165 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1165)) (countLit q [-15]) (countLit q [-18]) (count1165 q) 1 (meaningNeg18 q) (meaning1165 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1165 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1165 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1165 = true := by
  have hs : count1165 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1165)) (countLit q [-15]) (countLit q [-18]) (count1165 q) 1 (meaningNeg15 q) (meaning1165 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1165 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1165 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 18 = true ∨ valuationOf q 1166 = true := by
  have hs : count1165 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (1166)) (countLit q [-15]) (countLit q [-18]) (count1165 q) 1 1 (meaningNeg15 q) (meaningNeg18 q) (meaning1166 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 1166 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 1166 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 1165 = false ∨ valuationOf q 1167 = true := by
  have hs : count1167 q = (countLit q [-14]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -18])
  have hm := merge_right (literal (valuationOf q) (1165)) (literal (valuationOf q) (1167)) (countLit q [-14]) (countLit q [-15, -18]) (count1167 q) 1 (meaning1165 q) (meaning1167 q) hs
  change valuationOf q 1165 = false ∨ valuationOf q 1167 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 1165 = false ∨ valuation q 1167 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 1166 = false ∨ valuationOf q 1168 = true := by
  have hs : count1167 q = (countLit q [-14]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -18])
  have hm := merge_right (literal (valuationOf q) (1166)) (literal (valuationOf q) (1168)) (countLit q [-14]) (countLit q [-15, -18]) (count1167 q) 2 (meaning1166 q) (meaning1168 q) hs
  change valuationOf q 1166 = false ∨ valuationOf q 1168 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 1166 = false ∨ valuation q 1168 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1167 = true := by
  have hs : count1167 q = (countLit q [-14]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -18])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1167)) (countLit q [-14]) (countLit q [-15, -18]) (count1167 q) 1 (meaningNeg14 q) (meaning1167 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1167 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1167 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1165 = false ∨ valuationOf q 1168 = true := by
  have hs : count1167 q = (countLit q [-14]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -18])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1165)) (literal (valuationOf q) (1168)) (countLit q [-14]) (countLit q [-15, -18]) (count1167 q) 1 1 (meaningNeg14 q) (meaning1165 q) (meaning1168 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1165 = false ∨ valuationOf q 1168 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1165 = false ∨ valuation q 1168 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1170 = true := by
  have hs : count1170 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1170)) (countLit q [-22]) (countLit q [-23]) (count1170 q) 1 (meaningNeg23 q) (meaning1170 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1170 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1170 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1170 = true := by
  have hs : count1170 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1170)) (countLit q [-22]) (countLit q [-23]) (count1170 q) 1 (meaningNeg22 q) (meaning1170 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1170 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1170 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 1170 = false ∨ valuationOf q 1172 = true := by
  have hs : count1172 q = (countLit q [-20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22, -23])
  have hm := merge_right (literal (valuationOf q) (1170)) (literal (valuationOf q) (1172)) (countLit q [-20]) (countLit q [-22, -23]) (count1172 q) 1 (meaning1170 q) (meaning1172 q) hs
  change valuationOf q 1170 = false ∨ valuationOf q 1172 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 1170 = false ∨ valuation q 1172 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1172 = true := by
  have hs : count1172 q = (countLit q [-20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22, -23])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1172)) (countLit q [-20]) (countLit q [-22, -23]) (count1172 q) 1 (meaningNeg20 q) (meaning1172 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1172 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1172 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1170 = false ∨ valuationOf q 1173 = true := by
  have hs : count1172 q = (countLit q [-20]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (1170)) (literal (valuationOf q) (1173)) (countLit q [-20]) (countLit q [-22, -23]) (count1172 q) 1 1 (meaningNeg20 q) (meaning1170 q) (meaning1173 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1170 = false ∨ valuationOf q 1173 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1170 = false ∨ valuation q 1173 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 1172 = false ∨ valuationOf q 1175 = true := by
  have hs : count1175 q = (countLit q [-14, -15, -18]) + (countLit q [-20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18]) (l₂ := [-20, -22, -23])
  have hm := merge_right (literal (valuationOf q) (1172)) (literal (valuationOf q) (1175)) (countLit q [-14, -15, -18]) (countLit q [-20, -22, -23]) (count1175 q) 1 (meaning1172 q) (meaning1175 q) hs
  change valuationOf q 1172 = false ∨ valuationOf q 1175 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 1172 = false ∨ valuation q 1175 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 1173 = false ∨ valuationOf q 1176 = true := by
  have hs : count1175 q = (countLit q [-14, -15, -18]) + (countLit q [-20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18]) (l₂ := [-20, -22, -23])
  have hm := merge_right (literal (valuationOf q) (1173)) (literal (valuationOf q) (1176)) (countLit q [-14, -15, -18]) (countLit q [-20, -22, -23]) (count1175 q) 2 (meaning1173 q) (meaning1176 q) hs
  change valuationOf q 1173 = false ∨ valuationOf q 1176 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 1173 = false ∨ valuation q 1176 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 1167 = false ∨ valuationOf q 1175 = true := by
  have hs : count1175 q = (countLit q [-14, -15, -18]) + (countLit q [-20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18]) (l₂ := [-20, -22, -23])
  have hm := merge_left (literal (valuationOf q) (1167)) (literal (valuationOf q) (1175)) (countLit q [-14, -15, -18]) (countLit q [-20, -22, -23]) (count1175 q) 1 (meaning1167 q) (meaning1175 q) hs
  change valuationOf q 1167 = false ∨ valuationOf q 1175 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 1167 = false ∨ valuation q 1175 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 1167 = false ∨ valuationOf q 1172 = false ∨ valuationOf q 1176 = true := by
  have hs : count1175 q = (countLit q [-14, -15, -18]) + (countLit q [-20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18]) (l₂ := [-20, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1167)) (literal (valuationOf q) (1172)) (literal (valuationOf q) (1176)) (countLit q [-14, -15, -18]) (countLit q [-20, -22, -23]) (count1175 q) 1 1 (meaning1167 q) (meaning1172 q) (meaning1176 q) hs
  change valuationOf q 1167 = false ∨ valuationOf q 1172 = false ∨ valuationOf q 1176 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 1167 = false ∨ valuation q 1172 = false ∨ valuation q 1176 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 1168 = false ∨ valuationOf q 1176 = true := by
  have hs : count1175 q = (countLit q [-14, -15, -18]) + (countLit q [-20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18]) (l₂ := [-20, -22, -23])
  have hm := merge_left (literal (valuationOf q) (1168)) (literal (valuationOf q) (1176)) (countLit q [-14, -15, -18]) (countLit q [-20, -22, -23]) (count1175 q) 2 (meaning1168 q) (meaning1176 q) hs
  change valuationOf q 1168 = false ∨ valuationOf q 1176 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 1168 = false ∨ valuation q 1176 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 1160 = false ∨ valuationOf q 1182 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -6, -8, -9, -10]) + (countLit q [-14, -15, -18, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -8, -9, -10]) (l₂ := [-14, -15, -18, -20, -22, -23])
  have hm := merge_left (literal (valuationOf q) (1160)) (literal (valuationOf q) (1182)) (countLit q [-2, -3, -6, -8, -9, -10]) (countLit q [-14, -15, -18, -20, -22, -23]) (count1181 q) 2 (meaning1160 q) (meaning1182 q) hs
  change valuationOf q 1160 = false ∨ valuationOf q 1182 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 1160 = false ∨ valuation q 1182 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 1160 = false ∨ valuationOf q 1175 = false ∨ valuationOf q 1183 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -6, -8, -9, -10]) + (countLit q [-14, -15, -18, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -8, -9, -10]) (l₂ := [-14, -15, -18, -20, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1160)) (literal (valuationOf q) (1175)) (literal (valuationOf q) (1183)) (countLit q [-2, -3, -6, -8, -9, -10]) (countLit q [-14, -15, -18, -20, -22, -23]) (count1181 q) 2 1 (meaning1160 q) (meaning1175 q) (meaning1183 q) hs
  change valuationOf q 1160 = false ∨ valuationOf q 1175 = false ∨ valuationOf q 1183 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 1160 = false ∨ valuation q 1175 = false ∨ valuation q 1183 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 1160 = false ∨ valuationOf q 1176 = false ∨ valuationOf q 1184 = true := by
  have hs : count1181 q = (countLit q [-2, -3, -6, -8, -9, -10]) + (countLit q [-14, -15, -18, -20, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -8, -9, -10]) (l₂ := [-14, -15, -18, -20, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1160)) (literal (valuationOf q) (1176)) (literal (valuationOf q) (1184)) (countLit q [-2, -3, -6, -8, -9, -10]) (countLit q [-14, -15, -18, -20, -22, -23]) (count1181 q) 2 2 (meaning1160 q) (meaning1176 q) (meaning1184 q) hs
  change valuationOf q 1160 = false ∨ valuationOf q 1176 = false ∨ valuationOf q 1184 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 1160 = false ∨ valuation q 1176 = false ∨ valuation q 1184 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1190)) (countLit q [-27]) (countLit q [-30]) (count1190 q) 1 (meaningNeg30 q) (meaning1190 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1190 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1190)) (countLit q [-27]) (countLit q [-30]) (count1190 q) 1 (meaningNeg27 q) (meaning1190 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1190 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 1190 = false ∨ valuationOf q 1192 = true := by
  have hs : count1192 q = (countLit q [-24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-27, -30])
  have hm := merge_right (literal (valuationOf q) (1190)) (literal (valuationOf q) (1192)) (countLit q [-24]) (countLit q [-27, -30]) (count1192 q) 1 (meaning1190 q) (meaning1192 q) hs
  change valuationOf q 1190 = false ∨ valuationOf q 1192 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 1190 = false ∨ valuation q 1192 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1192 = true := by
  have hs : count1192 q = (countLit q [-24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-27, -30])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1192)) (countLit q [-24]) (countLit q [-27, -30]) (count1192 q) 1 (meaningNeg24 q) (meaning1192 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1192 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1192 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1190 = false ∨ valuationOf q 1193 = true := by
  have hs : count1192 q = (countLit q [-24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-27, -30])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (1190)) (literal (valuationOf q) (1193)) (countLit q [-24]) (countLit q [-27, -30]) (count1192 q) 1 1 (meaningNeg24 q) (meaning1190 q) (meaning1193 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1190 = false ∨ valuationOf q 1193 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1190 = false ∨ valuation q 1193 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-33]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (1195)) (countLit q [-33]) (countLit q [-34]) (count1195 q) 1 (meaningNeg34 q) (meaning1195 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1195 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1195 = true := by
  have hs : count1195 q = (countLit q [-33]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1195)) (countLit q [-33]) (countLit q [-34]) (count1195 q) 1 (meaningNeg33 q) (meaning1195 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1195 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1195 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 1195 = false ∨ valuationOf q 1197 = true := by
  have hs : count1197 q = (countLit q [-32]) + (countLit q [-33, -34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33, -34])
  have hm := merge_right (literal (valuationOf q) (1195)) (literal (valuationOf q) (1197)) (countLit q [-32]) (countLit q [-33, -34]) (count1197 q) 1 (meaning1195 q) (meaning1197 q) hs
  change valuationOf q 1195 = false ∨ valuationOf q 1197 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 1195 = false ∨ valuation q 1197 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1197 = true := by
  have hs : count1197 q = (countLit q [-32]) + (countLit q [-33, -34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33, -34])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1197)) (countLit q [-32]) (countLit q [-33, -34]) (count1197 q) 1 (meaningNeg32 q) (meaning1197 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1197 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1197 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 1197 = false ∨ valuationOf q 1200 = true := by
  have hs : count1200 q = (countLit q [-24, -27, -30]) + (countLit q [-32, -33, -34]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30]) (l₂ := [-32, -33, -34])
  have hm := merge_right (literal (valuationOf q) (1197)) (literal (valuationOf q) (1200)) (countLit q [-24, -27, -30]) (countLit q [-32, -33, -34]) (count1200 q) 1 (meaning1197 q) (meaning1200 q) hs
  change valuationOf q 1197 = false ∨ valuationOf q 1200 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 1197 = false ∨ valuation q 1200 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1200 = true := by
  have hs : count1200 q = (countLit q [-24, -27, -30]) + (countLit q [-32, -33, -34]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30]) (l₂ := [-32, -33, -34])
  have hm := merge_left (literal (valuationOf q) (1192)) (literal (valuationOf q) (1200)) (countLit q [-24, -27, -30]) (countLit q [-32, -33, -34]) (count1200 q) 1 (meaning1192 q) (meaning1200 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1200 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1200 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E149.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112149
