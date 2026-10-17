import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1182 = true := by
  have hs : count1182 q = (countLit q [-2]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -6])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1182)) (countLit q [-2]) (countLit q [-5, -6]) (count1182 q) 1 (meaningNeg2 q) (meaning1182 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1182 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1182 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1185 = true := by
  have hs : count1185 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1185)) (countLit q [-11]) (countLit q [-13]) (count1185 q) 1 (meaningNeg11 q) (meaning1185 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1185 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1185 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 1185 = false ∨ valuationOf q 1187 = true := by
  have hs : count1187 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_right (literal (valuationOf q) (1185)) (literal (valuationOf q) (1187)) (countLit q [-8]) (countLit q [-11, -13]) (count1187 q) 1 (meaning1185 q) (meaning1187 q) hs
  change valuationOf q 1185 = false ∨ valuationOf q 1187 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 1185 = false ∨ valuation q 1187 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1187 = true := by
  have hs : count1187 q = (countLit q [-8]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1187)) (countLit q [-8]) (countLit q [-11, -13]) (count1187 q) 1 (meaningNeg8 q) (meaning1187 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1187 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1187 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 1187 = false ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-2, -5, -6]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-8, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1187)) (literal (valuationOf q) (1190)) (countLit q [-2, -5, -6]) (countLit q [-8, -11, -13]) (count1190 q) 1 (meaning1187 q) (meaning1190 q) hs
  change valuationOf q 1187 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 1187 = false ∨ valuation q 1190 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 1182 = false ∨ valuationOf q 1190 = true := by
  have hs : count1190 q = (countLit q [-2, -5, -6]) + (countLit q [-8, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-8, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1182)) (literal (valuationOf q) (1190)) (countLit q [-2, -5, -6]) (countLit q [-8, -11, -13]) (count1190 q) 1 (meaning1182 q) (meaning1190 q) hs
  change valuationOf q 1182 = false ∨ valuationOf q 1190 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 1182 = false ∨ valuation q 1190 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1196 = true := by
  have hs : count1196 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1196)) (countLit q [-18]) (countLit q [-19]) (count1196 q) 1 (meaningNeg18 q) (meaning1196 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1196 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1196 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 1196 = false ∨ valuationOf q 1198 = true := by
  have hs : count1198 q = (countLit q [-16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1196)) (literal (valuationOf q) (1198)) (countLit q [-16]) (countLit q [-18, -19]) (count1198 q) 1 (meaning1196 q) (meaning1198 q) hs
  change valuationOf q 1196 = false ∨ valuationOf q 1198 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 1196 = false ∨ valuation q 1198 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1201 = true := by
  have hs : count1201 q = (countLit q [-23]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1201)) (countLit q [-23]) (countLit q [-26]) (count1201 q) 1 (meaningNeg26 q) (meaning1201 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1201 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1201 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1203 = true := by
  have hs : count1203 q = (countLit q [-20]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-23, -26])
  have hm := merge_right (literal (valuationOf q) (1201)) (literal (valuationOf q) (1203)) (countLit q [-20]) (countLit q [-23, -26]) (count1203 q) 1 (meaning1201 q) (meaning1203 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1203 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1203 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1203 = true := by
  have hs : count1203 q = (countLit q [-20]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-23, -26])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1203)) (countLit q [-20]) (countLit q [-23, -26]) (count1203 q) 1 (meaningNeg20 q) (meaning1203 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1203 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1203 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 1203 = false ∨ valuationOf q 1206 = true := by
  have hs : count1206 q = (countLit q [-16, -18, -19]) + (countLit q [-20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-20, -23, -26])
  have hm := merge_right (literal (valuationOf q) (1203)) (literal (valuationOf q) (1206)) (countLit q [-16, -18, -19]) (countLit q [-20, -23, -26]) (count1206 q) 1 (meaning1203 q) (meaning1206 q) hs
  change valuationOf q 1203 = false ∨ valuationOf q 1206 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 1203 = false ∨ valuation q 1206 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 1198 = false ∨ valuationOf q 1203 = false ∨ valuationOf q 1207 = true := by
  have hs : count1206 q = (countLit q [-16, -18, -19]) + (countLit q [-20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1198)) (literal (valuationOf q) (1203)) (literal (valuationOf q) (1207)) (countLit q [-16, -18, -19]) (countLit q [-20, -23, -26]) (count1206 q) 1 1 (meaning1198 q) (meaning1203 q) (meaning1207 q) hs
  change valuationOf q 1198 = false ∨ valuationOf q 1203 = false ∨ valuationOf q 1207 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 1198 = false ∨ valuation q 1203 = false ∨ valuation q 1207 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 1206 = false ∨ valuationOf q 1212 = true := by
  have hs : count1212 q = (countLit q [-2, -5, -6, -8, -11, -13]) + (countLit q [-16, -18, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13]) (l₂ := [-16, -18, -19, -20, -23, -26])
  have hm := merge_right (literal (valuationOf q) (1206)) (literal (valuationOf q) (1212)) (countLit q [-2, -5, -6, -8, -11, -13]) (countLit q [-16, -18, -19, -20, -23, -26]) (count1212 q) 1 (meaning1206 q) (meaning1212 q) hs
  change valuationOf q 1206 = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 1206 = false ∨ valuation q 1212 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 1207 = false ∨ valuationOf q 1213 = true := by
  have hs : count1212 q = (countLit q [-2, -5, -6, -8, -11, -13]) + (countLit q [-16, -18, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13]) (l₂ := [-16, -18, -19, -20, -23, -26])
  have hm := merge_right (literal (valuationOf q) (1207)) (literal (valuationOf q) (1213)) (countLit q [-2, -5, -6, -8, -11, -13]) (countLit q [-16, -18, -19, -20, -23, -26]) (count1212 q) 2 (meaning1207 q) (meaning1213 q) hs
  change valuationOf q 1207 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 1207 = false ∨ valuation q 1213 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 1190 = false ∨ valuationOf q 1212 = true := by
  have hs : count1212 q = (countLit q [-2, -5, -6, -8, -11, -13]) + (countLit q [-16, -18, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13]) (l₂ := [-16, -18, -19, -20, -23, -26])
  have hm := merge_left (literal (valuationOf q) (1190)) (literal (valuationOf q) (1212)) (countLit q [-2, -5, -6, -8, -11, -13]) (countLit q [-16, -18, -19, -20, -23, -26]) (count1212 q) 1 (meaning1190 q) (meaning1212 q) hs
  change valuationOf q 1190 = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 1190 = false ∨ valuation q 1212 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 1190 = false ∨ valuationOf q 1206 = false ∨ valuationOf q 1213 = true := by
  have hs : count1212 q = (countLit q [-2, -5, -6, -8, -11, -13]) + (countLit q [-16, -18, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -8, -11, -13]) (l₂ := [-16, -18, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1190)) (literal (valuationOf q) (1206)) (literal (valuationOf q) (1213)) (countLit q [-2, -5, -6, -8, -11, -13]) (countLit q [-16, -18, -19, -20, -23, -26]) (count1212 q) 1 1 (meaning1190 q) (meaning1206 q) (meaning1213 q) hs
  change valuationOf q 1190 = false ∨ valuationOf q 1206 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 1190 = false ∨ valuation q 1206 = false ∨ valuation q 1213 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1222 = true := by
  have hs : count1222 q = (countLit q [-30]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32])
  have hm := merge_right (literal (valuationOf q) (-32)) (literal (valuationOf q) (1222)) (countLit q [-30]) (countLit q [-32]) (count1222 q) 1 (meaningNeg32 q) (meaning1222 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1222 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1222 = true := by
  have hs : count1222 q = (countLit q [-30]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1222)) (countLit q [-30]) (countLit q [-32]) (count1222 q) 1 (meaningNeg30 q) (meaning1222 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1222 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 32 = true ∨ valuationOf q 1223 = true := by
  have hs : count1222 q = (countLit q [-30]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-32)) (literal (valuationOf q) (1223)) (countLit q [-30]) (countLit q [-32]) (count1222 q) 1 1 (meaningNeg30 q) (meaningNeg32 q) (meaning1223 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 32)) = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 32 = true ∨ valuation q 1223 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 1222 = false ∨ valuationOf q 1224 = true := by
  have hs : count1224 q = (countLit q [-28]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -32])
  have hm := merge_right (literal (valuationOf q) (1222)) (literal (valuationOf q) (1224)) (countLit q [-28]) (countLit q [-30, -32]) (count1224 q) 1 (meaning1222 q) (meaning1224 q) hs
  change valuationOf q 1222 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 1222 = false ∨ valuation q 1224 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 1223 = false ∨ valuationOf q 1225 = true := by
  have hs : count1224 q = (countLit q [-28]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -32])
  have hm := merge_right (literal (valuationOf q) (1223)) (literal (valuationOf q) (1225)) (countLit q [-28]) (countLit q [-30, -32]) (count1224 q) 2 (meaning1223 q) (meaning1225 q) hs
  change valuationOf q 1223 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 1223 = false ∨ valuation q 1225 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1224 = true := by
  have hs : count1224 q = (countLit q [-28]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -32])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1224)) (countLit q [-28]) (countLit q [-30, -32]) (count1224 q) 1 (meaningNeg28 q) (meaning1224 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1224 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1222 = false ∨ valuationOf q 1225 = true := by
  have hs : count1224 q = (countLit q [-28]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -32])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (1222)) (literal (valuationOf q) (1225)) (countLit q [-28]) (countLit q [-30, -32]) (count1224 q) 1 1 (meaningNeg28 q) (meaning1222 q) (meaning1225 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1222 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1222 = false ∨ valuation q 1225 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1227 = true := by
  have hs : count1227 q = (countLit q [-35]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1227)) (countLit q [-35]) (countLit q [-38]) (count1227 q) 1 (meaningNeg38 q) (meaning1227 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1227 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1227 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1227 = true := by
  have hs : count1227 q = (countLit q [-35]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1227)) (countLit q [-35]) (countLit q [-38]) (count1227 q) 1 (meaningNeg35 q) (meaning1227 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1227 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1227 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1228 = true := by
  have hs : count1227 q = (countLit q [-35]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1228)) (countLit q [-35]) (countLit q [-38]) (count1227 q) 1 1 (meaningNeg35 q) (meaningNeg38 q) (meaning1228 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1228 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 38 = true ∨ valuation q 1228 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 1227 = false ∨ valuationOf q 1229 = true := by
  have hs : count1229 q = (countLit q [-33]) + (countLit q [-35, -38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -38])
  have hm := merge_right (literal (valuationOf q) (1227)) (literal (valuationOf q) (1229)) (countLit q [-33]) (countLit q [-35, -38]) (count1229 q) 1 (meaning1227 q) (meaning1229 q) hs
  change valuationOf q 1227 = false ∨ valuationOf q 1229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 1227 = false ∨ valuation q 1229 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1229 = true := by
  have hs : count1229 q = (countLit q [-33]) + (countLit q [-35, -38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -38])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1229)) (countLit q [-33]) (countLit q [-35, -38]) (count1229 q) 1 (meaningNeg33 q) (meaning1229 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1229 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1229 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1227 = false ∨ valuationOf q 1230 = true := by
  have hs : count1229 q = (countLit q [-33]) + (countLit q [-35, -38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -38])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1227)) (literal (valuationOf q) (1230)) (countLit q [-33]) (countLit q [-35, -38]) (count1229 q) 1 1 (meaningNeg33 q) (meaning1227 q) (meaning1230 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1227 = false ∨ valuationOf q 1230 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1227 = false ∨ valuation q 1230 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1228 = false ∨ valuationOf q 1231 = true := by
  have hs : count1229 q = (countLit q [-33]) + (countLit q [-35, -38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -38])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1228)) (literal (valuationOf q) (1231)) (countLit q [-33]) (countLit q [-35, -38]) (count1229 q) 1 2 (meaningNeg33 q) (meaning1228 q) (meaning1231 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1228 = false ∨ valuationOf q 1231 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1228 = false ∨ valuation q 1231 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 1229 = false ∨ valuationOf q 1232 = true := by
  have hs : count1232 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -35, -38]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -35, -38])
  have hm := merge_right (literal (valuationOf q) (1229)) (literal (valuationOf q) (1232)) (countLit q [-28, -30, -32]) (countLit q [-33, -35, -38]) (count1232 q) 1 (meaning1229 q) (meaning1232 q) hs
  change valuationOf q 1229 = false ∨ valuationOf q 1232 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 1229 = false ∨ valuation q 1232 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E154.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112154
