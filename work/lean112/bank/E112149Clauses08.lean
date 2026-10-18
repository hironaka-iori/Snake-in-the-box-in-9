import E112149Semantics
import B112E149Inputs
namespace Snake9.Regrowth.E112149
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1201 = true := by
  have hs : count1200 q = (countLit q [-24, -27, -30]) + (countLit q [-32, -33, -34]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30]) (l₂ := [-32, -33, -34])
  have hm := merge_two (literal (valuationOf q) (1192)) (literal (valuationOf q) (1197)) (literal (valuationOf q) (1201)) (countLit q [-24, -27, -30]) (countLit q [-32, -33, -34]) (count1200 q) 1 1 (meaning1192 q) (meaning1197 q) (meaning1201 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1201 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1197 = false ∨ valuation q 1201 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 1193 = false ∨ valuationOf q 1201 = true := by
  have hs : count1200 q = (countLit q [-24, -27, -30]) + (countLit q [-32, -33, -34]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30]) (l₂ := [-32, -33, -34])
  have hm := merge_left (literal (valuationOf q) (1193)) (literal (valuationOf q) (1201)) (countLit q [-24, -27, -30]) (countLit q [-32, -33, -34]) (count1200 q) 2 (meaning1193 q) (meaning1201 q) hs
  change valuationOf q 1193 = false ∨ valuationOf q 1201 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 1193 = false ∨ valuation q 1201 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 1193 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1202 = true := by
  have hs : count1200 q = (countLit q [-24, -27, -30]) + (countLit q [-32, -33, -34]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30]) (l₂ := [-32, -33, -34])
  have hm := merge_two (literal (valuationOf q) (1193)) (literal (valuationOf q) (1197)) (literal (valuationOf q) (1202)) (countLit q [-24, -27, -30]) (countLit q [-32, -33, -34]) (count1200 q) 2 1 (meaning1193 q) (meaning1197 q) (meaning1202 q) hs
  change valuationOf q 1193 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1202 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 1193 = false ∨ valuation q 1197 = false ∨ valuation q 1202 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1206 = true := by
  have hs : count1206 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1206)) (countLit q [-39]) (countLit q [-41]) (count1206 q) 1 (meaningNeg41 q) (meaning1206 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1206 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1206 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1206 = true := by
  have hs : count1206 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1206)) (countLit q [-39]) (countLit q [-41]) (count1206 q) 1 (meaningNeg39 q) (meaning1206 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1206 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1206 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1207 = true := by
  have hs : count1206 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1207)) (countLit q [-39]) (countLit q [-41]) (count1206 q) 1 1 (meaningNeg39 q) (meaningNeg41 q) (meaning1207 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1207 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 1207 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 1206 = false ∨ valuationOf q 1208 = true := by
  have hs : count1208 q = (countLit q [-37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -41])
  have hm := merge_right (literal (valuationOf q) (1206)) (literal (valuationOf q) (1208)) (countLit q [-37]) (countLit q [-39, -41]) (count1208 q) 1 (meaning1206 q) (meaning1208 q) hs
  change valuationOf q 1206 = false ∨ valuationOf q 1208 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 1206 = false ∨ valuation q 1208 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 1207 = false ∨ valuationOf q 1209 = true := by
  have hs : count1208 q = (countLit q [-37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -41])
  have hm := merge_right (literal (valuationOf q) (1207)) (literal (valuationOf q) (1209)) (countLit q [-37]) (countLit q [-39, -41]) (count1208 q) 2 (meaning1207 q) (meaning1209 q) hs
  change valuationOf q 1207 = false ∨ valuationOf q 1209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 1207 = false ∨ valuation q 1209 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1208 = true := by
  have hs : count1208 q = (countLit q [-37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -41])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1208)) (countLit q [-37]) (countLit q [-39, -41]) (count1208 q) 1 (meaningNeg37 q) (meaning1208 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1208 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1208 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1206 = false ∨ valuationOf q 1209 = true := by
  have hs : count1208 q = (countLit q [-37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -41])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (1206)) (literal (valuationOf q) (1209)) (countLit q [-37]) (countLit q [-39, -41]) (count1208 q) 1 1 (meaningNeg37 q) (meaning1206 q) (meaning1209 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1206 = false ∨ valuationOf q 1209 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1206 = false ∨ valuation q 1209 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1211 = true := by
  have hs : count1211 q = (countLit q [-44]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1211)) (countLit q [-44]) (countLit q [-47]) (count1211 q) 1 (meaningNeg44 q) (meaning1211 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1211 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1211 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 1211 = false ∨ valuationOf q 1213 = true := by
  have hs : count1213 q = (countLit q [-42]) + (countLit q [-44, -47]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44, -47])
  have hm := merge_right (literal (valuationOf q) (1211)) (literal (valuationOf q) (1213)) (countLit q [-42]) (countLit q [-44, -47]) (count1213 q) 1 (meaning1211 q) (meaning1213 q) hs
  change valuationOf q 1211 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 1211 = false ∨ valuation q 1213 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1213 = true := by
  have hs : count1213 q = (countLit q [-42]) + (countLit q [-44, -47]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44, -47])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1213)) (countLit q [-42]) (countLit q [-44, -47]) (count1213 q) 1 (meaningNeg42 q) (meaning1213 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1213 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1211 = false ∨ valuationOf q 1214 = true := by
  have hs : count1213 q = (countLit q [-42]) + (countLit q [-44, -47]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44, -47])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (1211)) (literal (valuationOf q) (1214)) (countLit q [-42]) (countLit q [-44, -47]) (count1213 q) 1 1 (meaningNeg42 q) (meaning1211 q) (meaning1214 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1211 = false ∨ valuationOf q 1214 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1211 = false ∨ valuation q 1214 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1216 = true := by
  have hs : count1216 q = (countLit q [-37, -39, -41]) + (countLit q [-42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-42, -44, -47])
  have hm := merge_right (literal (valuationOf q) (1213)) (literal (valuationOf q) (1216)) (countLit q [-37, -39, -41]) (countLit q [-42, -44, -47]) (count1216 q) 1 (meaning1213 q) (meaning1216 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1216 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1216 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 1214 = false ∨ valuationOf q 1217 = true := by
  have hs : count1216 q = (countLit q [-37, -39, -41]) + (countLit q [-42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-42, -44, -47])
  have hm := merge_right (literal (valuationOf q) (1214)) (literal (valuationOf q) (1217)) (countLit q [-37, -39, -41]) (countLit q [-42, -44, -47]) (count1216 q) 2 (meaning1214 q) (meaning1217 q) hs
  change valuationOf q 1214 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 1214 = false ∨ valuation q 1217 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 1208 = false ∨ valuationOf q 1216 = true := by
  have hs : count1216 q = (countLit q [-37, -39, -41]) + (countLit q [-42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-42, -44, -47])
  have hm := merge_left (literal (valuationOf q) (1208)) (literal (valuationOf q) (1216)) (countLit q [-37, -39, -41]) (countLit q [-42, -44, -47]) (count1216 q) 1 (meaning1208 q) (meaning1216 q) hs
  change valuationOf q 1208 = false ∨ valuationOf q 1216 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 1208 = false ∨ valuation q 1216 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 1208 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1217 = true := by
  have hs : count1216 q = (countLit q [-37, -39, -41]) + (countLit q [-42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-42, -44, -47])
  have hm := merge_two (literal (valuationOf q) (1208)) (literal (valuationOf q) (1213)) (literal (valuationOf q) (1217)) (countLit q [-37, -39, -41]) (countLit q [-42, -44, -47]) (count1216 q) 1 1 (meaning1208 q) (meaning1213 q) (meaning1217 q) hs
  change valuationOf q 1208 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 1208 = false ∨ valuation q 1213 = false ∨ valuation q 1217 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 1209 = false ∨ valuationOf q 1217 = true := by
  have hs : count1216 q = (countLit q [-37, -39, -41]) + (countLit q [-42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-42, -44, -47])
  have hm := merge_left (literal (valuationOf q) (1209)) (literal (valuationOf q) (1217)) (countLit q [-37, -39, -41]) (countLit q [-42, -44, -47]) (count1216 q) 2 (meaning1209 q) (meaning1217 q) hs
  change valuationOf q 1209 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 1209 = false ∨ valuation q 1217 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 1217 = false ∨ valuationOf q 1223 = true := by
  have hs : count1222 q = (countLit q [-24, -27, -30, -32, -33, -34]) + (countLit q [-37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30, -32, -33, -34]) (l₂ := [-37, -39, -41, -42, -44, -47])
  have hm := merge_right (literal (valuationOf q) (1217)) (literal (valuationOf q) (1223)) (countLit q [-24, -27, -30, -32, -33, -34]) (countLit q [-37, -39, -41, -42, -44, -47]) (count1222 q) 2 (meaning1217 q) (meaning1223 q) hs
  change valuationOf q 1217 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 1217 = false ∨ valuation q 1223 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1223 = true := by
  have hs : count1222 q = (countLit q [-24, -27, -30, -32, -33, -34]) + (countLit q [-37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30, -32, -33, -34]) (l₂ := [-37, -39, -41, -42, -44, -47])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1223)) (countLit q [-24, -27, -30, -32, -33, -34]) (countLit q [-37, -39, -41, -42, -44, -47]) (count1222 q) 1 1 (meaning1200 q) (meaning1216 q) (meaning1223 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1216 = false ∨ valuation q 1223 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-24, -27, -30, -32, -33, -34]) + (countLit q [-37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30, -32, -33, -34]) (l₂ := [-37, -39, -41, -42, -44, -47])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1224)) (countLit q [-24, -27, -30, -32, -33, -34]) (countLit q [-37, -39, -41, -42, -44, -47]) (count1222 q) 1 2 (meaning1200 q) (meaning1217 q) (meaning1224 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1217 = false ∨ valuation q 1224 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-24, -27, -30, -32, -33, -34]) + (countLit q [-37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30, -32, -33, -34]) (l₂ := [-37, -39, -41, -42, -44, -47])
  have hm := merge_two (literal (valuationOf q) (1201)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1224)) (countLit q [-24, -27, -30, -32, -33, -34]) (countLit q [-37, -39, -41, -42, -44, -47]) (count1222 q) 2 1 (meaning1201 q) (meaning1216 q) (meaning1224 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1216 = false ∨ valuation q 1224 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true := by
  have hs : count1222 q = (countLit q [-24, -27, -30, -32, -33, -34]) + (countLit q [-37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30, -32, -33, -34]) (l₂ := [-37, -39, -41, -42, -44, -47])
  have hm := merge_two (literal (valuationOf q) (1201)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1225)) (countLit q [-24, -27, -30, -32, -33, -34]) (countLit q [-37, -39, -41, -42, -44, -47]) (count1222 q) 2 2 (meaning1201 q) (meaning1217 q) (meaning1225 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1217 = false ∨ valuation q 1225 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-24, -27, -30, -32, -33, -34]) + (countLit q [-37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30, -32, -33, -34]) (l₂ := [-37, -39, -41, -42, -44, -47])
  have hm := merge_left (literal (valuationOf q) (1202)) (literal (valuationOf q) (1224)) (countLit q [-24, -27, -30, -32, -33, -34]) (countLit q [-37, -39, -41, -42, -44, -47]) (count1222 q) 3 (meaning1202 q) (meaning1224 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1224 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1225 = true := by
  have hs : count1222 q = (countLit q [-24, -27, -30, -32, -33, -34]) + (countLit q [-37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-24, -27, -30, -32, -33, -34]) (l₂ := [-37, -39, -41, -42, -44, -47])
  have hm := merge_two (literal (valuationOf q) (1202)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1225)) (countLit q [-24, -27, -30, -32, -33, -34]) (countLit q [-37, -39, -41, -42, -44, -47]) (count1222 q) 3 1 (meaning1202 q) (meaning1216 q) (meaning1225 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1216 = false ∨ valuation q 1225 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 1182 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1236 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]) + (countLit q [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]) (l₂ := [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47])
  have hm := merge_two (literal (valuationOf q) (1182)) (literal (valuationOf q) (1225)) (literal (valuationOf q) (1236)) (countLit q [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]) (countLit q [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]) (count1231 q) 2 4 (meaning1182 q) (meaning1225 q) (meaning1236 q) hs
  change valuationOf q 1182 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 1182 = false ∨ valuation q 1225 = false ∨ valuation q 1236 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 1183 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1236 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]) + (countLit q [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]) (l₂ := [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47])
  have hm := merge_two (literal (valuationOf q) (1183)) (literal (valuationOf q) (1224)) (literal (valuationOf q) (1236)) (countLit q [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]) (countLit q [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]) (count1231 q) 3 3 (meaning1183 q) (meaning1224 q) (meaning1236 q) hs
  change valuationOf q 1183 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 1183 = false ∨ valuation q 1224 = false ∨ valuation q 1236 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 1184 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1236 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]) + (countLit q [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]) (l₂ := [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47])
  have hm := merge_two (literal (valuationOf q) (1184)) (literal (valuationOf q) (1223)) (literal (valuationOf q) (1236)) (countLit q [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]) (countLit q [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]) (count1231 q) 4 2 (meaning1184 q) (meaning1223 q) (meaning1236 q) hs
  change valuationOf q 1184 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 1184 = false ∨ valuation q 1223 = false ∨ valuation q 1236 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1240 = true := by
  have hs : count1240 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1240)) (countLit q [-50]) (countLit q [-52]) (count1240 q) 1 (meaningNeg50 q) (meaning1240 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1240 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 1240 = false ∨ valuationOf q 1242 = true := by
  have hs : count1242 q = (countLit q [-49]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50, -52])
  have hm := merge_right (literal (valuationOf q) (1240)) (literal (valuationOf q) (1242)) (countLit q [-49]) (countLit q [-50, -52]) (count1242 q) 1 (meaning1240 q) (meaning1242 q) hs
  change valuationOf q 1240 = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 1240 = false ∨ valuation q 1242 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1250 = true := by
  have hs : count1250 q = (countLit q [-49, -50, -52]) + (countLit q [-54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-49, -50, -52]) (l₂ := [-54, -56, -58])
  have hm := merge_left (literal (valuationOf q) (1242)) (literal (valuationOf q) (1250)) (countLit q [-49, -50, -52]) (countLit q [-54, -56, -58]) (count1250 q) 1 (meaning1242 q) (meaning1250 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1250 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E149.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112149
