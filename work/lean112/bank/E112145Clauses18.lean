import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-38, -41, -42]) + (countLit q [-43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -42]) (l₂ := [-43, -45, -47, -50])
  have hm := merge_right (literal (valuationOf q) (1300)) (literal (valuationOf q) (1304)) (countLit q [-38, -41, -42]) (countLit q [-43, -45, -47, -50]) (count1304 q) 1 (meaning1300 q) (meaning1304 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1304 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1305 = true := by
  have hs : count1304 q = (countLit q [-38, -41, -42]) + (countLit q [-43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -42]) (l₂ := [-43, -45, -47, -50])
  have hm := merge_right (literal (valuationOf q) (1301)) (literal (valuationOf q) (1305)) (countLit q [-38, -41, -42]) (countLit q [-43, -45, -47, -50]) (count1304 q) 2 (meaning1301 q) (meaning1305 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1305 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-38, -41, -42]) + (countLit q [-43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -42]) (l₂ := [-43, -45, -47, -50])
  have hm := merge_left (literal (valuationOf q) (1293)) (literal (valuationOf q) (1304)) (countLit q [-38, -41, -42]) (countLit q [-43, -45, -47, -50]) (count1304 q) 1 (meaning1293 q) (meaning1304 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1304 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1300 = false ∨ valuationOf q 1305 = true := by
  have hs : count1304 q = (countLit q [-38, -41, -42]) + (countLit q [-43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -42]) (l₂ := [-43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1300)) (literal (valuationOf q) (1305)) (countLit q [-38, -41, -42]) (countLit q [-43, -45, -47, -50]) (count1304 q) 1 1 (meaning1293 q) (meaning1300 q) (meaning1305 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1300 = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1300 = false ∨ valuation q 1305 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1305 = true := by
  have hs : count1304 q = (countLit q [-38, -41, -42]) + (countLit q [-43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -42]) (l₂ := [-43, -45, -47, -50])
  have hm := merge_left (literal (valuationOf q) (1294)) (literal (valuationOf q) (1305)) (countLit q [-38, -41, -42]) (countLit q [-43, -45, -47, -50]) (count1304 q) 2 (meaning1294 q) (meaning1305 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1305 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1300 = false ∨ valuationOf q 1306 = true := by
  have hs : count1304 q = (countLit q [-38, -41, -42]) + (countLit q [-43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -42]) (l₂ := [-43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1294)) (literal (valuationOf q) (1300)) (literal (valuationOf q) (1306)) (countLit q [-38, -41, -42]) (countLit q [-43, -45, -47, -50]) (count1304 q) 2 1 (meaning1294 q) (meaning1300 q) (meaning1306 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1300 = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1300 = false ∨ valuation q 1306 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1306 = true := by
  have hs : count1304 q = (countLit q [-38, -41, -42]) + (countLit q [-43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -42]) (l₂ := [-43, -45, -47, -50])
  have hm := merge_left (literal (valuationOf q) (1295)) (literal (valuationOf q) (1306)) (countLit q [-38, -41, -42]) (countLit q [-43, -45, -47, -50]) (count1304 q) 3 (meaning1295 q) (meaning1306 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1306 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-25, -29, -30, -31, -32, -35]) + (countLit q [-38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30, -31, -32, -35]) (l₂ := [-38, -41, -42, -43, -45, -47, -50])
  have hm := merge_right (literal (valuationOf q) (1304)) (literal (valuationOf q) (1311)) (countLit q [-25, -29, -30, -31, -32, -35]) (countLit q [-38, -41, -42, -43, -45, -47, -50]) (count1311 q) 1 (meaning1304 q) (meaning1311 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1311 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1312 = true := by
  have hs : count1311 q = (countLit q [-25, -29, -30, -31, -32, -35]) + (countLit q [-38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30, -31, -32, -35]) (l₂ := [-38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1285)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1312)) (countLit q [-25, -29, -30, -31, -32, -35]) (countLit q [-38, -41, -42, -43, -45, -47, -50]) (count1311 q) 1 1 (meaning1285 q) (meaning1304 q) (meaning1312 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1304 = false ∨ valuation q 1312 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1313 = true := by
  have hs : count1311 q = (countLit q [-25, -29, -30, -31, -32, -35]) + (countLit q [-38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30, -31, -32, -35]) (l₂ := [-38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1285)) (literal (valuationOf q) (1305)) (literal (valuationOf q) (1313)) (countLit q [-25, -29, -30, -31, -32, -35]) (countLit q [-38, -41, -42, -43, -45, -47, -50]) (count1311 q) 1 2 (meaning1285 q) (meaning1305 q) (meaning1313 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1305 = false ∨ valuation q 1313 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1314 = true := by
  have hs : count1311 q = (countLit q [-25, -29, -30, -31, -32, -35]) + (countLit q [-38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30, -31, -32, -35]) (l₂ := [-38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1285)) (literal (valuationOf q) (1306)) (literal (valuationOf q) (1314)) (countLit q [-25, -29, -30, -31, -32, -35]) (countLit q [-38, -41, -42, -43, -45, -47, -50]) (count1311 q) 1 3 (meaning1285 q) (meaning1306 q) (meaning1314 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1306 = false ∨ valuation q 1314 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1313 = true := by
  have hs : count1311 q = (countLit q [-25, -29, -30, -31, -32, -35]) + (countLit q [-38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30, -31, -32, -35]) (l₂ := [-38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1286)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1313)) (countLit q [-25, -29, -30, -31, -32, -35]) (countLit q [-38, -41, -42, -43, -45, -47, -50]) (count1311 q) 2 1 (meaning1286 q) (meaning1304 q) (meaning1313 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1304 = false ∨ valuation q 1313 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1314 = true := by
  have hs : count1311 q = (countLit q [-25, -29, -30, -31, -32, -35]) + (countLit q [-38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30, -31, -32, -35]) (l₂ := [-38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1286)) (literal (valuationOf q) (1305)) (literal (valuationOf q) (1314)) (countLit q [-25, -29, -30, -31, -32, -35]) (countLit q [-38, -41, -42, -43, -45, -47, -50]) (count1311 q) 2 2 (meaning1286 q) (meaning1305 q) (meaning1314 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1305 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1305 = false ∨ valuation q 1314 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1287 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1314 = true := by
  have hs : count1311 q = (countLit q [-25, -29, -30, -31, -32, -35]) + (countLit q [-38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30, -31, -32, -35]) (l₂ := [-38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1287)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1314)) (countLit q [-25, -29, -30, -31, -32, -35]) (countLit q [-38, -41, -42, -43, -45, -47, -50]) (count1311 q) 3 1 (meaning1287 q) (meaning1304 q) (meaning1314 q) hs
  change valuationOf q 1287 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1287 = false ∨ valuation q 1304 = false ∨ valuation q 1314 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1315 = true := by
  have hs : count1311 q = (countLit q [-25, -29, -30, -31, -32, -35]) + (countLit q [-38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-25, -29, -30, -31, -32, -35]) (l₂ := [-38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1288)) (literal (valuationOf q) (1304)) (literal (valuationOf q) (1315)) (countLit q [-25, -29, -30, -31, -32, -35]) (countLit q [-38, -41, -42, -43, -45, -47, -50]) (count1311 q) 4 1 (meaning1288 q) (meaning1304 q) (meaning1315 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1304 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1304 = false ∨ valuation q 1315 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1325 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1264)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1325)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 1 3 (meaning1264 q) (meaning1313 q) (meaning1325 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1313 = false ∨ valuation q 1325 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1325 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1265)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1325)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 2 2 (meaning1265 q) (meaning1312 q) (meaning1325 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1312 = false ∨ valuation q 1325 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1326 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1265)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1326)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 2 3 (meaning1265 q) (meaning1313 q) (meaning1326 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1313 = false ∨ valuation q 1326 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1327 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1265)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1327)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 2 4 (meaning1265 q) (meaning1314 q) (meaning1327 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1314 = false ∨ valuation q 1327 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1326 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1266)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1326)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 3 2 (meaning1266 q) (meaning1312 q) (meaning1326 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1312 = false ∨ valuation q 1326 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1327 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1266)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1327)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 3 3 (meaning1266 q) (meaning1313 q) (meaning1327 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1313 = false ∨ valuation q 1327 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1328 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1266)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1328)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 3 4 (meaning1266 q) (meaning1314 q) (meaning1328 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1314 = false ∨ valuation q 1328 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1327 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1267)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1327)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 4 2 (meaning1267 q) (meaning1312 q) (meaning1327 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1312 = false ∨ valuation q 1327 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1328 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1267)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1328)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 4 3 (meaning1267 q) (meaning1313 q) (meaning1328 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1313 = false ∨ valuation q 1328 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1329 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1267)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1329)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 4 4 (meaning1267 q) (meaning1314 q) (meaning1329 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1314 = false ∨ valuation q 1329 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1330 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1267)) (literal (valuationOf q) (1315)) (literal (valuationOf q) (1330)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 4 5 (meaning1267 q) (meaning1315 q) (meaning1330 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1315 = false ∨ valuation q 1330 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1328 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1268)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1328)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 5 2 (meaning1268 q) (meaning1312 q) (meaning1328 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1312 = false ∨ valuation q 1328 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1329 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1268)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1329)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 5 3 (meaning1268 q) (meaning1313 q) (meaning1329 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1313 = false ∨ valuation q 1329 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1330 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1268)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1330)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 5 4 (meaning1268 q) (meaning1314 q) (meaning1330 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1314 = false ∨ valuation q 1330 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1329 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1269)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1329)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 6 2 (meaning1269 q) (meaning1312 q) (meaning1329 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1312 = false ∨ valuation q 1329 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1330 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1269)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1330)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 6 3 (meaning1269 q) (meaning1313 q) (meaning1330 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1313 = false ∨ valuation q 1330 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1329 = true := by
  have hs : count1322 q = (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) + (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (l₂ := [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1311)) (literal (valuationOf q) (1329)) (countLit q [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]) (countLit q [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]) (count1322 q) 7 1 (meaning1270 q) (meaning1311 q) (meaning1329 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1311 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1311 = false ∨ valuation q 1329 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E145.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112145
