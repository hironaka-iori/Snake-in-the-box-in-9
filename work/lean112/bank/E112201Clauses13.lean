import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1315 = true := by
  have hs : count1315 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1315)) (countLit q [-3]) (countLit q [-4]) (count1315 q) 1 (meaningNeg3 q) (meaning1315 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1315 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 4 = true ∨ valuationOf q 1316 = true := by
  have hs : count1315 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (1316)) (countLit q [-3]) (countLit q [-4]) (count1315 q) 1 1 (meaningNeg3 q) (meaningNeg4 q) (meaning1316 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 4 = true ∨ valuation q 1316 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 1315 = false ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-2]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -4])
  have hm := merge_right (literal (valuationOf q) (1315)) (literal (valuationOf q) (1317)) (countLit q [-2]) (countLit q [-3, -4]) (count1317 q) 1 (meaning1315 q) (meaning1317 q) hs
  change valuationOf q 1315 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 1315 = false ∨ valuation q 1317 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 1316 = false ∨ valuationOf q 1318 = true := by
  have hs : count1317 q = (countLit q [-2]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -4])
  have hm := merge_right (literal (valuationOf q) (1316)) (literal (valuationOf q) (1318)) (countLit q [-2]) (countLit q [-3, -4]) (count1317 q) 2 (meaning1316 q) (meaning1318 q) hs
  change valuationOf q 1316 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 1316 = false ∨ valuation q 1318 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-2]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -4])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1317)) (countLit q [-2]) (countLit q [-3, -4]) (count1317 q) 1 (meaningNeg2 q) (meaning1317 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1317 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1316 = false ∨ valuationOf q 1319 = true := by
  have hs : count1317 q = (countLit q [-2]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1319)) (countLit q [-2]) (countLit q [-3, -4]) (count1317 q) 1 2 (meaningNeg2 q) (meaning1316 q) (meaning1319 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1316 = false ∨ valuation q 1319 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1320)) (countLit q [-9]) (countLit q [-10]) (count1320 q) 1 (meaningNeg10 q) (meaning1320 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1320 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1321)) (countLit q [-9]) (countLit q [-10]) (count1320 q) 1 1 (meaningNeg9 q) (meaningNeg10 q) (meaning1321 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 10 = true ∨ valuation q 1321 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_right (literal (valuationOf q) (1320)) (literal (valuationOf q) (1322)) (countLit q [-8]) (countLit q [-9, -10]) (count1322 q) 1 (meaning1320 q) (meaning1322 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1322 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1321 = false ∨ valuationOf q 1324 = true := by
  have hs : count1322 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1324)) (countLit q [-8]) (countLit q [-9, -10]) (count1322 q) 1 2 (meaningNeg8 q) (meaning1321 q) (meaning1324 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1321 = false ∨ valuation q 1324 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1325 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_left (literal (valuationOf q) (1317)) (literal (valuationOf q) (1325)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 1 (meaning1317 q) (meaning1325 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1325 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1328 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1317)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1328)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 1 3 (meaning1317 q) (meaning1324 q) (meaning1328 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1324 = false ∨ valuation q 1328 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1326 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_left (literal (valuationOf q) (1318)) (literal (valuationOf q) (1326)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 2 (meaning1318 q) (meaning1326 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1326 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1328 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1328)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 3 1 (meaning1319 q) (meaning1322 q) (meaning1328 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1322 = false ∨ valuation q 1328 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1330 = true := by
  have hs : count1325 q = (countLit q [-2, -3, -4]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1330)) (countLit q [-2, -3, -4]) (countLit q [-8, -9, -10]) (count1325 q) 3 3 (meaning1319 q) (meaning1324 q) (meaning1330 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1324 = false ∨ valuation q 1330 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-15]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1331)) (countLit q [-15]) (countLit q [-19]) (count1331 q) 1 (meaningNeg19 q) (meaning1331 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1331 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-15]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1331)) (countLit q [-15]) (countLit q [-19]) (count1331 q) 1 (meaningNeg15 q) (meaning1331 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1331 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1332 = true := by
  have hs : count1331 q = (countLit q [-15]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1332)) (countLit q [-15]) (countLit q [-19]) (count1331 q) 1 1 (meaningNeg15 q) (meaningNeg19 q) (meaning1332 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 1332 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-14]) + (countLit q [-15, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -19])
  have hm := merge_right (literal (valuationOf q) (1331)) (literal (valuationOf q) (1333)) (countLit q [-14]) (countLit q [-15, -19]) (count1333 q) 1 (meaning1331 q) (meaning1333 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1333 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1334 = true := by
  have hs : count1333 q = (countLit q [-14]) + (countLit q [-15, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -19])
  have hm := merge_right (literal (valuationOf q) (1332)) (literal (valuationOf q) (1334)) (countLit q [-14]) (countLit q [-15, -19]) (count1333 q) 2 (meaning1332 q) (meaning1334 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1334 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-14]) + (countLit q [-15, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -19])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1333)) (countLit q [-14]) (countLit q [-15, -19]) (count1333 q) 1 (meaningNeg14 q) (meaning1333 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1333 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1331 = false ∨ valuationOf q 1334 = true := by
  have hs : count1333 q = (countLit q [-14]) + (countLit q [-15, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -19])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1334)) (countLit q [-14]) (countLit q [-15, -19]) (count1333 q) 1 1 (meaningNeg14 q) (meaning1331 q) (meaning1334 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1331 = false ∨ valuation q 1334 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1336 = true := by
  have hs : count1336 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1336)) (countLit q [-20]) (countLit q [-22]) (count1336 q) 1 (meaningNeg22 q) (meaning1336 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1336 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1336 = true := by
  have hs : count1336 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1336)) (countLit q [-20]) (countLit q [-22]) (count1336 q) 1 (meaningNeg20 q) (meaning1336 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1336 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1337 = true := by
  have hs : count1336 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1337)) (countLit q [-20]) (countLit q [-22]) (count1336 q) 1 1 (meaningNeg20 q) (meaningNeg22 q) (meaning1337 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 1337 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1338)) (countLit q [-25]) (countLit q [-26]) (count1338 q) 1 (meaningNeg26 q) (meaning1338 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1338 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1338)) (countLit q [-25]) (countLit q [-26]) (count1338 q) 1 (meaningNeg25 q) (meaning1338 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1338 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1339 = true := by
  have hs : count1338 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1339)) (countLit q [-25]) (countLit q [-26]) (count1338 q) 1 1 (meaningNeg25 q) (meaningNeg26 q) (meaning1339 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 1339 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_right (literal (valuationOf q) (1338)) (literal (valuationOf q) (1340)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1340 q) 1 (meaning1338 q) (meaning1340 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1340 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_right (literal (valuationOf q) (1339)) (literal (valuationOf q) (1341)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1340 q) 2 (meaning1339 q) (meaning1341 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1341 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1336)) (literal (valuationOf q) (1340)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1340 q) 1 (meaning1336 q) (meaning1340 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1340 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1341)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1340 q) 1 1 (meaning1336 q) (meaning1338 q) (meaning1341 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1338 = false ∨ valuation q 1341 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E201.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112201
