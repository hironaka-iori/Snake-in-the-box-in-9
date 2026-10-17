import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-26, -29, -32, -34, -35, -37]) + (countLit q [-41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32, -34, -35, -37]) (l₂ := [-41, -42, -43, -44, -48, -49, -52])
  have hm := merge_right (literal (valuationOf q) (1313)) (literal (valuationOf q) (1320)) (countLit q [-26, -29, -32, -34, -35, -37]) (countLit q [-41, -42, -43, -44, -48, -49, -52]) (count1319 q) 2 (meaning1313 q) (meaning1320 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1320 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-26, -29, -32, -34, -35, -37]) + (countLit q [-41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32, -34, -35, -37]) (l₂ := [-41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1320)) (countLit q [-26, -29, -32, -34, -35, -37]) (countLit q [-41, -42, -43, -44, -48, -49, -52]) (count1319 q) 1 1 (meaning1293 q) (meaning1312 q) (meaning1320 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1312 = false ∨ valuation q 1320 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-26, -29, -32, -34, -35, -37]) + (countLit q [-41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32, -34, -35, -37]) (l₂ := [-41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1294)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1321)) (countLit q [-26, -29, -32, -34, -35, -37]) (countLit q [-41, -42, -43, -44, -48, -49, -52]) (count1319 q) 2 1 (meaning1294 q) (meaning1312 q) (meaning1321 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1312 = false ∨ valuation q 1321 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1322 = true := by
  have hs : count1319 q = (countLit q [-26, -29, -32, -34, -35, -37]) + (countLit q [-41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -32, -34, -35, -37]) (l₂ := [-41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1295)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1322)) (countLit q [-26, -29, -32, -34, -35, -37]) (countLit q [-41, -42, -43, -44, -48, -49, -52]) (count1319 q) 3 1 (meaning1295 q) (meaning1312 q) (meaning1322 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1312 = false ∨ valuation q 1322 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1331)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 1 2 (meaning1273 q) (meaning1320 q) (meaning1331 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1320 = false ∨ valuation q 1331 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 1 4 (meaning1273 q) (meaning1322 q) (meaning1333 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1322 = false ∨ valuation q 1333 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1331 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1331)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 2 1 (meaning1274 q) (meaning1319 q) (meaning1331 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1319 = false ∨ valuation q 1331 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1332 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1332)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 2 2 (meaning1274 q) (meaning1320 q) (meaning1332 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1320 = false ∨ valuation q 1332 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 2 3 (meaning1274 q) (meaning1321 q) (meaning1333 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1321 = false ∨ valuation q 1333 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1332 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1275)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1332)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 3 1 (meaning1275 q) (meaning1319 q) (meaning1332 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1319 = false ∨ valuation q 1332 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1275)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 3 2 (meaning1275 q) (meaning1320 q) (meaning1333 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1320 = false ∨ valuation q 1333 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1334 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1275)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 3 3 (meaning1275 q) (meaning1321 q) (meaning1334 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1321 = false ∨ valuation q 1334 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1276 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1276)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 4 1 (meaning1276 q) (meaning1319 q) (meaning1333 q) hs
  change valuationOf q 1276 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1276 = false ∨ valuation q 1319 = false ∨ valuation q 1333 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1276 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1334 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1276)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 4 2 (meaning1276 q) (meaning1320 q) (meaning1334 q) hs
  change valuationOf q 1276 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1276 = false ∨ valuation q 1320 = false ∨ valuation q 1334 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1334 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1277)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 5 1 (meaning1277 q) (meaning1319 q) (meaning1334 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1319 = false ∨ valuation q 1334 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1335 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1277)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1335)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 5 2 (meaning1277 q) (meaning1320 q) (meaning1335 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1320 = false ∨ valuation q 1335 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1335 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) + (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (l₂ := [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1278)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1335)) (countLit q [-2, -6, -7, -8, -10, -12, -14, -17, -20, -21, -22, -24]) (countLit q [-26, -29, -32, -34, -35, -37, -41, -42, -43, -44, -48, -49, -52]) (count1329 q) 6 1 (meaning1278 q) (meaning1319 q) (meaning1335 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1319 = false ∨ valuation q 1335 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1339 = true := by
  have hs : count1339 q = (countLit q [-54]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1339)) (countLit q [-54]) (countLit q [-58]) (count1339 q) 1 (meaningNeg58 q) (meaning1339 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1339 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-53]) + (countLit q [-54, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54, -58])
  have hm := merge_right (literal (valuationOf q) (1339)) (literal (valuationOf q) (1341)) (countLit q [-53]) (countLit q [-54, -58]) (count1341 q) 1 (meaning1339 q) (meaning1341 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1341 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1344)) (countLit q [-61]) (countLit q [-63]) (count1344 q) 1 (meaningNeg63 q) (meaning1344 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1344 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1344)) (countLit q [-61]) (countLit q [-63]) (count1344 q) 1 (meaningNeg61 q) (meaning1344 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1344 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-60]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1344)) (literal (valuationOf q) (1346)) (countLit q [-60]) (countLit q [-61, -63]) (count1346 q) 1 (meaning1344 q) (meaning1346 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1346 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-60]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -63])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1346)) (countLit q [-60]) (countLit q [-61, -63]) (count1346 q) 1 (meaningNeg60 q) (meaning1346 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1346 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true := by
  have hs : count1346 q = (countLit q [-60]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1347)) (countLit q [-60]) (countLit q [-61, -63]) (count1346 q) 1 1 (meaningNeg60 q) (meaning1344 q) (meaning1347 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1344 = false ∨ valuation q 1347 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-53, -54, -58]) + (countLit q [-60, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58]) (l₂ := [-60, -61, -63])
  have hm := merge_right (literal (valuationOf q) (1346)) (literal (valuationOf q) (1349)) (countLit q [-53, -54, -58]) (countLit q [-60, -61, -63]) (count1349 q) 1 (meaning1346 q) (meaning1349 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1349 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-53, -54, -58]) + (countLit q [-60, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58]) (l₂ := [-60, -61, -63])
  have hm := merge_right (literal (valuationOf q) (1347)) (literal (valuationOf q) (1350)) (countLit q [-53, -54, -58]) (countLit q [-60, -61, -63]) (count1349 q) 2 (meaning1347 q) (meaning1350 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1350 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-53, -54, -58]) + (countLit q [-60, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58]) (l₂ := [-60, -61, -63])
  have hm := merge_left (literal (valuationOf q) (1341)) (literal (valuationOf q) (1349)) (countLit q [-53, -54, -58]) (countLit q [-60, -61, -63]) (count1349 q) 1 (meaning1341 q) (meaning1349 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1349 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-53, -54, -58]) + (countLit q [-60, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58]) (l₂ := [-60, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-53, -54, -58]) (countLit q [-60, -61, -63]) (count1349 q) 1 1 (meaning1341 q) (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1346 = false ∨ valuation q 1350 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1355 = true := by
  have hs : count1355 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1355)) (countLit q [-69]) (countLit q [-70]) (count1355 q) 1 (meaningNeg70 q) (meaning1355 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1355 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1355 = true := by
  have hs : count1355 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1355)) (countLit q [-69]) (countLit q [-70]) (count1355 q) 1 (meaningNeg69 q) (meaning1355 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1355 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1357 = true := by
  have hs : count1357 q = (countLit q [-67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69, -70])
  have hm := merge_right (literal (valuationOf q) (1355)) (literal (valuationOf q) (1357)) (countLit q [-67]) (countLit q [-69, -70]) (count1357 q) 1 (meaning1355 q) (meaning1357 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1357 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1357 = true := by
  have hs : count1357 q = (countLit q [-67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1357)) (countLit q [-67]) (countLit q [-69, -70]) (count1357 q) 1 (meaningNeg67 q) (meaning1357 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1357 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E179.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112179
