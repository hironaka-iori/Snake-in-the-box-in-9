import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 1 4 (meaning1273 q) (meaning1322 q) (meaning1333 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1322 = false ∨ valuation q 1333 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1331 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1331)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 2 1 (meaning1274 q) (meaning1319 q) (meaning1331 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1319 = false ∨ valuation q 1331 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1332 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1332)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 2 2 (meaning1274 q) (meaning1320 q) (meaning1332 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1320 = false ∨ valuation q 1332 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 2 3 (meaning1274 q) (meaning1321 q) (meaning1333 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1321 = false ∨ valuation q 1333 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1334 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 2 4 (meaning1274 q) (meaning1322 q) (meaning1334 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1322 = false ∨ valuation q 1334 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1332 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1275)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1332)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 3 1 (meaning1275 q) (meaning1319 q) (meaning1332 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1319 = false ∨ valuation q 1332 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1275)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 3 2 (meaning1275 q) (meaning1320 q) (meaning1333 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1320 = false ∨ valuation q 1333 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1334 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1275)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 3 3 (meaning1275 q) (meaning1321 q) (meaning1334 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1321 = false ∨ valuation q 1334 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1276 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1276)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1333)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 4 1 (meaning1276 q) (meaning1319 q) (meaning1333 q) hs
  change valuationOf q 1276 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1276 = false ∨ valuation q 1319 = false ∨ valuation q 1333 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 1276 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1334 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1276)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 4 2 (meaning1276 q) (meaning1320 q) (meaning1334 q) hs
  change valuationOf q 1276 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 1276 = false ∨ valuation q 1320 = false ∨ valuation q 1334 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1334 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1277)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1334)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 5 1 (meaning1277 q) (meaning1319 q) (meaning1334 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1319 = false ∨ valuation q 1334 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1335 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1278)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1335)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 6 1 (meaning1278 q) (meaning1319 q) (meaning1335 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1319 = false ∨ valuation q 1335 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1339 = true := by
  have hs : count1339 q = (countLit q [-55]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (1339)) (countLit q [-55]) (countLit q [-59]) (count1339 q) 1 (meaningNeg59 q) (meaning1339 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1339 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-54]) + (countLit q [-55, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -59])
  have hm := merge_right (literal (valuationOf q) (1339)) (literal (valuationOf q) (1341)) (countLit q [-54]) (countLit q [-55, -59]) (count1341 q) 1 (meaning1339 q) (meaning1341 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1341 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-54]) + (countLit q [-55, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -59])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1341)) (countLit q [-54]) (countLit q [-55, -59]) (count1341 q) 1 (meaningNeg54 q) (meaning1341 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1341 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (1344)) (countLit q [-62]) (countLit q [-64]) (count1344 q) 1 (meaningNeg64 q) (meaning1344 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1344 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1344)) (countLit q [-62]) (countLit q [-64]) (count1344 q) 1 (meaningNeg62 q) (meaning1344 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1344 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-61]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -64])
  have hm := merge_right (literal (valuationOf q) (1344)) (literal (valuationOf q) (1346)) (countLit q [-61]) (countLit q [-62, -64]) (count1346 q) 1 (meaning1344 q) (meaning1346 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1346 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-61]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -64])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1346)) (countLit q [-61]) (countLit q [-62, -64]) (count1346 q) 1 (meaningNeg61 q) (meaning1346 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1346 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true := by
  have hs : count1346 q = (countLit q [-61]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -64])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1347)) (countLit q [-61]) (countLit q [-62, -64]) (count1346 q) 1 1 (meaningNeg61 q) (meaning1344 q) (meaning1347 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1344 = false ∨ valuation q 1347 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-54, -55, -59]) + (countLit q [-61, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59]) (l₂ := [-61, -62, -64])
  have hm := merge_right (literal (valuationOf q) (1346)) (literal (valuationOf q) (1349)) (countLit q [-54, -55, -59]) (countLit q [-61, -62, -64]) (count1349 q) 1 (meaning1346 q) (meaning1349 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1349 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-54, -55, -59]) + (countLit q [-61, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59]) (l₂ := [-61, -62, -64])
  have hm := merge_right (literal (valuationOf q) (1347)) (literal (valuationOf q) (1350)) (countLit q [-54, -55, -59]) (countLit q [-61, -62, -64]) (count1349 q) 2 (meaning1347 q) (meaning1350 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1350 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-54, -55, -59]) + (countLit q [-61, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59]) (l₂ := [-61, -62, -64])
  have hm := merge_left (literal (valuationOf q) (1341)) (literal (valuationOf q) (1349)) (countLit q [-54, -55, -59]) (countLit q [-61, -62, -64]) (count1349 q) 1 (meaning1341 q) (meaning1349 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1349 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-54, -55, -59]) + (countLit q [-61, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59]) (l₂ := [-61, -62, -64])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-54, -55, -59]) (countLit q [-61, -62, -64]) (count1349 q) 1 1 (meaning1341 q) (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1346 = false ∨ valuation q 1350 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1351 = true := by
  have hs : count1349 q = (countLit q [-54, -55, -59]) + (countLit q [-61, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59]) (l₂ := [-61, -62, -64])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1351)) (countLit q [-54, -55, -59]) (countLit q [-61, -62, -64]) (count1349 q) 1 2 (meaning1341 q) (meaning1347 q) (meaning1351 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1347 = false ∨ valuation q 1351 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1355 = true := by
  have hs : count1355 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1355)) (countLit q [-69]) (countLit q [-70]) (count1355 q) 1 (meaningNeg70 q) (meaning1355 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1355 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1355 = true := by
  have hs : count1355 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1355)) (countLit q [-69]) (countLit q [-70]) (count1355 q) 1 (meaningNeg69 q) (meaning1355 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1355 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1356 = true := by
  have hs : count1355 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1356)) (countLit q [-69]) (countLit q [-70]) (count1355 q) 1 1 (meaningNeg69 q) (meaningNeg70 q) (meaning1356 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 1356 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1357 = true := by
  have hs : count1357 q = (countLit q [-68]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69, -70])
  have hm := merge_right (literal (valuationOf q) (1355)) (literal (valuationOf q) (1357)) (countLit q [-68]) (countLit q [-69, -70]) (count1357 q) 1 (meaning1355 q) (meaning1357 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1357 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1358 = true := by
  have hs : count1357 q = (countLit q [-68]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69, -70])
  have hm := merge_right (literal (valuationOf q) (1356)) (literal (valuationOf q) (1358)) (countLit q [-68]) (countLit q [-69, -70]) (count1357 q) 2 (meaning1356 q) (meaning1358 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1358 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1357 = true := by
  have hs : count1357 q = (countLit q [-68]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1357)) (countLit q [-68]) (countLit q [-69, -70]) (count1357 q) 1 (meaningNeg68 q) (meaning1357 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1357 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1355 = false ∨ valuationOf q 1358 = true := by
  have hs : count1357 q = (countLit q [-68]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1358)) (countLit q [-68]) (countLit q [-69, -70]) (count1357 q) 1 1 (meaningNeg68 q) (meaning1355 q) (meaning1358 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1355 = false ∨ valuation q 1358 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E175.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112175
