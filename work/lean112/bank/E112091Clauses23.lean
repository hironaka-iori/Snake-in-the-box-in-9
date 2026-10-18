import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1363)) (countLit q [-53]) (countLit q [-55]) (count1363 q) 1 (meaningNeg53 q) (meaning1363 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1363 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1364 = true := by
  have hs : count1363 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1364)) (countLit q [-53]) (countLit q [-55]) (count1363 q) 1 1 (meaningNeg53 q) (meaningNeg55 q) (meaning1364 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 1364 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53, -55])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1365)) (countLit q [-52]) (countLit q [-53, -55]) (count1365 q) 1 (meaning1363 q) (meaning1365 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1365 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53, -55])
  have hm := merge_right (literal (valuationOf q) (1364)) (literal (valuationOf q) (1366)) (countLit q [-52]) (countLit q [-53, -55]) (count1365 q) 2 (meaning1364 q) (meaning1366 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1366 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53, -55])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1365)) (countLit q [-52]) (countLit q [-53, -55]) (count1365 q) 1 (meaningNeg52 q) (meaning1365 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1365 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1363 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1366)) (countLit q [-52]) (countLit q [-53, -55]) (count1365 q) 1 1 (meaningNeg52 q) (meaning1363 q) (meaning1366 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1363 = false ∨ valuation q 1366 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1364 = false ∨ valuationOf q 1367 = true := by
  have hs : count1365 q = (countLit q [-52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1367)) (countLit q [-52]) (countLit q [-53, -55]) (count1365 q) 1 2 (meaningNeg52 q) (meaning1364 q) (meaning1367 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1364 = false ∨ valuation q 1367 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1368)) (countLit q [-61]) (countLit q [-62]) (count1368 q) 1 (meaningNeg62 q) (meaning1368 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1368 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1368)) (countLit q [-61]) (countLit q [-62]) (count1368 q) 1 (meaningNeg61 q) (meaning1368 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1368 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1369 = true := by
  have hs : count1368 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1369)) (countLit q [-61]) (countLit q [-62]) (count1368 q) 1 1 (meaningNeg61 q) (meaningNeg62 q) (meaning1369 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 62 = true ∨ valuation q 1369 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-57]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-61, -62])
  have hm := merge_right (literal (valuationOf q) (1368)) (literal (valuationOf q) (1370)) (countLit q [-57]) (countLit q [-61, -62]) (count1370 q) 1 (meaning1368 q) (meaning1370 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1370 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-57]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-61, -62])
  have hm := merge_right (literal (valuationOf q) (1369)) (literal (valuationOf q) (1371)) (countLit q [-57]) (countLit q [-61, -62]) (count1370 q) 2 (meaning1369 q) (meaning1371 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1371 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-57]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-61, -62])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1370)) (countLit q [-57]) (countLit q [-61, -62]) (count1370 q) 1 (meaningNeg57 q) (meaning1370 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1370 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-57]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-61, -62])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1371)) (countLit q [-57]) (countLit q [-61, -62]) (count1370 q) 1 1 (meaningNeg57 q) (meaning1368 q) (meaning1371 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1368 = false ∨ valuation q 1371 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1369 = false ∨ valuationOf q 1372 = true := by
  have hs : count1370 q = (countLit q [-57]) + (countLit q [-61, -62]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-61, -62])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1372)) (countLit q [-57]) (countLit q [-61, -62]) (count1370 q) 1 2 (meaningNeg57 q) (meaning1369 q) (meaning1372 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1369 = false ∨ valuation q 1372 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_right (literal (valuationOf q) (1370)) (literal (valuationOf q) (1373)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 1 (meaning1370 q) (meaning1373 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1373 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1374)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 1 1 (meaning1365 q) (meaning1370 q) (meaning1374 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1370 = false ∨ valuation q 1374 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1375)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 1 2 (meaning1365 q) (meaning1371 q) (meaning1375 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1371 = false ∨ valuation q 1375 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1372)) (literal (valuationOf q) (1376)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 1 3 (meaning1365 q) (meaning1372 q) (meaning1376 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1372 = false ∨ valuation q 1376 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1375)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 2 1 (meaning1366 q) (meaning1370 q) (meaning1375 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1370 = false ∨ valuation q 1375 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1376)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 2 2 (meaning1366 q) (meaning1371 q) (meaning1376 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1371 = false ∨ valuation q 1376 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1377 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1372)) (literal (valuationOf q) (1377)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 2 3 (meaning1366 q) (meaning1372 q) (meaning1377 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1372 = false ∨ valuation q 1377 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1376)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 3 1 (meaning1367 q) (meaning1370 q) (meaning1376 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1370 = false ∨ valuation q 1376 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1377 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1377)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 3 2 (meaning1367 q) (meaning1371 q) (meaning1377 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1371 = false ∨ valuation q 1377 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1378 = true := by
  have hs : count1373 q = (countLit q [-52, -53, -55]) + (countLit q [-57, -61, -62]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55]) (l₂ := [-57, -61, -62])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1372)) (literal (valuationOf q) (1378)) (countLit q [-52, -53, -55]) (countLit q [-57, -61, -62]) (count1373 q) 3 3 (meaning1367 q) (meaning1372 q) (meaning1378 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1372 = false ∨ valuation q 1378 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1379)) (countLit q [-65]) (countLit q [-68]) (count1379 q) 1 (meaningNeg68 q) (meaning1379 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1379 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1379)) (countLit q [-65]) (countLit q [-68]) (count1379 q) 1 (meaningNeg65 q) (meaning1379 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1379 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (1379)) (literal (valuationOf q) (1381)) (countLit q [-63]) (countLit q [-65, -68]) (count1381 q) 1 (meaning1379 q) (meaning1381 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1381 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1381)) (countLit q [-63]) (countLit q [-65, -68]) (count1381 q) 1 (meaningNeg63 q) (meaning1381 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1381 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1379 = false ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1382)) (countLit q [-63]) (countLit q [-65, -68]) (count1381 q) 1 1 (meaningNeg63 q) (meaning1379 q) (meaning1382 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1379 = false ∨ valuation q 1382 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-70]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1384)) (countLit q [-70]) (countLit q [-73]) (count1384 q) 1 (meaningNeg73 q) (meaning1384 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1384 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1386)) (countLit q [-75]) (countLit q [-76]) (count1386 q) 1 (meaningNeg76 q) (meaning1386 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1386 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E091.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112091
