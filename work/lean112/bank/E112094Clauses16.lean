import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-64, -65, -67]) + (countLit q [-70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-64, -65, -67]) (l₂ := [-70, -73, -76, -77])
  have hm := merge_right (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-64, -65, -67]) (countLit q [-70, -73, -76, -77]) (count1350 q) 1 (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1350 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1351 = true := by
  have hs : count1350 q = (countLit q [-64, -65, -67]) + (countLit q [-70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-64, -65, -67]) (l₂ := [-70, -73, -76, -77])
  have hm := merge_right (literal (valuationOf q) (1347)) (literal (valuationOf q) (1351)) (countLit q [-64, -65, -67]) (countLit q [-70, -73, -76, -77]) (count1350 q) 2 (meaning1347 q) (meaning1351 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1351 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-64, -65, -67]) + (countLit q [-70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-64, -65, -67]) (l₂ := [-70, -73, -76, -77])
  have hm := merge_left (literal (valuationOf q) (1339)) (literal (valuationOf q) (1350)) (countLit q [-64, -65, -67]) (countLit q [-70, -73, -76, -77]) (count1350 q) 1 (meaning1339 q) (meaning1350 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1350 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1351 = true := by
  have hs : count1350 q = (countLit q [-64, -65, -67]) + (countLit q [-70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-64, -65, -67]) (l₂ := [-70, -73, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1339)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1351)) (countLit q [-64, -65, -67]) (countLit q [-70, -73, -76, -77]) (count1350 q) 1 1 (meaning1339 q) (meaning1346 q) (meaning1351 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1346 = false ∨ valuation q 1351 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1352 = true := by
  have hs : count1350 q = (countLit q [-64, -65, -67]) + (countLit q [-70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-64, -65, -67]) (l₂ := [-70, -73, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1339)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1352)) (countLit q [-64, -65, -67]) (countLit q [-70, -73, -76, -77]) (count1350 q) 1 2 (meaning1339 q) (meaning1347 q) (meaning1352 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1347 = false ∨ valuation q 1352 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1352 = true := by
  have hs : count1350 q = (countLit q [-64, -65, -67]) + (countLit q [-70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-64, -65, -67]) (l₂ := [-70, -73, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1340)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1352)) (countLit q [-64, -65, -67]) (countLit q [-70, -73, -76, -77]) (count1350 q) 2 1 (meaning1340 q) (meaning1346 q) (meaning1352 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1346 = false ∨ valuation q 1352 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1357 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1357)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 1 (meaning1350 q) (meaning1357 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1357 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1358 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_right (literal (valuationOf q) (1351)) (literal (valuationOf q) (1358)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 2 (meaning1351 q) (meaning1358 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1358 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1359 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_right (literal (valuationOf q) (1352)) (literal (valuationOf q) (1359)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 3 (meaning1352 q) (meaning1359 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1359 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1358 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1358)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 1 1 (meaning1331 q) (meaning1350 q) (meaning1358 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1350 = false ∨ valuation q 1358 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1359 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1359)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 1 2 (meaning1331 q) (meaning1351 q) (meaning1359 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1351 = false ∨ valuation q 1359 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1360 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1360)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 1 3 (meaning1331 q) (meaning1352 q) (meaning1360 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1352 = false ∨ valuation q 1360 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1358 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_left (literal (valuationOf q) (1332)) (literal (valuationOf q) (1358)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 2 (meaning1332 q) (meaning1358 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1358 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1359 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1359)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 2 1 (meaning1332 q) (meaning1350 q) (meaning1359 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1350 = false ∨ valuation q 1359 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1360 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1360)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 2 2 (meaning1332 q) (meaning1351 q) (meaning1360 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1351 = false ∨ valuation q 1360 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1360 = true := by
  have hs : count1357 q = (countLit q [-54, -55, -57, -59, -60, -63]) + (countLit q [-64, -65, -67, -70, -73, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63]) (l₂ := [-64, -65, -67, -70, -73, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1360)) (countLit q [-54, -55, -57, -59, -60, -63]) (countLit q [-64, -65, -67, -70, -73, -76, -77]) (count1357 q) 3 1 (meaning1333 q) (meaning1350 q) (meaning1360 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1350 = false ∨ valuation q 1360 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1370)) (countLit q [-80]) (countLit q [-82]) (count1370 q) 1 (meaningNeg82 q) (meaning1370 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1370 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1370)) (countLit q [-80]) (countLit q [-82]) (count1370 q) 1 (meaningNeg80 q) (meaning1370 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1370 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1371)) (countLit q [-80]) (countLit q [-82]) (count1370 q) 1 1 (meaningNeg80 q) (meaningNeg82 q) (meaning1371 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 1371 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1372 = true := by
  have hs : count1372 q = (countLit q [-78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80, -82])
  have hm := merge_right (literal (valuationOf q) (1370)) (literal (valuationOf q) (1372)) (countLit q [-78]) (countLit q [-80, -82]) (count1372 q) 1 (meaning1370 q) (meaning1372 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1372 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1373 = true := by
  have hs : count1372 q = (countLit q [-78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80, -82])
  have hm := merge_right (literal (valuationOf q) (1371)) (literal (valuationOf q) (1373)) (countLit q [-78]) (countLit q [-80, -82]) (count1372 q) 2 (meaning1371 q) (meaning1373 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1373 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1372 = true := by
  have hs : count1372 q = (countLit q [-78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80, -82])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1372)) (countLit q [-78]) (countLit q [-80, -82]) (count1372 q) 1 (meaningNeg78 q) (meaning1372 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1372 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1370 = false ∨ valuationOf q 1373 = true := by
  have hs : count1372 q = (countLit q [-78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1373)) (countLit q [-78]) (countLit q [-80, -82]) (count1372 q) 1 1 (meaningNeg78 q) (meaning1370 q) (meaning1373 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1370 = false ∨ valuation q 1373 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1371 = false ∨ valuationOf q 1374 = true := by
  have hs : count1372 q = (countLit q [-78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1374)) (countLit q [-78]) (countLit q [-80, -82]) (count1372 q) 1 2 (meaningNeg78 q) (meaning1371 q) (meaning1374 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1371 = false ∨ valuation q 1374 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1375 = true := by
  have hs : count1375 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1375)) (countLit q [-84]) (countLit q [-86]) (count1375 q) 1 (meaningNeg86 q) (meaning1375 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1375 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1375 = true := by
  have hs : count1375 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1375)) (countLit q [-84]) (countLit q [-86]) (count1375 q) 1 (meaningNeg84 q) (meaning1375 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1375 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1376 = true := by
  have hs : count1375 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1376)) (countLit q [-84]) (countLit q [-86]) (count1375 q) 1 1 (meaningNeg84 q) (meaningNeg86 q) (meaning1376 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 1376 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1377 = true := by
  have hs : count1377 q = (countLit q [-87]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1377)) (countLit q [-87]) (countLit q [-92]) (count1377 q) 1 (meaningNeg87 q) (meaning1377 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1377 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1378 = true := by
  have hs : count1377 q = (countLit q [-87]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1378)) (countLit q [-87]) (countLit q [-92]) (count1377 q) 1 1 (meaningNeg87 q) (meaningNeg92 q) (meaning1378 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 92 = true ∨ valuation q 1378 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-84, -86]) + (countLit q [-87, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -86]) (l₂ := [-87, -92])
  have hm := merge_right (literal (valuationOf q) (1377)) (literal (valuationOf q) (1379)) (countLit q [-84, -86]) (countLit q [-87, -92]) (count1379 q) 1 (meaning1377 q) (meaning1379 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1379 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-84, -86]) + (countLit q [-87, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -86]) (l₂ := [-87, -92])
  have hm := merge_left (literal (valuationOf q) (1375)) (literal (valuationOf q) (1379)) (countLit q [-84, -86]) (countLit q [-87, -92]) (count1379 q) 1 (meaning1375 q) (meaning1379 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1379 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1380 = true := by
  have hs : count1379 q = (countLit q [-84, -86]) + (countLit q [-87, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -86]) (l₂ := [-87, -92])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1377)) (literal (valuationOf q) (1380)) (countLit q [-84, -86]) (countLit q [-87, -92]) (count1379 q) 1 1 (meaning1375 q) (meaning1377 q) (meaning1380 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1377 = false ∨ valuation q 1380 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E094.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112094
