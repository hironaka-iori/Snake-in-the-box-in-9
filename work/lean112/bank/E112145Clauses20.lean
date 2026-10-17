import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-65, -67, -69]) + (countLit q [-71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69]) (l₂ := [-71, -74, -76, -77])
  have hm := merge_left (literal (valuationOf q) (1351)) (literal (valuationOf q) (1362)) (countLit q [-65, -67, -69]) (countLit q [-71, -74, -76, -77]) (count1362 q) 1 (meaning1351 q) (meaning1362 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1362 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-65, -67, -69]) + (countLit q [-71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69]) (l₂ := [-71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1363)) (countLit q [-65, -67, -69]) (countLit q [-71, -74, -76, -77]) (count1362 q) 1 1 (meaning1351 q) (meaning1358 q) (meaning1363 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1358 = false ∨ valuation q 1363 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-65, -67, -69]) + (countLit q [-71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69]) (l₂ := [-71, -74, -76, -77])
  have hm := merge_left (literal (valuationOf q) (1352)) (literal (valuationOf q) (1363)) (countLit q [-65, -67, -69]) (countLit q [-71, -74, -76, -77]) (count1362 q) 2 (meaning1352 q) (meaning1363 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1363 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-65, -67, -69]) + (countLit q [-71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69]) (l₂ := [-71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1364)) (countLit q [-65, -67, -69]) (countLit q [-71, -74, -76, -77]) (count1362 q) 2 1 (meaning1352 q) (meaning1358 q) (meaning1364 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1358 = false ∨ valuation q 1364 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1365 = true := by
  have hs : count1362 q = (countLit q [-65, -67, -69]) + (countLit q [-71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69]) (l₂ := [-71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1365)) (countLit q [-65, -67, -69]) (countLit q [-71, -74, -76, -77]) (count1362 q) 2 2 (meaning1352 q) (meaning1359 q) (meaning1365 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1359 = false ∨ valuation q 1365 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-65, -67, -69]) + (countLit q [-71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69]) (l₂ := [-71, -74, -76, -77])
  have hm := merge_left (literal (valuationOf q) (1353)) (literal (valuationOf q) (1364)) (countLit q [-65, -67, -69]) (countLit q [-71, -74, -76, -77]) (count1362 q) 3 (meaning1353 q) (meaning1364 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1364 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1365 = true := by
  have hs : count1362 q = (countLit q [-65, -67, -69]) + (countLit q [-71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69]) (l₂ := [-71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1365)) (countLit q [-65, -67, -69]) (countLit q [-71, -74, -76, -77]) (count1362 q) 3 1 (meaning1353 q) (meaning1358 q) (meaning1365 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1358 = false ∨ valuation q 1365 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-53, -55, -57, -58, -59, -63]) + (countLit q [-65, -67, -69, -71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63]) (l₂ := [-65, -67, -69, -71, -74, -76, -77])
  have hm := merge_left (literal (valuationOf q) (1343)) (literal (valuationOf q) (1369)) (countLit q [-53, -55, -57, -58, -59, -63]) (countLit q [-65, -67, -69, -71, -74, -76, -77]) (count1369 q) 1 (meaning1343 q) (meaning1369 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1369 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-53, -55, -57, -58, -59, -63]) + (countLit q [-65, -67, -69, -71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63]) (l₂ := [-65, -67, -69, -71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1370)) (countLit q [-53, -55, -57, -58, -59, -63]) (countLit q [-65, -67, -69, -71, -74, -76, -77]) (count1369 q) 1 1 (meaning1343 q) (meaning1362 q) (meaning1370 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1362 = false ∨ valuation q 1370 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-53, -55, -57, -58, -59, -63]) + (countLit q [-65, -67, -69, -71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63]) (l₂ := [-65, -67, -69, -71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1371)) (countLit q [-53, -55, -57, -58, -59, -63]) (countLit q [-65, -67, -69, -71, -74, -76, -77]) (count1369 q) 1 2 (meaning1343 q) (meaning1363 q) (meaning1371 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1363 = false ∨ valuation q 1371 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-53, -55, -57, -58, -59, -63]) + (countLit q [-65, -67, -69, -71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63]) (l₂ := [-65, -67, -69, -71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1372)) (countLit q [-53, -55, -57, -58, -59, -63]) (countLit q [-65, -67, -69, -71, -74, -76, -77]) (count1369 q) 1 3 (meaning1343 q) (meaning1364 q) (meaning1372 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1364 = false ∨ valuation q 1372 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true := by
  have hs : count1369 q = (countLit q [-53, -55, -57, -58, -59, -63]) + (countLit q [-65, -67, -69, -71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63]) (l₂ := [-65, -67, -69, -71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1373)) (countLit q [-53, -55, -57, -58, -59, -63]) (countLit q [-65, -67, -69, -71, -74, -76, -77]) (count1369 q) 1 4 (meaning1343 q) (meaning1365 q) (meaning1373 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1365 = false ∨ valuation q 1373 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-53, -55, -57, -58, -59, -63]) + (countLit q [-65, -67, -69, -71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63]) (l₂ := [-65, -67, -69, -71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1371)) (countLit q [-53, -55, -57, -58, -59, -63]) (countLit q [-65, -67, -69, -71, -74, -76, -77]) (count1369 q) 2 1 (meaning1344 q) (meaning1362 q) (meaning1371 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1362 = false ∨ valuation q 1371 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-53, -55, -57, -58, -59, -63]) + (countLit q [-65, -67, -69, -71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63]) (l₂ := [-65, -67, -69, -71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1372)) (countLit q [-53, -55, -57, -58, -59, -63]) (countLit q [-65, -67, -69, -71, -74, -76, -77]) (count1369 q) 2 2 (meaning1344 q) (meaning1363 q) (meaning1372 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1363 = false ∨ valuation q 1372 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1373 = true := by
  have hs : count1369 q = (countLit q [-53, -55, -57, -58, -59, -63]) + (countLit q [-65, -67, -69, -71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63]) (l₂ := [-65, -67, -69, -71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1373)) (countLit q [-53, -55, -57, -58, -59, -63]) (countLit q [-65, -67, -69, -71, -74, -76, -77]) (count1369 q) 2 3 (meaning1344 q) (meaning1364 q) (meaning1373 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1364 = false ∨ valuation q 1373 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-53, -55, -57, -58, -59, -63]) + (countLit q [-65, -67, -69, -71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57, -58, -59, -63]) (l₂ := [-65, -67, -69, -71, -74, -76, -77])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1372)) (countLit q [-53, -55, -57, -58, -59, -63]) (countLit q [-65, -67, -69, -71, -74, -76, -77]) (count1369 q) 3 1 (meaning1345 q) (meaning1362 q) (meaning1372 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1362 = false ∨ valuation q 1372 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1380 = true := by
  have hs : count1380 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1380)) (countLit q [-83]) (countLit q [-84]) (count1380 q) 1 (meaningNeg84 q) (meaning1380 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1380 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1380 = true := by
  have hs : count1380 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1380)) (countLit q [-83]) (countLit q [-84]) (count1380 q) 1 (meaningNeg83 q) (meaning1380 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1380 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1382 = true := by
  have hs : count1382 q = (countLit q [-79]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-83, -84])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1382)) (countLit q [-79]) (countLit q [-83, -84]) (count1382 q) 1 (meaning1380 q) (meaning1382 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1382 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1385 = true := by
  have hs : count1385 q = (countLit q [-86]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1385)) (countLit q [-86]) (countLit q [-90]) (count1385 q) 1 (meaningNeg86 q) (meaning1385 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1385 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1387 = true := by
  have hs : count1387 q = (countLit q [-85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86, -90])
  have hm := merge_right (literal (valuationOf q) (1385)) (literal (valuationOf q) (1387)) (countLit q [-85]) (countLit q [-86, -90]) (count1387 q) 1 (meaning1385 q) (meaning1387 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1387 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1387 = true := by
  have hs : count1387 q = (countLit q [-85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86, -90])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1387)) (countLit q [-85]) (countLit q [-86, -90]) (count1387 q) 1 (meaningNeg85 q) (meaning1387 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1387 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1390 = true := by
  have hs : count1390 q = (countLit q [-79, -83, -84]) + (countLit q [-85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -83, -84]) (l₂ := [-85, -86, -90])
  have hm := merge_right (literal (valuationOf q) (1387)) (literal (valuationOf q) (1390)) (countLit q [-79, -83, -84]) (countLit q [-85, -86, -90]) (count1390 q) 1 (meaning1387 q) (meaning1390 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1390 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1390 = true := by
  have hs : count1390 q = (countLit q [-79, -83, -84]) + (countLit q [-85, -86, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -83, -84]) (l₂ := [-85, -86, -90])
  have hm := merge_left (literal (valuationOf q) (1382)) (literal (valuationOf q) (1390)) (countLit q [-79, -83, -84]) (countLit q [-85, -86, -90]) (count1390 q) 1 (meaning1382 q) (meaning1390 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1390 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1396 = true := by
  have hs : count1396 q = (countLit q [-93]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1396)) (countLit q [-93]) (countLit q [-95]) (count1396 q) 1 (meaningNeg93 q) (meaning1396 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1396 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-92]) + (countLit q [-93, -95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -95])
  have hm := merge_right (literal (valuationOf q) (1396)) (literal (valuationOf q) (1398)) (countLit q [-92]) (countLit q [-93, -95]) (count1398 q) 1 (meaning1396 q) (meaning1398 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1398 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-92]) + (countLit q [-93, -95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -95])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1398)) (countLit q [-92]) (countLit q [-93, -95]) (count1398 q) 1 (meaningNeg92 q) (meaning1398 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1398 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1401 = true := by
  have hs : count1401 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1401)) (countLit q [-99]) (countLit q [-100]) (count1401 q) 1 (meaningNeg100 q) (meaning1401 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1401 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1403)) (countLit q [-101]) (countLit q [-102]) (count1403 q) 1 (meaningNeg102 q) (meaning1403 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1403 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1403)) (countLit q [-101]) (countLit q [-102]) (count1403 q) 1 (meaningNeg101 q) (meaning1403 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1403 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-99, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-101, -102])
  have hm := merge_right (literal (valuationOf q) (1403)) (literal (valuationOf q) (1405)) (countLit q [-99, -100]) (countLit q [-101, -102]) (count1405 q) 1 (meaning1403 q) (meaning1405 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1405 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-99, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-101, -102])
  have hm := merge_left (literal (valuationOf q) (1401)) (literal (valuationOf q) (1405)) (countLit q [-99, -100]) (countLit q [-101, -102]) (count1405 q) 1 (meaning1401 q) (meaning1405 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1405 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E145.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112145
