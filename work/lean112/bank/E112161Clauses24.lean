import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1340 = true := by
  have hs : count1339 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1340)) (countLit q [-19]) (countLit q [-21]) (count1339 q) 1 1 (meaningNeg19 q) (meaningNeg21 q) (meaning1340 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 1340 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (1339)) (literal (valuationOf q) (1341)) (countLit q [-17]) (countLit q [-19, -21]) (count1341 q) 1 (meaning1339 q) (meaning1341 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1341 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1342 = true := by
  have hs : count1341 q = (countLit q [-17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (1340)) (literal (valuationOf q) (1342)) (countLit q [-17]) (countLit q [-19, -21]) (count1341 q) 2 (meaning1340 q) (meaning1342 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1342 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1341)) (countLit q [-17]) (countLit q [-19, -21]) (count1341 q) 1 (meaningNeg17 q) (meaning1341 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1341 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1339 = false ∨ valuationOf q 1342 = true := by
  have hs : count1341 q = (countLit q [-17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1342)) (countLit q [-17]) (countLit q [-19, -21]) (count1341 q) 1 1 (meaningNeg17 q) (meaning1339 q) (meaning1342 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1339 = false ∨ valuation q 1342 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1340 = false ∨ valuationOf q 1343 = true := by
  have hs : count1341 q = (countLit q [-17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1343)) (countLit q [-17]) (countLit q [-19, -21]) (count1341 q) 1 2 (meaningNeg17 q) (meaning1340 q) (meaning1343 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1340 = false ∨ valuation q 1343 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1344)) (countLit q [-22]) (countLit q [-24]) (count1344 q) 1 (meaningNeg24 q) (meaning1344 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1344 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1344)) (countLit q [-22]) (countLit q [-24]) (count1344 q) 1 (meaningNeg22 q) (meaning1344 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1344 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1345)) (countLit q [-22]) (countLit q [-24]) (count1344 q) 1 1 (meaningNeg22 q) (meaningNeg24 q) (meaning1345 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 24 = true ∨ valuation q 1345 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-25]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1346)) (countLit q [-25]) (countLit q [-29]) (count1346 q) 1 (meaningNeg29 q) (meaning1346 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1346 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-25]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1346)) (countLit q [-25]) (countLit q [-29]) (count1346 q) 1 (meaningNeg25 q) (meaning1346 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1346 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 29 = true ∨ valuationOf q 1347 = true := by
  have hs : count1346 q = (countLit q [-25]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (1347)) (countLit q [-25]) (countLit q [-29]) (count1346 q) 1 1 (meaningNeg25 q) (meaningNeg29 q) (meaning1347 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 29 = true ∨ valuation q 1347 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-22, -24]) + (countLit q [-25, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -29])
  have hm := merge_right (literal (valuationOf q) (1346)) (literal (valuationOf q) (1348)) (countLit q [-22, -24]) (countLit q [-25, -29]) (count1348 q) 1 (meaning1346 q) (meaning1348 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1348 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-22, -24]) + (countLit q [-25, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -29])
  have hm := merge_right (literal (valuationOf q) (1347)) (literal (valuationOf q) (1349)) (countLit q [-22, -24]) (countLit q [-25, -29]) (count1348 q) 2 (meaning1347 q) (meaning1349 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1349 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-22, -24]) + (countLit q [-25, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -29])
  have hm := merge_left (literal (valuationOf q) (1344)) (literal (valuationOf q) (1348)) (countLit q [-22, -24]) (countLit q [-25, -29]) (count1348 q) 1 (meaning1344 q) (meaning1348 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1348 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-22, -24]) + (countLit q [-25, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -29])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1349)) (countLit q [-22, -24]) (countLit q [-25, -29]) (count1348 q) 1 1 (meaning1344 q) (meaning1346 q) (meaning1349 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1346 = false ∨ valuation q 1349 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1350 = true := by
  have hs : count1348 q = (countLit q [-22, -24]) + (countLit q [-25, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -29])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1350)) (countLit q [-22, -24]) (countLit q [-25, -29]) (count1348 q) 1 2 (meaning1344 q) (meaning1347 q) (meaning1350 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1347 = false ∨ valuation q 1350 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-22, -24]) + (countLit q [-25, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -29])
  have hm := merge_left (literal (valuationOf q) (1345)) (literal (valuationOf q) (1349)) (countLit q [-22, -24]) (countLit q [-25, -29]) (count1348 q) 2 (meaning1345 q) (meaning1349 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1349 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1348 q = (countLit q [-22, -24]) + (countLit q [-25, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -29])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-22, -24]) (countLit q [-25, -29]) (count1348 q) 2 1 (meaning1345 q) (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1346 = false ∨ valuation q 1350 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1351 = true := by
  have hs : count1348 q = (countLit q [-22, -24]) + (countLit q [-25, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -29])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1351)) (countLit q [-22, -24]) (countLit q [-25, -29]) (count1348 q) 2 2 (meaning1345 q) (meaning1347 q) (meaning1351 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1347 = false ∨ valuation q 1351 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1352 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_right (literal (valuationOf q) (1348)) (literal (valuationOf q) (1352)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 1 (meaning1348 q) (meaning1352 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1352 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1353 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1353)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 2 (meaning1349 q) (meaning1353 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1353 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1354 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1354)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 3 (meaning1350 q) (meaning1354 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1354 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1355 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_right (literal (valuationOf q) (1351)) (literal (valuationOf q) (1355)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 4 (meaning1351 q) (meaning1355 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1355 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1352 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_left (literal (valuationOf q) (1341)) (literal (valuationOf q) (1352)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 1 (meaning1341 q) (meaning1352 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1352 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1353 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1348)) (literal (valuationOf q) (1353)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 1 1 (meaning1341 q) (meaning1348 q) (meaning1353 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1348 = false ∨ valuation q 1353 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1354 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1354)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 1 2 (meaning1341 q) (meaning1349 q) (meaning1354 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1349 = false ∨ valuation q 1354 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1355 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1355)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 1 3 (meaning1341 q) (meaning1350 q) (meaning1355 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1350 = false ∨ valuation q 1355 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1356 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1356)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 1 4 (meaning1341 q) (meaning1351 q) (meaning1356 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1351 = false ∨ valuation q 1356 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1353 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_left (literal (valuationOf q) (1342)) (literal (valuationOf q) (1353)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 2 (meaning1342 q) (meaning1353 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1353 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1354 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1348)) (literal (valuationOf q) (1354)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 2 1 (meaning1342 q) (meaning1348 q) (meaning1354 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1348 = false ∨ valuation q 1354 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1355 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1355)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 2 2 (meaning1342 q) (meaning1349 q) (meaning1355 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1349 = false ∨ valuation q 1355 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E161.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112161
