import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1314 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1249)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1314)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 4 3 (meaning1249 q) (meaning1297 q) (meaning1314 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1297 = false ∨ valuation q 1314 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1315 = true := by
  have hs : count1308 q = (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52])
  have hm := merge_two (literal (valuationOf q) (1249)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1315)) (countLit q [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]) (count1308 q) 4 4 (meaning1249 q) (meaning1298 q) (meaning1315 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1298 = false ∨ valuation q 1315 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1321 = true := by
  have hs : count1321 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1321)) (countLit q [-55]) (countLit q [-57]) (count1321 q) 1 (meaningNeg57 q) (meaning1321 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1321 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1323 = true := by
  have hs : count1323 q = (countLit q [-54]) + (countLit q [-55, -57]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -57])
  have hm := merge_right (literal (valuationOf q) (1321)) (literal (valuationOf q) (1323)) (countLit q [-54]) (countLit q [-55, -57]) (count1323 q) 1 (meaning1321 q) (meaning1323 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1323 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1323 = true := by
  have hs : count1323 q = (countLit q [-54]) + (countLit q [-55, -57]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -57])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1323)) (countLit q [-54]) (countLit q [-55, -57]) (count1323 q) 1 (meaningNeg54 q) (meaning1323 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1323 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1321 = false ∨ valuationOf q 1324 = true := by
  have hs : count1323 q = (countLit q [-54]) + (countLit q [-55, -57]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -57])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1324)) (countLit q [-54]) (countLit q [-55, -57]) (count1323 q) 1 1 (meaningNeg54 q) (meaning1321 q) (meaning1324 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1321 = false ∨ valuation q 1324 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-60]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1326)) (countLit q [-60]) (countLit q [-63]) (count1326 q) 1 (meaningNeg63 q) (meaning1326 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1326 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-60]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1326)) (countLit q [-60]) (countLit q [-63]) (count1326 q) 1 (meaningNeg60 q) (meaning1326 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1326 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-60]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1327)) (countLit q [-60]) (countLit q [-63]) (count1326 q) 1 1 (meaningNeg60 q) (meaningNeg63 q) (meaning1327 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 63 = true ∨ valuation q 1327 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1328 = true := by
  have hs : count1328 q = (countLit q [-59]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -63])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1328)) (countLit q [-59]) (countLit q [-60, -63]) (count1328 q) 1 (meaning1326 q) (meaning1328 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1328 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1329 = true := by
  have hs : count1328 q = (countLit q [-59]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -63])
  have hm := merge_right (literal (valuationOf q) (1327)) (literal (valuationOf q) (1329)) (countLit q [-59]) (countLit q [-60, -63]) (count1328 q) 2 (meaning1327 q) (meaning1329 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1329 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1328 = true := by
  have hs : count1328 q = (countLit q [-59]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60, -63])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1328)) (countLit q [-59]) (countLit q [-60, -63]) (count1328 q) 1 (meaningNeg59 q) (meaning1328 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1328 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-54, -55, -57]) + (countLit q [-59, -60, -63]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-59, -60, -63])
  have hm := merge_right (literal (valuationOf q) (1328)) (literal (valuationOf q) (1331)) (countLit q [-54, -55, -57]) (countLit q [-59, -60, -63]) (count1331 q) 1 (meaning1328 q) (meaning1331 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1331 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1332 = true := by
  have hs : count1331 q = (countLit q [-54, -55, -57]) + (countLit q [-59, -60, -63]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-59, -60, -63])
  have hm := merge_right (literal (valuationOf q) (1329)) (literal (valuationOf q) (1332)) (countLit q [-54, -55, -57]) (countLit q [-59, -60, -63]) (count1331 q) 2 (meaning1329 q) (meaning1332 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1332 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-54, -55, -57]) + (countLit q [-59, -60, -63]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-59, -60, -63])
  have hm := merge_left (literal (valuationOf q) (1323)) (literal (valuationOf q) (1331)) (countLit q [-54, -55, -57]) (countLit q [-59, -60, -63]) (count1331 q) 1 (meaning1323 q) (meaning1331 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1331 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1332 = true := by
  have hs : count1331 q = (countLit q [-54, -55, -57]) + (countLit q [-59, -60, -63]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-59, -60, -63])
  have hm := merge_two (literal (valuationOf q) (1323)) (literal (valuationOf q) (1328)) (literal (valuationOf q) (1332)) (countLit q [-54, -55, -57]) (countLit q [-59, -60, -63]) (count1331 q) 1 1 (meaning1323 q) (meaning1328 q) (meaning1332 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1328 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1328 = false ∨ valuation q 1332 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1333 = true := by
  have hs : count1331 q = (countLit q [-54, -55, -57]) + (countLit q [-59, -60, -63]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-59, -60, -63])
  have hm := merge_two (literal (valuationOf q) (1323)) (literal (valuationOf q) (1329)) (literal (valuationOf q) (1333)) (countLit q [-54, -55, -57]) (countLit q [-59, -60, -63]) (count1331 q) 1 2 (meaning1323 q) (meaning1329 q) (meaning1333 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1329 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1329 = false ∨ valuation q 1333 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1332 = true := by
  have hs : count1331 q = (countLit q [-54, -55, -57]) + (countLit q [-59, -60, -63]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57]) (l₂ := [-59, -60, -63])
  have hm := merge_left (literal (valuationOf q) (1324)) (literal (valuationOf q) (1332)) (countLit q [-54, -55, -57]) (countLit q [-59, -60, -63]) (count1331 q) 2 (meaning1324 q) (meaning1332 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1332 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1337 = true := by
  have hs : count1337 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1337)) (countLit q [-65]) (countLit q [-67]) (count1337 q) 1 (meaningNeg65 q) (meaning1337 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1337 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1338 = true := by
  have hs : count1337 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1338)) (countLit q [-65]) (countLit q [-67]) (count1337 q) 1 1 (meaningNeg65 q) (meaningNeg67 q) (meaning1338 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 1338 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1339 = true := by
  have hs : count1339 q = (countLit q [-64]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65, -67])
  have hm := merge_right (literal (valuationOf q) (1337)) (literal (valuationOf q) (1339)) (countLit q [-64]) (countLit q [-65, -67]) (count1339 q) 1 (meaning1337 q) (meaning1339 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1339 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1340 = true := by
  have hs : count1339 q = (countLit q [-64]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65, -67])
  have hm := merge_right (literal (valuationOf q) (1338)) (literal (valuationOf q) (1340)) (countLit q [-64]) (countLit q [-65, -67]) (count1339 q) 2 (meaning1338 q) (meaning1340 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1340 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1339 = true := by
  have hs : count1339 q = (countLit q [-64]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65, -67])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1339)) (countLit q [-64]) (countLit q [-65, -67]) (count1339 q) 1 (meaningNeg64 q) (meaning1339 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1339 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1342 = true := by
  have hs : count1342 q = (countLit q [-70]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1342)) (countLit q [-70]) (countLit q [-73]) (count1342 q) 1 (meaningNeg73 q) (meaning1342 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1342 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1342 = true := by
  have hs : count1342 q = (countLit q [-70]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1342)) (countLit q [-70]) (countLit q [-73]) (count1342 q) 1 (meaningNeg70 q) (meaning1342 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1342 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1344)) (countLit q [-76]) (countLit q [-77]) (count1344 q) 1 (meaningNeg77 q) (meaning1344 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1344 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1344)) (countLit q [-76]) (countLit q [-77]) (count1344 q) 1 (meaningNeg76 q) (meaning1344 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1344 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1345)) (countLit q [-76]) (countLit q [-77]) (count1344 q) 1 1 (meaningNeg76 q) (meaningNeg77 q) (meaning1345 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 77 = true ∨ valuation q 1345 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1344)) (literal (valuationOf q) (1346)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count1346 q) 1 (meaning1344 q) (meaning1346 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1346 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1347 = true := by
  have hs : count1346 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1345)) (literal (valuationOf q) (1347)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count1346 q) 2 (meaning1345 q) (meaning1347 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1347 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (1342)) (literal (valuationOf q) (1346)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count1346 q) 1 (meaning1342 q) (meaning1346 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1346 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true := by
  have hs : count1346 q = (countLit q [-70, -73]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1347)) (countLit q [-70, -73]) (countLit q [-76, -77]) (count1346 q) 1 1 (meaning1342 q) (meaning1344 q) (meaning1347 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1344 = false ∨ valuation q 1347 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E094.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112094
