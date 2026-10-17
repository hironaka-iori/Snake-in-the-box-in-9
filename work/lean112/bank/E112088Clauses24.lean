import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1430 = true := by
  have hs : count1425 q = (countLit q [-3, -5, -6, -8, -9, -13, -16]) + (countLit q [-19, -20, -21, -23, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16]) (l₂ := [-19, -20, -21, -23, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1430)) (countLit q [-3, -5, -6, -8, -9, -13, -16]) (countLit q [-19, -20, -21, -23, -25, -27, -28]) (count1425 q) 3 3 (meaning1400 q) (meaning1420 q) (meaning1430 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1420 = false ∨ valuation q 1430 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1431 = true := by
  have hs : count1425 q = (countLit q [-3, -5, -6, -8, -9, -13, -16]) + (countLit q [-19, -20, -21, -23, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16]) (l₂ := [-19, -20, -21, -23, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1431)) (countLit q [-3, -5, -6, -8, -9, -13, -16]) (countLit q [-19, -20, -21, -23, -25, -27, -28]) (count1425 q) 3 4 (meaning1400 q) (meaning1421 q) (meaning1431 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1421 = false ∨ valuation q 1431 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1432 = true := by
  have hs : count1425 q = (countLit q [-3, -5, -6, -8, -9, -13, -16]) + (countLit q [-19, -20, -21, -23, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16]) (l₂ := [-19, -20, -21, -23, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1432)) (countLit q [-3, -5, -6, -8, -9, -13, -16]) (countLit q [-19, -20, -21, -23, -25, -27, -28]) (count1425 q) 3 5 (meaning1400 q) (meaning1422 q) (meaning1432 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1422 = false ∨ valuation q 1432 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1428 = true := by
  have hs : count1425 q = (countLit q [-3, -5, -6, -8, -9, -13, -16]) + (countLit q [-19, -20, -21, -23, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16]) (l₂ := [-19, -20, -21, -23, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1401)) (literal (valuationOf q) (1428)) (countLit q [-3, -5, -6, -8, -9, -13, -16]) (countLit q [-19, -20, -21, -23, -25, -27, -28]) (count1425 q) 4 (meaning1401 q) (meaning1428 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1428 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1429 = true := by
  have hs : count1425 q = (countLit q [-3, -5, -6, -8, -9, -13, -16]) + (countLit q [-19, -20, -21, -23, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16]) (l₂ := [-19, -20, -21, -23, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1429)) (countLit q [-3, -5, -6, -8, -9, -13, -16]) (countLit q [-19, -20, -21, -23, -25, -27, -28]) (count1425 q) 4 1 (meaning1401 q) (meaning1418 q) (meaning1429 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1418 = false ∨ valuation q 1429 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1430 = true := by
  have hs : count1425 q = (countLit q [-3, -5, -6, -8, -9, -13, -16]) + (countLit q [-19, -20, -21, -23, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16]) (l₂ := [-19, -20, -21, -23, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1430)) (countLit q [-3, -5, -6, -8, -9, -13, -16]) (countLit q [-19, -20, -21, -23, -25, -27, -28]) (count1425 q) 4 2 (meaning1401 q) (meaning1419 q) (meaning1430 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1419 = false ∨ valuation q 1430 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1439)) (countLit q [-32]) (countLit q [-33]) (count1439 q) 1 (meaningNeg33 q) (meaning1439 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1439 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1439)) (countLit q [-32]) (countLit q [-33]) (count1439 q) 1 (meaningNeg32 q) (meaning1439 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1439 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1440 = true := by
  have hs : count1439 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1440)) (countLit q [-32]) (countLit q [-33]) (count1439 q) 1 1 (meaningNeg32 q) (meaningNeg33 q) (meaning1440 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 33 = true ∨ valuation q 1440 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-29]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-32, -33])
  have hm := merge_right (literal (valuationOf q) (1439)) (literal (valuationOf q) (1441)) (countLit q [-29]) (countLit q [-32, -33]) (count1441 q) 1 (meaning1439 q) (meaning1441 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1441 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-29]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-32, -33])
  have hm := merge_right (literal (valuationOf q) (1440)) (literal (valuationOf q) (1442)) (countLit q [-29]) (countLit q [-32, -33]) (count1441 q) 2 (meaning1440 q) (meaning1442 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1442 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-29]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-32, -33])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1441)) (countLit q [-29]) (countLit q [-32, -33]) (count1441 q) 1 (meaningNeg29 q) (meaning1441 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1441 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-29]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-32, -33])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1442)) (countLit q [-29]) (countLit q [-32, -33]) (count1441 q) 1 1 (meaningNeg29 q) (meaning1439 q) (meaning1442 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1439 = false ∨ valuation q 1442 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-29]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-32, -33])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1443)) (countLit q [-29]) (countLit q [-32, -33]) (count1441 q) 1 2 (meaningNeg29 q) (meaning1440 q) (meaning1443 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1440 = false ∨ valuation q 1443 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1444)) (countLit q [-35]) (countLit q [-36]) (count1444 q) 1 (meaningNeg36 q) (meaning1444 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1444 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1444)) (countLit q [-35]) (countLit q [-36]) (count1444 q) 1 (meaningNeg35 q) (meaning1444 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1444 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1445 = true := by
  have hs : count1444 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1445)) (countLit q [-35]) (countLit q [-36]) (count1444 q) 1 1 (meaningNeg35 q) (meaningNeg36 q) (meaning1445 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 1445 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1446)) (countLit q [-39]) (countLit q [-40]) (count1446 q) 1 (meaningNeg40 q) (meaning1446 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1446 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1446)) (countLit q [-39]) (countLit q [-40]) (count1446 q) 1 (meaningNeg39 q) (meaning1446 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1446 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 40 = true ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (1447)) (countLit q [-39]) (countLit q [-40]) (count1446 q) 1 1 (meaningNeg39 q) (meaningNeg40 q) (meaning1447 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 1447 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-35, -36]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -40])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (countLit q [-35, -36]) (countLit q [-39, -40]) (count1448 q) 1 (meaning1446 q) (meaning1448 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-35, -36]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -40])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (countLit q [-35, -36]) (countLit q [-39, -40]) (count1448 q) 2 (meaning1447 q) (meaning1449 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-35, -36]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -40])
  have hm := merge_left (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (countLit q [-35, -36]) (countLit q [-39, -40]) (count1448 q) 1 (meaning1444 q) (meaning1448 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1448 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-35, -36]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1449)) (countLit q [-35, -36]) (countLit q [-39, -40]) (count1448 q) 1 1 (meaning1444 q) (meaning1446 q) (meaning1449 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1446 = false ∨ valuation q 1449 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true := by
  have hs : count1448 q = (countLit q [-35, -36]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1450)) (countLit q [-35, -36]) (countLit q [-39, -40]) (count1448 q) 1 2 (meaning1444 q) (meaning1447 q) (meaning1450 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1447 = false ∨ valuation q 1450 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-35, -36]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -40])
  have hm := merge_left (literal (valuationOf q) (1445)) (literal (valuationOf q) (1449)) (countLit q [-35, -36]) (countLit q [-39, -40]) (count1448 q) 2 (meaning1445 q) (meaning1449 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1449 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1450 = true := by
  have hs : count1448 q = (countLit q [-35, -36]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1450)) (countLit q [-35, -36]) (countLit q [-39, -40]) (count1448 q) 2 1 (meaning1445 q) (meaning1446 q) (meaning1450 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1446 = false ∨ valuation q 1450 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1451 = true := by
  have hs : count1448 q = (countLit q [-35, -36]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1451)) (countLit q [-35, -36]) (countLit q [-39, -40]) (count1448 q) 2 2 (meaning1445 q) (meaning1447 q) (meaning1451 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1447 = false ∨ valuation q 1451 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 1 (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1452 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 2 (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1453 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 3 (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1454 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_right (literal (valuationOf q) (1451)) (literal (valuationOf q) (1455)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 4 (meaning1451 q) (meaning1455 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1455 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E088.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112088
