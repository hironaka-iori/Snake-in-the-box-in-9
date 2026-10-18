import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1444)) (countLit q [-52]) (countLit q [-54]) (count1444 q) 1 (meaningNeg52 q) (meaning1444 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1444 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1445 = true := by
  have hs : count1444 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1445)) (countLit q [-52]) (countLit q [-54]) (count1444 q) 1 1 (meaningNeg52 q) (meaningNeg54 q) (meaning1445 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 1445 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1446)) (countLit q [-56]) (countLit q [-57]) (count1446 q) 1 (meaningNeg57 q) (meaning1446 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1446 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1446)) (countLit q [-56]) (countLit q [-57]) (count1446 q) 1 (meaningNeg56 q) (meaning1446 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1446 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1447)) (countLit q [-56]) (countLit q [-57]) (count1446 q) 1 1 (meaningNeg56 q) (meaningNeg57 q) (meaning1447 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 57 = true ∨ valuation q 1447 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-52, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -57])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (countLit q [-52, -54]) (countLit q [-56, -57]) (count1448 q) 1 (meaning1446 q) (meaning1448 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-52, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -57])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (countLit q [-52, -54]) (countLit q [-56, -57]) (count1448 q) 2 (meaning1447 q) (meaning1449 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-52, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (countLit q [-52, -54]) (countLit q [-56, -57]) (count1448 q) 1 (meaning1444 q) (meaning1448 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1448 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-52, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1449)) (countLit q [-52, -54]) (countLit q [-56, -57]) (count1448 q) 1 1 (meaning1444 q) (meaning1446 q) (meaning1449 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1446 = false ∨ valuation q 1449 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true := by
  have hs : count1448 q = (countLit q [-52, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1450)) (countLit q [-52, -54]) (countLit q [-56, -57]) (count1448 q) 1 2 (meaning1444 q) (meaning1447 q) (meaning1450 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1447 = false ∨ valuation q 1450 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-52, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1445)) (literal (valuationOf q) (1449)) (countLit q [-52, -54]) (countLit q [-56, -57]) (count1448 q) 2 (meaning1445 q) (meaning1449 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1449 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1450 = true := by
  have hs : count1448 q = (countLit q [-52, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1450)) (countLit q [-52, -54]) (countLit q [-56, -57]) (count1448 q) 2 1 (meaning1445 q) (meaning1446 q) (meaning1450 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1446 = false ∨ valuation q 1450 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1451 = true := by
  have hs : count1448 q = (countLit q [-52, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1451)) (countLit q [-52, -54]) (countLit q [-56, -57]) (count1448 q) 2 2 (meaning1445 q) (meaning1447 q) (meaning1451 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1447 = false ∨ valuation q 1451 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 1 (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1452 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 2 (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1453 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 3 (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1454 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1451)) (literal (valuationOf q) (1455)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 4 (meaning1451 q) (meaning1455 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1455 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1441)) (literal (valuationOf q) (1452)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 1 (meaning1441 q) (meaning1452 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1452 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1453)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 1 1 (meaning1441 q) (meaning1448 q) (meaning1453 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1448 = false ∨ valuation q 1453 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1454)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 1 2 (meaning1441 q) (meaning1449 q) (meaning1454 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1449 = false ∨ valuation q 1454 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1455)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 1 3 (meaning1441 q) (meaning1450 q) (meaning1455 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1450 = false ∨ valuation q 1455 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1456)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 1 4 (meaning1441 q) (meaning1451 q) (meaning1456 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1451 = false ∨ valuation q 1456 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1442)) (literal (valuationOf q) (1453)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 2 (meaning1442 q) (meaning1453 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1453 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1454)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 2 1 (meaning1442 q) (meaning1448 q) (meaning1454 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1448 = false ∨ valuation q 1454 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1455)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 2 2 (meaning1442 q) (meaning1449 q) (meaning1455 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1449 = false ∨ valuation q 1455 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1456)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 2 3 (meaning1442 q) (meaning1450 q) (meaning1456 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1450 = false ∨ valuation q 1456 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1457)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 2 4 (meaning1442 q) (meaning1451 q) (meaning1457 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1451 = false ∨ valuation q 1457 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1443)) (literal (valuationOf q) (1454)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 3 (meaning1443 q) (meaning1454 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1454 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1455)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 3 1 (meaning1443 q) (meaning1448 q) (meaning1455 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1448 = false ∨ valuation q 1455 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1456)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 3 2 (meaning1443 q) (meaning1449 q) (meaning1456 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1449 = false ∨ valuation q 1456 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1457)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 3 3 (meaning1443 q) (meaning1450 q) (meaning1457 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1450 = false ∨ valuation q 1457 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1458 = true := by
  have hs : count1452 q = (countLit q [-44, -48, -49]) + (countLit q [-52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -49]) (l₂ := [-52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1458)) (countLit q [-44, -48, -49]) (countLit q [-52, -54, -56, -57]) (count1452 q) 3 4 (meaning1443 q) (meaning1451 q) (meaning1458 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1451 = false ∨ valuation q 1458 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E171.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112171
