import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1451 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_left (literal (valuationOf q) (1443)) (literal (valuationOf q) (1451)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 1 (meaning1443 q) (meaning1451 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1451 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 1 1 (meaning1443 q) (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1448 = false ∨ valuation q 1452 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 1 2 (meaning1443 q) (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1449 = false ∨ valuation q 1453 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 1 3 (meaning1443 q) (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1450 = false ∨ valuation q 1454 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1452 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_left (literal (valuationOf q) (1444)) (literal (valuationOf q) (1452)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 2 (meaning1444 q) (meaning1452 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1452 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1453)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 2 1 (meaning1444 q) (meaning1448 q) (meaning1453 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1448 = false ∨ valuation q 1453 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_left (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 3 (meaning1445 q) (meaning1453 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1453 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1454)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 3 1 (meaning1445 q) (meaning1448 q) (meaning1454 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1448 = false ∨ valuation q 1454 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1457)) (countLit q [-71]) (countLit q [-73]) (count1457 q) 1 (meaningNeg73 q) (meaning1457 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1457 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1457)) (countLit q [-71]) (countLit q [-73]) (count1457 q) 1 (meaningNeg71 q) (meaning1457 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1457 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1458)) (countLit q [-71]) (countLit q [-73]) (count1457 q) 1 1 (meaningNeg71 q) (meaningNeg73 q) (meaning1458 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 1458 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1457)) (literal (valuationOf q) (1459)) (countLit q [-69]) (countLit q [-71, -73]) (count1459 q) 1 (meaning1457 q) (meaning1459 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1459 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1458)) (literal (valuationOf q) (1460)) (countLit q [-69]) (countLit q [-71, -73]) (count1459 q) 2 (meaning1458 q) (meaning1460 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1460 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1459)) (countLit q [-69]) (countLit q [-71, -73]) (count1459 q) 1 (meaningNeg69 q) (meaning1459 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1459 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1460)) (countLit q [-69]) (countLit q [-71, -73]) (count1459 q) 1 1 (meaningNeg69 q) (meaning1457 q) (meaning1460 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1457 = false ∨ valuation q 1460 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1458 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-69]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1461)) (countLit q [-69]) (countLit q [-71, -73]) (count1459 q) 1 2 (meaningNeg69 q) (meaning1458 q) (meaning1461 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1458 = false ∨ valuation q 1461 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1462)) (countLit q [-76]) (countLit q [-79]) (count1462 q) 1 (meaningNeg79 q) (meaning1462 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1462 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1462)) (countLit q [-76]) (countLit q [-79]) (count1462 q) 1 (meaningNeg76 q) (meaning1462 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1462 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1463)) (countLit q [-76]) (countLit q [-79]) (count1462 q) 1 1 (meaningNeg76 q) (meaningNeg79 q) (meaning1463 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 79 = true ∨ valuation q 1463 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1464)) (countLit q [-81]) (countLit q [-83]) (count1464 q) 1 (meaningNeg83 q) (meaning1464 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1464 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1464)) (countLit q [-81]) (countLit q [-83]) (count1464 q) 1 (meaningNeg81 q) (meaning1464 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1464 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 83 = true ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-83)) (literal (valuationOf q) (1465)) (countLit q [-81]) (countLit q [-83]) (count1464 q) 1 1 (meaningNeg81 q) (meaningNeg83 q) (meaning1465 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 83)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 1465 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-76, -79]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -83])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-76, -79]) (countLit q [-81, -83]) (count1466 q) 1 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-76, -79]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -83])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1467)) (countLit q [-76, -79]) (countLit q [-81, -83]) (count1466 q) 2 (meaning1465 q) (meaning1467 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1467 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-76, -79]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -83])
  have hm := merge_left (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-76, -79]) (countLit q [-81, -83]) (count1466 q) 1 (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1466 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-76, -79]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -83])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-76, -79]) (countLit q [-81, -83]) (count1466 q) 1 1 (meaning1462 q) (meaning1464 q) (meaning1467 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-76, -79]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -83])
  have hm := merge_left (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-76, -79]) (countLit q [-81, -83]) (count1466 q) 2 (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1467 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -79, -81, -83])
  have hm := merge_right (literal (valuationOf q) (1466)) (literal (valuationOf q) (1470)) (countLit q [-69, -71, -73]) (countLit q [-76, -79, -81, -83]) (count1470 q) 1 (meaning1466 q) (meaning1470 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1470 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -79, -81, -83])
  have hm := merge_right (literal (valuationOf q) (1467)) (literal (valuationOf q) (1471)) (countLit q [-69, -71, -73]) (countLit q [-76, -79, -81, -83]) (count1470 q) 2 (meaning1467 q) (meaning1471 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1471 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -79, -81, -83])
  have hm := merge_left (literal (valuationOf q) (1459)) (literal (valuationOf q) (1470)) (countLit q [-69, -71, -73]) (countLit q [-76, -79, -81, -83]) (count1470 q) 1 (meaning1459 q) (meaning1470 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1470 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1471)) (countLit q [-69, -71, -73]) (countLit q [-76, -79, -81, -83]) (count1470 q) 1 1 (meaning1459 q) (meaning1466 q) (meaning1471 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1466 = false ∨ valuation q 1471 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1472)) (countLit q [-69, -71, -73]) (countLit q [-76, -79, -81, -83]) (count1470 q) 1 2 (meaning1459 q) (meaning1467 q) (meaning1472 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1467 = false ∨ valuation q 1472 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E183.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112183
