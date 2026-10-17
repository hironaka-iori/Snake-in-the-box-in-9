import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-56, -59, -60]) + (countLit q [-64, -65, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-64, -65, -67, -69])
  have hm := merge_right (literal (valuationOf q) (1490)) (literal (valuationOf q) (1494)) (countLit q [-56, -59, -60]) (countLit q [-64, -65, -67, -69]) (count1494 q) 1 (meaning1490 q) (meaning1494 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1494 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-56, -59, -60]) + (countLit q [-64, -65, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-64, -65, -67, -69])
  have hm := merge_right (literal (valuationOf q) (1491)) (literal (valuationOf q) (1495)) (countLit q [-56, -59, -60]) (countLit q [-64, -65, -67, -69]) (count1494 q) 2 (meaning1491 q) (meaning1495 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1495 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-56, -59, -60]) + (countLit q [-64, -65, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-64, -65, -67, -69])
  have hm := merge_left (literal (valuationOf q) (1483)) (literal (valuationOf q) (1494)) (countLit q [-56, -59, -60]) (countLit q [-64, -65, -67, -69]) (count1494 q) 1 (meaning1483 q) (meaning1494 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1494 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-56, -59, -60]) + (countLit q [-64, -65, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-64, -65, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1495)) (countLit q [-56, -59, -60]) (countLit q [-64, -65, -67, -69]) (count1494 q) 1 1 (meaning1483 q) (meaning1490 q) (meaning1495 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1490 = false ∨ valuation q 1495 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-56, -59, -60]) + (countLit q [-64, -65, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-64, -65, -67, -69])
  have hm := merge_left (literal (valuationOf q) (1484)) (literal (valuationOf q) (1495)) (countLit q [-56, -59, -60]) (countLit q [-64, -65, -67, -69]) (count1494 q) 2 (meaning1484 q) (meaning1495 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1495 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1496 = true := by
  have hs : count1494 q = (countLit q [-56, -59, -60]) + (countLit q [-64, -65, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-64, -65, -67, -69])
  have hm := merge_two (literal (valuationOf q) (1484)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1496)) (countLit q [-56, -59, -60]) (countLit q [-64, -65, -67, -69]) (count1494 q) 2 1 (meaning1484 q) (meaning1490 q) (meaning1496 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1490 = false ∨ valuation q 1496 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1496 = true := by
  have hs : count1494 q = (countLit q [-56, -59, -60]) + (countLit q [-64, -65, -67, -69]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60]) (l₂ := [-64, -65, -67, -69])
  have hm := merge_left (literal (valuationOf q) (1485)) (literal (valuationOf q) (1496)) (countLit q [-56, -59, -60]) (countLit q [-64, -65, -67, -69]) (count1494 q) 3 (meaning1485 q) (meaning1496 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1496 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1501)) (countLit q [-72]) (countLit q [-74]) (count1501 q) 1 (meaningNeg74 q) (meaning1501 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1501 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1501)) (countLit q [-72]) (countLit q [-74]) (count1501 q) 1 (meaningNeg72 q) (meaning1501 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1501 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1502)) (countLit q [-72]) (countLit q [-74]) (count1501 q) 1 1 (meaningNeg72 q) (meaningNeg74 q) (meaning1502 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 74 = true ∨ valuation q 1502 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1503)) (countLit q [-76]) (countLit q [-77]) (count1503 q) 1 (meaningNeg77 q) (meaning1503 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1503 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1503)) (countLit q [-76]) (countLit q [-77]) (count1503 q) 1 (meaningNeg76 q) (meaning1503 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1503 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1504)) (countLit q [-76]) (countLit q [-77]) (count1503 q) 1 1 (meaningNeg76 q) (meaningNeg77 q) (meaning1504 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 77 = true ∨ valuation q 1504 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-72, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1503)) (literal (valuationOf q) (1505)) (countLit q [-72, -74]) (countLit q [-76, -77]) (count1505 q) 1 (meaning1503 q) (meaning1505 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1505 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-72, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (countLit q [-72, -74]) (countLit q [-76, -77]) (count1505 q) 2 (meaning1504 q) (meaning1506 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-72, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1505)) (countLit q [-72, -74]) (countLit q [-76, -77]) (count1505 q) 1 (meaning1501 q) (meaning1505 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1505 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-72, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1506)) (countLit q [-72, -74]) (countLit q [-76, -77]) (count1505 q) 1 1 (meaning1501 q) (meaning1503 q) (meaning1506 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1503 = false ∨ valuation q 1506 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true := by
  have hs : count1505 q = (countLit q [-72, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1507)) (countLit q [-72, -74]) (countLit q [-76, -77]) (count1505 q) 1 2 (meaning1501 q) (meaning1504 q) (meaning1507 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1504 = false ∨ valuation q 1507 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-72, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1506)) (countLit q [-72, -74]) (countLit q [-76, -77]) (count1505 q) 2 (meaning1502 q) (meaning1506 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1506 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1507 = true := by
  have hs : count1505 q = (countLit q [-72, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1507)) (countLit q [-72, -74]) (countLit q [-76, -77]) (count1505 q) 2 1 (meaning1502 q) (meaning1503 q) (meaning1507 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1503 = false ∨ valuation q 1507 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1509 = true := by
  have hs : count1509 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1509)) (countLit q [-80]) (countLit q [-81]) (count1509 q) 1 (meaningNeg81 q) (meaning1509 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1509 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1509 = true := by
  have hs : count1509 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1509)) (countLit q [-80]) (countLit q [-81]) (count1509 q) 1 (meaningNeg80 q) (meaning1509 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1509 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1510 = true := by
  have hs : count1509 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1510)) (countLit q [-80]) (countLit q [-81]) (count1509 q) 1 1 (meaningNeg80 q) (meaningNeg81 q) (meaning1510 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 1510 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1511 = true := by
  have hs : count1511 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1511)) (countLit q [-83]) (countLit q [-84]) (count1511 q) 1 (meaningNeg84 q) (meaning1511 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1511 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1511 = true := by
  have hs : count1511 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1511)) (countLit q [-83]) (countLit q [-84]) (count1511 q) 1 (meaningNeg83 q) (meaning1511 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1511 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1512 = true := by
  have hs : count1511 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1512)) (countLit q [-83]) (countLit q [-84]) (count1511 q) 1 1 (meaningNeg83 q) (meaningNeg84 q) (meaning1512 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 1512 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-80, -81]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-83, -84])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1513)) (countLit q [-80, -81]) (countLit q [-83, -84]) (count1513 q) 1 (meaning1511 q) (meaning1513 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1513 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-80, -81]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-83, -84])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-80, -81]) (countLit q [-83, -84]) (count1513 q) 2 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-80, -81]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-83, -84])
  have hm := merge_left (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-80, -81]) (countLit q [-83, -84]) (count1513 q) 1 (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1513 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-80, -81]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-83, -84])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1514)) (countLit q [-80, -81]) (countLit q [-83, -84]) (count1513 q) 1 1 (meaning1509 q) (meaning1511 q) (meaning1514 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1511 = false ∨ valuation q 1514 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-80, -81]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-83, -84])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-80, -81]) (countLit q [-83, -84]) (count1513 q) 2 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-72, -74, -76, -77]) + (countLit q [-80, -81, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -77]) (l₂ := [-80, -81, -83, -84])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1517)) (countLit q [-72, -74, -76, -77]) (countLit q [-80, -81, -83, -84]) (count1517 q) 1 (meaning1513 q) (meaning1517 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1517 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E146.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112146
