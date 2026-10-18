import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1496)) (countLit q [-91]) (countLit q [-92, -96]) (count1496 q) 1 (meaningNeg91 q) (meaning1496 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1496 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1497)) (countLit q [-91]) (countLit q [-92, -96]) (count1496 q) 1 1 (meaningNeg91 q) (meaning1494 q) (meaning1497 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1494 = false ∨ valuation q 1497 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1498)) (countLit q [-91]) (countLit q [-92, -96]) (count1496 q) 1 2 (meaningNeg91 q) (meaning1495 q) (meaning1498 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1495 = false ∨ valuation q 1498 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_right (literal (valuationOf q) (1496)) (literal (valuationOf q) (1499)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 1 (meaning1496 q) (meaning1499 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1499 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_right (literal (valuationOf q) (1497)) (literal (valuationOf q) (1500)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 2 (meaning1497 q) (meaning1500 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1500 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_left (literal (valuationOf q) (1491)) (literal (valuationOf q) (1499)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 1 (meaning1491 q) (meaning1499 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1499 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1500)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 1 1 (meaning1491 q) (meaning1496 q) (meaning1500 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1496 = false ∨ valuation q 1500 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1501)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 1 2 (meaning1491 q) (meaning1497 q) (meaning1501 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1497 = false ∨ valuation q 1501 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1502 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1502)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 1 3 (meaning1491 q) (meaning1498 q) (meaning1502 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1498 = false ∨ valuation q 1502 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1500)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 2 (meaning1492 q) (meaning1500 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1500 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1501)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 2 1 (meaning1492 q) (meaning1496 q) (meaning1501 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = false ∨ valuation q 1501 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1502 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1502)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 2 2 (meaning1492 q) (meaning1497 q) (meaning1502 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1497 = false ∨ valuation q 1502 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_left (literal (valuationOf q) (1493)) (literal (valuationOf q) (1501)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 3 (meaning1493 q) (meaning1501 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1501 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1502 = true := by
  have hs : count1499 q = (countLit q [-84, -88, -90]) + (countLit q [-91, -92, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90]) (l₂ := [-91, -92, -96])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1502)) (countLit q [-84, -88, -90]) (countLit q [-91, -92, -96]) (count1499 q) 3 1 (meaning1493 q) (meaning1496 q) (meaning1502 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1496 = false ∨ valuation q 1502 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1505)) (countLit q [-99]) (countLit q [-101]) (count1505 q) 1 (meaningNeg101 q) (meaning1505 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1505 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1505)) (countLit q [-99]) (countLit q [-101]) (count1505 q) 1 (meaningNeg99 q) (meaning1505 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1505 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1506)) (countLit q [-99]) (countLit q [-101]) (count1505 q) 1 1 (meaningNeg99 q) (meaningNeg101 q) (meaning1506 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 101 = true ∨ valuation q 1506 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-98]) (countLit q [-99, -101]) (count1507 q) 1 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (countLit q [-98]) (countLit q [-99, -101]) (count1507 q) 2 (meaning1506 q) (meaning1508 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1507)) (countLit q [-98]) (countLit q [-99, -101]) (count1507 q) 1 (meaningNeg98 q) (meaning1507 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1507 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-98]) (countLit q [-99, -101]) (count1507 q) 1 1 (meaningNeg98 q) (meaning1505 q) (meaning1508 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (countLit q [-98]) (countLit q [-99, -101]) (count1507 q) 1 2 (meaningNeg98 q) (meaning1506 q) (meaning1509 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1506 = false ∨ valuation q 1509 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1510)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 (meaningNeg106 q) (meaning1510 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1510 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1510)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 (meaningNeg104 q) (meaning1510 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1510 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 106 = true ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-106)) (literal (valuationOf q) (1511)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 1 (meaningNeg104 q) (meaningNeg106 q) (meaning1511 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 106)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 1511 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1512)) (countLit q [-107]) (countLit q [-109]) (count1512 q) 1 (meaningNeg107 q) (meaning1512 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1512 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 109 = true ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-109)) (literal (valuationOf q) (1513)) (countLit q [-107]) (countLit q [-109]) (count1512 q) 1 1 (meaningNeg107 q) (meaningNeg109 q) (meaning1513 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 109)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 109 = true ∨ valuation q 1513 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-104, -106]) (countLit q [-107, -109]) (count1514 q) 1 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1515)) (countLit q [-104, -106]) (countLit q [-107, -109]) (count1514 q) 2 (meaning1513 q) (meaning1515 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1515 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-104, -106]) (countLit q [-107, -109]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1515)) (countLit q [-104, -106]) (countLit q [-107, -109]) (count1514 q) 1 1 (meaning1510 q) (meaning1512 q) (meaning1515 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1512 = false ∨ valuation q 1515 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1516)) (countLit q [-104, -106]) (countLit q [-107, -109]) (count1514 q) 1 2 (meaning1510 q) (meaning1513 q) (meaning1516 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1513 = false ∨ valuation q 1516 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E183.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112183
