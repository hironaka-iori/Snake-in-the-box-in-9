import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1596)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 3 1 (meaning1584 q) (meaning1589 q) (meaning1596 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1589 = false ∨ valuation q 1596 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1597 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1597)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 3 2 (meaning1584 q) (meaning1590 q) (meaning1597 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1590 = false ∨ valuation q 1597 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1600)) (countLit q [-102]) (countLit q [-103]) (count1600 q) 1 (meaningNeg103 q) (meaning1600 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1600 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1600)) (countLit q [-102]) (countLit q [-103]) (count1600 q) 1 (meaningNeg102 q) (meaning1600 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1600 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1601)) (countLit q [-102]) (countLit q [-103]) (count1600 q) 1 1 (meaningNeg102 q) (meaningNeg103 q) (meaning1601 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 1601 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1602)) (countLit q [-104]) (countLit q [-106]) (count1602 q) 1 (meaningNeg106 q) (meaning1602 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1602 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1602)) (countLit q [-104]) (countLit q [-106]) (count1602 q) 1 (meaningNeg104 q) (meaning1602 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1602 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 106 = true ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-106)) (literal (valuationOf q) (1603)) (countLit q [-104]) (countLit q [-106]) (count1602 q) 1 1 (meaningNeg104 q) (meaningNeg106 q) (meaning1603 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 106)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 1603 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-102, -103]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -106])
  have hm := merge_right (literal (valuationOf q) (1602)) (literal (valuationOf q) (1604)) (countLit q [-102, -103]) (countLit q [-104, -106]) (count1604 q) 1 (meaning1602 q) (meaning1604 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1604 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-102, -103]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -106])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1605)) (countLit q [-102, -103]) (countLit q [-104, -106]) (count1604 q) 2 (meaning1603 q) (meaning1605 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1605 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-102, -103]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -106])
  have hm := merge_left (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-102, -103]) (countLit q [-104, -106]) (count1604 q) 1 (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1604 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-102, -103]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -106])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1605)) (countLit q [-102, -103]) (countLit q [-104, -106]) (count1604 q) 1 1 (meaning1600 q) (meaning1602 q) (meaning1605 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1602 = false ∨ valuation q 1605 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-102, -103]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -106])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1606)) (countLit q [-102, -103]) (countLit q [-104, -106]) (count1604 q) 1 2 (meaning1600 q) (meaning1603 q) (meaning1606 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1603 = false ∨ valuation q 1606 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-102, -103]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -106])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-102, -103]) (countLit q [-104, -106]) (count1604 q) 2 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-102, -103]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-102, -103]) (l₂ := [-104, -106])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1606)) (countLit q [-102, -103]) (countLit q [-104, -106]) (count1604 q) 2 1 (meaning1601 q) (meaning1602 q) (meaning1606 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1602 = false ∨ valuation q 1606 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-109]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1608)) (countLit q [-109]) (countLit q [-112]) (count1608 q) 1 (meaningNeg112 q) (meaning1608 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1608 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-109]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1608)) (countLit q [-109]) (countLit q [-112]) (count1608 q) 1 (meaningNeg109 q) (meaning1608 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1608 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-109]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-109)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1609)) (countLit q [-109]) (countLit q [-112]) (count1608 q) 1 1 (meaningNeg109 q) (meaningNeg112 q) (meaning1609 q) hs
  change (! (valuationOf q 109)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 112 = true ∨ valuation q 1609 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-113]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-115])
  have hm := merge_right (literal (valuationOf q) (-115)) (literal (valuationOf q) (1610)) (countLit q [-113]) (countLit q [-115]) (count1610 q) 1 (meaningNeg115 q) (meaning1610 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1610 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-113]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-115])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1610)) (countLit q [-113]) (countLit q [-115]) (count1610 q) 1 (meaningNeg113 q) (meaning1610 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1610 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 115 = true ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-113]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-115])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-115)) (literal (valuationOf q) (1611)) (countLit q [-113]) (countLit q [-115]) (count1610 q) 1 1 (meaningNeg113 q) (meaningNeg115 q) (meaning1611 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 115)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 115 = true ∨ valuation q 1611 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-109, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -115])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1612)) (countLit q [-109, -112]) (countLit q [-113, -115]) (count1612 q) 1 (meaning1610 q) (meaning1612 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-109, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -115])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (countLit q [-109, -112]) (countLit q [-113, -115]) (count1612 q) 2 (meaning1611 q) (meaning1613 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-109, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -115])
  have hm := merge_left (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-109, -112]) (countLit q [-113, -115]) (count1612 q) 1 (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-109, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1613)) (countLit q [-109, -112]) (countLit q [-113, -115]) (count1612 q) 1 1 (meaning1608 q) (meaning1610 q) (meaning1613 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = false ∨ valuation q 1613 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-109, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1614)) (countLit q [-109, -112]) (countLit q [-113, -115]) (count1612 q) 1 2 (meaning1608 q) (meaning1611 q) (meaning1614 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1611 = false ∨ valuation q 1614 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-109, -112]) + (countLit q [-113, -115]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -115])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1614)) (countLit q [-109, -112]) (countLit q [-113, -115]) (count1612 q) 2 1 (meaning1609 q) (meaning1610 q) (meaning1614 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1610 = false ∨ valuation q 1614 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_right (literal (valuationOf q) (1612)) (literal (valuationOf q) (1616)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 1 (meaning1612 q) (meaning1616 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1616 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_right (literal (valuationOf q) (1613)) (literal (valuationOf q) (1617)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 2 (meaning1613 q) (meaning1617 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1617 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_left (literal (valuationOf q) (1604)) (literal (valuationOf q) (1616)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 1 (meaning1604 q) (meaning1616 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1616 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1617)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 1 1 (meaning1604 q) (meaning1612 q) (meaning1617 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1612 = false ∨ valuation q 1617 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1618)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 1 2 (meaning1604 q) (meaning1613 q) (meaning1618 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1613 = false ∨ valuation q 1618 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E120.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112120
