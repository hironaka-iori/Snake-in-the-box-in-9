import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1647)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 2 1 (meaning1635 q) (meaning1641 q) (meaning1647 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1641 = false ∨ valuation q 1647 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1648)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 2 2 (meaning1635 q) (meaning1642 q) (meaning1648 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1642 = false ∨ valuation q 1648 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1649)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 2 3 (meaning1635 q) (meaning1643 q) (meaning1649 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1647)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 3 (meaning1636 q) (meaning1647 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1647 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1648 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1648)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 3 1 (meaning1636 q) (meaning1641 q) (meaning1648 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1641 = false ∨ valuation q 1648 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1649)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 3 2 (meaning1636 q) (meaning1642 q) (meaning1649 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1642 = false ∨ valuation q 1649 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true := by
  have hs : count1645 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -97, -98, -101]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -97, -98, -101])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1650)) (countLit q [-90, -92, -93]) (countLit q [-95, -97, -98, -101]) (count1645 q) 3 3 (meaning1636 q) (meaning1643 q) (meaning1650 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1652)) (countLit q [-104]) (countLit q [-107]) (count1652 q) 1 (meaningNeg107 q) (meaning1652 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1652 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1652)) (countLit q [-104]) (countLit q [-107]) (count1652 q) 1 (meaningNeg104 q) (meaning1652 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1652 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1653)) (countLit q [-104]) (countLit q [-107]) (count1652 q) 1 1 (meaningNeg104 q) (meaningNeg107 q) (meaning1653 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 107 = true ∨ valuation q 1653 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1654)) (countLit q [-108]) (countLit q [-109]) (count1654 q) 1 (meaningNeg109 q) (meaning1654 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1654 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-108)) (literal (valuationOf q) (1654)) (countLit q [-108]) (countLit q [-109]) (count1654 q) 1 (meaningNeg108 q) (meaning1654 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1654 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 109 = true ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_two (literal (valuationOf q) (-108)) (literal (valuationOf q) (-109)) (literal (valuationOf q) (1655)) (countLit q [-108]) (countLit q [-109]) (count1654 q) 1 1 (meaningNeg108 q) (meaningNeg109 q) (meaning1655 q) hs
  change (! (valuationOf q 108)) = false ∨ (! (valuationOf q 109)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 1655 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1656 = true := by
  have hs : count1656 q = (countLit q [-104, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-108, -109])
  have hm := merge_right (literal (valuationOf q) (1654)) (literal (valuationOf q) (1656)) (countLit q [-104, -107]) (countLit q [-108, -109]) (count1656 q) 1 (meaning1654 q) (meaning1656 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1656 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1657 = true := by
  have hs : count1656 q = (countLit q [-104, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-108, -109])
  have hm := merge_right (literal (valuationOf q) (1655)) (literal (valuationOf q) (1657)) (countLit q [-104, -107]) (countLit q [-108, -109]) (count1656 q) 2 (meaning1655 q) (meaning1657 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1657 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1656 = true := by
  have hs : count1656 q = (countLit q [-104, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-108, -109])
  have hm := merge_left (literal (valuationOf q) (1652)) (literal (valuationOf q) (1656)) (countLit q [-104, -107]) (countLit q [-108, -109]) (count1656 q) 1 (meaning1652 q) (meaning1656 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1656 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1657 = true := by
  have hs : count1656 q = (countLit q [-104, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-108, -109])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1657)) (countLit q [-104, -107]) (countLit q [-108, -109]) (count1656 q) 1 1 (meaning1652 q) (meaning1654 q) (meaning1657 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1654 = false ∨ valuation q 1657 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1658 = true := by
  have hs : count1656 q = (countLit q [-104, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-108, -109])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1658)) (countLit q [-104, -107]) (countLit q [-108, -109]) (count1656 q) 1 2 (meaning1652 q) (meaning1655 q) (meaning1658 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1655 = false ∨ valuation q 1658 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1656 q = (countLit q [-104, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-108, -109])
  have hm := merge_left (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-104, -107]) (countLit q [-108, -109]) (count1656 q) 2 (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1657 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1656 q = (countLit q [-104, -107]) + (countLit q [-108, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-108, -109])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-104, -107]) (countLit q [-108, -109]) (count1656 q) 2 1 (meaning1653 q) (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1654 = false ∨ valuation q 1658 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1660 = true := by
  have hs : count1660 q = (countLit q [-111]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1660)) (countLit q [-111]) (countLit q [-114]) (count1660 q) 1 (meaningNeg114 q) (meaning1660 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1660 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1660 = true := by
  have hs : count1660 q = (countLit q [-111]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1660)) (countLit q [-111]) (countLit q [-114]) (count1660 q) 1 (meaningNeg111 q) (meaning1660 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1660 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1661 = true := by
  have hs : count1660 q = (countLit q [-111]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1661)) (countLit q [-111]) (countLit q [-114]) (count1660 q) 1 1 (meaningNeg111 q) (meaningNeg114 q) (meaning1661 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 114 = true ∨ valuation q 1661 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1662 = true := by
  have hs : count1662 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1662)) (countLit q [-115]) (countLit q [-117]) (count1662 q) 1 (meaningNeg117 q) (meaning1662 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1662 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1662 = true := by
  have hs : count1662 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1662)) (countLit q [-115]) (countLit q [-117]) (count1662 q) 1 (meaningNeg115 q) (meaning1662 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1662 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1663 = true := by
  have hs : count1662 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1663)) (countLit q [-115]) (countLit q [-117]) (count1662 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1663 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1663 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1664 = true := by
  have hs : count1664 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1662)) (literal (valuationOf q) (1664)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1664 q) 1 (meaning1662 q) (meaning1664 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1664 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1663)) (literal (valuationOf q) (1665)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1664 q) 2 (meaning1663 q) (meaning1665 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1665 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1664 = true := by
  have hs : count1664 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1660)) (literal (valuationOf q) (1664)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1664 q) 1 (meaning1660 q) (meaning1664 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1664 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1665)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1664 q) 1 1 (meaning1660 q) (meaning1662 q) (meaning1665 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1662 = false ∨ valuation q 1665 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1666 = true := by
  have hs : count1664 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1666)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1664 q) 1 2 (meaning1660 q) (meaning1663 q) (meaning1666 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1663 = false ∨ valuation q 1666 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1661)) (literal (valuationOf q) (1665)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1664 q) 2 (meaning1661 q) (meaning1665 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1665 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E187.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112187
