import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec62 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1985 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-83, -84]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1718)) (countLit q [-83, -84]) (countLit q [-87, -88]) (count1717 q) 1 1 (meaning1713 q) (meaning1715 q) (meaning1718 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1985 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1715 = false ∨ valuation q 1718 = true := counterClause1985 (baseVal q)

theorem counterClause1986 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1721)) (countLit q [-91]) (countLit q [-92]) (count1721 q) 1 (meaningNeg92 q) (meaning1721 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1986 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1721 = true := counterClause1986 (baseVal q)

theorem counterClause1987 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1724)) (countLit q [-93]) (countLit q [-94]) (count1723 q) 1 1 (meaningNeg93 q) (meaningNeg94 q) (meaning1724 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1987 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 1724 = true := counterClause1987 (baseVal q)

theorem counterClause1988 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-91, -92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-91, -92]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1724)) (literal (valuationOf q) (1726)) (countLit q [-91, -92]) (countLit q [-93, -94]) (count1725 q) 2 (meaning1724 q) (meaning1726 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1988 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1726 = true := counterClause1988 (baseVal q)

theorem counterClause1989 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1725 = true := by
  have hs : count1725 q = (countLit q [-91, -92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-91, -92]) (l₂ := [-93, -94])
  have hm := merge_left (literal (valuationOf q) (1721)) (literal (valuationOf q) (1725)) (countLit q [-91, -92]) (countLit q [-93, -94]) (count1725 q) 1 (meaning1721 q) (meaning1725 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1989 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1725 = true := counterClause1989 (baseVal q)

theorem counterClause1990 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-91, -92]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-91, -92]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (1721)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1727)) (countLit q [-91, -92]) (countLit q [-93, -94]) (count1725 q) 1 2 (meaning1721 q) (meaning1724 q) (meaning1727 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1990 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1724 = false ∨ valuation q 1727 = true := counterClause1990 (baseVal q)

theorem counterClause1991 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1731 = true := by
  have hs : count1729 q = (countLit q [-83, -84, -87, -88]) + (countLit q [-91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -84, -87, -88]) (l₂ := [-91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1731)) (countLit q [-83, -84, -87, -88]) (countLit q [-91, -92, -93, -94]) (count1729 q) 1 2 (meaning1717 q) (meaning1726 q) (meaning1731 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1991 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1726 = false ∨ valuation q 1731 = true := counterClause1991 (baseVal q)

theorem counterClause1992 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1732 = true := by
  have hs : count1729 q = (countLit q [-83, -84, -87, -88]) + (countLit q [-91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -84, -87, -88]) (l₂ := [-91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1727)) (literal (valuationOf q) (1732)) (countLit q [-83, -84, -87, -88]) (countLit q [-91, -92, -93, -94]) (count1729 q) 1 3 (meaning1717 q) (meaning1727 q) (meaning1732 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1992 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1727 = false ∨ valuation q 1732 = true := counterClause1992 (baseVal q)

theorem counterClause1993 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1731 = true := by
  have hs : count1729 q = (countLit q [-83, -84, -87, -88]) + (countLit q [-91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -84, -87, -88]) (l₂ := [-91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1718)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1731)) (countLit q [-83, -84, -87, -88]) (countLit q [-91, -92, -93, -94]) (count1729 q) 2 1 (meaning1718 q) (meaning1725 q) (meaning1731 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1993 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1725 = false ∨ valuation q 1731 = true := counterClause1993 (baseVal q)

theorem counterClause1994 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1732 = true := by
  have hs : count1729 q = (countLit q [-83, -84, -87, -88]) + (countLit q [-91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -84, -87, -88]) (l₂ := [-91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1718)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1732)) (countLit q [-83, -84, -87, -88]) (countLit q [-91, -92, -93, -94]) (count1729 q) 2 2 (meaning1718 q) (meaning1726 q) (meaning1732 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1994 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1726 = false ∨ valuation q 1732 = true := counterClause1994 (baseVal q)

theorem counterClause1995 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1741 = true := by
  have hs : count1737 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) + (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80]) (l₂ := [-83, -84, -87, -88, -91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1741)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) (count1737 q) 2 3 (meaning1706 q) (meaning1731 q) (meaning1741 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1995 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1731 = false ∨ valuation q 1741 = true := counterClause1995 (baseVal q)

theorem counterClause1996 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1742 = true := by
  have hs : count1737 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) + (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80]) (l₂ := [-83, -84, -87, -88, -91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1742)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) (count1737 q) 3 3 (meaning1707 q) (meaning1731 q) (meaning1742 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1742 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1996 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1731 = false ∨ valuation q 1742 = true := counterClause1996 (baseVal q)

theorem counterClause1997 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1744 = true := by
  have hs : count1737 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) + (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80]) (l₂ := [-83, -84, -87, -88, -91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1744)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) (count1737 q) 4 4 (meaning1708 q) (meaning1732 q) (meaning1744 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1997 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1732 = false ∨ valuation q 1744 = true := counterClause1997 (baseVal q)

theorem counterClause1998 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1744 = true := by
  have hs : count1737 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) + (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80]) (l₂ := [-83, -84, -87, -88, -91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1709)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1744)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) (count1737 q) 5 3 (meaning1709 q) (meaning1731 q) (meaning1744 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1998 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1731 = false ∨ valuation q 1744 = true := counterClause1998 (baseVal q)

theorem counterClause1999 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1745 = true := by
  have hs : count1737 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) + (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80]) (l₂ := [-83, -84, -87, -88, -91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1709)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1745)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) (count1737 q) 5 4 (meaning1709 q) (meaning1732 q) (meaning1745 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1999 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1732 = false ∨ valuation q 1745 = true := counterClause1999 (baseVal q)

theorem counterClause2000 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1745 = true := by
  have hs : count1737 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) + (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80]) (l₂ := [-83, -84, -87, -88, -91, -92, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1745)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80]) (countLit q [-83, -84, -87, -88, -91, -92, -93, -94]) (count1737 q) 6 3 (meaning1710 q) (meaning1731 q) (meaning1745 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2000 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1731 = false ∨ valuation q 1745 = true := counterClause2000 (baseVal q)

theorem counterClause2001 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1753 = true := by
  have hs : count1753 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1753)) (countLit q [-95]) (countLit q [-97]) (count1753 q) 1 (meaningNeg97 q) (meaning1753 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2001 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1753 = true := counterClause2001 (baseVal q)

theorem counterClause2002 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1753 = true := by
  have hs : count1753 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1753)) (countLit q [-95]) (countLit q [-97]) (count1753 q) 1 (meaningNeg95 q) (meaning1753 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2002 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1753 = true := counterClause2002 (baseVal q)

theorem counterClause2003 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1754 = true := by
  have hs : count1753 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1754)) (countLit q [-95]) (countLit q [-97]) (count1753 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning1754 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2003 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 1754 = true := counterClause2003 (baseVal q)

theorem counterClause2004 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1757 = true := by
  have hs : count1757 q = (countLit q [-95, -97]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (1753)) (literal (valuationOf q) (1757)) (countLit q [-95, -97]) (countLit q [-99, -101]) (count1757 q) 1 (meaning1753 q) (meaning1757 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2004 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1757 = true := counterClause2004 (baseVal q)

theorem counterClause2005 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1758 = true := by
  have hs : count1757 q = (countLit q [-95, -97]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -97]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (1754)) (literal (valuationOf q) (1758)) (countLit q [-95, -97]) (countLit q [-99, -101]) (count1757 q) 2 (meaning1754 q) (meaning1758 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2005 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1758 = true := counterClause2005 (baseVal q)

theorem counterClause2006 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1761 = true := by
  have hs : count1761 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1761)) (countLit q [-102]) (countLit q [-104]) (count1761 q) 1 (meaningNeg104 q) (meaning1761 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2006 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1761 = true := counterClause2006 (baseVal q)

theorem counterClause2007 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1761 = true := by
  have hs : count1761 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1761)) (countLit q [-102]) (countLit q [-104]) (count1761 q) 1 (meaningNeg102 q) (meaning1761 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2007 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1761 = true := counterClause2007 (baseVal q)

theorem counterClause2008 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1762 = true := by
  have hs : count1761 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1762)) (countLit q [-102]) (countLit q [-104]) (count1761 q) 1 1 (meaningNeg102 q) (meaningNeg104 q) (meaning1762 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2008 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 104 = true ∨ valuation q 1762 = true := counterClause2008 (baseVal q)

theorem counterClause2009 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1763 = true := by
  have hs : count1763 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1763)) (countLit q [-106]) (countLit q [-107]) (count1763 q) 1 (meaningNeg107 q) (meaning1763 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2009 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1763 = true := counterClause2009 (baseVal q)

theorem counterClause2010 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1763 = true := by
  have hs : count1763 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1763)) (countLit q [-106]) (countLit q [-107]) (count1763 q) 1 (meaningNeg106 q) (meaning1763 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2010 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1763 = true := counterClause2010 (baseVal q)

theorem counterClause2011 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1764 = true := by
  have hs : count1763 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1764)) (countLit q [-106]) (countLit q [-107]) (count1763 q) 1 1 (meaningNeg106 q) (meaningNeg107 q) (meaning1764 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause2011 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 107 = true ∨ valuation q 1764 = true := counterClause2011 (baseVal q)

theorem counterClause2012 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1765 = true := by
  have hs : count1765 q = (countLit q [-102, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1763)) (literal (valuationOf q) (1765)) (countLit q [-102, -104]) (countLit q [-106, -107]) (count1765 q) 1 (meaning1763 q) (meaning1765 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2012 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1765 = true := counterClause2012 (baseVal q)

theorem counterClause2013 (q : Nat → Bool) : valuationOf q 1764 = false ∨ valuationOf q 1766 = true := by
  have hs : count1765 q = (countLit q [-102, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1764)) (literal (valuationOf q) (1766)) (countLit q [-102, -104]) (countLit q [-106, -107]) (count1765 q) 2 (meaning1764 q) (meaning1766 q) hs
  change valuationOf q 1764 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2013 (q : Snake 81) (h : Conditions q) : valuation q 1764 = false ∨ valuation q 1766 = true := counterClause2013 (baseVal q)

theorem counterClause2014 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1766 = true := by
  have hs : count1765 q = (countLit q [-102, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1766)) (countLit q [-102, -104]) (countLit q [-106, -107]) (count1765 q) 1 1 (meaning1761 q) (meaning1763 q) (meaning1766 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2014 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1763 = false ∨ valuation q 1766 = true := counterClause2014 (baseVal q)

theorem counterClause2015 (q : Nat → Bool) : valuationOf q 1761 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1767 = true := by
  have hs : count1765 q = (countLit q [-102, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1761)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1767)) (countLit q [-102, -104]) (countLit q [-106, -107]) (count1765 q) 1 2 (meaning1761 q) (meaning1764 q) (meaning1767 q) hs
  change valuationOf q 1761 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2015 (q : Snake 81) (h : Conditions q) : valuation q 1761 = false ∨ valuation q 1764 = false ∨ valuation q 1767 = true := counterClause2015 (baseVal q)

theorem counterClause2016 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1767 = true := by
  have hs : count1765 q = (countLit q [-102, -104]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-102, -104]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1762)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1767)) (countLit q [-102, -104]) (countLit q [-106, -107]) (count1765 q) 2 1 (meaning1762 q) (meaning1763 q) (meaning1767 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2016 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1763 = false ∨ valuation q 1767 = true := counterClause2016 (baseVal q)

theorem block62 (q : Snake 81) (h : Conditions q) : B112E260.Block62 (valuation q) :=
  ⟨clause1985 q h, clause1986 q h, clause1987 q h, clause1988 q h, clause1989 q h, clause1990 q h, clause1991 q h, clause1992 q h, clause1993 q h, clause1994 q h, clause1995 q h, clause1996 q h, clause1997 q h, clause1998 q h, clause1999 q h, clause2000 q h, clause2001 q h, clause2002 q h, clause2003 q h, clause2004 q h, clause2005 q h, clause2006 q h, clause2007 q h, clause2008 q h, clause2009 q h, clause2010 q h, clause2011 q h, clause2012 q h, clause2013 q h, clause2014 q h, clause2015 q h, clause2016 q h⟩

end
end Snake9.Regrowth.E112260
