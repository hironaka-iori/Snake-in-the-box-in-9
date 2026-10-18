import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec60 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1921 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1716 = true := by
  have hs : count1713 q = (countLit q [-63, -66, -68, -70]) + (countLit q [-71, -74, -76, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -70]) (l₂ := [-71, -74, -76, -78])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1716)) (countLit q [-63, -66, -68, -70]) (countLit q [-71, -74, -76, -78]) (count1713 q) 2 2 (meaning1702 q) (meaning1710 q) (meaning1716 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1921 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1710 = false ∨ valuation q 1716 = true := counterClause1921 (baseVal q)

theorem counterClause1922 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1721)) (countLit q [-80]) (countLit q [-81]) (count1721 q) 1 (meaningNeg80 q) (meaning1721 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1922 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1721 = true := counterClause1922 (baseVal q)

theorem counterClause1923 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1722)) (countLit q [-80]) (countLit q [-81]) (count1721 q) 1 1 (meaningNeg80 q) (meaningNeg81 q) (meaning1722 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1923 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 1722 = true := counterClause1923 (baseVal q)

theorem counterClause1924 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1723)) (countLit q [-84]) (countLit q [-85]) (count1723 q) 1 (meaningNeg84 q) (meaning1723 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1924 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1723 = true := counterClause1924 (baseVal q)

theorem counterClause1925 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1724)) (countLit q [-84]) (countLit q [-85]) (count1723 q) 1 1 (meaningNeg84 q) (meaningNeg85 q) (meaning1724 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1925 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 85 = true ∨ valuation q 1724 = true := counterClause1925 (baseVal q)

theorem counterClause1926 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-80, -81]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-84, -85])
  have hm := merge_two (literal (valuationOf q) (1721)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1727)) (countLit q [-80, -81]) (countLit q [-84, -85]) (count1725 q) 1 2 (meaning1721 q) (meaning1724 q) (meaning1727 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1926 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1724 = false ∨ valuation q 1727 = true := counterClause1926 (baseVal q)

theorem counterClause1927 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-80, -81]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-84, -85])
  have hm := merge_two (literal (valuationOf q) (1722)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1727)) (countLit q [-80, -81]) (countLit q [-84, -85]) (count1725 q) 2 1 (meaning1722 q) (meaning1723 q) (meaning1727 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1927 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1723 = false ∨ valuation q 1727 = true := counterClause1927 (baseVal q)

theorem counterClause1928 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1730 = true := by
  have hs : count1729 q = (countLit q [-88]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1730)) (countLit q [-88]) (countLit q [-92]) (count1729 q) 1 1 (meaningNeg88 q) (meaningNeg92 q) (meaning1730 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1928 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 92 = true ∨ valuation q 1730 = true := counterClause1928 (baseVal q)

theorem counterClause1929 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1734 = true := by
  have hs : count1733 q = (countLit q [-88, -92]) + (countLit q [-93, -98]) := List.countP_append (p := literal q) (l₁ := [-88, -92]) (l₂ := [-93, -98])
  have hm := merge_left (literal (valuationOf q) (1730)) (literal (valuationOf q) (1734)) (countLit q [-88, -92]) (countLit q [-93, -98]) (count1733 q) 2 (meaning1730 q) (meaning1734 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1929 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1734 = true := counterClause1929 (baseVal q)

theorem counterClause1930 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1741 = true := by
  have hs : count1737 q = (countLit q [-80, -81, -84, -85]) + (countLit q [-88, -92, -93, -98]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -84, -85]) (l₂ := [-88, -92, -93, -98])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1741)) (countLit q [-80, -81, -84, -85]) (countLit q [-88, -92, -93, -98]) (count1737 q) 3 2 (meaning1727 q) (meaning1734 q) (meaning1741 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1930 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1734 = false ∨ valuation q 1741 = true := counterClause1930 (baseVal q)

theorem counterClause1931 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-63, -66, -68, -70, -71, -74, -76, -78]) + (countLit q [-80, -81, -84, -85, -88, -92, -93, -98]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -70, -71, -74, -76, -78]) (l₂ := [-80, -81, -84, -85, -88, -92, -93, -98])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1752)) (countLit q [-63, -66, -68, -70, -71, -74, -76, -78]) (countLit q [-80, -81, -84, -85, -88, -92, -93, -98]) (count1745 q) 3 5 (meaning1715 q) (meaning1741 q) (meaning1752 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1931 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1741 = false ∨ valuation q 1752 = true := counterClause1931 (baseVal q)

theorem counterClause1932 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-63, -66, -68, -70, -71, -74, -76, -78]) + (countLit q [-80, -81, -84, -85, -88, -92, -93, -98]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -70, -71, -74, -76, -78]) (l₂ := [-80, -81, -84, -85, -88, -92, -93, -98])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1753)) (countLit q [-63, -66, -68, -70, -71, -74, -76, -78]) (countLit q [-80, -81, -84, -85, -88, -92, -93, -98]) (count1745 q) 4 5 (meaning1716 q) (meaning1741 q) (meaning1753 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1932 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1741 = false ∨ valuation q 1753 = true := counterClause1932 (baseVal q)

theorem counterClause1933 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1763 = true := by
  have hs : count1763 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1763)) (countLit q [-102]) (countLit q [-104]) (count1763 q) 1 (meaningNeg102 q) (meaning1763 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1933 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1763 = true := counterClause1933 (baseVal q)

theorem counterClause1934 (q : Nat → Bool) : valuationOf q 1763 = false ∨ valuationOf q 1765 = true := by
  have hs : count1765 q = (countLit q [-99, -100]) + (countLit q [-102, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-102, -104])
  have hm := merge_right (literal (valuationOf q) (1763)) (literal (valuationOf q) (1765)) (countLit q [-99, -100]) (countLit q [-102, -104]) (count1765 q) 1 (meaning1763 q) (meaning1765 q) hs
  change valuationOf q 1763 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1934 (q : Snake 81) (h : Conditions q) : valuation q 1763 = false ∨ valuation q 1765 = true := counterClause1934 (baseVal q)

theorem counterClause1935 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1769 = true := by
  have hs : count1769 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1769)) (countLit q [-106]) (countLit q [-108]) (count1769 q) 1 (meaningNeg106 q) (meaning1769 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1935 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1769 = true := counterClause1935 (baseVal q)

theorem counterClause1936 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1771 = true := by
  have hs : count1771 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-110)) (literal (valuationOf q) (1771)) (countLit q [-110]) (countLit q [-111]) (count1771 q) 1 (meaningNeg110 q) (meaning1771 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1936 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1771 = true := counterClause1936 (baseVal q)

theorem counterClause1937 (q : Nat → Bool) : valuationOf q 1769 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1774 = true := by
  have hs : count1773 q = (countLit q [-106, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1769)) (literal (valuationOf q) (1771)) (literal (valuationOf q) (1774)) (countLit q [-106, -108]) (countLit q [-110, -111]) (count1773 q) 1 1 (meaning1769 q) (meaning1771 q) (meaning1774 q) hs
  change valuationOf q 1769 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1937 (q : Snake 81) (h : Conditions q) : valuation q 1769 = false ∨ valuation q 1771 = false ∨ valuation q 1774 = true := counterClause1937 (baseVal q)

theorem counterClause1938 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1778 = true := by
  have hs : count1777 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_right (literal (valuationOf q) (1774)) (literal (valuationOf q) (1778)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1777 q) 2 (meaning1774 q) (meaning1778 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1938 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1778 = true := counterClause1938 (baseVal q)

theorem counterClause1939 (q : Nat → Bool) : valuationOf q 1765 = false ∨ valuationOf q 1777 = true := by
  have hs : count1777 q = (countLit q [-99, -100, -102, -104]) + (countLit q [-106, -108, -110, -111]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104]) (l₂ := [-106, -108, -110, -111])
  have hm := merge_left (literal (valuationOf q) (1765)) (literal (valuationOf q) (1777)) (countLit q [-99, -100, -102, -104]) (countLit q [-106, -108, -110, -111]) (count1777 q) 1 (meaning1765 q) (meaning1777 q) hs
  change valuationOf q 1765 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1939 (q : Snake 81) (h : Conditions q) : valuation q 1765 = false ∨ valuation q 1777 = true := counterClause1939 (baseVal q)

theorem counterClause1940 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1786 = true := by
  have hs : count1785 q = (countLit q [-115]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1786)) (countLit q [-115]) (countLit q [-116]) (count1785 q) 1 1 (meaningNeg115 q) (meaningNeg116 q) (meaning1786 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1940 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 1786 = true := counterClause1940 (baseVal q)

theorem counterClause1941 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1787 = true := by
  have hs : count1787 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_right (literal (valuationOf q) (-119)) (literal (valuationOf q) (1787)) (countLit q [-117]) (countLit q [-119]) (count1787 q) 1 (meaningNeg119 q) (meaning1787 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1941 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1787 = true := counterClause1941 (baseVal q)

theorem counterClause1942 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1787 = true := by
  have hs : count1787 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_left (literal (valuationOf q) (-117)) (literal (valuationOf q) (1787)) (countLit q [-117]) (countLit q [-119]) (count1787 q) 1 (meaningNeg117 q) (meaning1787 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1942 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1787 = true := counterClause1942 (baseVal q)

theorem counterClause1943 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1789 = true := by
  have hs : count1789 q = (countLit q [-115, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-117, -119])
  have hm := merge_right (literal (valuationOf q) (1787)) (literal (valuationOf q) (1789)) (countLit q [-115, -116]) (countLit q [-117, -119]) (count1789 q) 1 (meaning1787 q) (meaning1789 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1943 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1789 = true := counterClause1943 (baseVal q)

theorem counterClause1944 (q : Nat → Bool) : valuationOf q 1786 = false ∨ valuationOf q 1787 = false ∨ valuationOf q 1791 = true := by
  have hs : count1789 q = (countLit q [-115, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-117, -119])
  have hm := merge_two (literal (valuationOf q) (1786)) (literal (valuationOf q) (1787)) (literal (valuationOf q) (1791)) (countLit q [-115, -116]) (countLit q [-117, -119]) (count1789 q) 2 1 (meaning1786 q) (meaning1787 q) (meaning1791 q) hs
  change valuationOf q 1786 = false ∨ valuationOf q 1787 = false ∨ valuationOf q 1791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1944 (q : Snake 81) (h : Conditions q) : valuation q 1786 = false ∨ valuation q 1787 = false ∨ valuation q 1791 = true := counterClause1944 (baseVal q)

theorem counterClause1945 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1793 = true := by
  have hs : count1793 q = (countLit q [-120]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-120]) (l₂ := [-122])
  have hm := merge_left (literal (valuationOf q) (-120)) (literal (valuationOf q) (1793)) (countLit q [-120]) (countLit q [-122]) (count1793 q) 1 (meaningNeg120 q) (meaning1793 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1793 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1945 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1793 = true := counterClause1945 (baseVal q)

theorem counterClause1946 (q : Nat → Bool) : valuationOf q 126 = true ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-124]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-126])
  have hm := merge_right (literal (valuationOf q) (-126)) (literal (valuationOf q) (1795)) (countLit q [-124]) (countLit q [-126]) (count1795 q) 1 (meaningNeg126 q) (meaning1795 q) hs
  change (! (valuationOf q 126)) = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1946 (q : Snake 81) (h : Conditions q) : valuation q 126 = true ∨ valuation q 1795 = true := counterClause1946 (baseVal q)

theorem counterClause1947 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1795 = true := by
  have hs : count1795 q = (countLit q [-124]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-124]) (l₂ := [-126])
  have hm := merge_left (literal (valuationOf q) (-124)) (literal (valuationOf q) (1795)) (countLit q [-124]) (countLit q [-126]) (count1795 q) 1 (meaningNeg124 q) (meaning1795 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1947 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1795 = true := counterClause1947 (baseVal q)

theorem counterClause1948 (q : Nat → Bool) : valuationOf q 1795 = false ∨ valuationOf q 1797 = true := by
  have hs : count1797 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_right (literal (valuationOf q) (1795)) (literal (valuationOf q) (1797)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1797 q) 1 (meaning1795 q) (meaning1797 q) hs
  change valuationOf q 1795 = false ∨ valuationOf q 1797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1948 (q : Snake 81) (h : Conditions q) : valuation q 1795 = false ∨ valuation q 1797 = true := counterClause1948 (baseVal q)

theorem counterClause1949 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1798 = true := by
  have hs : count1797 q = (countLit q [-120, -122]) + (countLit q [-124, -126]) := List.countP_append (p := literal q) (l₁ := [-120, -122]) (l₂ := [-124, -126])
  have hm := merge_two (literal (valuationOf q) (1793)) (literal (valuationOf q) (1795)) (literal (valuationOf q) (1798)) (countLit q [-120, -122]) (countLit q [-124, -126]) (count1797 q) 1 1 (meaning1793 q) (meaning1795 q) (meaning1798 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1795 = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1949 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1795 = false ∨ valuation q 1798 = true := counterClause1949 (baseVal q)

theorem counterClause1950 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1802 = true := by
  have hs : count1801 q = (countLit q [-115, -116, -117, -119]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -117, -119]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1797)) (literal (valuationOf q) (1802)) (countLit q [-115, -116, -117, -119]) (countLit q [-120, -122, -124, -126]) (count1801 q) 1 1 (meaning1789 q) (meaning1797 q) (meaning1802 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1797 = false ∨ valuationOf q 1802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1950 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1797 = false ∨ valuation q 1802 = true := counterClause1950 (baseVal q)

theorem counterClause1951 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1805 = true := by
  have hs : count1801 q = (countLit q [-115, -116, -117, -119]) + (countLit q [-120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-115, -116, -117, -119]) (l₂ := [-120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1798)) (literal (valuationOf q) (1805)) (countLit q [-115, -116, -117, -119]) (countLit q [-120, -122, -124, -126]) (count1801 q) 3 2 (meaning1791 q) (meaning1798 q) (meaning1805 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1798 = false ∨ valuationOf q 1805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1951 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1798 = false ∨ valuation q 1805 = true := counterClause1951 (baseVal q)

theorem counterClause1952 (q : Nat → Bool) : valuationOf q 1777 = false ∨ valuationOf q 1805 = false ∨ valuationOf q 1814 = true := by
  have hs : count1809 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -117, -119, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -117, -119, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1777)) (literal (valuationOf q) (1805)) (literal (valuationOf q) (1814)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -117, -119, -120, -122, -124, -126]) (count1809 q) 1 5 (meaning1777 q) (meaning1805 q) (meaning1814 q) hs
  change valuationOf q 1777 = false ∨ valuationOf q 1805 = false ∨ valuationOf q 1814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1952 (q : Snake 81) (h : Conditions q) : valuation q 1777 = false ∨ valuation q 1805 = false ∨ valuation q 1814 = true := counterClause1952 (baseVal q)

theorem block60 (q : Snake 81) (h : Conditions q) : B112E057.Block60 (valuation q) :=
  ⟨clause1921 q h, clause1922 q h, clause1923 q h, clause1924 q h, clause1925 q h, clause1926 q h, clause1927 q h, clause1928 q h, clause1929 q h, clause1930 q h, clause1931 q h, clause1932 q h, clause1933 q h, clause1934 q h, clause1935 q h, clause1936 q h, clause1937 q h, clause1938 q h, clause1939 q h, clause1940 q h, clause1941 q h, clause1942 q h, clause1943 q h, clause1944 q h, clause1945 q h, clause1946 q h, clause1947 q h, clause1948 q h, clause1949 q h, clause1950 q h, clause1951 q h, clause1952 q h⟩

end
end Snake9.Regrowth.E112057
