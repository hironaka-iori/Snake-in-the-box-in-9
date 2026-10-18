import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1718 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1699)) (literal (valuationOf q) (1718)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 4 8 (meaning1636 q) (meaning1699 q) (meaning1718 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1699 = false ∨ valuation q 1718 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1719 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1700)) (literal (valuationOf q) (1719)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 4 9 (meaning1636 q) (meaning1700 q) (meaning1719 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1700 = false ∨ valuation q 1719 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1714 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1714)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 5 3 (meaning1637 q) (meaning1694 q) (meaning1714 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1694 = false ∨ valuation q 1714 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1715 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1715)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 5 4 (meaning1637 q) (meaning1695 q) (meaning1715 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1695 = false ∨ valuation q 1715 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1716 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1716)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 5 5 (meaning1637 q) (meaning1696 q) (meaning1716 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1696 = false ∨ valuation q 1716 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1717 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1717)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 5 6 (meaning1637 q) (meaning1697 q) (meaning1717 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1697 = false ∨ valuation q 1717 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1718 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1718)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 5 7 (meaning1637 q) (meaning1698 q) (meaning1718 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1698 = false ∨ valuation q 1718 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1719 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1699)) (literal (valuationOf q) (1719)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 5 8 (meaning1637 q) (meaning1699 q) (meaning1719 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1699 = false ∨ valuation q 1719 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1716 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1716)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 6 4 (meaning1638 q) (meaning1695 q) (meaning1716 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1695 = false ∨ valuation q 1716 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1717 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1717)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 6 5 (meaning1638 q) (meaning1696 q) (meaning1717 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1696 = false ∨ valuation q 1717 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1718 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1718)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 6 6 (meaning1638 q) (meaning1697 q) (meaning1718 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1697 = false ∨ valuation q 1718 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1719 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1719)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 6 7 (meaning1638 q) (meaning1698 q) (meaning1719 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1698 = false ∨ valuation q 1719 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1716 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1716)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 7 3 (meaning1639 q) (meaning1694 q) (meaning1716 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1694 = false ∨ valuation q 1716 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1717 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1717)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 7 4 (meaning1639 q) (meaning1695 q) (meaning1717 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1695 = false ∨ valuation q 1717 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1718 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1718)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 7 5 (meaning1639 q) (meaning1696 q) (meaning1718 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1696 = false ∨ valuation q 1718 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1719 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1719)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 7 6 (meaning1639 q) (meaning1697 q) (meaning1719 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1697 = false ∨ valuation q 1719 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1718 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1718)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 8 4 (meaning1640 q) (meaning1695 q) (meaning1718 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1695 = false ∨ valuation q 1718 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1719 = true := by
  have hs : count1707 q = (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) + (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (l₂ := [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1719)) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]) (countLit q [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1707 q) 8 5 (meaning1640 q) (meaning1696 q) (meaning1719 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1696 = false ∨ valuation q 1719 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1744 = true := by
  have hs : count1726 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) + (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (l₂ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1726 q) 6 13 (meaning1575 q) (meaning1719 q) (meaning1744 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1719 = false ∨ valuation q 1744 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1744 = true := by
  have hs : count1726 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) + (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (l₂ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1726 q) 7 12 (meaning1576 q) (meaning1718 q) (meaning1744 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1718 = false ∨ valuation q 1744 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1744 = true := by
  have hs : count1726 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) + (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (l₂ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1726 q) 8 11 (meaning1577 q) (meaning1717 q) (meaning1744 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1717 = false ∨ valuation q 1744 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1744 = true := by
  have hs : count1726 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) + (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (l₂ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1726 q) 9 10 (meaning1578 q) (meaning1716 q) (meaning1744 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1716 = false ∨ valuation q 1744 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1744 = true := by
  have hs : count1726 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) + (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (l₂ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1726 q) 10 9 (meaning1579 q) (meaning1715 q) (meaning1744 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1715 = false ∨ valuation q 1744 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1744 = true := by
  have hs : count1726 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) + (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (l₂ := [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1744)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (countLit q [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]) (count1726 q) 11 8 (meaning1580 q) (meaning1714 q) (meaning1744 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1714 = false ∨ valuation q 1744 = true := counterClause920 (baseVal q)

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false := by
  rw [value1744]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1726 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 47 = false ∨ valuation q 64 = false ∨ valuation q 103 = false := by
  rw [value12, value47, value64, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (102 : Vertex) (230 : Vertex) (358 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value26, value27, value30, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (162 : Vertex) (168 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value28, value29, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (166 : Vertex) (167 : Vertex) (422 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value45, value46, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (236 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 54 = false ∨ valuation q 103 = false ∨ valuation q 114 = false := by
  rw [value47, value54, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (230 : Vertex) (246 : Vertex) (486 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value50, value51, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (236 : Vertex) (237 : Vertex) (492 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value61, value62, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (353 : Vertex) (355 : Vertex) (361 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E152.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112152
