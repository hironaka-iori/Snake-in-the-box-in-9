import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1690 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_two (literal (valuationOf q) (1685)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1690)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 1 1 (meaning1685 q) (meaning1687 q) (meaning1690 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1687 = false ∨ valuation q 1690 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1690 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_left (literal (valuationOf q) (1686)) (literal (valuationOf q) (1690)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 2 (meaning1686 q) (meaning1690 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1690 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1693 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_left (literal (valuationOf q) (1681)) (literal (valuationOf q) (1693)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 1 (meaning1681 q) (meaning1693 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1693 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1694 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1694)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 1 1 (meaning1681 q) (meaning1689 q) (meaning1694 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1689 = false ∨ valuation q 1694 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1695 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1695)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 1 2 (meaning1681 q) (meaning1690 q) (meaning1695 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1690 = false ∨ valuation q 1695 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1694 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_left (literal (valuationOf q) (1682)) (literal (valuationOf q) (1694)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 2 (meaning1682 q) (meaning1694 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1694 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1695 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1695)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 2 1 (meaning1682 q) (meaning1689 q) (meaning1695 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1689 = false ∨ valuation q 1695 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1696 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1696)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 2 2 (meaning1682 q) (meaning1690 q) (meaning1696 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1690 = false ∨ valuation q 1696 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1695 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_left (literal (valuationOf q) (1683)) (literal (valuationOf q) (1695)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 3 (meaning1683 q) (meaning1695 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1695 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1696 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1696)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 3 1 (meaning1683 q) (meaning1689 q) (meaning1696 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1689 = false ∨ valuation q 1696 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1697 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1697)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 3 2 (meaning1683 q) (meaning1690 q) (meaning1697 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1690 = false ∨ valuation q 1697 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1701 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_right (literal (valuationOf q) (1693)) (literal (valuationOf q) (1701)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 1 (meaning1693 q) (meaning1701 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1701 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1703 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_right (literal (valuationOf q) (1695)) (literal (valuationOf q) (1703)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 (meaning1695 q) (meaning1703 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1703 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1702 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1702)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 1 1 (meaning1669 q) (meaning1693 q) (meaning1702 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1693 = false ∨ valuation q 1702 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1703 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1703)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 1 2 (meaning1669 q) (meaning1694 q) (meaning1703 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1694 = false ∨ valuation q 1703 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1704 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1704)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 1 3 (meaning1669 q) (meaning1695 q) (meaning1704 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1695 = false ∨ valuation q 1704 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1705 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1705)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 1 4 (meaning1669 q) (meaning1696 q) (meaning1705 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1696 = false ∨ valuation q 1705 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 1 5 (meaning1669 q) (meaning1697 q) (meaning1706 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1697 = false ∨ valuation q 1706 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1703 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1703)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 1 (meaning1670 q) (meaning1693 q) (meaning1703 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1693 = false ∨ valuation q 1703 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1704 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1704)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 2 (meaning1670 q) (meaning1694 q) (meaning1704 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1694 = false ∨ valuation q 1704 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1705 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1705)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 3 (meaning1670 q) (meaning1695 q) (meaning1705 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1695 = false ∨ valuation q 1705 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 4 (meaning1670 q) (meaning1696 q) (meaning1706 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1696 = false ∨ valuation q 1706 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 5 (meaning1670 q) (meaning1697 q) (meaning1707 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1697 = false ∨ valuation q 1707 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1704 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1704)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 1 (meaning1671 q) (meaning1693 q) (meaning1704 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1693 = false ∨ valuation q 1704 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1705 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1705)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 2 (meaning1671 q) (meaning1694 q) (meaning1705 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1694 = false ∨ valuation q 1705 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 3 (meaning1671 q) (meaning1695 q) (meaning1706 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1695 = false ∨ valuation q 1706 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 4 (meaning1671 q) (meaning1696 q) (meaning1707 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1696 = false ∨ valuation q 1707 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 5 (meaning1671 q) (meaning1697 q) (meaning1708 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1697 = false ∨ valuation q 1708 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1704 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_left (literal (valuationOf q) (1672)) (literal (valuationOf q) (1704)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 (meaning1672 q) (meaning1704 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1704 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1705 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1705)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 1 (meaning1672 q) (meaning1693 q) (meaning1705 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1693 = false ∨ valuation q 1705 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 2 (meaning1672 q) (meaning1694 q) (meaning1706 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1694 = false ∨ valuation q 1706 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 3 (meaning1672 q) (meaning1695 q) (meaning1707 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1695 = false ∨ valuation q 1707 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E024.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112024
