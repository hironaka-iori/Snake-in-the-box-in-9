import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1726)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 2 2 (meaning1712 q) (meaning1720 q) (meaning1726 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1720 = false ∨ valuation q 1726 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1727 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1727)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 2 3 (meaning1712 q) (meaning1721 q) (meaning1727 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1721 = false ∨ valuation q 1727 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1728 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1728)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 2 4 (meaning1712 q) (meaning1722 q) (meaning1728 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1722 = false ∨ valuation q 1728 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_left (literal (valuationOf q) (1713)) (literal (valuationOf q) (1725)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 3 (meaning1713 q) (meaning1725 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1725 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1726)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 3 1 (meaning1713 q) (meaning1719 q) (meaning1726 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1719 = false ∨ valuation q 1726 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1727 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1727)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 3 2 (meaning1713 q) (meaning1720 q) (meaning1727 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1720 = false ∨ valuation q 1727 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1728 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1728)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 3 3 (meaning1713 q) (meaning1721 q) (meaning1728 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1721 = false ∨ valuation q 1728 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_left (literal (valuationOf q) (1714)) (literal (valuationOf q) (1726)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 4 (meaning1714 q) (meaning1726 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1726 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1727 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1727)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 4 1 (meaning1714 q) (meaning1719 q) (meaning1727 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1719 = false ∨ valuation q 1727 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1728 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1728)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 4 2 (meaning1714 q) (meaning1720 q) (meaning1728 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1720 = false ∨ valuation q 1728 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1729 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1729)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 4 3 (meaning1714 q) (meaning1721 q) (meaning1729 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1721 = false ∨ valuation q 1729 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1731 = true := by
  have hs : count1731 q = (countLit q [-109]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1731)) (countLit q [-109]) (countLit q [-112]) (count1731 q) 1 (meaningNeg112 q) (meaning1731 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1731 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1731 = true := by
  have hs : count1731 q = (countLit q [-109]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1731)) (countLit q [-109]) (countLit q [-112]) (count1731 q) 1 (meaningNeg109 q) (meaning1731 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1731 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1732 = true := by
  have hs : count1731 q = (countLit q [-109]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-109)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1732)) (countLit q [-109]) (countLit q [-112]) (count1731 q) 1 1 (meaningNeg109 q) (meaningNeg112 q) (meaning1732 q) hs
  change (! (valuationOf q 109)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 112 = true ∨ valuation q 1732 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1733)) (countLit q [-113]) (countLit q [-114]) (count1733 q) 1 (meaningNeg114 q) (meaning1733 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1733 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1733)) (countLit q [-113]) (countLit q [-114]) (count1733 q) 1 (meaningNeg113 q) (meaning1733 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1733 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1734 = true := by
  have hs : count1733 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1734)) (countLit q [-113]) (countLit q [-114]) (count1733 q) 1 1 (meaningNeg113 q) (meaningNeg114 q) (meaning1734 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 1734 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-109, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -114])
  have hm := merge_right (literal (valuationOf q) (1733)) (literal (valuationOf q) (1735)) (countLit q [-109, -112]) (countLit q [-113, -114]) (count1735 q) 1 (meaning1733 q) (meaning1735 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1735 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-109, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -114])
  have hm := merge_right (literal (valuationOf q) (1734)) (literal (valuationOf q) (1736)) (countLit q [-109, -112]) (countLit q [-113, -114]) (count1735 q) 2 (meaning1734 q) (meaning1736 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1736 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-109, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1731)) (literal (valuationOf q) (1735)) (countLit q [-109, -112]) (countLit q [-113, -114]) (count1735 q) 1 (meaning1731 q) (meaning1735 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1735 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-109, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1736)) (countLit q [-109, -112]) (countLit q [-113, -114]) (count1735 q) 1 1 (meaning1731 q) (meaning1733 q) (meaning1736 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1733 = false ∨ valuation q 1736 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1737 = true := by
  have hs : count1735 q = (countLit q [-109, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1737)) (countLit q [-109, -112]) (countLit q [-113, -114]) (count1735 q) 1 2 (meaning1731 q) (meaning1734 q) (meaning1737 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1734 = false ∨ valuation q 1737 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-109, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1732)) (literal (valuationOf q) (1736)) (countLit q [-109, -112]) (countLit q [-113, -114]) (count1735 q) 2 (meaning1732 q) (meaning1736 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1736 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1737 = true := by
  have hs : count1735 q = (countLit q [-109, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1737)) (countLit q [-109, -112]) (countLit q [-113, -114]) (count1735 q) 2 1 (meaning1732 q) (meaning1733 q) (meaning1737 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1733 = false ∨ valuation q 1737 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1738 = true := by
  have hs : count1735 q = (countLit q [-109, -112]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -112]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1732)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1738)) (countLit q [-109, -112]) (countLit q [-113, -114]) (count1735 q) 2 2 (meaning1732 q) (meaning1734 q) (meaning1738 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1734 = false ∨ valuation q 1738 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1739 = true := by
  have hs : count1739 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_right (literal (valuationOf q) (-119)) (literal (valuationOf q) (1739)) (countLit q [-117]) (countLit q [-119]) (count1739 q) 1 (meaningNeg119 q) (meaning1739 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1739 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1739 = true := by
  have hs : count1739 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_left (literal (valuationOf q) (-117)) (literal (valuationOf q) (1739)) (countLit q [-117]) (countLit q [-119]) (count1739 q) 1 (meaningNeg117 q) (meaning1739 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1739 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 119 = true ∨ valuationOf q 1740 = true := by
  have hs : count1739 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_two (literal (valuationOf q) (-117)) (literal (valuationOf q) (-119)) (literal (valuationOf q) (1740)) (countLit q [-117]) (countLit q [-119]) (count1739 q) 1 1 (meaningNeg117 q) (meaningNeg119 q) (meaning1740 q) hs
  change (! (valuationOf q 117)) = false ∨ (! (valuationOf q 119)) = false ∨ valuationOf q 1740 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 1740 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_right (literal (valuationOf q) (-123)) (literal (valuationOf q) (1741)) (countLit q [-122]) (countLit q [-123]) (count1741 q) 1 (meaningNeg123 q) (meaning1741 q) hs
  change (! (valuationOf q 123)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 1741 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_left (literal (valuationOf q) (-122)) (literal (valuationOf q) (1741)) (countLit q [-122]) (countLit q [-123]) (count1741 q) 1 (meaningNeg122 q) (meaning1741 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1741 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 123 = true ∨ valuationOf q 1742 = true := by
  have hs : count1741 q = (countLit q [-122]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-123])
  have hm := merge_two (literal (valuationOf q) (-122)) (literal (valuationOf q) (-123)) (literal (valuationOf q) (1742)) (countLit q [-122]) (countLit q [-123]) (count1741 q) 1 1 (meaningNeg122 q) (meaningNeg123 q) (meaning1742 q) hs
  change (! (valuationOf q 122)) = false ∨ (! (valuationOf q 123)) = false ∨ valuationOf q 1742 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 1742 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-117, -119]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-122, -123])
  have hm := merge_right (literal (valuationOf q) (1741)) (literal (valuationOf q) (1743)) (countLit q [-117, -119]) (countLit q [-122, -123]) (count1743 q) 1 (meaning1741 q) (meaning1743 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1743 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E186.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112186
