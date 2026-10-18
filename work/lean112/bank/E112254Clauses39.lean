import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_left (literal (valuationOf q) (1688)) (literal (valuationOf q) (1699)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 1 (meaning1688 q) (meaning1699 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1699 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1700)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 1 1 (meaning1688 q) (meaning1695 q) (meaning1700 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1695 = false ∨ valuation q 1700 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1701)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 1 2 (meaning1688 q) (meaning1696 q) (meaning1701 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1696 = false ∨ valuation q 1701 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1702 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1702)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 1 3 (meaning1688 q) (meaning1697 q) (meaning1702 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1697 = false ∨ valuation q 1702 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1703 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1703)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 1 4 (meaning1688 q) (meaning1698 q) (meaning1703 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1698 = false ∨ valuation q 1703 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_left (literal (valuationOf q) (1689)) (literal (valuationOf q) (1700)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 2 (meaning1689 q) (meaning1700 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1700 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1701)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 2 1 (meaning1689 q) (meaning1695 q) (meaning1701 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1695 = false ∨ valuation q 1701 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1702 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1702)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 2 2 (meaning1689 q) (meaning1696 q) (meaning1702 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1696 = false ∨ valuation q 1702 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1703 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1703)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 2 3 (meaning1689 q) (meaning1697 q) (meaning1703 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1697 = false ∨ valuation q 1703 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_left (literal (valuationOf q) (1690)) (literal (valuationOf q) (1701)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 3 (meaning1690 q) (meaning1701 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1701 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1702 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1690)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1702)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 3 1 (meaning1690 q) (meaning1695 q) (meaning1702 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1695 = false ∨ valuation q 1702 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1703 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1690)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1703)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 3 2 (meaning1690 q) (meaning1696 q) (meaning1703 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1696 = false ∨ valuation q 1703 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1704 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_two (literal (valuationOf q) (1690)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1704)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 3 3 (meaning1690 q) (meaning1697 q) (meaning1704 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1697 = false ∨ valuation q 1704 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1706 = true := by
  have hs : count1706 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1706)) (countLit q [-105]) (countLit q [-108]) (count1706 q) 1 (meaningNeg108 q) (meaning1706 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1706 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1706 = true := by
  have hs : count1706 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1706)) (countLit q [-105]) (countLit q [-108]) (count1706 q) 1 (meaningNeg105 q) (meaning1706 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1706 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1707 = true := by
  have hs : count1706 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1707)) (countLit q [-105]) (countLit q [-108]) (count1706 q) 1 1 (meaningNeg105 q) (meaningNeg108 q) (meaning1707 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 108 = true ∨ valuation q 1707 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1708 = true := by
  have hs : count1708 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1708)) (countLit q [-110]) (countLit q [-111]) (count1708 q) 1 (meaningNeg111 q) (meaning1708 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1708 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1708 = true := by
  have hs : count1708 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-110)) (literal (valuationOf q) (1708)) (countLit q [-110]) (countLit q [-111]) (count1708 q) 1 (meaningNeg110 q) (meaning1708 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1708 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1710 = true := by
  have hs : count1710 q = (countLit q [-105, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-105, -108]) (l₂ := [-110, -111])
  have hm := merge_right (literal (valuationOf q) (1708)) (literal (valuationOf q) (1710)) (countLit q [-105, -108]) (countLit q [-110, -111]) (count1710 q) 1 (meaning1708 q) (meaning1710 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1710 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1710 = true := by
  have hs : count1710 q = (countLit q [-105, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-105, -108]) (l₂ := [-110, -111])
  have hm := merge_left (literal (valuationOf q) (1706)) (literal (valuationOf q) (1710)) (countLit q [-105, -108]) (countLit q [-110, -111]) (count1710 q) 1 (meaning1706 q) (meaning1710 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1710 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1711 = true := by
  have hs : count1710 q = (countLit q [-105, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-105, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1711)) (countLit q [-105, -108]) (countLit q [-110, -111]) (count1710 q) 1 1 (meaning1706 q) (meaning1708 q) (meaning1711 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1708 = false ∨ valuation q 1711 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1711 = true := by
  have hs : count1710 q = (countLit q [-105, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-105, -108]) (l₂ := [-110, -111])
  have hm := merge_left (literal (valuationOf q) (1707)) (literal (valuationOf q) (1711)) (countLit q [-105, -108]) (countLit q [-110, -111]) (count1710 q) 2 (meaning1707 q) (meaning1711 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1711 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1712 = true := by
  have hs : count1710 q = (countLit q [-105, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-105, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1712)) (countLit q [-105, -108]) (countLit q [-110, -111]) (count1710 q) 2 1 (meaning1707 q) (meaning1708 q) (meaning1712 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1708 = false ∨ valuation q 1712 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1714 = true := by
  have hs : count1714 q = (countLit q [-114]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1714)) (countLit q [-114]) (countLit q [-117]) (count1714 q) 1 (meaningNeg117 q) (meaning1714 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1714 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1714 = true := by
  have hs : count1714 q = (countLit q [-114]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-114)) (literal (valuationOf q) (1714)) (countLit q [-114]) (countLit q [-117]) (count1714 q) 1 (meaningNeg114 q) (meaning1714 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1714 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1715 = true := by
  have hs : count1714 q = (countLit q [-114]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-114)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1715)) (countLit q [-114]) (countLit q [-117]) (count1714 q) 1 1 (meaningNeg114 q) (meaningNeg117 q) (meaning1715 q) hs
  change (! (valuationOf q 114)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 117 = true ∨ valuation q 1715 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1716 = true := by
  have hs : count1716 q = (countLit q [-121]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-122])
  have hm := merge_right (literal (valuationOf q) (-122)) (literal (valuationOf q) (1716)) (countLit q [-121]) (countLit q [-122]) (count1716 q) 1 (meaningNeg122 q) (meaning1716 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1716 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 1716 = true := by
  have hs : count1716 q = (countLit q [-121]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-122])
  have hm := merge_left (literal (valuationOf q) (-121)) (literal (valuationOf q) (1716)) (countLit q [-121]) (countLit q [-122]) (count1716 q) 1 (meaningNeg121 q) (meaning1716 q) hs
  change (! (valuationOf q 121)) = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 1716 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 122 = true ∨ valuationOf q 1717 = true := by
  have hs : count1716 q = (countLit q [-121]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-122])
  have hm := merge_two (literal (valuationOf q) (-121)) (literal (valuationOf q) (-122)) (literal (valuationOf q) (1717)) (countLit q [-121]) (countLit q [-122]) (count1716 q) 1 1 (meaningNeg121 q) (meaningNeg122 q) (meaning1717 q) hs
  change (! (valuationOf q 121)) = false ∨ (! (valuationOf q 122)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 1717 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1718 = true := by
  have hs : count1718 q = (countLit q [-114, -117]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-114, -117]) (l₂ := [-121, -122])
  have hm := merge_right (literal (valuationOf q) (1716)) (literal (valuationOf q) (1718)) (countLit q [-114, -117]) (countLit q [-121, -122]) (count1718 q) 1 (meaning1716 q) (meaning1718 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1718 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1719 = true := by
  have hs : count1718 q = (countLit q [-114, -117]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-114, -117]) (l₂ := [-121, -122])
  have hm := merge_right (literal (valuationOf q) (1717)) (literal (valuationOf q) (1719)) (countLit q [-114, -117]) (countLit q [-121, -122]) (count1718 q) 2 (meaning1717 q) (meaning1719 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1719 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1718 = true := by
  have hs : count1718 q = (countLit q [-114, -117]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-114, -117]) (l₂ := [-121, -122])
  have hm := merge_left (literal (valuationOf q) (1714)) (literal (valuationOf q) (1718)) (countLit q [-114, -117]) (countLit q [-121, -122]) (count1718 q) 1 (meaning1714 q) (meaning1718 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1718 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E254.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112254
