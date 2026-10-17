import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1671 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1671)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 1 (meaning1658 q) (meaning1665 q) (meaning1671 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1665 = false ∨ valuation q 1671 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1672 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1672)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 2 (meaning1658 q) (meaning1666 q) (meaning1672 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1666 = false ∨ valuation q 1672 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1673 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1673)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 3 (meaning1658 q) (meaning1667 q) (meaning1673 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1667 = false ∨ valuation q 1673 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1674 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1674)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 4 (meaning1658 q) (meaning1668 q) (meaning1674 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1668 = false ∨ valuation q 1674 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1671 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_left (literal (valuationOf q) (1659)) (literal (valuationOf q) (1671)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 (meaning1659 q) (meaning1671 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1671 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1672 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1672)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 1 (meaning1659 q) (meaning1665 q) (meaning1672 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1665 = false ∨ valuation q 1672 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1673 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1673)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 2 (meaning1659 q) (meaning1666 q) (meaning1673 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1666 = false ∨ valuation q 1673 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1674 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1674)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 3 (meaning1659 q) (meaning1667 q) (meaning1674 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1667 = false ∨ valuation q 1674 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1675 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1675)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 4 (meaning1659 q) (meaning1668 q) (meaning1675 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1668 = false ∨ valuation q 1675 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1672 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_left (literal (valuationOf q) (1660)) (literal (valuationOf q) (1672)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 (meaning1660 q) (meaning1672 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1672 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1673 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1673)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 1 (meaning1660 q) (meaning1665 q) (meaning1673 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1665 = false ∨ valuation q 1673 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1674 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1674)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 2 (meaning1660 q) (meaning1666 q) (meaning1674 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1666 = false ∨ valuation q 1674 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1675 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1675)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 3 (meaning1660 q) (meaning1667 q) (meaning1675 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1667 = false ∨ valuation q 1675 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1676 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1676)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 4 (meaning1660 q) (meaning1668 q) (meaning1676 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1668 = false ∨ valuation q 1676 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1677 = true := by
  have hs : count1677 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1677)) (countLit q [-107]) (countLit q [-108]) (count1677 q) 1 (meaningNeg108 q) (meaning1677 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1677 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1677 = true := by
  have hs : count1677 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1677)) (countLit q [-107]) (countLit q [-108]) (count1677 q) 1 (meaningNeg107 q) (meaning1677 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1677 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1678 = true := by
  have hs : count1677 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1678)) (countLit q [-107]) (countLit q [-108]) (count1677 q) 1 1 (meaningNeg107 q) (meaningNeg108 q) (meaning1678 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 1678 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1679 = true := by
  have hs : count1679 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1679)) (countLit q [-110]) (countLit q [-111]) (count1679 q) 1 (meaningNeg111 q) (meaning1679 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1679 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1679 = true := by
  have hs : count1679 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-110)) (literal (valuationOf q) (1679)) (countLit q [-110]) (countLit q [-111]) (count1679 q) 1 (meaningNeg110 q) (meaning1679 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1679 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 111 = true ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_two (literal (valuationOf q) (-110)) (literal (valuationOf q) (-111)) (literal (valuationOf q) (1680)) (countLit q [-110]) (countLit q [-111]) (count1679 q) 1 1 (meaningNeg110 q) (meaningNeg111 q) (meaning1680 q) hs
  change (! (valuationOf q 110)) = false ∨ (! (valuationOf q 111)) = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 1680 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1681 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_right (literal (valuationOf q) (1679)) (literal (valuationOf q) (1681)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 1 (meaning1679 q) (meaning1681 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1681 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1682 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_right (literal (valuationOf q) (1680)) (literal (valuationOf q) (1682)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 2 (meaning1680 q) (meaning1682 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1682 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1681 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_left (literal (valuationOf q) (1677)) (literal (valuationOf q) (1681)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 1 (meaning1677 q) (meaning1681 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1681 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1682 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1682)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 1 1 (meaning1677 q) (meaning1679 q) (meaning1682 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1679 = false ∨ valuation q 1682 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1683 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1683)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 1 2 (meaning1677 q) (meaning1680 q) (meaning1683 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1680 = false ∨ valuation q 1683 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1682 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_left (literal (valuationOf q) (1678)) (literal (valuationOf q) (1682)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 2 (meaning1678 q) (meaning1682 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1682 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1683 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1683)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 2 1 (meaning1678 q) (meaning1679 q) (meaning1683 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1679 = false ∨ valuation q 1683 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1685 = true := by
  have hs : count1685 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1685)) (countLit q [-115]) (countLit q [-117]) (count1685 q) 1 (meaningNeg117 q) (meaning1685 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1685 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1685 = true := by
  have hs : count1685 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1685)) (countLit q [-115]) (countLit q [-117]) (count1685 q) 1 (meaningNeg115 q) (meaning1685 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1685 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1686 = true := by
  have hs : count1685 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1686)) (countLit q [-115]) (countLit q [-117]) (count1685 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1686 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1686 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1687 = true := by
  have hs : count1687 q = (countLit q [-118]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-119])
  have hm := merge_right (literal (valuationOf q) (-119)) (literal (valuationOf q) (1687)) (countLit q [-118]) (countLit q [-119]) (count1687 q) 1 (meaningNeg119 q) (meaning1687 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1687 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1687 = true := by
  have hs : count1687 q = (countLit q [-118]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-119])
  have hm := merge_left (literal (valuationOf q) (-118)) (literal (valuationOf q) (1687)) (countLit q [-118]) (countLit q [-119]) (count1687 q) 1 (meaningNeg118 q) (meaning1687 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1687 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E026.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112026
