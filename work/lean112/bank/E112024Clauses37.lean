import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1671 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_left (literal (valuationOf q) (1659)) (literal (valuationOf q) (1671)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 (meaning1659 q) (meaning1671 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1671 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1672 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1672)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 1 (meaning1659 q) (meaning1665 q) (meaning1672 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1665 = false ∨ valuation q 1672 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1673 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1673)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 2 (meaning1659 q) (meaning1666 q) (meaning1673 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1666 = false ∨ valuation q 1673 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1674 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1674)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 3 (meaning1659 q) (meaning1667 q) (meaning1674 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1667 = false ∨ valuation q 1674 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1675 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1675)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 4 (meaning1659 q) (meaning1668 q) (meaning1675 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1668 = false ∨ valuation q 1675 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1672 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_left (literal (valuationOf q) (1660)) (literal (valuationOf q) (1672)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 (meaning1660 q) (meaning1672 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1672 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1673 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1673)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 1 (meaning1660 q) (meaning1665 q) (meaning1673 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1665 = false ∨ valuation q 1673 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1674 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1674)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 2 (meaning1660 q) (meaning1666 q) (meaning1674 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1666 = false ∨ valuation q 1674 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1675 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1675)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 3 (meaning1660 q) (meaning1667 q) (meaning1675 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1667 = false ∨ valuation q 1675 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1676 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1676)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 4 4 (meaning1660 q) (meaning1668 q) (meaning1676 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1668 = false ∨ valuation q 1676 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1677 = true := by
  have hs : count1677 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1677)) (countLit q [-107]) (countLit q [-108]) (count1677 q) 1 (meaningNeg108 q) (meaning1677 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1677 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1677 = true := by
  have hs : count1677 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1677)) (countLit q [-107]) (countLit q [-108]) (count1677 q) 1 (meaningNeg107 q) (meaning1677 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1677 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1678 = true := by
  have hs : count1677 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1678)) (countLit q [-107]) (countLit q [-108]) (count1677 q) 1 1 (meaningNeg107 q) (meaningNeg108 q) (meaning1678 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 1678 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1679 = true := by
  have hs : count1679 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1679)) (countLit q [-110]) (countLit q [-111]) (count1679 q) 1 (meaningNeg111 q) (meaning1679 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1679 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1679 = true := by
  have hs : count1679 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-110)) (literal (valuationOf q) (1679)) (countLit q [-110]) (countLit q [-111]) (count1679 q) 1 (meaningNeg110 q) (meaning1679 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1679 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 111 = true ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_two (literal (valuationOf q) (-110)) (literal (valuationOf q) (-111)) (literal (valuationOf q) (1680)) (countLit q [-110]) (countLit q [-111]) (count1679 q) 1 1 (meaningNeg110 q) (meaningNeg111 q) (meaning1680 q) hs
  change (! (valuationOf q 110)) = false ∨ (! (valuationOf q 111)) = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 1680 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1681 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_right (literal (valuationOf q) (1679)) (literal (valuationOf q) (1681)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 1 (meaning1679 q) (meaning1681 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1681 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1682 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_right (literal (valuationOf q) (1680)) (literal (valuationOf q) (1682)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 2 (meaning1680 q) (meaning1682 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1682 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1681 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_left (literal (valuationOf q) (1677)) (literal (valuationOf q) (1681)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 1 (meaning1677 q) (meaning1681 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1681 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1682 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1682)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 1 1 (meaning1677 q) (meaning1679 q) (meaning1682 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1679 = false ∨ valuation q 1682 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1683 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1683)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 1 2 (meaning1677 q) (meaning1680 q) (meaning1683 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1680 = false ∨ valuation q 1683 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1682 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_left (literal (valuationOf q) (1678)) (literal (valuationOf q) (1682)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 2 (meaning1678 q) (meaning1682 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1682 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1683 = true := by
  have hs : count1681 q = (countLit q [-107, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-110, -111])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1683)) (countLit q [-107, -108]) (countLit q [-110, -111]) (count1681 q) 2 1 (meaning1678 q) (meaning1679 q) (meaning1683 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1679 = false ∨ valuation q 1683 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1685 = true := by
  have hs : count1685 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1685)) (countLit q [-115]) (countLit q [-117]) (count1685 q) 1 (meaningNeg117 q) (meaning1685 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1685 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1685 = true := by
  have hs : count1685 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1685)) (countLit q [-115]) (countLit q [-117]) (count1685 q) 1 (meaningNeg115 q) (meaning1685 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1685 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1686 = true := by
  have hs : count1685 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1686)) (countLit q [-115]) (countLit q [-117]) (count1685 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1686 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1686 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1687 = true := by
  have hs : count1687 q = (countLit q [-118]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-119])
  have hm := merge_right (literal (valuationOf q) (-119)) (literal (valuationOf q) (1687)) (countLit q [-118]) (countLit q [-119]) (count1687 q) 1 (meaningNeg119 q) (meaning1687 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1687 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1687 = true := by
  have hs : count1687 q = (countLit q [-118]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-119])
  have hm := merge_left (literal (valuationOf q) (-118)) (literal (valuationOf q) (1687)) (countLit q [-118]) (countLit q [-119]) (count1687 q) 1 (meaningNeg118 q) (meaning1687 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1687 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 119 = true ∨ valuationOf q 1688 = true := by
  have hs : count1687 q = (countLit q [-118]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-119])
  have hm := merge_two (literal (valuationOf q) (-118)) (literal (valuationOf q) (-119)) (literal (valuationOf q) (1688)) (countLit q [-118]) (countLit q [-119]) (count1687 q) 1 1 (meaningNeg118 q) (meaningNeg119 q) (meaning1688 q) hs
  change (! (valuationOf q 118)) = false ∨ (! (valuationOf q 119)) = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 1688 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1689 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_right (literal (valuationOf q) (1687)) (literal (valuationOf q) (1689)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 1 (meaning1687 q) (meaning1689 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1689 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1690 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_right (literal (valuationOf q) (1688)) (literal (valuationOf q) (1690)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 2 (meaning1688 q) (meaning1690 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1690 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1689 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_left (literal (valuationOf q) (1685)) (literal (valuationOf q) (1689)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 1 (meaning1685 q) (meaning1689 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1689 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E024.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112024
