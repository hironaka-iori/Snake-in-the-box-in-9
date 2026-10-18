import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1677 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -70, -77, -78]) + (countLit q [-79, -81, -82, -83, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78]) (l₂ := [-79, -81, -82, -83, -86, -87, -92])
  have hm := merge_left (literal (valuationOf q) (1650)) (literal (valuationOf q) (1677)) (countLit q [-65, -66, -67, -69, -70, -77, -78]) (countLit q [-79, -81, -82, -83, -86, -87, -92]) (count1672 q) 6 (meaning1650 q) (meaning1677 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1677 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1678 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -70, -77, -78]) + (countLit q [-79, -81, -82, -83, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78]) (l₂ := [-79, -81, -82, -83, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1678)) (countLit q [-65, -66, -67, -69, -70, -77, -78]) (countLit q [-79, -81, -82, -83, -86, -87, -92]) (count1672 q) 6 1 (meaning1650 q) (meaning1665 q) (meaning1678 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1665 = false ∨ valuation q 1678 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1679 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -70, -77, -78]) + (countLit q [-79, -81, -82, -83, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78]) (l₂ := [-79, -81, -82, -83, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1679)) (countLit q [-65, -66, -67, -69, -70, -77, -78]) (countLit q [-79, -81, -82, -83, -86, -87, -92]) (count1672 q) 6 2 (meaning1650 q) (meaning1666 q) (meaning1679 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1666 = false ∨ valuation q 1679 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1680 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -70, -77, -78]) + (countLit q [-79, -81, -82, -83, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78]) (l₂ := [-79, -81, -82, -83, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1680)) (countLit q [-65, -66, -67, -69, -70, -77, -78]) (countLit q [-79, -81, -82, -83, -86, -87, -92]) (count1672 q) 6 3 (meaning1650 q) (meaning1667 q) (meaning1680 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1667 = false ∨ valuation q 1680 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1678 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -70, -77, -78]) + (countLit q [-79, -81, -82, -83, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78]) (l₂ := [-79, -81, -82, -83, -86, -87, -92])
  have hm := merge_left (literal (valuationOf q) (1651)) (literal (valuationOf q) (1678)) (countLit q [-65, -66, -67, -69, -70, -77, -78]) (countLit q [-79, -81, -82, -83, -86, -87, -92]) (count1672 q) 7 (meaning1651 q) (meaning1678 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1678 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1679 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -70, -77, -78]) + (countLit q [-79, -81, -82, -83, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78]) (l₂ := [-79, -81, -82, -83, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1679)) (countLit q [-65, -66, -67, -69, -70, -77, -78]) (countLit q [-79, -81, -82, -83, -86, -87, -92]) (count1672 q) 7 1 (meaning1651 q) (meaning1665 q) (meaning1679 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1665 = false ∨ valuation q 1679 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1686 = true := by
  have hs : count1686 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1686)) (countLit q [-97]) (countLit q [-99]) (count1686 q) 1 (meaningNeg99 q) (meaning1686 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1686 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1686 = true := by
  have hs : count1686 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1686)) (countLit q [-97]) (countLit q [-99]) (count1686 q) 1 (meaningNeg97 q) (meaning1686 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1686 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1687 = true := by
  have hs : count1686 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1687)) (countLit q [-97]) (countLit q [-99]) (count1686 q) 1 1 (meaningNeg97 q) (meaningNeg99 q) (meaning1687 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 99 = true ∨ valuation q 1687 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1688 = true := by
  have hs : count1688 q = (countLit q [-94]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97, -99])
  have hm := merge_right (literal (valuationOf q) (1686)) (literal (valuationOf q) (1688)) (countLit q [-94]) (countLit q [-97, -99]) (count1688 q) 1 (meaning1686 q) (meaning1688 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1688 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1689 = true := by
  have hs : count1688 q = (countLit q [-94]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97, -99])
  have hm := merge_right (literal (valuationOf q) (1687)) (literal (valuationOf q) (1689)) (countLit q [-94]) (countLit q [-97, -99]) (count1688 q) 2 (meaning1687 q) (meaning1689 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1689 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1688 = true := by
  have hs : count1688 q = (countLit q [-94]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97, -99])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1688)) (countLit q [-94]) (countLit q [-97, -99]) (count1688 q) 1 (meaningNeg94 q) (meaning1688 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1688 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1686 = false ∨ valuationOf q 1689 = true := by
  have hs : count1688 q = (countLit q [-94]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97, -99])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1689)) (countLit q [-94]) (countLit q [-97, -99]) (count1688 q) 1 1 (meaningNeg94 q) (meaning1686 q) (meaning1689 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1686 = false ∨ valuation q 1689 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1687 = false ∨ valuationOf q 1690 = true := by
  have hs : count1688 q = (countLit q [-94]) + (countLit q [-97, -99]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97, -99])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1690)) (countLit q [-94]) (countLit q [-97, -99]) (count1688 q) 1 2 (meaningNeg94 q) (meaning1687 q) (meaning1690 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1687 = false ∨ valuation q 1690 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1691 = true := by
  have hs : count1691 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1691)) (countLit q [-100]) (countLit q [-101]) (count1691 q) 1 (meaningNeg101 q) (meaning1691 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1691 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1691 = true := by
  have hs : count1691 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1691)) (countLit q [-100]) (countLit q [-101]) (count1691 q) 1 (meaningNeg100 q) (meaning1691 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1691 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1692 = true := by
  have hs : count1691 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1692)) (countLit q [-100]) (countLit q [-101]) (count1691 q) 1 1 (meaningNeg100 q) (meaningNeg101 q) (meaning1692 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 1692 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1693 = true := by
  have hs : count1693 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1693)) (countLit q [-102]) (countLit q [-103]) (count1693 q) 1 (meaningNeg103 q) (meaning1693 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1693 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1693 = true := by
  have hs : count1693 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1693)) (countLit q [-102]) (countLit q [-103]) (count1693 q) 1 (meaningNeg102 q) (meaning1693 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1693 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1694 = true := by
  have hs : count1693 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1694)) (countLit q [-102]) (countLit q [-103]) (count1693 q) 1 1 (meaningNeg102 q) (meaningNeg103 q) (meaning1694 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 1694 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1695 = true := by
  have hs : count1695 q = (countLit q [-100, -101]) + (countLit q [-102, -103]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -103])
  have hm := merge_right (literal (valuationOf q) (1693)) (literal (valuationOf q) (1695)) (countLit q [-100, -101]) (countLit q [-102, -103]) (count1695 q) 1 (meaning1693 q) (meaning1695 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1695 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1696 = true := by
  have hs : count1695 q = (countLit q [-100, -101]) + (countLit q [-102, -103]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -103])
  have hm := merge_right (literal (valuationOf q) (1694)) (literal (valuationOf q) (1696)) (countLit q [-100, -101]) (countLit q [-102, -103]) (count1695 q) 2 (meaning1694 q) (meaning1696 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1696 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1695 = true := by
  have hs : count1695 q = (countLit q [-100, -101]) + (countLit q [-102, -103]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -103])
  have hm := merge_left (literal (valuationOf q) (1691)) (literal (valuationOf q) (1695)) (countLit q [-100, -101]) (countLit q [-102, -103]) (count1695 q) 1 (meaning1691 q) (meaning1695 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1695 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1696 = true := by
  have hs : count1695 q = (countLit q [-100, -101]) + (countLit q [-102, -103]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -103])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1696)) (countLit q [-100, -101]) (countLit q [-102, -103]) (count1695 q) 1 1 (meaning1691 q) (meaning1693 q) (meaning1696 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1693 = false ∨ valuation q 1696 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1697 = true := by
  have hs : count1695 q = (countLit q [-100, -101]) + (countLit q [-102, -103]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -103])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1697)) (countLit q [-100, -101]) (countLit q [-102, -103]) (count1695 q) 1 2 (meaning1691 q) (meaning1694 q) (meaning1697 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1694 = false ∨ valuation q 1697 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1696 = true := by
  have hs : count1695 q = (countLit q [-100, -101]) + (countLit q [-102, -103]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -103])
  have hm := merge_left (literal (valuationOf q) (1692)) (literal (valuationOf q) (1696)) (countLit q [-100, -101]) (countLit q [-102, -103]) (count1695 q) 2 (meaning1692 q) (meaning1696 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1696 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1697 = true := by
  have hs : count1695 q = (countLit q [-100, -101]) + (countLit q [-102, -103]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -103])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1697)) (countLit q [-100, -101]) (countLit q [-102, -103]) (count1695 q) 2 1 (meaning1692 q) (meaning1693 q) (meaning1697 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1693 = false ∨ valuation q 1697 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1698 = true := by
  have hs : count1695 q = (countLit q [-100, -101]) + (countLit q [-102, -103]) := List.countP_append (p := literal q) (l₁ := [-100, -101]) (l₂ := [-102, -103])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1698)) (countLit q [-100, -101]) (countLit q [-102, -103]) (count1695 q) 2 2 (meaning1692 q) (meaning1694 q) (meaning1698 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1694 = false ∨ valuation q 1698 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_right (literal (valuationOf q) (1695)) (literal (valuationOf q) (1699)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 1 (meaning1695 q) (meaning1699 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1699 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_right (literal (valuationOf q) (1696)) (literal (valuationOf q) (1700)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 2 (meaning1696 q) (meaning1700 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1700 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_right (literal (valuationOf q) (1697)) (literal (valuationOf q) (1701)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 3 (meaning1697 q) (meaning1701 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1701 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1702 = true := by
  have hs : count1699 q = (countLit q [-94, -97, -99]) + (countLit q [-100, -101, -102, -103]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99]) (l₂ := [-100, -101, -102, -103])
  have hm := merge_right (literal (valuationOf q) (1698)) (literal (valuationOf q) (1702)) (countLit q [-94, -97, -99]) (countLit q [-100, -101, -102, -103]) (count1699 q) 4 (meaning1698 q) (meaning1702 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1702 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E254.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112254
