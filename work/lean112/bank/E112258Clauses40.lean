import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1677 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1650)) (literal (valuationOf q) (1677)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 6 (meaning1650 q) (meaning1677 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1677 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1678 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1678)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 6 1 (meaning1650 q) (meaning1665 q) (meaning1678 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1665 = false ∨ valuation q 1678 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1679 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1679)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 6 2 (meaning1650 q) (meaning1666 q) (meaning1679 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1666 = false ∨ valuation q 1679 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1680 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1680)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 6 3 (meaning1650 q) (meaning1667 q) (meaning1680 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1667 = false ∨ valuation q 1680 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1686 = true := by
  have hs : count1686 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1686)) (countLit q [-93]) (countLit q [-94]) (count1686 q) 1 (meaningNeg94 q) (meaning1686 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1686 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1686 = true := by
  have hs : count1686 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1686)) (countLit q [-93]) (countLit q [-94]) (count1686 q) 1 (meaningNeg93 q) (meaning1686 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1686 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1687 = true := by
  have hs : count1686 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1687)) (countLit q [-93]) (countLit q [-94]) (count1686 q) 1 1 (meaningNeg93 q) (meaningNeg94 q) (meaning1687 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 1687 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1688 = true := by
  have hs : count1688 q = (countLit q [-90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1686)) (literal (valuationOf q) (1688)) (countLit q [-90]) (countLit q [-93, -94]) (count1688 q) 1 (meaning1686 q) (meaning1688 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1688 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1689 = true := by
  have hs : count1688 q = (countLit q [-90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1687)) (literal (valuationOf q) (1689)) (countLit q [-90]) (countLit q [-93, -94]) (count1688 q) 2 (meaning1687 q) (meaning1689 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1689 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1688 = true := by
  have hs : count1688 q = (countLit q [-90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -94])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1688)) (countLit q [-90]) (countLit q [-93, -94]) (count1688 q) 1 (meaningNeg90 q) (meaning1688 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1688 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1686 = false ∨ valuationOf q 1689 = true := by
  have hs : count1688 q = (countLit q [-90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1689)) (countLit q [-90]) (countLit q [-93, -94]) (count1688 q) 1 1 (meaningNeg90 q) (meaning1686 q) (meaning1689 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1686 = false ∨ valuation q 1689 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1687 = false ∨ valuationOf q 1690 = true := by
  have hs : count1688 q = (countLit q [-90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1690)) (countLit q [-90]) (countLit q [-93, -94]) (count1688 q) 1 2 (meaningNeg90 q) (meaning1687 q) (meaning1690 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1687 = false ∨ valuation q 1690 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1691 = true := by
  have hs : count1691 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1691)) (countLit q [-98]) (countLit q [-99]) (count1691 q) 1 (meaningNeg99 q) (meaning1691 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1691 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1691 = true := by
  have hs : count1691 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1691)) (countLit q [-98]) (countLit q [-99]) (count1691 q) 1 (meaningNeg98 q) (meaning1691 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1691 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1692 = true := by
  have hs : count1691 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1692)) (countLit q [-98]) (countLit q [-99]) (count1691 q) 1 1 (meaningNeg98 q) (meaningNeg99 q) (meaning1692 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 1692 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1693 = true := by
  have hs : count1693 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1693)) (countLit q [-102]) (countLit q [-105]) (count1693 q) 1 (meaningNeg105 q) (meaning1693 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1693 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1693 = true := by
  have hs : count1693 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1693)) (countLit q [-102]) (countLit q [-105]) (count1693 q) 1 (meaningNeg102 q) (meaning1693 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1693 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1694 = true := by
  have hs : count1693 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1694)) (countLit q [-102]) (countLit q [-105]) (count1693 q) 1 1 (meaningNeg102 q) (meaningNeg105 q) (meaning1694 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 1694 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1695 = true := by
  have hs : count1695 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_right (literal (valuationOf q) (1693)) (literal (valuationOf q) (1695)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1695 q) 1 (meaning1693 q) (meaning1695 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1695 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1696 = true := by
  have hs : count1695 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_right (literal (valuationOf q) (1694)) (literal (valuationOf q) (1696)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1695 q) 2 (meaning1694 q) (meaning1696 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1696 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1695 = true := by
  have hs : count1695 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_left (literal (valuationOf q) (1691)) (literal (valuationOf q) (1695)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1695 q) 1 (meaning1691 q) (meaning1695 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1695 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1696 = true := by
  have hs : count1695 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1696)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1695 q) 1 1 (meaning1691 q) (meaning1693 q) (meaning1696 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1693 = false ∨ valuation q 1696 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1697 = true := by
  have hs : count1695 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1697)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1695 q) 1 2 (meaning1691 q) (meaning1694 q) (meaning1697 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1694 = false ∨ valuation q 1697 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1696 = true := by
  have hs : count1695 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_left (literal (valuationOf q) (1692)) (literal (valuationOf q) (1696)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1695 q) 2 (meaning1692 q) (meaning1696 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1696 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1697 = true := by
  have hs : count1695 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1697)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1695 q) 2 1 (meaning1692 q) (meaning1693 q) (meaning1697 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1693 = false ∨ valuation q 1697 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1698 = true := by
  have hs : count1695 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1698)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1695 q) 2 2 (meaning1692 q) (meaning1694 q) (meaning1698 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1694 = false ∨ valuation q 1698 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_right (literal (valuationOf q) (1695)) (literal (valuationOf q) (1699)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 1 (meaning1695 q) (meaning1699 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1699 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_right (literal (valuationOf q) (1696)) (literal (valuationOf q) (1700)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 2 (meaning1696 q) (meaning1700 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1700 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_right (literal (valuationOf q) (1697)) (literal (valuationOf q) (1701)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 3 (meaning1697 q) (meaning1701 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1701 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1702 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_right (literal (valuationOf q) (1698)) (literal (valuationOf q) (1702)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 4 (meaning1698 q) (meaning1702 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1702 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_left (literal (valuationOf q) (1688)) (literal (valuationOf q) (1699)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 1 (meaning1688 q) (meaning1699 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1699 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1700)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 1 1 (meaning1688 q) (meaning1695 q) (meaning1700 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1695 = false ∨ valuation q 1700 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E258.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112258
