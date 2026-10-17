import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1727)) (literal (valuationOf q) (1759)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 5 (meaning1727 q) (meaning1759 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1759 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1760)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 5 1 (meaning1727 q) (meaning1747 q) (meaning1760 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1747 = false ∨ valuation q 1760 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1761)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 5 2 (meaning1727 q) (meaning1748 q) (meaning1761 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1748 = false ∨ valuation q 1761 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1762)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 5 3 (meaning1727 q) (meaning1749 q) (meaning1762 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1749 = false ∨ valuation q 1762 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1763)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 5 4 (meaning1727 q) (meaning1750 q) (meaning1763 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1750 = false ∨ valuation q 1763 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1764)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 5 5 (meaning1727 q) (meaning1751 q) (meaning1764 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1751 = false ∨ valuation q 1764 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1762)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 6 2 (meaning1728 q) (meaning1748 q) (meaning1762 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1748 = false ∨ valuation q 1762 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1763)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 6 3 (meaning1728 q) (meaning1749 q) (meaning1763 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1749 = false ∨ valuation q 1763 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1764 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1764)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 6 4 (meaning1728 q) (meaning1750 q) (meaning1764 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1750 = false ∨ valuation q 1764 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1771 = true := by
  have hs : count1771 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1771)) (countLit q [-96]) (countLit q [-98]) (count1771 q) 1 (meaningNeg98 q) (meaning1771 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1771 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1771 = true := by
  have hs : count1771 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1771)) (countLit q [-96]) (countLit q [-98]) (count1771 q) 1 (meaningNeg96 q) (meaning1771 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1771 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1772 = true := by
  have hs : count1771 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1772)) (countLit q [-96]) (countLit q [-98]) (count1771 q) 1 1 (meaningNeg96 q) (meaningNeg98 q) (meaning1772 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 98 = true ∨ valuation q 1772 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1773 = true := by
  have hs : count1773 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1773)) (countLit q [-100]) (countLit q [-101]) (count1773 q) 1 (meaningNeg101 q) (meaning1773 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1773 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1773 = true := by
  have hs : count1773 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1773)) (countLit q [-100]) (countLit q [-101]) (count1773 q) 1 (meaningNeg100 q) (meaning1773 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1773 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1774 = true := by
  have hs : count1773 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1774)) (countLit q [-100]) (countLit q [-101]) (count1773 q) 1 1 (meaningNeg100 q) (meaningNeg101 q) (meaning1774 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 1774 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1775 = true := by
  have hs : count1775 q = (countLit q [-96, -98]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -101])
  have hm := merge_right (literal (valuationOf q) (1773)) (literal (valuationOf q) (1775)) (countLit q [-96, -98]) (countLit q [-100, -101]) (count1775 q) 1 (meaning1773 q) (meaning1775 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1775 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-96, -98]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -101])
  have hm := merge_right (literal (valuationOf q) (1774)) (literal (valuationOf q) (1776)) (countLit q [-96, -98]) (countLit q [-100, -101]) (count1775 q) 2 (meaning1774 q) (meaning1776 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1776 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1775 = true := by
  have hs : count1775 q = (countLit q [-96, -98]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -101])
  have hm := merge_left (literal (valuationOf q) (1771)) (literal (valuationOf q) (1775)) (countLit q [-96, -98]) (countLit q [-100, -101]) (count1775 q) 1 (meaning1771 q) (meaning1775 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1775 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-96, -98]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1776)) (countLit q [-96, -98]) (countLit q [-100, -101]) (count1775 q) 1 1 (meaning1771 q) (meaning1773 q) (meaning1776 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1773 = false ∨ valuation q 1776 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-96, -98]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1774)) (literal (valuationOf q) (1777)) (countLit q [-96, -98]) (countLit q [-100, -101]) (count1775 q) 1 2 (meaning1771 q) (meaning1774 q) (meaning1777 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1774 = false ∨ valuation q 1777 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-96, -98]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -101])
  have hm := merge_left (literal (valuationOf q) (1772)) (literal (valuationOf q) (1776)) (countLit q [-96, -98]) (countLit q [-100, -101]) (count1775 q) 2 (meaning1772 q) (meaning1776 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1776 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-96, -98]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1777)) (countLit q [-96, -98]) (countLit q [-100, -101]) (count1775 q) 2 1 (meaning1772 q) (meaning1773 q) (meaning1777 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1773 = false ∨ valuation q 1777 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1778 = true := by
  have hs : count1775 q = (countLit q [-96, -98]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1774)) (literal (valuationOf q) (1778)) (countLit q [-96, -98]) (countLit q [-100, -101]) (count1775 q) 2 2 (meaning1772 q) (meaning1774 q) (meaning1778 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1774 = false ∨ valuation q 1778 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1779 = true := by
  have hs : count1779 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1779)) (countLit q [-103]) (countLit q [-105]) (count1779 q) 1 (meaningNeg105 q) (meaning1779 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1779 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1779 = true := by
  have hs : count1779 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1779)) (countLit q [-103]) (countLit q [-105]) (count1779 q) 1 (meaningNeg103 q) (meaning1779 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1779 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1780 = true := by
  have hs : count1779 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1780)) (countLit q [-103]) (countLit q [-105]) (count1779 q) 1 1 (meaningNeg103 q) (meaningNeg105 q) (meaning1780 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 1780 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-106]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1781)) (countLit q [-106]) (countLit q [-109]) (count1781 q) 1 (meaningNeg109 q) (meaning1781 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1781 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-106]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1781)) (countLit q [-106]) (countLit q [-109]) (count1781 q) 1 (meaningNeg106 q) (meaning1781 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1781 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 109 = true ∨ valuationOf q 1782 = true := by
  have hs : count1781 q = (countLit q [-106]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-109])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-109)) (literal (valuationOf q) (1782)) (countLit q [-106]) (countLit q [-109]) (count1781 q) 1 1 (meaningNeg106 q) (meaningNeg109 q) (meaning1782 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 109)) = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 109 = true ∨ valuation q 1782 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1783 = true := by
  have hs : count1783 q = (countLit q [-103, -105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -109])
  have hm := merge_right (literal (valuationOf q) (1781)) (literal (valuationOf q) (1783)) (countLit q [-103, -105]) (countLit q [-106, -109]) (count1783 q) 1 (meaning1781 q) (meaning1783 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1783 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1782 = false ∨ valuationOf q 1784 = true := by
  have hs : count1783 q = (countLit q [-103, -105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -109])
  have hm := merge_right (literal (valuationOf q) (1782)) (literal (valuationOf q) (1784)) (countLit q [-103, -105]) (countLit q [-106, -109]) (count1783 q) 2 (meaning1782 q) (meaning1784 q) hs
  change valuationOf q 1782 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1782 = false ∨ valuation q 1784 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1779 = false ∨ valuationOf q 1783 = true := by
  have hs : count1783 q = (countLit q [-103, -105]) + (countLit q [-106, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -109])
  have hm := merge_left (literal (valuationOf q) (1779)) (literal (valuationOf q) (1783)) (countLit q [-103, -105]) (countLit q [-106, -109]) (count1783 q) 1 (meaning1779 q) (meaning1783 q) hs
  change valuationOf q 1779 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1779 = false ∨ valuation q 1783 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E036.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112036
