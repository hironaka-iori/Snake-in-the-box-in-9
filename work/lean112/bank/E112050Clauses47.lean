import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1760)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 5 1 (meaning1727 q) (meaning1747 q) (meaning1760 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1747 = false ∨ valuation q 1760 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1761)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 5 2 (meaning1727 q) (meaning1748 q) (meaning1761 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1748 = false ∨ valuation q 1761 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1762)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 5 3 (meaning1727 q) (meaning1749 q) (meaning1762 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1749 = false ∨ valuation q 1762 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1763)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 5 4 (meaning1727 q) (meaning1750 q) (meaning1763 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1750 = false ∨ valuation q 1763 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1764)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 5 5 (meaning1727 q) (meaning1751 q) (meaning1764 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1751 = false ∨ valuation q 1764 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1765 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1765)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 5 6 (meaning1727 q) (meaning1752 q) (meaning1765 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1752 = false ∨ valuation q 1765 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1761)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 6 1 (meaning1728 q) (meaning1747 q) (meaning1761 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1747 = false ∨ valuation q 1761 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1762)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 6 2 (meaning1728 q) (meaning1748 q) (meaning1762 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1748 = false ∨ valuation q 1762 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1763)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 6 3 (meaning1728 q) (meaning1749 q) (meaning1763 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1749 = false ∨ valuation q 1763 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1764 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1764)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 6 4 (meaning1728 q) (meaning1750 q) (meaning1764 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1750 = false ∨ valuation q 1764 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1765 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1765)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 6 5 (meaning1728 q) (meaning1751 q) (meaning1765 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1751 = false ∨ valuation q 1765 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1766 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1766)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 6 6 (meaning1728 q) (meaning1752 q) (meaning1766 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1752 = false ∨ valuation q 1766 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1764 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1764)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 7 3 (meaning1729 q) (meaning1749 q) (meaning1764 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1749 = false ∨ valuation q 1764 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1771 = true := by
  have hs : count1771 q = (countLit q [-96]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1771)) (countLit q [-96]) (countLit q [-97]) (count1771 q) 1 (meaningNeg97 q) (meaning1771 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1771 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1771 = true := by
  have hs : count1771 q = (countLit q [-96]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1771)) (countLit q [-96]) (countLit q [-97]) (count1771 q) 1 (meaningNeg96 q) (meaning1771 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1771 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1772 = true := by
  have hs : count1771 q = (countLit q [-96]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1772)) (countLit q [-96]) (countLit q [-97]) (count1771 q) 1 1 (meaningNeg96 q) (meaningNeg97 q) (meaning1772 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 97 = true ∨ valuation q 1772 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1773 = true := by
  have hs : count1773 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1773)) (countLit q [-100]) (countLit q [-101]) (count1773 q) 1 (meaningNeg101 q) (meaning1773 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1773 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1773 = true := by
  have hs : count1773 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1773)) (countLit q [-100]) (countLit q [-101]) (count1773 q) 1 (meaningNeg100 q) (meaning1773 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1773 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1774 = true := by
  have hs : count1773 q = (countLit q [-100]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1774)) (countLit q [-100]) (countLit q [-101]) (count1773 q) 1 1 (meaningNeg100 q) (meaningNeg101 q) (meaning1774 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 1774 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1775 = true := by
  have hs : count1775 q = (countLit q [-96, -97]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-100, -101])
  have hm := merge_right (literal (valuationOf q) (1773)) (literal (valuationOf q) (1775)) (countLit q [-96, -97]) (countLit q [-100, -101]) (count1775 q) 1 (meaning1773 q) (meaning1775 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1775 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1774 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-96, -97]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-100, -101])
  have hm := merge_right (literal (valuationOf q) (1774)) (literal (valuationOf q) (1776)) (countLit q [-96, -97]) (countLit q [-100, -101]) (count1775 q) 2 (meaning1774 q) (meaning1776 q) hs
  change valuationOf q 1774 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1774 = false ∨ valuation q 1776 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1775 = true := by
  have hs : count1775 q = (countLit q [-96, -97]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-100, -101])
  have hm := merge_left (literal (valuationOf q) (1771)) (literal (valuationOf q) (1775)) (countLit q [-96, -97]) (countLit q [-100, -101]) (count1775 q) 1 (meaning1771 q) (meaning1775 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1775 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-96, -97]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1776)) (countLit q [-96, -97]) (countLit q [-100, -101]) (count1775 q) 1 1 (meaning1771 q) (meaning1773 q) (meaning1776 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1773 = false ∨ valuation q 1776 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-96, -97]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (1771)) (literal (valuationOf q) (1774)) (literal (valuationOf q) (1777)) (countLit q [-96, -97]) (countLit q [-100, -101]) (count1775 q) 1 2 (meaning1771 q) (meaning1774 q) (meaning1777 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1774 = false ∨ valuation q 1777 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1776 = true := by
  have hs : count1775 q = (countLit q [-96, -97]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-100, -101])
  have hm := merge_left (literal (valuationOf q) (1772)) (literal (valuationOf q) (1776)) (countLit q [-96, -97]) (countLit q [-100, -101]) (count1775 q) 2 (meaning1772 q) (meaning1776 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1776 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1777 = true := by
  have hs : count1775 q = (countLit q [-96, -97]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1773)) (literal (valuationOf q) (1777)) (countLit q [-96, -97]) (countLit q [-100, -101]) (count1775 q) 2 1 (meaning1772 q) (meaning1773 q) (meaning1777 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1773 = false ∨ valuationOf q 1777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1773 = false ∨ valuation q 1777 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1778 = true := by
  have hs : count1775 q = (countLit q [-96, -97]) + (countLit q [-100, -101]) := List.countP_append (p := literal q) (l₁ := [-96, -97]) (l₂ := [-100, -101])
  have hm := merge_two (literal (valuationOf q) (1772)) (literal (valuationOf q) (1774)) (literal (valuationOf q) (1778)) (countLit q [-96, -97]) (countLit q [-100, -101]) (count1775 q) 2 2 (meaning1772 q) (meaning1774 q) (meaning1778 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1774 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1774 = false ∨ valuation q 1778 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1779 = true := by
  have hs : count1779 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1779)) (countLit q [-103]) (countLit q [-104]) (count1779 q) 1 (meaningNeg104 q) (meaning1779 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1779 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1779 = true := by
  have hs : count1779 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1779)) (countLit q [-103]) (countLit q [-104]) (count1779 q) 1 (meaningNeg103 q) (meaning1779 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1779 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1780 = true := by
  have hs : count1779 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1780)) (countLit q [-103]) (countLit q [-104]) (count1779 q) 1 1 (meaningNeg103 q) (meaningNeg104 q) (meaning1780 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 1780 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1781)) (countLit q [-108]) (countLit q [-109]) (count1781 q) 1 (meaningNeg109 q) (meaning1781 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1781 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1781 = true := by
  have hs : count1781 q = (countLit q [-108]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-108)) (literal (valuationOf q) (1781)) (countLit q [-108]) (countLit q [-109]) (count1781 q) 1 (meaningNeg108 q) (meaning1781 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1781 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E050.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112050
