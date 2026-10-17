import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1762)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 3 5 (meaning1725 q) (meaning1751 q) (meaning1762 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1751 = false ∨ valuation q 1762 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1759)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 4 1 (meaning1726 q) (meaning1747 q) (meaning1759 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1747 = false ∨ valuation q 1759 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1760)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 4 2 (meaning1726 q) (meaning1748 q) (meaning1760 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1748 = false ∨ valuation q 1760 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1761)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 4 3 (meaning1726 q) (meaning1749 q) (meaning1761 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1749 = false ∨ valuation q 1761 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1762)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 4 4 (meaning1726 q) (meaning1750 q) (meaning1762 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1750 = false ∨ valuation q 1762 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1763)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 4 5 (meaning1726 q) (meaning1751 q) (meaning1763 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1751 = false ∨ valuation q 1763 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1760)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 5 1 (meaning1727 q) (meaning1747 q) (meaning1760 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1747 = false ∨ valuation q 1760 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1761)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 5 2 (meaning1727 q) (meaning1748 q) (meaning1761 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1748 = false ∨ valuation q 1761 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1762)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 5 3 (meaning1727 q) (meaning1749 q) (meaning1762 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1749 = false ∨ valuation q 1762 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1763)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 5 4 (meaning1727 q) (meaning1750 q) (meaning1763 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1750 = false ∨ valuation q 1763 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1764)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 5 5 (meaning1727 q) (meaning1751 q) (meaning1764 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1751 = false ∨ valuation q 1764 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1761)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 6 1 (meaning1728 q) (meaning1747 q) (meaning1761 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1747 = false ∨ valuation q 1761 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1762)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 6 2 (meaning1728 q) (meaning1748 q) (meaning1762 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1748 = false ∨ valuation q 1762 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1763)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 6 3 (meaning1728 q) (meaning1749 q) (meaning1763 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1749 = false ∨ valuation q 1763 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1762)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 7 1 (meaning1729 q) (meaning1747 q) (meaning1762 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1747 = false ∨ valuation q 1762 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1779 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1779)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 1 8 (meaning1691 q) (meaning1762 q) (meaning1779 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1762 = false ∨ valuation q 1779 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1778 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1778)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 2 6 (meaning1692 q) (meaning1760 q) (meaning1778 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1760 = false ∨ valuation q 1778 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1779 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1779)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 2 7 (meaning1692 q) (meaning1761 q) (meaning1779 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1761 = false ∨ valuation q 1779 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1692 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1781 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1692)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 2 9 (meaning1692 q) (meaning1763 q) (meaning1781 q) hs
  change valuationOf q 1692 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1692 = false ∨ valuation q 1763 = false ∨ valuation q 1781 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1778 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1778)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 3 5 (meaning1693 q) (meaning1759 q) (meaning1778 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1759 = false ∨ valuation q 1778 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1779 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1779)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 3 6 (meaning1693 q) (meaning1760 q) (meaning1779 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1760 = false ∨ valuation q 1779 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1780 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1780)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 3 7 (meaning1693 q) (meaning1761 q) (meaning1780 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1761 = false ∨ valuation q 1780 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1781 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 3 8 (meaning1693 q) (meaning1762 q) (meaning1781 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1762 = false ∨ valuation q 1781 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 3 9 (meaning1693 q) (meaning1763 q) (meaning1782 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1763 = false ∨ valuation q 1782 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1693 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1693)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 3 10 (meaning1693 q) (meaning1764 q) (meaning1783 q) hs
  change valuationOf q 1693 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1693 = false ∨ valuation q 1764 = false ∨ valuation q 1783 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1779 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1779)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 4 5 (meaning1694 q) (meaning1759 q) (meaning1779 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1759 = false ∨ valuation q 1779 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1780 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1780)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 4 6 (meaning1694 q) (meaning1760 q) (meaning1780 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1760 = false ∨ valuation q 1780 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1781 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 4 7 (meaning1694 q) (meaning1761 q) (meaning1781 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1761 = false ∨ valuation q 1781 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 4 8 (meaning1694 q) (meaning1762 q) (meaning1782 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1762 = false ∨ valuation q 1782 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 4 9 (meaning1694 q) (meaning1763 q) (meaning1783 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1763 = false ∨ valuation q 1783 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1779 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1779)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 5 4 (meaning1695 q) (meaning1758 q) (meaning1779 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1758 = false ∨ valuation q 1779 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1780 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1780)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 5 5 (meaning1695 q) (meaning1759 q) (meaning1780 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1759 = false ∨ valuation q 1780 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E186.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112186
