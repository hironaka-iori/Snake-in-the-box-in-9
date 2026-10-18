import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1719 = true := by
  have hs : count1718 q = (countLit q [-114, -117]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-114, -117]) (l₂ := [-121, -122])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1719)) (countLit q [-114, -117]) (countLit q [-121, -122]) (count1718 q) 1 1 (meaning1714 q) (meaning1716 q) (meaning1719 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1716 = false ∨ valuation q 1719 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1720 = true := by
  have hs : count1718 q = (countLit q [-114, -117]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-114, -117]) (l₂ := [-121, -122])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1720)) (countLit q [-114, -117]) (countLit q [-121, -122]) (count1718 q) 1 2 (meaning1714 q) (meaning1717 q) (meaning1720 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1717 = false ∨ valuation q 1720 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1719 = true := by
  have hs : count1718 q = (countLit q [-114, -117]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-114, -117]) (l₂ := [-121, -122])
  have hm := merge_left (literal (valuationOf q) (1715)) (literal (valuationOf q) (1719)) (countLit q [-114, -117]) (countLit q [-121, -122]) (count1718 q) 2 (meaning1715 q) (meaning1719 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1719 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1720 = true := by
  have hs : count1718 q = (countLit q [-114, -117]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-114, -117]) (l₂ := [-121, -122])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1720)) (countLit q [-114, -117]) (countLit q [-121, -122]) (count1718 q) 2 1 (meaning1715 q) (meaning1716 q) (meaning1720 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1716 = false ∨ valuation q 1720 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1721 = true := by
  have hs : count1718 q = (countLit q [-114, -117]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-114, -117]) (l₂ := [-121, -122])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1721)) (countLit q [-114, -117]) (countLit q [-121, -122]) (count1718 q) 2 2 (meaning1715 q) (meaning1717 q) (meaning1721 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1717 = false ∨ valuation q 1721 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1722 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1718)) (literal (valuationOf q) (1722)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 1 (meaning1718 q) (meaning1722 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1722 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1723 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1719)) (literal (valuationOf q) (1723)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 2 (meaning1719 q) (meaning1723 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1723 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1724 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1720)) (literal (valuationOf q) (1724)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 3 (meaning1720 q) (meaning1724 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1724 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1725 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1721)) (literal (valuationOf q) (1725)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 4 (meaning1721 q) (meaning1725 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1725 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1722 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_left (literal (valuationOf q) (1710)) (literal (valuationOf q) (1722)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 1 (meaning1710 q) (meaning1722 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1722 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1723 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1723)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 1 1 (meaning1710 q) (meaning1718 q) (meaning1723 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1718 = false ∨ valuation q 1723 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1724)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 1 2 (meaning1710 q) (meaning1719 q) (meaning1724 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1719 = false ∨ valuation q 1724 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1725)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 1 3 (meaning1710 q) (meaning1720 q) (meaning1725 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1720 = false ∨ valuation q 1725 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1726)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 1 4 (meaning1710 q) (meaning1721 q) (meaning1726 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1721 = false ∨ valuation q 1726 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1723 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_left (literal (valuationOf q) (1711)) (literal (valuationOf q) (1723)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 2 (meaning1711 q) (meaning1723 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1723 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1724 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1724)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 2 1 (meaning1711 q) (meaning1718 q) (meaning1724 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1718 = false ∨ valuation q 1724 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1726 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1726)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 2 3 (meaning1711 q) (meaning1720 q) (meaning1726 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1720 = false ∨ valuation q 1726 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1724 = true := by
  have hs : count1722 q = (countLit q [-105, -108, -110, -111]) + (countLit q [-114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110, -111]) (l₂ := [-114, -117, -121, -122])
  have hm := merge_left (literal (valuationOf q) (1712)) (literal (valuationOf q) (1724)) (countLit q [-105, -108, -110, -111]) (countLit q [-114, -117, -121, -122]) (count1722 q) 3 (meaning1712 q) (meaning1724 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1724 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1730 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1722)) (literal (valuationOf q) (1730)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 1 (meaning1722 q) (meaning1730 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1730 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1731 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1723)) (literal (valuationOf q) (1731)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 2 (meaning1723 q) (meaning1731 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1731 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1732 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1724)) (literal (valuationOf q) (1732)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 3 (meaning1724 q) (meaning1732 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1732 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1731 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1731)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 1 1 (meaning1699 q) (meaning1722 q) (meaning1731 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1722 = false ∨ valuation q 1731 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1732 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1732)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 1 2 (meaning1699 q) (meaning1723 q) (meaning1732 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1723 = false ∨ valuation q 1732 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1733 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1733)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 1 3 (meaning1699 q) (meaning1724 q) (meaning1733 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1724 = false ∨ valuation q 1733 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1734)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 1 4 (meaning1699 q) (meaning1725 q) (meaning1734 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1725 = false ∨ valuation q 1734 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1732 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1732)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 2 1 (meaning1700 q) (meaning1722 q) (meaning1732 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1722 = false ∨ valuation q 1732 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1733 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1733)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 2 2 (meaning1700 q) (meaning1723 q) (meaning1733 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1723 = false ∨ valuation q 1733 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1734)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 2 3 (meaning1700 q) (meaning1724 q) (meaning1734 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1724 = false ∨ valuation q 1734 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1735 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1735)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 2 4 (meaning1700 q) (meaning1725 q) (meaning1735 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1725 = false ∨ valuation q 1735 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1736 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1736)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 2 5 (meaning1700 q) (meaning1726 q) (meaning1736 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1726 = false ∨ valuation q 1736 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1732 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_left (literal (valuationOf q) (1701)) (literal (valuationOf q) (1732)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 3 (meaning1701 q) (meaning1732 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1732 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1733 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1733)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 3 1 (meaning1701 q) (meaning1722 q) (meaning1733 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1722 = false ∨ valuation q 1733 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E254.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112254
