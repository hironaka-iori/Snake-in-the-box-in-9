import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec57 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1825 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1572 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1572)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 3 1 (meaning1559 q) (meaning1565 q) (meaning1572 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1825 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1565 = false ∨ valuation q 1572 = true := counterClause1825 (baseVal q)

theorem counterClause1826 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1573 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1573)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 3 2 (meaning1559 q) (meaning1566 q) (meaning1573 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1826 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1566 = false ∨ valuation q 1573 = true := counterClause1826 (baseVal q)

theorem counterClause1827 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1574 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1574)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 3 3 (meaning1559 q) (meaning1567 q) (meaning1574 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1827 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1567 = false ∨ valuation q 1574 = true := counterClause1827 (baseVal q)

theorem counterClause1828 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1572 = true := by
  have hs : count1569 q = (countLit q [-18, -19, -22, -23]) + (countLit q [-25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -22, -23]) (l₂ := [-25, -27, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1560)) (literal (valuationOf q) (1572)) (countLit q [-18, -19, -22, -23]) (countLit q [-25, -27, -29, -31]) (count1569 q) 4 (meaning1560 q) (meaning1572 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1828 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1572 = true := counterClause1828 (baseVal q)

theorem counterClause1829 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1579 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_right (literal (valuationOf q) (1571)) (literal (valuationOf q) (1579)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 3 (meaning1571 q) (meaning1579 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1829 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1579 = true := counterClause1829 (baseVal q)

theorem counterClause1830 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1580 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_right (literal (valuationOf q) (1572)) (literal (valuationOf q) (1580)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 4 (meaning1572 q) (meaning1580 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1830 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1580 = true := counterClause1830 (baseVal q)

theorem counterClause1831 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1579 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1579)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 1 2 (meaning1545 q) (meaning1570 q) (meaning1579 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1831 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1570 = false ∨ valuation q 1579 = true := counterClause1831 (baseVal q)

theorem counterClause1832 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1580 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1580)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 1 3 (meaning1545 q) (meaning1571 q) (meaning1580 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1832 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1571 = false ∨ valuation q 1580 = true := counterClause1832 (baseVal q)

theorem counterClause1833 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1581 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1581)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 1 4 (meaning1545 q) (meaning1572 q) (meaning1581 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1833 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1572 = false ∨ valuation q 1581 = true := counterClause1833 (baseVal q)

theorem counterClause1834 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1579 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1579)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 2 1 (meaning1546 q) (meaning1569 q) (meaning1579 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1834 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1569 = false ∨ valuation q 1579 = true := counterClause1834 (baseVal q)

theorem counterClause1835 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1580 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1580)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 2 2 (meaning1546 q) (meaning1570 q) (meaning1580 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1835 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1570 = false ∨ valuation q 1580 = true := counterClause1835 (baseVal q)

theorem counterClause1836 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1581 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1581)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 2 3 (meaning1546 q) (meaning1571 q) (meaning1581 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1836 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1571 = false ∨ valuation q 1581 = true := counterClause1836 (baseVal q)

theorem counterClause1837 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1582 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1582)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 2 4 (meaning1546 q) (meaning1572 q) (meaning1582 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1837 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1572 = false ∨ valuation q 1582 = true := counterClause1837 (baseVal q)

theorem counterClause1838 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1580 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1580)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 3 1 (meaning1547 q) (meaning1569 q) (meaning1580 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1838 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1569 = false ∨ valuation q 1580 = true := counterClause1838 (baseVal q)

theorem counterClause1839 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1581 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1581)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 3 2 (meaning1547 q) (meaning1570 q) (meaning1581 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1839 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1570 = false ∨ valuation q 1581 = true := counterClause1839 (baseVal q)

theorem counterClause1840 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1582 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1582)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 3 3 (meaning1547 q) (meaning1571 q) (meaning1582 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1840 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1571 = false ∨ valuation q 1582 = true := counterClause1840 (baseVal q)

theorem counterClause1841 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1583 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1583)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 3 4 (meaning1547 q) (meaning1572 q) (meaning1583 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1841 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1572 = false ∨ valuation q 1583 = true := counterClause1841 (baseVal q)

theorem counterClause1842 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1584 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1584)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 3 5 (meaning1547 q) (meaning1573 q) (meaning1584 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1842 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1573 = false ∨ valuation q 1584 = true := counterClause1842 (baseVal q)

theorem counterClause1843 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1585 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1585)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 3 6 (meaning1547 q) (meaning1574 q) (meaning1585 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1843 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1574 = false ∨ valuation q 1585 = true := counterClause1843 (baseVal q)

theorem counterClause1844 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1581 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1581)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 4 1 (meaning1548 q) (meaning1569 q) (meaning1581 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1844 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1569 = false ∨ valuation q 1581 = true := counterClause1844 (baseVal q)

theorem counterClause1845 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1582 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1582)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 4 2 (meaning1548 q) (meaning1570 q) (meaning1582 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1845 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1570 = false ∨ valuation q 1582 = true := counterClause1845 (baseVal q)

theorem counterClause1846 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1583 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1583)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 4 3 (meaning1548 q) (meaning1571 q) (meaning1583 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1846 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1571 = false ∨ valuation q 1583 = true := counterClause1846 (baseVal q)

theorem counterClause1847 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1584 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1584)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 4 4 (meaning1548 q) (meaning1572 q) (meaning1584 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1847 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1572 = false ∨ valuation q 1584 = true := counterClause1847 (baseVal q)

theorem counterClause1848 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1582 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1582)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 5 1 (meaning1549 q) (meaning1569 q) (meaning1582 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1848 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1569 = false ∨ valuation q 1582 = true := counterClause1848 (baseVal q)

theorem counterClause1849 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1583 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1583)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 5 2 (meaning1549 q) (meaning1570 q) (meaning1583 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1849 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1570 = false ∨ valuation q 1583 = true := counterClause1849 (baseVal q)

theorem counterClause1850 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1584 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) + (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17]) (l₂ := [-18, -19, -22, -23, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1584)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17]) (countLit q [-18, -19, -22, -23, -25, -27, -29, -31]) (count1577 q) 5 3 (meaning1549 q) (meaning1571 q) (meaning1584 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1850 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1571 = false ∨ valuation q 1584 = true := counterClause1850 (baseVal q)

theorem counterClause1851 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1593)) (countLit q [-33]) (countLit q [-35]) (count1593 q) 1 (meaningNeg35 q) (meaning1593 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1851 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1593 = true := counterClause1851 (baseVal q)

theorem counterClause1852 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1593)) (countLit q [-33]) (countLit q [-35]) (count1593 q) 1 (meaningNeg33 q) (meaning1593 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1852 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1593 = true := counterClause1852 (baseVal q)

theorem counterClause1853 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1595 = true := by
  have hs : count1595 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1595)) (countLit q [-37]) (countLit q [-38]) (count1595 q) 1 (meaningNeg38 q) (meaning1595 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1853 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1595 = true := counterClause1853 (baseVal q)

theorem counterClause1854 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1595 = true := by
  have hs : count1595 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1595)) (countLit q [-37]) (countLit q [-38]) (count1595 q) 1 (meaningNeg37 q) (meaning1595 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1854 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1595 = true := counterClause1854 (baseVal q)

theorem counterClause1855 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1596)) (countLit q [-37]) (countLit q [-38]) (count1595 q) 1 1 (meaningNeg37 q) (meaningNeg38 q) (meaning1596 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1855 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 1596 = true := counterClause1855 (baseVal q)

theorem counterClause1856 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1597 = true := by
  have hs : count1597 q = (countLit q [-33, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (1595)) (literal (valuationOf q) (1597)) (countLit q [-33, -35]) (countLit q [-37, -38]) (count1597 q) 1 (meaning1595 q) (meaning1597 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1856 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1597 = true := counterClause1856 (baseVal q)

theorem block57 (q : Snake 81) (h : Conditions q) : B112E260.Block57 (valuation q) :=
  ⟨clause1825 q h, clause1826 q h, clause1827 q h, clause1828 q h, clause1829 q h, clause1830 q h, clause1831 q h, clause1832 q h, clause1833 q h, clause1834 q h, clause1835 q h, clause1836 q h, clause1837 q h, clause1838 q h, clause1839 q h, clause1840 q h, clause1841 q h, clause1842 q h, clause1843 q h, clause1844 q h, clause1845 q h, clause1846 q h, clause1847 q h, clause1848 q h, clause1849 q h, clause1850 q h, clause1851 q h, clause1852 q h, clause1853 q h, clause1854 q h, clause1855 q h, clause1856 q h⟩

end
end Snake9.Regrowth.E112260
