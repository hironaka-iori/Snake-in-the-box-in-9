import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1676 = true := by
  have hs : count1675 q = (countLit q [-114, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1676)) (countLit q [-114, -116]) (countLit q [-117, -119]) (count1675 q) 1 1 (meaning1671 q) (meaning1673 q) (meaning1676 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1673 = false ∨ valuation q 1676 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1677 = true := by
  have hs : count1675 q = (countLit q [-114, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1677)) (countLit q [-114, -116]) (countLit q [-117, -119]) (count1675 q) 1 2 (meaning1671 q) (meaning1674 q) (meaning1677 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1674 = false ∨ valuation q 1677 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1676 = true := by
  have hs : count1675 q = (countLit q [-114, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -119])
  have hm := merge_left (literal (valuationOf q) (1672)) (literal (valuationOf q) (1676)) (countLit q [-114, -116]) (countLit q [-117, -119]) (count1675 q) 2 (meaning1672 q) (meaning1676 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1676 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1677 = true := by
  have hs : count1675 q = (countLit q [-114, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1677)) (countLit q [-114, -116]) (countLit q [-117, -119]) (count1675 q) 2 1 (meaning1672 q) (meaning1673 q) (meaning1677 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1673 = false ∨ valuation q 1677 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1678 = true := by
  have hs : count1675 q = (countLit q [-114, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1678)) (countLit q [-114, -116]) (countLit q [-117, -119]) (count1675 q) 2 2 (meaning1672 q) (meaning1674 q) (meaning1678 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1674 = false ∨ valuation q 1678 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1679 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_right (literal (valuationOf q) (1675)) (literal (valuationOf q) (1679)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 1 (meaning1675 q) (meaning1679 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1679 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_right (literal (valuationOf q) (1676)) (literal (valuationOf q) (1680)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 2 (meaning1676 q) (meaning1680 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1680 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1681 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_right (literal (valuationOf q) (1677)) (literal (valuationOf q) (1681)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 3 (meaning1677 q) (meaning1681 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1681 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1680)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 1 1 (meaning1667 q) (meaning1675 q) (meaning1680 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1675 = false ∨ valuation q 1680 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1681 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1676)) (literal (valuationOf q) (1681)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 1 2 (meaning1667 q) (meaning1676 q) (meaning1681 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1676 = false ∨ valuation q 1681 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1682 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1682)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 1 3 (meaning1667 q) (meaning1677 q) (meaning1682 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1677 = false ∨ valuation q 1682 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1683 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1683)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 1 4 (meaning1667 q) (meaning1678 q) (meaning1683 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1678 = false ∨ valuation q 1683 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1681 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1681)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 2 1 (meaning1668 q) (meaning1675 q) (meaning1681 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1675 = false ∨ valuation q 1681 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1682 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1676)) (literal (valuationOf q) (1682)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 2 2 (meaning1668 q) (meaning1676 q) (meaning1682 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1676 = false ∨ valuation q 1682 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1683 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1683)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 2 3 (meaning1668 q) (meaning1677 q) (meaning1683 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1677 = false ∨ valuation q 1683 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1684 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1684)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 2 4 (meaning1668 q) (meaning1678 q) (meaning1684 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1678 = false ∨ valuation q 1684 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1681 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_left (literal (valuationOf q) (1669)) (literal (valuationOf q) (1681)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 3 (meaning1669 q) (meaning1681 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1681 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1682 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1682)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 3 1 (meaning1669 q) (meaning1675 q) (meaning1682 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1675 = false ∨ valuation q 1682 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1683 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1676)) (literal (valuationOf q) (1683)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 3 2 (meaning1669 q) (meaning1676 q) (meaning1683 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1676 = false ∨ valuation q 1683 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1684 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1684)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 3 3 (meaning1669 q) (meaning1677 q) (meaning1684 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1677 = false ∨ valuation q 1684 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1682 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_left (literal (valuationOf q) (1670)) (literal (valuationOf q) (1682)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 4 (meaning1670 q) (meaning1682 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1682 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1683 = true := by
  have hs : count1679 q = (countLit q [-106, -108, -109, -111]) + (countLit q [-114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-106, -108, -109, -111]) (l₂ := [-114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1683)) (countLit q [-106, -108, -109, -111]) (countLit q [-114, -116, -117, -119]) (count1679 q) 4 1 (meaning1670 q) (meaning1675 q) (meaning1683 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1675 = false ∨ valuation q 1683 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1690 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_right (literal (valuationOf q) (1682)) (literal (valuationOf q) (1690)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 4 (meaning1682 q) (meaning1690 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1690 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_right (literal (valuationOf q) (1684)) (literal (valuationOf q) (1692)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 6 (meaning1684 q) (meaning1692 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1692 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1689 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1689)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 1 2 (meaning1655 q) (meaning1680 q) (meaning1689 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1680 = false ∨ valuation q 1689 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1690 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1690)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 1 3 (meaning1655 q) (meaning1681 q) (meaning1690 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1681 = false ∨ valuation q 1690 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1691 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1691)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 1 4 (meaning1655 q) (meaning1682 q) (meaning1691 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1682 = false ∨ valuation q 1691 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1692)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 1 5 (meaning1655 q) (meaning1683 q) (meaning1692 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1683 = false ∨ valuation q 1692 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1689 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1689)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 2 1 (meaning1656 q) (meaning1679 q) (meaning1689 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1679 = false ∨ valuation q 1689 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1690 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1690)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 2 2 (meaning1656 q) (meaning1680 q) (meaning1690 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1680 = false ∨ valuation q 1690 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1691 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1691)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 2 3 (meaning1656 q) (meaning1681 q) (meaning1691 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1681 = false ∨ valuation q 1691 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1692 = true := by
  have hs : count1687 q = (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) + (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98, -101, -102, -103, -105]) (l₂ := [-106, -108, -109, -111, -114, -116, -117, -119])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1692)) (countLit q [-90, -91, -97, -98, -101, -102, -103, -105]) (countLit q [-106, -108, -109, -111, -114, -116, -117, -119]) (count1687 q) 2 4 (meaning1656 q) (meaning1682 q) (meaning1692 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1682 = false ∨ valuation q 1692 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E004.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112004
