import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec59 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1889 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-47]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1617)) (countLit q [-47]) (countLit q [-52]) (count1617 q) 1 (meaningNeg47 q) (meaning1617 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1889 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1617 = true := counterClause1889 (baseVal q)

theorem counterClause1890 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-47]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1618)) (countLit q [-47]) (countLit q [-52]) (count1617 q) 1 1 (meaningNeg47 q) (meaningNeg52 q) (meaning1618 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1890 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 52 = true ∨ valuation q 1618 = true := counterClause1890 (baseVal q)

theorem counterClause1891 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1619)) (countLit q [-53]) (countLit q [-54]) (count1619 q) 1 (meaningNeg54 q) (meaning1619 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1891 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1619 = true := counterClause1891 (baseVal q)

theorem counterClause1892 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1619)) (countLit q [-53]) (countLit q [-54]) (count1619 q) 1 (meaningNeg53 q) (meaning1619 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1892 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1619 = true := counterClause1892 (baseVal q)

theorem counterClause1893 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-47, -52]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -52]) (l₂ := [-53, -54])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1621)) (countLit q [-47, -52]) (countLit q [-53, -54]) (count1621 q) 1 (meaning1619 q) (meaning1621 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1893 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1621 = true := counterClause1893 (baseVal q)

theorem counterClause1894 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-47, -52]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -52]) (l₂ := [-53, -54])
  have hm := merge_left (literal (valuationOf q) (1617)) (literal (valuationOf q) (1621)) (countLit q [-47, -52]) (countLit q [-53, -54]) (count1621 q) 1 (meaning1617 q) (meaning1621 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1894 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1621 = true := counterClause1894 (baseVal q)

theorem counterClause1895 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-47, -52]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -52]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1622)) (countLit q [-47, -52]) (countLit q [-53, -54]) (count1621 q) 1 1 (meaning1617 q) (meaning1619 q) (meaning1622 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1895 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = false ∨ valuation q 1622 = true := counterClause1895 (baseVal q)

theorem counterClause1896 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-47, -52]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -52]) (l₂ := [-53, -54])
  have hm := merge_left (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-47, -52]) (countLit q [-53, -54]) (count1621 q) 2 (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1896 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1622 = true := counterClause1896 (baseVal q)

theorem counterClause1897 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1621 q = (countLit q [-47, -52]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-47, -52]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-47, -52]) (countLit q [-53, -54]) (count1621 q) 2 1 (meaning1618 q) (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1897 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1619 = false ∨ valuation q 1623 = true := counterClause1897 (baseVal q)

theorem counterClause1898 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1625)) (countLit q [-55]) (countLit q [-57]) (count1625 q) 1 (meaningNeg57 q) (meaning1625 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1898 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1625 = true := counterClause1898 (baseVal q)

theorem counterClause1899 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1625)) (countLit q [-55]) (countLit q [-57]) (count1625 q) 1 (meaningNeg55 q) (meaning1625 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1899 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1625 = true := counterClause1899 (baseVal q)

theorem counterClause1900 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1626)) (countLit q [-55]) (countLit q [-57]) (count1625 q) 1 1 (meaningNeg55 q) (meaningNeg57 q) (meaning1626 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1900 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 1626 = true := counterClause1900 (baseVal q)

theorem counterClause1901 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1627 = true := by
  have hs : count1627 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (1627)) (countLit q [-59]) (countLit q [-61]) (count1627 q) 1 (meaningNeg61 q) (meaning1627 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1901 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1627 = true := counterClause1901 (baseVal q)

theorem counterClause1902 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1627 = true := by
  have hs : count1627 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1627)) (countLit q [-59]) (countLit q [-61]) (count1627 q) 1 (meaningNeg59 q) (meaning1627 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1902 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1627 = true := counterClause1902 (baseVal q)

theorem counterClause1903 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 61 = true ∨ valuationOf q 1628 = true := by
  have hs : count1627 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-61)) (literal (valuationOf q) (1628)) (countLit q [-59]) (countLit q [-61]) (count1627 q) 1 1 (meaningNeg59 q) (meaningNeg61 q) (meaning1628 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 61)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1903 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 61 = true ∨ valuation q 1628 = true := counterClause1903 (baseVal q)

theorem counterClause1904 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1629 = true := by
  have hs : count1629 q = (countLit q [-58]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -61])
  have hm := merge_right (literal (valuationOf q) (1627)) (literal (valuationOf q) (1629)) (countLit q [-58]) (countLit q [-59, -61]) (count1629 q) 1 (meaning1627 q) (meaning1629 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1904 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1629 = true := counterClause1904 (baseVal q)

theorem counterClause1905 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1630 = true := by
  have hs : count1629 q = (countLit q [-58]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -61])
  have hm := merge_right (literal (valuationOf q) (1628)) (literal (valuationOf q) (1630)) (countLit q [-58]) (countLit q [-59, -61]) (count1629 q) 2 (meaning1628 q) (meaning1630 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1905 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1630 = true := counterClause1905 (baseVal q)

theorem counterClause1906 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1629 = true := by
  have hs : count1629 q = (countLit q [-58]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -61])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1629)) (countLit q [-58]) (countLit q [-59, -61]) (count1629 q) 1 (meaningNeg58 q) (meaning1629 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1906 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1629 = true := counterClause1906 (baseVal q)

theorem counterClause1907 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1627 = false ∨ valuationOf q 1630 = true := by
  have hs : count1629 q = (countLit q [-58]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -61])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1630)) (countLit q [-58]) (countLit q [-59, -61]) (count1629 q) 1 1 (meaningNeg58 q) (meaning1627 q) (meaning1630 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1907 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1627 = false ∨ valuation q 1630 = true := counterClause1907 (baseVal q)

theorem counterClause1908 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-55, -57]) + (countLit q [-58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1629)) (literal (valuationOf q) (1632)) (countLit q [-55, -57]) (countLit q [-58, -59, -61]) (count1632 q) 1 (meaning1629 q) (meaning1632 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1908 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1632 = true := counterClause1908 (baseVal q)

theorem counterClause1909 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-55, -57]) + (countLit q [-58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1630)) (literal (valuationOf q) (1633)) (countLit q [-55, -57]) (countLit q [-58, -59, -61]) (count1632 q) 2 (meaning1630 q) (meaning1633 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1909 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1633 = true := counterClause1909 (baseVal q)

theorem counterClause1910 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-55, -57]) + (countLit q [-58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -59, -61])
  have hm := merge_left (literal (valuationOf q) (1625)) (literal (valuationOf q) (1632)) (countLit q [-55, -57]) (countLit q [-58, -59, -61]) (count1632 q) 1 (meaning1625 q) (meaning1632 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1910 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1632 = true := counterClause1910 (baseVal q)

theorem counterClause1911 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-55, -57]) + (countLit q [-58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1633)) (countLit q [-55, -57]) (countLit q [-58, -59, -61]) (count1632 q) 1 1 (meaning1625 q) (meaning1629 q) (meaning1633 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1911 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1629 = false ∨ valuation q 1633 = true := counterClause1911 (baseVal q)

theorem counterClause1912 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-55, -57]) + (countLit q [-58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -59, -61])
  have hm := merge_left (literal (valuationOf q) (1626)) (literal (valuationOf q) (1633)) (countLit q [-55, -57]) (countLit q [-58, -59, -61]) (count1632 q) 2 (meaning1626 q) (meaning1633 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1912 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1633 = true := counterClause1912 (baseVal q)

theorem counterClause1913 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1634 = true := by
  have hs : count1632 q = (countLit q [-55, -57]) + (countLit q [-58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1634)) (countLit q [-55, -57]) (countLit q [-58, -59, -61]) (count1632 q) 2 1 (meaning1626 q) (meaning1629 q) (meaning1634 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1913 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1629 = false ∨ valuation q 1634 = true := counterClause1913 (baseVal q)

theorem counterClause1914 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1637)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 1 (meaning1632 q) (meaning1637 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1914 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1637 = true := counterClause1914 (baseVal q)

theorem counterClause1915 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1638)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 2 (meaning1633 q) (meaning1638 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1915 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1638 = true := counterClause1915 (baseVal q)

theorem counterClause1916 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1639 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_right (literal (valuationOf q) (1634)) (literal (valuationOf q) (1639)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 3 (meaning1634 q) (meaning1639 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1916 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1639 = true := counterClause1916 (baseVal q)

theorem counterClause1917 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1638)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 1 1 (meaning1621 q) (meaning1632 q) (meaning1638 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1917 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1632 = false ∨ valuation q 1638 = true := counterClause1917 (baseVal q)

theorem counterClause1918 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1639 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1639)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 1 2 (meaning1621 q) (meaning1633 q) (meaning1639 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1918 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1633 = false ∨ valuation q 1639 = true := counterClause1918 (baseVal q)

theorem counterClause1919 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1639 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1639)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 2 1 (meaning1622 q) (meaning1632 q) (meaning1639 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1919 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1632 = false ∨ valuation q 1639 = true := counterClause1919 (baseVal q)

theorem counterClause1920 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-47, -52, -53, -54]) + (countLit q [-55, -57, -58, -59, -61]) := List.countP_append (p := literal q) (l₁ := [-47, -52, -53, -54]) (l₂ := [-55, -57, -58, -59, -61])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1640)) (countLit q [-47, -52, -53, -54]) (countLit q [-55, -57, -58, -59, -61]) (count1637 q) 2 2 (meaning1622 q) (meaning1633 q) (meaning1640 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1920 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1633 = false ∨ valuation q 1640 = true := counterClause1920 (baseVal q)

theorem block59 (q : Snake 81) (h : Conditions q) : B112E260.Block59 (valuation q) :=
  ⟨clause1889 q h, clause1890 q h, clause1891 q h, clause1892 q h, clause1893 q h, clause1894 q h, clause1895 q h, clause1896 q h, clause1897 q h, clause1898 q h, clause1899 q h, clause1900 q h, clause1901 q h, clause1902 q h, clause1903 q h, clause1904 q h, clause1905 q h, clause1906 q h, clause1907 q h, clause1908 q h, clause1909 q h, clause1910 q h, clause1911 q h, clause1912 q h, clause1913 q h, clause1914 q h, clause1915 q h, clause1916 q h, clause1917 q h, clause1918 q h, clause1919 q h, clause1920 q h⟩

end
end Snake9.Regrowth.E112260
