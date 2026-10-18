import Dfs112FirstBooleanPart0007
namespace Dfs112FirstBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem step1868 (p : Nat → Bool) (h : Constraints p) : p 1498 = true ∨ p 1485 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1498 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1485 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1493 = true := (step1685 p h)
  exact (Or.elim (step998 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step1869 (p : Nat → Bool) (h : Constraints p) : p 1499 = true ∨ p 1486 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1499 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1486 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1493 = true := (step1685 p h)
  exact (Or.elim (step1001 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step1870 (p : Nat → Bool) (h : Constraints p) : p 1487 = false ∨ p 1500 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1487 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1500 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1493 = true := (step1685 p h)
  exact (Or.elim (step1005 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1871 (p : Nat → Bool) (h : Constraints p) : p 1488 = false ∨ p 1501 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1488 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1501 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1493 = true := (step1685 p h)
  exact (Or.elim (step1008 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1872 (p : Nat → Bool) (h : Constraints p) : p 1499 = false ∨ p 1508 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1499 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1508 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1474 = true := (step1576 p h)
  exact (Or.elim (step1009 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1873 (p : Nat → Bool) (h : Constraints p) : p 1475 = false ∨ p 1507 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1475 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1507 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1497 = true := (step1577 p h)
  exact (Or.elim (step1011 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1874 (p : Nat → Bool) (h : Constraints p) : p 1508 = true ∨ p 1476 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1508 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1476 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1497 = true := (step1577 p h)
  exact (Or.elim (step1016 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step1875 (p : Nat → Bool) (h : Constraints p) : p 1509 = true ∨ p 1477 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1509 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1477 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1497 = true := (step1577 p h)
  exact (Or.elim (step1023 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step1876 (p : Nat → Bool) (h : Constraints p) : p 1510 = true ∨ p 1478 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1510 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1478 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1497 = true := (step1577 p h)
  exact (Or.elim (step1028 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step1877 (p : Nat → Bool) (h : Constraints p) : p 1511 = true ∨ p 1479 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1511 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1479 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1497 = true := (step1577 p h)
  exact (Or.elim (step1032 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step1878 (p : Nat → Bool) (h : Constraints p) : p 1648 = true ∨ p 1635 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1648 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1635 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1643 = true := (step1579 p h)
  exact (Or.elim (step1261 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step1879 (p : Nat → Bool) (h : Constraints p) : p 1636 = false ∨ p 1649 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1636 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1649 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1643 = true := (step1579 p h)
  exact (Or.elim (step1266 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1880 (p : Nat → Bool) (h : Constraints p) : p 1637 = false ∨ p 1650 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1637 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1650 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1643 = true := (step1579 p h)
  exact (Or.elim (step1271 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1881 (p : Nat → Bool) (h : Constraints p) : p 1657 = true ∨ p 1624 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1657 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1624 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1647 = true := (step1585 p h)
  exact (Or.elim (step1286 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u0)))))

theorem step1882 (p : Nat → Bool) (h : Constraints p) : p 1625 = false ∨ p 1658 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1625 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1658 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1647 = true := (step1585 p h)
  exact (Or.elim (step1293 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1883 (p : Nat → Bool) (h : Constraints p) : p 1626 = false ∨ p 1659 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1626 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1659 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1647 = true := (step1585 p h)
  exact (Or.elim (step1300 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1884 (p : Nat → Bool) (h : Constraints p) : p 1627 = false ∨ p 1660 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1627 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1660 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1647 = true := (step1585 p h)
  exact (Or.elim (step1306 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1885 (p : Nat → Bool) (h : Constraints p) : p 1688 = false ∨ p 1721 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1688 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1721 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1711 = true := (step1586 p h)
  exact (Or.elim (step1417 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1886 (p : Nat → Bool) (h : Constraints p) : p 1689 = false ∨ p 1722 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1689 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1722 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1711 = true := (step1586 p h)
  exact (Or.elim (step1423 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1887 (p : Nat → Bool) (h : Constraints p) : p 1690 = false ∨ p 1723 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1690 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1723 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1711 = true := (step1586 p h)
  exact (Or.elim (step1428 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1888 (p : Nat → Bool) (h : Constraints p) : p 1691 = false ∨ p 1724 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1691 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1724 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1711 = true := (step1586 p h)
  exact (Or.elim (step1434 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1889 (p : Nat → Bool) (h : Constraints p) : p 1692 = false ∨ p 1725 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1692 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1725 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1711 = true := (step1586 p h)
  exact (Or.elim (step1440 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1890 (p : Nat → Bool) (h : Constraints p) : p 1693 = false ∨ p 1726 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1693 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1726 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1711 = true := (step1586 p h)
  exact (Or.elim (step1444 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1891 (p : Nat → Bool) (h : Constraints p) : p 1725 = false ∨ p 1743 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1725 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1743 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1656 = true := (step1590 p h)
  exact (Or.elim (step1447 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1892 (p : Nat → Bool) (h : Constraints p) : p 1726 = false ∨ p 1744 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1726 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1744 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1656 = true := (step1590 p h)
  exact (Or.elim (step1448 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1893 (p : Nat → Bool) (h : Constraints p) : p 1727 = false ∨ p 1745 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1727 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1745 = false := bool_false_of_not_true (fun hl => hc (Or.inr hl))
  have t0 : p 1656 = true := (step1590 p h)
  exact (Or.elim (step1449 p h) (fun l0 => (bool_contra t0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u0 l1)) (fun r1 => (bool_contra r1 u1)))))

theorem step1894 (p : Nat → Bool) (h : Constraints p) : p 1590 = false ∨ p 1750 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1590 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1750 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1780 = false := (step1504 p h)
  exact (Or.elim (step1496 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1895 (p : Nat → Bool) (h : Constraints p) : p 1591 = false ∨ p 1749 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1591 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1749 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1780 = false := (step1504 p h)
  exact (Or.elim (step1497 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1896 (p : Nat → Bool) (h : Constraints p) : p 1592 = false ∨ p 1748 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1592 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1748 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1780 = false := (step1504 p h)
  exact (Or.elim (step1498 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1897 (p : Nat → Bool) (h : Constraints p) : p 1593 = false ∨ p 1747 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1593 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1747 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1780 = false := (step1504 p h)
  exact (Or.elim (step1499 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1898 (p : Nat → Bool) (h : Constraints p) : p 1594 = false ∨ p 1746 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1594 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1746 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1780 = false := (step1504 p h)
  exact (Or.elim (step1500 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1899 (p : Nat → Bool) (h : Constraints p) : p 1595 = false ∨ p 1745 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1595 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1745 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1780 = false := (step1504 p h)
  exact (Or.elim (step1501 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1900 (p : Nat → Bool) (h : Constraints p) : p 1596 = false ∨ p 1744 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1596 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1744 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1780 = false := (step1504 p h)
  exact (Or.elim (step1502 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1901 (p : Nat → Bool) (h : Constraints p) : p 1597 = false ∨ p 1743 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1597 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 1743 = true := bool_true_of_not_false (fun hl => hc (Or.inr hl))
  have t0 : p 1780 = false := (step1504 p h)
  exact (Or.elim (step1503 p h) (fun l0 => (bool_contra u0 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (bool_contra r1 t0)))))

theorem step1902 (p : Nat → Bool) (h : Constraints p) : p 56 = false ∨ p 64 = false ∨ p 67 = false ∨ p 72 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 56 = true := bool_true_of_not_false (fun hl => hc (Or.inl hl))
  have u1 : p 64 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 72 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr hl))))
  have t0 : p 55 = false := (Or.elim (step185 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u3 r2))))))))
  have t1 : p 65 = false := (Or.elim (step245 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u0 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (False.elim (bool_contra u2 r2))))))))
  exact (Or.elim (step1767 p h) (fun l0 => (bool_contra l0 t0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra l1 t1)) (fun r1 => (bool_contra u1 r1)))))

theorem step1903 (p : Nat → Bool) (h : Constraints p) : p 103 = true ∨ p 1691 = true ∨ p 94 = false ∨ p 67 = false ∨ p 1676 = false ∨ p 1673 = false ∨ p 1712 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 103 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 1691 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 94 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1676 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1673 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))))
  have u6 : p 1712 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl)))))))
  have t0 : p 1685 = false := (Or.elim (step1353 p h) (fun l0 => (False.elim (bool_contra u4 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u1))))))
  have t1 : p 1699 = false := (Or.elim (step1643 p h) (fun l0 => (False.elim (bool_contra l0 u6))) (fun r0 => r0))
  have t2 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 109 = true := (Or.elim (step1365 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t4 : p 110 = true := (Or.elim (step1364 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t6 : p 111 = true := (Or.elim (step1368 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t7 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t5))))
  have t8 : p 1708 = false := (Or.elim (step1393 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u6))))
  have t9 : p 118 = true := (Or.elim (step1827 p h) (fun l0 => (False.elim (bool_contra t3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t10 : p 119 = false := (Or.elim (step645 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t3 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t7 l2))) (fun r2 => r2))))))
  have t11 : p 98 = false := (Or.elim (step642 p h) (fun l0 => (False.elim (bool_contra t9 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t3 l2))) (fun r2 => (False.elim (bool_contra t7 r2))))))))
  have t12 : p 1705 = true := (Or.elim (step1382 p h) (fun l0 => (False.elim (bool_contra l0 t10))) (fun r0 => r0))
  have t13 : p 1679 = true := (Or.elim (step1328 p h) (fun l0 => (False.elim (bool_contra l0 t11))) (fun r0 => r0))
  have t14 : p 1703 = false := (Or.elim (step1387 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t12 l1))) (fun r1 => (False.elim (bool_contra r1 t8))))))
  have t15 : p 1682 = false := (Or.elim (step1337 p h) (fun l0 => (False.elim (bool_contra t13 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t16 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t14))))
  have t17 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t14))))
  have t18 : p 106 = false := (Or.elim (step1620 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t4 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 t15))) (fun r2 => (False.elim (bool_contra t17 r2))))))))
  have t19 : p 115 = false := (Or.elim (step625 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t17 l2))) (fun r2 => (False.elim (bool_contra t16 r2))))))))
  have t20 : p 93 = false := (Or.elim (step479 p h) (fun l0 => (False.elim (bool_contra u2 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u3 l1))) (fun r1 => (Or.elim r1 (fun l2 => l2) (fun r2 => (False.elim (bool_contra t17 r2))))))))
  have t21 : p 1681 = false := (Or.elim (step1591 p h) (fun l0 => (False.elim (bool_contra l0 u1))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra u5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u4 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra t6 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra l4 t20))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra l5 t11))) (fun r5 => (Or.elim r5 (fun l6 => l6) (fun r6 => (Or.elim r6 (fun l7 => (False.elim (bool_contra l7 t18))) (fun r7 => (False.elim (bool_contra t4 r7))))))))))))))))))
  have t22 : p 114 = true := (Or.elim (step1840 p h) (fun l0 => (False.elim (bool_contra l0 t19))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra l2 u0))) (fun r2 => (False.elim (bool_contra t7 r2))))))))
  have t23 : p 104 = true := (Or.elim (step1331 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t21))))
  exact (Or.elim (step619 p h) (fun l0 => (bool_contra t22 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t23 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t7 l2)) (fun r2 => (bool_contra t17 r2)))))))

theorem step1904 (p : Nat → Bool) (h : Constraints p) : p 1691 = true ∨ p 94 = false ∨ p 67 = false ∨ p 1676 = false ∨ p 1673 = false ∨ p 1712 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1691 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 94 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 67 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inl hl))))
  have u3 : p 1676 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  have u4 : p 1673 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  have u5 : p 1712 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))
  have t0 : p 1699 = false := (Or.elim (step1643 p h) (fun l0 => (False.elim (bool_contra l0 u5))) (fun r0 => r0))
  have t1 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t2 : p 109 = true := (Or.elim (step1365 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t4 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t5 : p 1708 = false := (Or.elim (step1393 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u5))))
  have t6 : p 1685 = false := (Or.elim (step1353 p h) (fun l0 => (False.elim (bool_contra u3 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (False.elim (bool_contra r1 u0))))))
  have t7 : p 103 = true := (Or.elim (step1903 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 u0))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra u1 l2))) (fun r2 => (Or.elim r2 (fun l3 => (False.elim (bool_contra u2 l3))) (fun r3 => (Or.elim r3 (fun l4 => (False.elim (bool_contra u3 l4))) (fun r4 => (Or.elim r4 (fun l5 => (False.elim (bool_contra u4 l5))) (fun r5 => (False.elim (bool_contra r5 u5))))))))))))))
  have t8 : p 105 = false := (Or.elim (step547 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  have t9 : p 104 = false := (Or.elim (step546 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => l1) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t2 l2))) (fun r2 => (False.elim (bool_contra t4 r2))))))))
  have t10 : p 118 = false := (Or.elim (step1542 p h) (fun l0 => (False.elim (bool_contra t7 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t2 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => r2))))))
  have t11 : p 1682 = true := (Or.elim (step1332 p h) (fun l0 => (False.elim (bool_contra l0 t9))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra l1 t8))) (fun r1 => r1))))
  have t12 : p 1705 = true := (Or.elim (step1671 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t10))))
  have t13 : p 1679 = false := (Or.elim (step1337 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t11 l1))) (fun r1 => (False.elim (bool_contra r1 t6))))))
  have t14 : p 1703 = false := (Or.elim (step1387 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t12 l1))) (fun r1 => (False.elim (bool_contra r1 t5))))))
  have t15 : p 101 = true := (Or.elim (step1327 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t13))))
  have t16 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t14))))
  exact (Or.elim (step482 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u2 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t15 l2)) (fun r2 => (bool_contra t16 r2)))))))

theorem step1905 (p : Nat → Bool) (h : Constraints p) : p 1556 = true ∨ p 55 = false ∨ p 64 = false := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1556 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 55 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 64 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1554 = false := (Or.elim (step1090 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1552 = false := (Or.elim (step1092 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 60 = true := (Or.elim (step1087 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t0))))
  have t3 : p 56 = true := (Or.elim (step1084 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  exact (Or.elim (step182 p h) (fun l0 => (bool_contra u1 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t3 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t2 l2)) (fun r2 => (bool_contra u2 r2)))))))

theorem step1906 (p : Nat → Bool) (h : Constraints p) : p 1712 = true ∨ p 118 = false ∨ p 121 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1712 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 118 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 121 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 1708 = false := (Or.elim (step1393 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 1699 = false := (Or.elim (step1643 p h) (fun l0 => (False.elim (bool_contra l0 u0))) (fun r0 => r0))
  have t2 : p 1697 = false := (Or.elim (step1370 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t3 : p 1695 = false := (Or.elim (step1372 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t1))))
  have t4 : p 113 = true := (Or.elim (step1367 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t2))))
  have t5 : p 109 = true := (Or.elim (step1365 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t3))))
  have t6 : p 119 = false := (Or.elim (step645 p h) (fun l0 => (False.elim (bool_contra u1 l0))) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t5 l1))) (fun r1 => (Or.elim r1 (fun l2 => (False.elim (bool_contra t4 l2))) (fun r2 => r2))))))
  have t7 : p 1705 = true := (Or.elim (step1382 p h) (fun l0 => (False.elim (bool_contra l0 t6))) (fun r0 => r0))
  have t8 : p 1703 = false := (Or.elim (step1387 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t7 l1))) (fun r1 => (False.elim (bool_contra r1 t0))))))
  have t9 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t10 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 t8))))
  have t11 : p 115 = true := (Or.elim (step1845 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t9 l1))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  exact (Or.elim (step625 p h) (fun l0 => (bool_contra t11 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra t4 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t10 l2)) (fun r2 => (bool_contra t9 r2)))))))

theorem step1907 (p : Nat → Bool) (h : Constraints p) : p 1703 = true ∨ p 113 = false ∨ p 121 = true := by
  apply Classical.byContradiction
  intro hc
  have u0 : p 1703 = false := bool_false_of_not_true (fun hl => hc (Or.inl hl))
  have u1 : p 113 = true := bool_true_of_not_false (fun hl => hc (Or.inr (Or.inl hl)))
  have u2 : p 121 = false := bool_false_of_not_true (fun hl => hc (Or.inr (Or.inr hl)))
  have t0 : p 117 = true := (Or.elim (step1378 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t1 : p 116 = true := (Or.elim (step1379 p h) (fun l0 => l0) (fun r0 => (False.elim (bool_contra r0 u0))))
  have t2 : p 115 = true := (Or.elim (step1845 p h) (fun l0 => l0) (fun r0 => (Or.elim r0 (fun l1 => (False.elim (bool_contra t0 l1))) (fun r1 => (False.elim (bool_contra r1 u2))))))
  exact (Or.elim (step625 p h) (fun l0 => (bool_contra t2 l0)) (fun r0 => (Or.elim r0 (fun l1 => (bool_contra u1 l1)) (fun r1 => (Or.elim r1 (fun l2 => (bool_contra t1 l2)) (fun r2 => (bool_contra t0 r2)))))))

end Dfs112FirstBoolean
