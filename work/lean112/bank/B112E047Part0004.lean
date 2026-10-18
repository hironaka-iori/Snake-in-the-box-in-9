import B112E047Part0003
namespace B112E047
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1799 : List Lit := [(88, false), (89, true), (85, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c723, c492] c1799 (by decide) p (sat_cons (step723 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1800 : List Lit := [(88, false), (89, true), (82, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c723, c493] c1800 (by decide) p (sat_cons (step723 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1801 : List Lit := [(88, false), (82, true), (85, true)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c723, c494] c1801 (by decide) p (sat_cons (step723 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1802 : List Lit := [(91, true), (92, true), (94, false), (93, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c725, c552] c1802 (by decide) p (sat_cons (step725 p h) (sat_cons (step552 p h) (sat_nil p)))
def c1803 : List Lit := [(91, true), (93, true), (94, false), (84, true)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c725, c554] c1803 (by decide) p (sat_cons (step725 p h) (sat_cons (step554 p h) (sat_nil p)))
def c1804 : List Lit := [(92, true), (91, true), (84, true), (94, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c725, c555] c1804 (by decide) p (sat_cons (step725 p h) (sat_cons (step555 p h) (sat_nil p)))
def c1805 : List Lit := [(98, false), (96, true), (91, true)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c727, c582] c1805 (by decide) p (sat_cons (step727 p h) (sat_cons (step582 p h) (sat_nil p)))
def c1806 : List Lit := [(99, false), (96, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c728, c583] c1806 (by decide) p (sat_cons (step728 p h) (sat_cons (step583 p h) (sat_nil p)))
def c1807 : List Lit := [(99, false), (92, true)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c728, c584] c1807 (by decide) p (sat_cons (step728 p h) (sat_cons (step584 p h) (sat_nil p)))
def c1808 : List Lit := [(100, false), (64, true), (101, true), (105, true), (111, true)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c729, c593] c1808 (by decide) p (sat_cons (step729 p h) (sat_cons (step593 p h) (sat_nil p)))
def c1809 : List Lit := [(64, true), (100, false), (105, true), (80, true), (111, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c729, c594] c1809 (by decide) p (sat_cons (step729 p h) (sat_cons (step594 p h) (sat_nil p)))
def c1810 : List Lit := [(100, false), (64, true), (80, true), (101, true), (111, true)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c729, c595] c1810 (by decide) p (sat_cons (step729 p h) (sat_cons (step595 p h) (sat_nil p)))
def c1811 : List Lit := [(113, true), (102, false), (82, true)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c730, c604] c1811 (by decide) p (sat_cons (step730 p h) (sat_cons (step604 p h) (sat_nil p)))
def c1812 : List Lit := [(107, false), (108, true), (104, true)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c732, c623] c1812 (by decide) p (sat_cons (step732 p h) (sat_cons (step623 p h) (sat_nil p)))
def c1813 : List Lit := [(113, true), (111, true), (115, true), (109, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c733, c631] c1813 (by decide) p (sat_cons (step733 p h) (sat_cons (step631 p h) (sat_nil p)))
def c1814 : List Lit := [(109, false), (111, true), (115, true), (110, true)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c733, c632] c1814 (by decide) p (sat_cons (step733 p h) (sat_cons (step632 p h) (sat_nil p)))
def c1815 : List Lit := [(111, true), (112, false), (91, true), (110, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c734, c655] c1815 (by decide) p (sat_cons (step734 p h) (sat_cons (step655 p h) (sat_nil p)))
def c1816 : List Lit := [(111, true), (101, true), (91, true), (112, false)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c734, c656] c1816 (by decide) p (sat_cons (step734 p h) (sat_cons (step656 p h) (sat_nil p)))
def c1817 : List Lit := [(116, false), (113, true), (115, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c736, c668] c1817 (by decide) p (sat_cons (step736 p h) (sat_cons (step668 p h) (sat_nil p)))
def c1818 : List Lit := [(118, false), (117, true)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c737, c675] c1818 (by decide) p (sat_cons (step737 p h) (sat_cons (step675 p h) (sat_nil p)))
def c1819 : List Lit := [(118, false), (108, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c737, c676] c1819 (by decide) p (sat_cons (step737 p h) (sat_cons (step676 p h) (sat_nil p)))
def c1820 : List Lit := [(241, false), (243, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1587, c744] c1820 (by decide) p (sat_cons (step1587 p h) (sat_cons (step744 p h) (sat_nil p)))
def c1821 : List Lit := [(239, false), (245, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1572, c748] c1821 (by decide) p (sat_cons (step1572 p h) (sat_cons (step748 p h) (sat_nil p)))
def c1822 : List Lit := [(129, false), (130, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1593, c751] c1822 (by decide) p (sat_cons (step1593 p h) (sat_cons (step751 p h) (sat_nil p)))
def c1823 : List Lit := [(247, false), (259, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1557, c761] c1823 (by decide) p (sat_cons (step1557 p h) (sat_cons (step761 p h) (sat_nil p)))
def c1824 : List Lit := [(138, false), (139, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1592, c767] c1824 (by decide) p (sat_cons (step1592 p h) (sat_cons (step767 p h) (sat_nil p)))
def c1825 : List Lit := [(265, false), (271, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1570, c773] c1825 (by decide) p (sat_cons (step1570 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1826 : List Lit := [(275, false), (277, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1584, c778] c1826 (by decide) p (sat_cons (step1584 p h) (sat_cons (step778 p h) (sat_nil p)))
def c1827 : List Lit := [(279, false), (285, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1569, c785] c1827 (by decide) p (sat_cons (step1569 p h) (sat_cons (step785 p h) (sat_nil p)))
def c1828 : List Lit := [(273, false), (287, false)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1556, c790] c1828 (by decide) p (sat_cons (step1556 p h) (sat_cons (step790 p h) (sat_nil p)))
def c1829 : List Lit := [(261, false), (289, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1549, c795] c1829 (by decide) p (sat_cons (step1549 p h) (sat_cons (step795 p h) (sat_nil p)))
def c1830 : List Lit := [(295, false), (301, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1568, c805] c1830 (by decide) p (sat_cons (step1568 p h) (sat_cons (step805 p h) (sat_nil p)))
def c1831 : List Lit := [(309, false), (311, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1583, c812] c1831 (by decide) p (sat_cons (step1583 p h) (sat_cons (step812 p h) (sat_nil p)))
def c1832 : List Lit := [(303, false), (315, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1555, c819] c1832 (by decide) p (sat_cons (step1555 p h) (sat_cons (step819 p h) (sat_nil p)))
def c1833 : List Lit := [(169, false), (170, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1591, c829] c1833 (by decide) p (sat_cons (step1591 p h) (sat_cons (step829 p h) (sat_nil p)))
def c1834 : List Lit := [(331, false), (333, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1582, c833] c1834 (by decide) p (sat_cons (step1582 p h) (sat_cons (step833 p h) (sat_nil p)))
def c1835 : List Lit := [(335, false), (341, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1566, c843] c1835 (by decide) p (sat_cons (step1566 p h) (sat_cons (step843 p h) (sat_nil p)))
def c1836 : List Lit := [(329, false), (343, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1554, c848] c1836 (by decide) p (sat_cons (step1554 p h) (sat_cons (step848 p h) (sat_nil p)))
def c1837 : List Lit := [(317, false), (345, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1548, c852] c1837 (by decide) p (sat_cons (step1548 p h) (sat_cons (step852 p h) (sat_nil p)))
def c1838 : List Lit := [(291, false), (347, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1545, c857] c1838 (by decide) p (sat_cons (step1545 p h) (sat_cons (step857 p h) (sat_nil p)))
def c1839 : List Lit := [(355, false), (357, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1580, c865] c1839 (by decide) p (sat_cons (step1580 p h) (sat_cons (step865 p h) (sat_nil p)))
def c1840 : List Lit := [(367, false), (369, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1579, c874] c1840 (by decide) p (sat_cons (step1579 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1841 : List Lit := [(365, false), (371, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1564, c878] c1841 (by decide) p (sat_cons (step1564 p h) (sat_cons (step878 p h) (sat_nil p)))
def c1842 : List Lit := [(361, false), (373, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1553, c882] c1842 (by decide) p (sat_cons (step1553 p h) (sat_cons (step882 p h) (sat_nil p)))
def c1843 : List Lit := [(193, false), (194, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c1590, c886] c1843 (by decide) p (sat_cons (step1590 p h) (sat_cons (step886 p h) (sat_nil p)))
def c1844 : List Lit := [(379, false), (385, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1563, c893] c1844 (by decide) p (sat_cons (step1563 p h) (sat_cons (step893 p h) (sat_nil p)))
def c1845 : List Lit := [(393, false), (399, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c1562, c903] c1845 (by decide) p (sat_cons (step1562 p h) (sat_cons (step903 p h) (sat_nil p)))
def c1846 : List Lit := [(387, false), (401, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c1552, c907] c1846 (by decide) p (sat_cons (step1552 p h) (sat_cons (step907 p h) (sat_nil p)))
def c1847 : List Lit := [(375, false), (403, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1547, c912] c1847 (by decide) p (sat_cons (step1547 p h) (sat_cons (step912 p h) (sat_nil p)))
def c1848 : List Lit := [(210, false), (211, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c1589, c919] c1848 (by decide) p (sat_cons (step1589 p h) (sat_cons (step919 p h) (sat_nil p)))
def c1849 : List Lit := [(409, false), (415, false)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c1561, c925] c1849 (by decide) p (sat_cons (step1561 p h) (sat_cons (step925 p h) (sat_nil p)))
def c1850 : List Lit := [(214, false), (215, false)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1588, c928] c1850 (by decide) p (sat_cons (step1588 p h) (sat_cons (step928 p h) (sat_nil p)))
def c1851 : List Lit := [(425, false), (427, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c1575, c935] c1851 (by decide) p (sat_cons (step1575 p h) (sat_cons (step935 p h) (sat_nil p)))
def c1852 : List Lit := [(423, false), (429, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1560, c939] c1852 (by decide) p (sat_cons (step1560 p h) (sat_cons (step939 p h) (sat_nil p)))
def c1853 : List Lit := [(417, false), (431, false)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1551, c944] c1853 (by decide) p (sat_cons (step1551 p h) (sat_cons (step944 p h) (sat_nil p)))
def c1854 : List Lit := [(437, false), (443, false)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1559, c957] c1854 (by decide) p (sat_cons (step1559 p h) (sat_cons (step957 p h) (sat_nil p)))
def c1855 : List Lit := [(445, false), (459, false)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1550, c974] c1855 (by decide) p (sat_cons (step1550 p h) (sat_cons (step974 p h) (sat_nil p)))
def c1856 : List Lit := [(433, false), (461, false)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c1546, c979] c1856 (by decide) p (sat_cons (step1546 p h) (sat_cons (step979 p h) (sat_nil p)))
def c1857 : List Lit := [(405, false), (463, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1544, c984] c1857 (by decide) p (sat_cons (step1544 p h) (sat_cons (step984 p h) (sat_nil p)))
def c1858 : List Lit := [(349, false), (465, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c989, c987] c1858 (by decide) p (sat_cons (step989 p h) (sat_cons (step987 p h) (sat_nil p)))
def c1859 : List Lit := [(1521, false), (1533, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1608, c1152] c1859 (by decide) p (sat_cons (step1608 p h) (sat_cons (step1152 p h) (sat_nil p)))
def c1860 : List Lit := [(1522, false), (1534, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c1608, c1156] c1860 (by decide) p (sat_cons (step1608 p h) (sat_cons (step1156 p h) (sat_nil p)))
def c1861 : List Lit := [(1523, false), (1535, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1608, c1159] c1861 (by decide) p (sat_cons (step1608 p h) (sat_cons (step1159 p h) (sat_nil p)))
def c1862 : List Lit := [(1533, false), (1541, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c1611, c1164] c1862 (by decide) p (sat_cons (step1611 p h) (sat_cons (step1164 p h) (sat_nil p)))
end B112E047
