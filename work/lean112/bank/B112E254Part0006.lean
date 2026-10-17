import B112E254Part0005
namespace B112E254
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1799 : List Lit := [(89, true), (39, true), (80, true), (100, false)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c654, c537] c1799 (by decide) p (sat_cons (step654 p h) (sat_cons (step537 p h) (sat_nil p)))
def c1800 : List Lit := [(40, true), (96, true), (98, true), (101, false)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c655, c539] c1800 (by decide) p (sat_cons (step655 p h) (sat_cons (step539 p h) (sat_nil p)))
def c1801 : List Lit := [(102, false), (64, true)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c656, c540] c1801 (by decide) p (sat_cons (step656 p h) (sat_cons (step540 p h) (sat_nil p)))
def c1802 : List Lit := [(102, false), (42, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c656, c541] c1802 (by decide) p (sat_cons (step656 p h) (sat_cons (step541 p h) (sat_nil p)))
def c1803 : List Lit := [(113, true), (107, true), (103, false), (68, true)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c657, c544] c1803 (by decide) p (sat_cons (step657 p h) (sat_cons (step544 p h) (sat_nil p)))
def c1804 : List Lit := [(104, true), (107, true), (103, false), (68, true)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c657, c545] c1804 (by decide) p (sat_cons (step657 p h) (sat_cons (step545 p h) (sat_nil p)))
def c1805 : List Lit := [(116, true), (72, true), (105, false), (109, true)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c658, c552] c1805 (by decide) p (sat_cons (step658 p h) (sat_cons (step552 p h) (sat_nil p)))
def c1806 : List Lit := [(108, false), (120, true), (109, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c659, c557] c1806 (by decide) p (sat_cons (step659 p h) (sat_cons (step557 p h) (sat_nil p)))
def c1807 : List Lit := [(50, true), (120, true), (108, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c659, c558] c1807 (by decide) p (sat_cons (step659 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1808 : List Lit := [(50, true), (108, false), (109, true)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c659, c559] c1808 (by decide) p (sat_cons (step659 p h) (sat_cons (step559 p h) (sat_nil p)))
def c1809 : List Lit := [(110, false), (112, true), (115, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c660, c564] c1809 (by decide) p (sat_cons (step660 p h) (sat_cons (step564 p h) (sat_nil p)))
def c1810 : List Lit := [(52, true), (110, false), (112, true)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c660, c565] c1810 (by decide) p (sat_cons (step660 p h) (sat_cons (step565 p h) (sat_nil p)))
def c1811 : List Lit := [(111, false), (118, true)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c661, c566] c1811 (by decide) p (sat_cons (step661 p h) (sat_cons (step566 p h) (sat_nil p)))
def c1812 : List Lit := [(111, false), (113, true)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c661, c567] c1812 (by decide) p (sat_cons (step661 p h) (sat_cons (step567 p h) (sat_nil p)))
def c1813 : List Lit := [(116, true), (115, true), (120, true), (114, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c662, c571] c1813 (by decide) p (sat_cons (step662 p h) (sat_cons (step571 p h) (sat_nil p)))
def c1814 : List Lit := [(56, true), (116, true), (120, true), (114, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c662, c572] c1814 (by decide) p (sat_cons (step662 p h) (sat_cons (step572 p h) (sat_nil p)))
def c1815 : List Lit := [(118, true), (119, true), (91, true), (117, false), (120, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c663, c577] c1815 (by decide) p (sat_cons (step663 p h) (sat_cons (step577 p h) (sat_nil p)))
def c1816 : List Lit := [(119, true), (57, true), (117, false), (91, true), (120, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c663, c578] c1816 (by decide) p (sat_cons (step663 p h) (sat_cons (step578 p h) (sat_nil p)))
def c1817 : List Lit := [(118, true), (120, true), (98, true), (121, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c664, c602] c1817 (by decide) p (sat_cons (step664 p h) (sat_cons (step602 p h) (sat_nil p)))
def c1818 : List Lit := [(120, true), (61, true), (98, true), (121, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c664, c603] c1818 (by decide) p (sat_cons (step664 p h) (sat_cons (step603 p h) (sat_nil p)))
def c1819 : List Lit := [(119, true), (116, true), (109, true), (120, true), (122, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c665, c605] c1819 (by decide) p (sat_cons (step665 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1820 : List Lit := [(116, true), (119, true), (63, true), (122, false), (120, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c665, c606] c1820 (by decide) p (sat_cons (step665 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1821 : List Lit := [(119, true), (109, true), (63, true), (120, true), (122, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c665, c607] c1821 (by decide) p (sat_cons (step665 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1822 : List Lit := [(63, true), (116, true), (109, true), (120, true), (122, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c665, c608] c1822 (by decide) p (sat_cons (step665 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1823 : List Lit := [(128, false), (129, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1447, c672] c1823 (by decide) p (sat_cons (step1447 p h) (sat_cons (step672 p h) (sat_nil p)))
def c1824 : List Lit := [(249, false), (251, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1443, c676] c1824 (by decide) p (sat_cons (step1443 p h) (sat_cons (step676 p h) (sat_nil p)))
def c1825 : List Lit := [(247, false), (253, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1436, c680] c1825 (by decide) p (sat_cons (step1436 p h) (sat_cons (step680 p h) (sat_nil p)))
def c1826 : List Lit := [(261, false), (267, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1435, c688] c1826 (by decide) p (sat_cons (step1435 p h) (sat_cons (step688 p h) (sat_nil p)))
def c1827 : List Lit := [(255, false), (269, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1427, c692] c1827 (by decide) p (sat_cons (step1427 p h) (sat_cons (step692 p h) (sat_nil p)))
def c1828 : List Lit := [(275, false), (281, false)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1434, c700] c1828 (by decide) p (sat_cons (step1434 p h) (sat_cons (step700 p h) (sat_nil p)))
def c1829 : List Lit := [(285, false), (287, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1442, c706] c1829 (by decide) p (sat_cons (step1442 p h) (sat_cons (step706 p h) (sat_nil p)))
def c1830 : List Lit := [(291, false), (293, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1441, c711] c1830 (by decide) p (sat_cons (step1441 p h) (sat_cons (step711 p h) (sat_nil p)))
def c1831 : List Lit := [(289, false), (295, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1433, c715] c1831 (by decide) p (sat_cons (step1433 p h) (sat_cons (step715 p h) (sat_nil p)))
def c1832 : List Lit := [(283, false), (297, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1426, c720] c1832 (by decide) p (sat_cons (step1426 p h) (sat_cons (step720 p h) (sat_nil p)))
def c1833 : List Lit := [(271, false), (299, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1421, c725] c1833 (by decide) p (sat_cons (step1421 p h) (sat_cons (step725 p h) (sat_nil p)))
def c1834 : List Lit := [(164, false), (165, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1446, c741] c1834 (by decide) p (sat_cons (step1446 p h) (sat_cons (step741 p h) (sat_nil p)))
def c1835 : List Lit := [(319, false), (325, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1432, c747] c1835 (by decide) p (sat_cons (step1432 p h) (sat_cons (step747 p h) (sat_nil p)))
def c1836 : List Lit := [(313, false), (327, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1425, c751] c1836 (by decide) p (sat_cons (step1425 p h) (sat_cons (step751 p h) (sat_nil p)))
def c1837 : List Lit := [(329, false), (357, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1420, c772] c1837 (by decide) p (sat_cons (step1420 p h) (sat_cons (step772 p h) (sat_nil p)))
def c1838 : List Lit := [(301, false), (359, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1417, c777] c1838 (by decide) p (sat_cons (step1417 p h) (sat_cons (step777 p h) (sat_nil p)))
def c1839 : List Lit := [(195, false), (196, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1445, c791] c1839 (by decide) p (sat_cons (step1445 p h) (sat_cons (step791 p h) (sat_nil p)))
def c1840 : List Lit := [(381, false), (383, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1439, c796] c1840 (by decide) p (sat_cons (step1439 p h) (sat_cons (step796 p h) (sat_nil p)))
def c1841 : List Lit := [(373, false), (387, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1424, c804] c1841 (by decide) p (sat_cons (step1424 p h) (sat_cons (step804 p h) (sat_nil p)))
def c1842 : List Lit := [(206, false), (207, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1444, c810] c1842 (by decide) p (sat_cons (step1444 p h) (sat_cons (step810 p h) (sat_nil p)))
def c1843 : List Lit := [(407, false), (413, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c1430, c821] c1843 (by decide) p (sat_cons (step1430 p h) (sat_cons (step821 p h) (sat_nil p)))
def c1844 : List Lit := [(389, false), (417, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1419, c829] c1844 (by decide) p (sat_cons (step1419 p h) (sat_cons (step829 p h) (sat_nil p)))
def c1845 : List Lit := [(423, false), (429, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c1429, c840] c1845 (by decide) p (sat_cons (step1429 p h) (sat_cons (step840 p h) (sat_nil p)))
def c1846 : List Lit := [(439, false), (441, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c1437, c845] c1846 (by decide) p (sat_cons (step1437 p h) (sat_cons (step845 p h) (sat_nil p)))
def c1847 : List Lit := [(447, false), (477, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1418, c876] c1847 (by decide) p (sat_cons (step1418 p h) (sat_cons (step876 p h) (sat_nil p)))
def c1848 : List Lit := [(419, false), (479, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c1416, c881] c1848 (by decide) p (sat_cons (step1416 p h) (sat_cons (step881 p h) (sat_nil p)))
def c1849 : List Lit := [(361, false), (481, false)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c886, c884] c1849 (by decide) p (sat_cons (step886 p h) (sat_cons (step884 p h) (sat_nil p)))
def c1850 : List Lit := [(1583, false), (1588, true)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1043] c1850 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1043 p h) (sat_nil p)))
def c1851 : List Lit := [(1584, false), (1589, true)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1045] c1851 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1045 p h) (sat_nil p)))
def c1852 : List Lit := [(1579, false), (1592, true)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1051] c1852 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1051 p h) (sat_nil p)))
def c1853 : List Lit := [(1580, false), (1593, true)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1055] c1853 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1055 p h) (sat_nil p)))
def c1854 : List Lit := [(1569, false), (1601, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1064] c1854 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1064 p h) (sat_nil p)))
def c1855 : List Lit := [(1570, false), (1602, true)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1069] c1855 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c1856 : List Lit := [(1571, false), (1603, true)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1072] c1856 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1072 p h) (sat_nil p)))
def c1857 : List Lit := [(1601, false), (1618, true)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1471, c1076] c1857 (by decide) p (sat_cons (step1471 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c1858 : List Lit := [(1602, false), (1619, true)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c1471, c1077] c1858 (by decide) p (sat_cons (step1471 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c1859 : List Lit := [(1603, false), (1620, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1471, c1078] c1859 (by decide) p (sat_cons (step1471 p h) (sat_cons (step1078 p h) (sat_nil p)))
def c1860 : List Lit := [(1604, false), (1621, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c1471, c1079] c1860 (by decide) p (sat_cons (step1471 p h) (sat_cons (step1079 p h) (sat_nil p)))
def c1861 : List Lit := [(1618, true), (1543, false)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1487, c1081] c1861 (by decide) p (sat_cons (step1487 p h) (sat_cons (step1081 p h) (sat_nil p)))
def c1862 : List Lit := [(1619, true), (1544, false)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c1487, c1086] c1862 (by decide) p (sat_cons (step1487 p h) (sat_cons (step1086 p h) (sat_nil p)))
end B112E254
