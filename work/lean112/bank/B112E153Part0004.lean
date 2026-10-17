import B112E153Part0003
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1803 : List Lit := [(116, true), (92, true), (102, true), (115, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c696, c577] c1803 (by decide) p (sat_cons (step696 p h) (sat_cons (step577 p h) (sat_nil p)))
def c1804 : List Lit := [(77, true), (119, true), (117, false), (106, true), (116, true)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c697, c589] c1804 (by decide) p (sat_cons (step697 p h) (sat_cons (step589 p h) (sat_nil p)))
def c1805 : List Lit := [(119, true), (124, true), (118, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c698, c591] c1805 (by decide) p (sat_cons (step698 p h) (sat_cons (step591 p h) (sat_nil p)))
def c1806 : List Lit := [(116, true), (124, true), (118, false)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c698, c592] c1806 (by decide) p (sat_cons (step698 p h) (sat_cons (step592 p h) (sat_nil p)))
def c1807 : List Lit := [(116, true), (119, true), (118, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c698, c593] c1807 (by decide) p (sat_cons (step698 p h) (sat_cons (step593 p h) (sat_nil p)))
def c1808 : List Lit := [(122, true), (120, true), (121, false), (124, true)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c699, c607] c1808 (by decide) p (sat_cons (step699 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1809 : List Lit := [(110, true), (120, true), (121, false), (124, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c699, c608] c1809 (by decide) p (sat_cons (step699 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1810 : List Lit := [(265, false), (271, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c1567, c716] c1810 (by decide) p (sat_cons (step1567 p h) (sat_cons (step716 p h) (sat_nil p)))
def c1811 : List Lit := [(259, false), (273, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c1561, c720] c1811 (by decide) p (sat_cons (step1561 p h) (sat_cons (step720 p h) (sat_nil p)))
def c1812 : List Lit := [(275, false), (303, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c1556, c736] c1812 (by decide) p (sat_cons (step1556 p h) (sat_cons (step736 p h) (sat_nil p)))
def c1813 : List Lit := [(333, false), (363, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c1555, c765] c1813 (by decide) p (sat_cons (step1555 p h) (sat_cons (step765 p h) (sat_nil p)))
def c1814 : List Lit := [(305, false), (365, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1552, c769] c1814 (by decide) p (sat_cons (step1552 p h) (sat_cons (step769 p h) (sat_nil p)))
def c1815 : List Lit := [(371, false), (377, false)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c1566, c783] c1815 (by decide) p (sat_cons (step1566 p h) (sat_cons (step783 p h) (sat_nil p)))
def c1816 : List Lit := [(385, false), (391, false)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c1565, c791] c1816 (by decide) p (sat_cons (step1565 p h) (sat_cons (step791 p h) (sat_nil p)))
def c1817 : List Lit := [(379, false), (393, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1560, c795] c1817 (by decide) p (sat_cons (step1560 p h) (sat_cons (step795 p h) (sat_nil p)))
def c1818 : List Lit := [(401, false), (407, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1564, c807] c1818 (by decide) p (sat_cons (step1564 p h) (sat_cons (step807 p h) (sat_nil p)))
def c1819 : List Lit := [(395, false), (425, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1554, c817] c1819 (by decide) p (sat_cons (step1554 p h) (sat_cons (step817 p h) (sat_nil p)))
def c1820 : List Lit := [(221, false), (222, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1570, c823] c1820 (by decide) p (sat_cons (step1570 p h) (sat_cons (step823 p h) (sat_nil p)))
def c1821 : List Lit := [(431, false), (437, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1563, c828] c1821 (by decide) p (sat_cons (step1563 p h) (sat_cons (step828 p h) (sat_nil p)))
def c1822 : List Lit := [(439, false), (453, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1558, c837] c1822 (by decide) p (sat_cons (step1558 p h) (sat_cons (step837 p h) (sat_nil p)))
def c1823 : List Lit := [(475, false), (481, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1562, c849] c1823 (by decide) p (sat_cons (step1562 p h) (sat_cons (step849 p h) (sat_nil p)))
def c1824 : List Lit := [(469, false), (483, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1557, c853] c1824 (by decide) p (sat_cons (step1557 p h) (sat_cons (step853 p h) (sat_nil p)))
def c1825 : List Lit := [(455, false), (485, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1553, c857] c1825 (by decide) p (sat_cons (step1553 p h) (sat_cons (step857 p h) (sat_nil p)))
def c1826 : List Lit := [(427, false), (487, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1551, c862] c1826 (by decide) p (sat_cons (step1551 p h) (sat_cons (step862 p h) (sat_nil p)))
def c1827 : List Lit := [(367, false), (489, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c867, c865] c1827 (by decide) p (sat_cons (step867 p h) (sat_cons (step865 p h) (sat_nil p)))
def c1828 : List Lit := [(890, true), (880, false)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1653, c927] c1828 (by decide) p (sat_cons (step1653 p h) (sat_cons (step927 p h) (sat_nil p)))
def c1829 : List Lit := [(881, false), (891, true)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1653, c928] c1829 (by decide) p (sat_cons (step1653 p h) (sat_cons (step928 p h) (sat_nil p)))
def c1830 : List Lit := [(882, false), (892, true)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1653, c929] c1830 (by decide) p (sat_cons (step1653 p h) (sat_cons (step929 p h) (sat_nil p)))
def c1831 : List Lit := [(928, false), (931, true)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1594, c988] c1831 (by decide) p (sat_cons (step1594 p h) (sat_cons (step988 p h) (sat_nil p)))
def c1832 : List Lit := [(929, false), (932, true)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1594, c989] c1832 (by decide) p (sat_cons (step1594 p h) (sat_cons (step989 p h) (sat_nil p)))
def c1833 : List Lit := [(939, false), (944, true)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1008] c1833 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1008 p h) (sat_nil p)))
def c1834 : List Lit := [(940, false), (945, true)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1009] c1834 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1009 p h) (sat_nil p)))
def c1835 : List Lit := [(941, false), (946, true)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1010] c1835 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1010 p h) (sat_nil p)))
def c1836 : List Lit := [(952, true), (918, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1670, c1022] c1836 (by decide) p (sat_cons (step1670 p h) (sat_cons (step1022 p h) (sat_nil p)))
def c1837 : List Lit := [(953, true), (919, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1670, c1026] c1837 (by decide) p (sat_cons (step1670 p h) (sat_cons (step1026 p h) (sat_nil p)))
def c1838 : List Lit := [(920, false), (953, true)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1596, c1031] c1838 (by decide) p (sat_cons (step1596 p h) (sat_cons (step1031 p h) (sat_nil p)))
def c1839 : List Lit := [(954, true), (920, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1670, c1032] c1839 (by decide) p (sat_cons (step1670 p h) (sat_cons (step1032 p h) (sat_nil p)))
def c1840 : List Lit := [(921, false), (954, true)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1596, c1036] c1840 (by decide) p (sat_cons (step1596 p h) (sat_cons (step1036 p h) (sat_nil p)))
def c1841 : List Lit := [(921, false), (955, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1670, c1037] c1841 (by decide) p (sat_cons (step1670 p h) (sat_cons (step1037 p h) (sat_nil p)))
def c1842 : List Lit := [(922, false), (956, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1670, c1040] c1842 (by decide) p (sat_cons (step1670 p h) (sat_cons (step1040 p h) (sat_nil p)))
def c1843 : List Lit := [(971, true), (952, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1042] c1843 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1042 p h) (sat_nil p)))
def c1844 : List Lit := [(972, true), (953, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1043] c1844 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1043 p h) (sat_nil p)))
def c1845 : List Lit := [(973, true), (954, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1044] c1845 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1044 p h) (sat_nil p)))
def c1846 : List Lit := [(974, true), (955, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1045] c1846 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1045 p h) (sat_nil p)))
def c1847 : List Lit := [(956, false), (975, true)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1046] c1847 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1046 p h) (sat_nil p)))
def c1848 : List Lit := [(957, false), (976, true)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1047] c1848 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1047 p h) (sat_nil p)))
def c1849 : List Lit := [(958, false), (977, true)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1048] c1849 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1048 p h) (sat_nil p)))
def c1850 : List Lit := [(972, true), (891, false)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1671, c1055] c1850 (by decide) p (sat_cons (step1671 p h) (sat_cons (step1055 p h) (sat_nil p)))
def c1851 : List Lit := [(971, false), (1126, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1404] c1851 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1404 p h) (sat_nil p)))
def c1852 : List Lit := [(972, false), (1125, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1405] c1852 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1405 p h) (sat_nil p)))
def c1853 : List Lit := [(973, false), (1124, false)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1406] c1853 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1406 p h) (sat_nil p)))
def c1854 : List Lit := [(974, false), (1123, false)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1407] c1854 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1407 p h) (sat_nil p)))
def c1855 : List Lit := [(975, false), (1122, false)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1408] c1855 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1408 p h) (sat_nil p)))
def c1856 : List Lit := [(976, false), (1121, false)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1409] c1856 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1409 p h) (sat_nil p)))
def c1857 : List Lit := [(977, false), (1120, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1410] c1857 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1410 p h) (sat_nil p)))
def c1858 : List Lit := [(978, false), (1119, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1411] c1858 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1411 p h) (sat_nil p)))
def c1859 : List Lit := [(1688, false), (1697, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1468] c1859 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1468 p h) (sat_nil p)))
def c1860 : List Lit := [(1638, false), (1783, false)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1498] c1860 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1498 p h) (sat_nil p)))
def c1861 : List Lit := [(928, false), (944, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1016, c1831, c991, c1012, c1593] c1861 (by decide) p (sat_cons (step1016 p h) (sat_cons (step1831 p h) (sat_cons (step991 p h) (sat_cons (step1012 p h) (sat_cons (step1593 p h) (sat_nil p))))))
def c1862 : List Lit := [(1021, true), (93, true), (99, false), (100, false)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c1123, c1127, c1129, c1125, c1120, c1620, c400, c382, c1789] c1862 (by decide) p (sat_cons (step1123 p h) (sat_cons (step1127 p h) (sat_cons (step1129 p h) (sat_cons (step1125 p h) (sat_cons (step1120 p h) (sat_cons (step1620 p h) (sat_cons (step400 p h) (sat_cons (step382 p h) (sat_cons (step1789 p h) (sat_nil p))))))))))
def c1863 : List Lit := [(124, false), (1082, true), (113, false), (100, false)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c642, c641, c1267] c1863 (by decide) p (sat_cons (step642 p h) (sat_cons (step641 p h) (sat_cons (step1267 p h) (sat_nil p))))
def c1864 : List Lit := [(90, false), (113, false), (1017, true), (100, false)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c340, c337, c1122] c1864 (by decide) p (sat_cons (step340 p h) (sat_cons (step337 p h) (sat_cons (step1122 p h) (sat_nil p))))
def c1865 : List Lit := [(91, false), (90, true), (101, true), (113, false), (96, false), (89, true), (107, false)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c284, c566, c1776] c1865 (by decide) p (sat_cons (step284 p h) (sat_cons (step566 p h) (sat_cons (step1776 p h) (sat_nil p))))
def c1866 : List Lit := [(994, false), (1003, true), (103, false), (105, false)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c1090, c1085, c1086, c1094, c1077, c1069, c1672] c1866 (by decide) p (sat_cons (step1090 p h) (sat_cons (step1085 p h) (sat_cons (step1086 p h) (sat_cons (step1094 p h) (sat_cons (step1077 p h) (sat_cons (step1069 p h) (sat_cons (step1672 p h) (sat_nil p))))))))
end B112E153
