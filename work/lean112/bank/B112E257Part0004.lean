import B112E257Part0003
namespace B112E257
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1774 : List Lit := [(81, false), (98, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c592, c469] c1774 (by decide) p (sat_cons (step592 p h) (sat_cons (step469 p h) (sat_nil p)))
def c1775 : List Lit := [(81, false), (83, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c592, c470] c1775 (by decide) p (sat_cons (step592 p h) (sat_cons (step470 p h) (sat_nil p)))
def c1776 : List Lit := [(82, false), (90, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c593, c471] c1776 (by decide) p (sat_cons (step593 p h) (sat_cons (step471 p h) (sat_nil p)))
def c1777 : List Lit := [(82, false), (84, true)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c593, c472] c1777 (by decide) p (sat_cons (step593 p h) (sat_cons (step472 p h) (sat_nil p)))
def c1778 : List Lit := [(85, false), (94, true)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c594, c477] c1778 (by decide) p (sat_cons (step594 p h) (sat_cons (step477 p h) (sat_nil p)))
def c1779 : List Lit := [(85, false), (86, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c594, c478] c1779 (by decide) p (sat_cons (step594 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1780 : List Lit := [(87, false), (88, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c595, c481] c1780 (by decide) p (sat_cons (step595 p h) (sat_cons (step481 p h) (sat_nil p)))
def c1781 : List Lit := [(87, false), (80, true)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c595, c482] c1781 (by decide) p (sat_cons (step595 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1782 : List Lit := [(89, false), (90, true)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c596, c486] c1782 (by decide) p (sat_cons (step596 p h) (sat_cons (step486 p h) (sat_nil p)))
def c1783 : List Lit := [(89, false), (24, true)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c596, c487] c1783 (by decide) p (sat_cons (step596 p h) (sat_cons (step487 p h) (sat_nil p)))
def c1784 : List Lit := [(91, false), (92, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c597, c492] c1784 (by decide) p (sat_cons (step597 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1785 : List Lit := [(91, false), (83, true)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c597, c493] c1785 (by decide) p (sat_cons (step597 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1786 : List Lit := [(93, false), (110, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c598, c496] c1786 (by decide) p (sat_cons (step598 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1787 : List Lit := [(93, false), (94, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c598, c497] c1787 (by decide) p (sat_cons (step598 p h) (sat_cons (step497 p h) (sat_nil p)))
def c1788 : List Lit := [(99, false), (98, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c599, c509] c1788 (by decide) p (sat_cons (step599 p h) (sat_cons (step509 p h) (sat_nil p)))
def c1789 : List Lit := [(99, false), (97, true)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c599, c510] c1789 (by decide) p (sat_cons (step599 p h) (sat_cons (step510 p h) (sat_nil p)))
def c1790 : List Lit := [(103, true), (101, false), (100, true)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c600, c513] c1790 (by decide) p (sat_cons (step600 p h) (sat_cons (step513 p h) (sat_nil p)))
def c1791 : List Lit := [(84, true), (100, true), (101, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c600, c514] c1791 (by decide) p (sat_cons (step600 p h) (sat_cons (step514 p h) (sat_nil p)))
def c1792 : List Lit := [(102, false), (103, true)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c601, c515] c1792 (by decide) p (sat_cons (step601 p h) (sat_cons (step515 p h) (sat_nil p)))
def c1793 : List Lit := [(102, false), (86, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c601, c516] c1793 (by decide) p (sat_cons (step601 p h) (sat_cons (step516 p h) (sat_nil p)))
def c1794 : List Lit := [(105, false), (104, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c602, c523] c1794 (by decide) p (sat_cons (step602 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1795 : List Lit := [(105, false), (88, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c602, c524] c1795 (by decide) p (sat_cons (step602 p h) (sat_cons (step524 p h) (sat_nil p)))
def c1796 : List Lit := [(107, false), (115, true), (90, true), (106, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c603, c528] c1796 (by decide) p (sat_cons (step603 p h) (sat_cons (step528 p h) (sat_nil p)))
def c1797 : List Lit := [(100, true), (92, true), (106, true), (109, false)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c605, c533] c1797 (by decide) p (sat_cons (step605 p h) (sat_cons (step533 p h) (sat_nil p)))
def c1798 : List Lit := [(226, true), (93, true), (111, true), (110, false)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c1521, c537] c1798 (by decide) p (sat_cons (step1521 p h) (sat_cons (step537 p h) (sat_nil p)))
def c1799 : List Lit := [(94, true), (110, true), (115, true), (69, true), (111, false)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c606, c543] c1799 (by decide) p (sat_cons (step606 p h) (sat_cons (step543 p h) (sat_nil p)))
def c1800 : List Lit := [(113, false), (116, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c608, c545] c1800 (by decide) p (sat_cons (step608 p h) (sat_cons (step545 p h) (sat_nil p)))
def c1801 : List Lit := [(110, true), (115, true), (114, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c609, c547] c1801 (by decide) p (sat_cons (step609 p h) (sat_cons (step547 p h) (sat_nil p)))
def c1802 : List Lit := [(73, true), (115, true), (114, false)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c609, c548] c1802 (by decide) p (sat_cons (step609 p h) (sat_cons (step548 p h) (sat_nil p)))
def c1803 : List Lit := [(110, true), (73, true), (114, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c609, c549] c1803 (by decide) p (sat_cons (step609 p h) (sat_cons (step549 p h) (sat_nil p)))
def c1804 : List Lit := [(235, false), (241, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c1538, c616] c1804 (by decide) p (sat_cons (step1538 p h) (sat_cons (step616 p h) (sat_nil p)))
def c1805 : List Lit := [(129, false), (130, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c1543, c623] c1805 (by decide) p (sat_cons (step1543 p h) (sat_cons (step623 p h) (sat_nil p)))
def c1806 : List Lit := [(247, false), (253, false)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c1537, c629] c1806 (by decide) p (sat_cons (step1537 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1807 : List Lit := [(243, false), (255, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c1532, c633] c1807 (by decide) p (sat_cons (step1532 p h) (sat_cons (step633 p h) (sat_nil p)))
def c1808 : List Lit := [(263, false), (265, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1541, c641] c1808 (by decide) p (sat_cons (step1541 p h) (sat_cons (step641 p h) (sat_nil p)))
def c1809 : List Lit := [(261, false), (267, false)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c1536, c645] c1809 (by decide) p (sat_cons (step1536 p h) (sat_cons (step645 p h) (sat_nil p)))
def c1810 : List Lit := [(269, false), (281, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c1531, c655] c1810 (by decide) p (sat_cons (step1531 p h) (sat_cons (step655 p h) (sat_nil p)))
def c1811 : List Lit := [(257, false), (283, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c1526, c660] c1811 (by decide) p (sat_cons (step1526 p h) (sat_cons (step660 p h) (sat_nil p)))
def c1812 : List Lit := [(291, false), (293, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c1540, c669] c1812 (by decide) p (sat_cons (step1540 p h) (sat_cons (step669 p h) (sat_nil p)))
def c1813 : List Lit := [(289, false), (295, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c1535, c673] c1813 (by decide) p (sat_cons (step1535 p h) (sat_cons (step673 p h) (sat_nil p)))
def c1814 : List Lit := [(152, false), (299, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1539, c678] c1814 (by decide) p (sat_cons (step1539 p h) (sat_cons (step678 p h) (sat_nil p)))
def c1815 : List Lit := [(301, false), (307, false)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c1534, c683] c1815 (by decide) p (sat_cons (step1534 p h) (sat_cons (step683 p h) (sat_nil p)))
def c1816 : List Lit := [(297, false), (309, false)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c1530, c688] c1816 (by decide) p (sat_cons (step1530 p h) (sat_cons (step688 p h) (sat_nil p)))
def c1817 : List Lit := [(323, false), (337, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1529, c708] c1817 (by decide) p (sat_cons (step1529 p h) (sat_cons (step708 p h) (sat_nil p)))
def c1818 : List Lit := [(311, false), (339, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1525, c712] c1818 (by decide) p (sat_cons (step1525 p h) (sat_cons (step712 p h) (sat_nil p)))
def c1819 : List Lit := [(285, false), (341, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1523, c717] c1819 (by decide) p (sat_cons (step1523 p h) (sat_cons (step717 p h) (sat_nil p)))
def c1820 : List Lit := [(403, false), (409, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1533, c762] c1820 (by decide) p (sat_cons (step1533 p h) (sat_cons (step762 p h) (sat_nil p)))
def c1821 : List Lit := [(437, false), (451, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1527, c787] c1821 (by decide) p (sat_cons (step1527 p h) (sat_cons (step787 p h) (sat_nil p)))
def c1822 : List Lit := [(425, false), (453, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1524, c791] c1822 (by decide) p (sat_cons (step1524 p h) (sat_cons (step791 p h) (sat_nil p)))
def c1823 : List Lit := [(399, false), (455, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1522, c796] c1823 (by decide) p (sat_cons (step1522 p h) (sat_cons (step796 p h) (sat_nil p)))
def c1824 : List Lit := [(343, false), (457, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c800, c798] c1824 (by decide) p (sat_cons (step800 p h) (sat_cons (step798 p h) (sat_nil p)))
def c1825 : List Lit := [(904, false), (1043, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1307] c1825 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1307 p h) (sat_nil p)))
def c1826 : List Lit := [(905, false), (1042, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1308] c1826 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1308 p h) (sat_nil p)))
def c1827 : List Lit := [(906, false), (1041, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1309] c1827 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1309 p h) (sat_nil p)))
def c1828 : List Lit := [(907, false), (1040, false)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1310] c1828 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1310 p h) (sat_nil p)))
def c1829 : List Lit := [(908, false), (1039, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1311] c1829 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1311 p h) (sat_nil p)))
def c1830 : List Lit := [(909, false), (1038, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1312] c1830 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1312 p h) (sat_nil p)))
def c1831 : List Lit := [(910, false), (1037, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1313] c1831 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1313 p h) (sat_nil p)))
def c1832 : List Lit := [(911, false), (1036, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1314] c1832 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1314 p h) (sat_nil p)))
def c1833 : List Lit := [(912, false), (1035, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1315] c1833 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1315 p h) (sat_nil p)))
def c1834 : List Lit := [(913, false), (1034, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1316] c1834 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1316 p h) (sat_nil p)))
def c1835 : List Lit := [(1509, false), (1650, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1474, c1470] c1835 (by decide) p (sat_cons (step1474 p h) (sat_cons (step1470 p h) (sat_nil p)))
def c1836 : List Lit := [(1510, false), (1649, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1474, c1471] c1836 (by decide) p (sat_cons (step1474 p h) (sat_cons (step1471 p h) (sat_nil p)))
def c1837 : List Lit := [(1511, false), (1648, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1474, c1472] c1837 (by decide) p (sat_cons (step1474 p h) (sat_cons (step1472 p h) (sat_nil p)))
end B112E257
