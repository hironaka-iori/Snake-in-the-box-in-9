import B112E259Part0003
namespace B112E259
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1796 : List Lit := [(59, true), (73, true), (64, false)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c618, c315] c1796 (by decide) p (sat_cons (step618 p h) (sat_cons (step315 p h) (sat_nil p)))
def c1797 : List Lit := [(73, true), (9, true), (64, false)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c618, c316] c1797 (by decide) p (sat_cons (step618 p h) (sat_cons (step316 p h) (sat_nil p)))
def c1798 : List Lit := [(59, true), (9, true), (64, false)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c618, c317] c1798 (by decide) p (sat_cons (step618 p h) (sat_cons (step317 p h) (sat_nil p)))
def c1799 : List Lit := [(66, false), (71, true), (65, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c619, c323] c1799 (by decide) p (sat_cons (step619 p h) (sat_cons (step323 p h) (sat_nil p)))
def c1800 : List Lit := [(66, false), (71, true), (56, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c619, c324] c1800 (by decide) p (sat_cons (step619 p h) (sat_cons (step324 p h) (sat_nil p)))
def c1801 : List Lit := [(66, false), (56, true), (65, true)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c619, c325] c1801 (by decide) p (sat_cons (step619 p h) (sat_cons (step325 p h) (sat_nil p)))
def c1802 : List Lit := [(72, true), (90, true), (68, false), (67, true), (58, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c620, c337] c1802 (by decide) p (sat_cons (step620 p h) (sat_cons (step337 p h) (sat_nil p)))
def c1803 : List Lit := [(90, true), (68, false), (67, true), (58, true), (12, true)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c620, c338] c1803 (by decide) p (sat_cons (step620 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1804 : List Lit := [(100, true), (59, true), (13, true), (73, true), (67, true), (69, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c621, c346] c1804 (by decide) p (sat_cons (step621 p h) (sat_cons (step346 p h) (sat_nil p)))
def c1805 : List Lit := [(72, true), (71, true), (74, false), (73, true)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c622, c377] c1805 (by decide) p (sat_cons (step622 p h) (sat_cons (step377 p h) (sat_nil p)))
def c1806 : List Lit := [(72, true), (74, false), (18, true), (73, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c622, c378] c1806 (by decide) p (sat_cons (step622 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1807 : List Lit := [(71, true), (74, false), (18, true), (73, true)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c622, c379] c1807 (by decide) p (sat_cons (step622 p h) (sat_cons (step379 p h) (sat_nil p)))
def c1808 : List Lit := [(72, true), (71, true), (18, true), (74, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c622, c380] c1808 (by decide) p (sat_cons (step622 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1809 : List Lit := [(86, true), (54, true), (76, true), (77, true), (79, true), (75, false), (81, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c623, c395] c1809 (by decide) p (sat_cons (step623 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1810 : List Lit := [(77, true), (83, true), (81, true), (82, false), (93, true)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c624, c465] c1810 (by decide) p (sat_cons (step624 p h) (sat_cons (step465 p h) (sat_nil p)))
def c1811 : List Lit := [(82, false), (93, true), (77, true), (83, true), (24, true)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c624, c466] c1811 (by decide) p (sat_cons (step624 p h) (sat_cons (step466 p h) (sat_nil p)))
def c1812 : List Lit := [(82, false), (81, true), (77, true), (24, true), (93, true)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c624, c467] c1812 (by decide) p (sat_cons (step624 p h) (sat_cons (step467 p h) (sat_nil p)))
def c1813 : List Lit := [(82, false), (81, true), (77, true), (24, true), (83, true)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c624, c468] c1813 (by decide) p (sat_cons (step624 p h) (sat_cons (step468 p h) (sat_nil p)))
def c1814 : List Lit := [(84, false), (81, true)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c625, c473] c1814 (by decide) p (sat_cons (step625 p h) (sat_cons (step473 p h) (sat_nil p)))
def c1815 : List Lit := [(84, false), (79, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c625, c474] c1815 (by decide) p (sat_cons (step625 p h) (sat_cons (step474 p h) (sat_nil p)))
def c1816 : List Lit := [(80, true), (83, true), (85, false)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c626, c476] c1816 (by decide) p (sat_cons (step626 p h) (sat_cons (step476 p h) (sat_nil p)))
def c1817 : List Lit := [(26, true), (83, true), (85, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c626, c477] c1817 (by decide) p (sat_cons (step626 p h) (sat_cons (step477 p h) (sat_nil p)))
def c1818 : List Lit := [(87, false), (86, true), (76, true), (90, true), (92, true)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c627, c501] c1818 (by decide) p (sat_cons (step627 p h) (sat_cons (step501 p h) (sat_nil p)))
def c1819 : List Lit := [(87, false), (28, true), (76, true), (86, true), (92, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c627, c502] c1819 (by decide) p (sat_cons (step627 p h) (sat_cons (step502 p h) (sat_nil p)))
def c1820 : List Lit := [(87, false), (28, true), (76, true), (86, true), (90, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c627, c503] c1820 (by decide) p (sat_cons (step627 p h) (sat_cons (step503 p h) (sat_nil p)))
def c1821 : List Lit := [(86, true), (89, false), (90, true), (79, true)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c628, c509] c1821 (by decide) p (sat_cons (step628 p h) (sat_cons (step509 p h) (sat_nil p)))
def c1822 : List Lit := [(86, true), (89, false), (67, true), (90, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c628, c510] c1822 (by decide) p (sat_cons (step628 p h) (sat_cons (step510 p h) (sat_nil p)))
def c1823 : List Lit := [(89, false), (79, true), (90, true), (67, true)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c628, c511] c1823 (by decide) p (sat_cons (step628 p h) (sat_cons (step511 p h) (sat_nil p)))
def c1824 : List Lit := [(89, false), (86, true), (79, true), (67, true)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c628, c512] c1824 (by decide) p (sat_cons (step628 p h) (sat_cons (step512 p h) (sat_nil p)))
def c1825 : List Lit := [(91, false), (80, true), (90, true)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c629, c532] c1825 (by decide) p (sat_cons (step629 p h) (sat_cons (step532 p h) (sat_nil p)))
def c1826 : List Lit := [(91, false), (90, true), (31, true)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c629, c533] c1826 (by decide) p (sat_cons (step629 p h) (sat_cons (step533 p h) (sat_nil p)))
def c1827 : List Lit := [(91, false), (80, true), (31, true)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c629, c534] c1827 (by decide) p (sat_cons (step629 p h) (sat_cons (step534 p h) (sat_nil p)))
def c1828 : List Lit := [(94, false), (92, true), (90, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c630, c543] c1828 (by decide) p (sat_cons (step630 p h) (sat_cons (step543 p h) (sat_nil p)))
def c1829 : List Lit := [(94, false), (92, true), (72, true)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c630, c544] c1829 (by decide) p (sat_cons (step630 p h) (sat_cons (step544 p h) (sat_nil p)))
def c1830 : List Lit := [(94, false), (72, true), (90, true)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c630, c545] c1830 (by decide) p (sat_cons (step630 p h) (sat_cons (step545 p h) (sat_nil p)))
def c1831 : List Lit := [(93, true), (73, true), (95, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c631, c547] c1831 (by decide) p (sat_cons (step631 p h) (sat_cons (step547 p h) (sat_nil p)))
def c1832 : List Lit := [(95, false), (93, true), (35, true)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c631, c548] c1832 (by decide) p (sat_cons (step631 p h) (sat_cons (step548 p h) (sat_nil p)))
def c1833 : List Lit := [(95, false), (35, true), (73, true)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c631, c549] c1833 (by decide) p (sat_cons (step631 p h) (sat_cons (step549 p h) (sat_nil p)))
def c1834 : List Lit := [(97, false), (96, true)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c632, c553] c1834 (by decide) p (sat_cons (step632 p h) (sat_cons (step553 p h) (sat_nil p)))
def c1835 : List Lit := [(97, false), (37, true)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c632, c554] c1835 (by decide) p (sat_cons (step632 p h) (sat_cons (step554 p h) (sat_nil p)))
def c1836 : List Lit := [(99, false), (102, true)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c633, c557] c1836 (by decide) p (sat_cons (step633 p h) (sat_cons (step557 p h) (sat_nil p)))
def c1837 : List Lit := [(99, false), (98, true)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c633, c558] c1837 (by decide) p (sat_cons (step633 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1838 : List Lit := [(101, false), (96, true), (100, true)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c634, c560] c1838 (by decide) p (sat_cons (step634 p h) (sat_cons (step560 p h) (sat_nil p)))
def c1839 : List Lit := [(41, true), (101, false), (100, true)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c634, c561] c1839 (by decide) p (sat_cons (step634 p h) (sat_cons (step561 p h) (sat_nil p)))
def c1840 : List Lit := [(104, false), (107, true), (105, true), (103, true)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c635, c567] c1840 (by decide) p (sat_cons (step635 p h) (sat_cons (step567 p h) (sat_nil p)))
def c1841 : List Lit := [(104, false), (107, true), (105, true), (76, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c635, c568] c1841 (by decide) p (sat_cons (step635 p h) (sat_cons (step568 p h) (sat_nil p)))
def c1842 : List Lit := [(104, false), (107, true), (76, true), (103, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c635, c569] c1842 (by decide) p (sat_cons (step635 p h) (sat_cons (step569 p h) (sat_nil p)))
def c1843 : List Lit := [(105, true), (104, false), (76, true), (103, true)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c635, c570] c1843 (by decide) p (sat_cons (step635 p h) (sat_cons (step570 p h) (sat_nil p)))
def c1844 : List Lit := [(107, false), (108, true), (223, true), (104, true)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1542, c574] c1844 (by decide) p (sat_cons (step1542 p h) (sat_cons (step574 p h) (sat_nil p)))
def c1845 : List Lit := [(44, true), (107, false), (223, true), (108, true)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c1542, c575] c1845 (by decide) p (sat_cons (step1542 p h) (sat_cons (step575 p h) (sat_nil p)))
def c1846 : List Lit := [(110, false), (106, true)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c637, c579] c1846 (by decide) p (sat_cons (step637 p h) (sat_cons (step579 p h) (sat_nil p)))
def c1847 : List Lit := [(116, false), (115, true)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c639, c587] c1847 (by decide) p (sat_cons (step639 p h) (sat_cons (step587 p h) (sat_nil p)))
def c1848 : List Lit := [(116, false), (53, true)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c639, c588] c1848 (by decide) p (sat_cons (step639 p h) (sat_cons (step588 p h) (sat_nil p)))
def c1849 : List Lit := [(120, false), (121, false)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c1572, c643] c1849 (by decide) p (sat_cons (step1572 p h) (sat_cons (step643 p h) (sat_nil p)))
def c1850 : List Lit := [(235, false), (241, false)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1562, c649] c1850 (by decide) p (sat_cons (step1562 p h) (sat_cons (step649 p h) (sat_nil p)))
def c1851 : List Lit := [(243, false), (255, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c1555, c667] c1851 (by decide) p (sat_cons (step1555 p h) (sat_cons (step667 p h) (sat_nil p)))
def c1852 : List Lit := [(263, false), (265, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1567, c675] c1852 (by decide) p (sat_cons (step1567 p h) (sat_cons (step675 p h) (sat_nil p)))
def c1853 : List Lit := [(261, false), (267, false)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1560, c679] c1853 (by decide) p (sat_cons (step1560 p h) (sat_cons (step679 p h) (sat_nil p)))
def c1854 : List Lit := [(138, false), (271, false)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1566, c683] c1854 (by decide) p (sat_cons (step1566 p h) (sat_cons (step683 p h) (sat_nil p)))
def c1855 : List Lit := [(273, false), (279, false)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1559, c688] c1855 (by decide) p (sat_cons (step1559 p h) (sat_cons (step688 p h) (sat_nil p)))
def c1856 : List Lit := [(269, false), (281, false)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c1554, c693] c1856 (by decide) p (sat_cons (step1554 p h) (sat_cons (step693 p h) (sat_nil p)))
def c1857 : List Lit := [(257, false), (283, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1549, c698] c1857 (by decide) p (sat_cons (step1549 p h) (sat_cons (step698 p h) (sat_nil p)))
def c1858 : List Lit := [(289, false), (295, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c1558, c711] c1858 (by decide) p (sat_cons (step1558 p h) (sat_cons (step711 p h) (sat_nil p)))
def c1859 : List Lit := [(169, false), (170, false)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1571, c735] c1859 (by decide) p (sat_cons (step1571 p h) (sat_cons (step735 p h) (sat_nil p)))
end B112E259
