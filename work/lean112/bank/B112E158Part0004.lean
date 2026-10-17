import B112E158Part0003
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1826 : List Lit := [(67, true), (63, false), (52, true), (62, true)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c691, c434] c1826 (by decide) p (sat_cons (step691 p h) (sat_cons (step434 p h) (sat_nil p)))
def c1827 : List Lit := [(66, true), (63, false), (62, true), (52, true)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c691, c435] c1827 (by decide) p (sat_cons (step691 p h) (sat_cons (step435 p h) (sat_nil p)))
def c1828 : List Lit := [(62, true), (64, true), (22, true), (65, false), (66, true), (69, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c692, c470] c1828 (by decide) p (sat_cons (step692 p h) (sat_cons (step470 p h) (sat_nil p)))
def c1829 : List Lit := [(69, true), (64, true), (70, true), (68, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c693, c494] c1829 (by decide) p (sat_cons (step693 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1830 : List Lit := [(57, true), (69, true), (68, false), (70, true)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c693, c495] c1830 (by decide) p (sat_cons (step693 p h) (sat_cons (step495 p h) (sat_nil p)))
def c1831 : List Lit := [(57, true), (64, true), (70, true), (68, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c693, c496] c1831 (by decide) p (sat_cons (step693 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1832 : List Lit := [(57, true), (69, true), (68, false), (64, true)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c693, c497] c1832 (by decide) p (sat_cons (step693 p h) (sat_cons (step497 p h) (sat_nil p)))
def c1833 : List Lit := [(67, true), (69, true), (71, false), (60, true), (70, true)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c694, c542] c1833 (by decide) p (sat_cons (step694 p h) (sat_cons (step542 p h) (sat_nil p)))
def c1834 : List Lit := [(69, true), (66, true), (71, false), (70, true), (60, true)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c694, c543] c1834 (by decide) p (sat_cons (step694 p h) (sat_cons (step543 p h) (sat_nil p)))
def c1835 : List Lit := [(67, true), (66, true), (71, false), (60, true), (70, true)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c694, c544] c1835 (by decide) p (sat_cons (step694 p h) (sat_cons (step544 p h) (sat_nil p)))
def c1836 : List Lit := [(67, true), (66, true), (71, false), (60, true), (69, true)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c694, c545] c1836 (by decide) p (sat_cons (step694 p h) (sat_cons (step545 p h) (sat_nil p)))
def c1837 : List Lit := [(75, true), (73, false), (88, true), (72, true)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c695, c549] c1837 (by decide) p (sat_cons (step695 p h) (sat_cons (step549 p h) (sat_nil p)))
def c1838 : List Lit := [(73, false), (88, true), (1, true), (72, true)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c695, c550] c1838 (by decide) p (sat_cons (step695 p h) (sat_cons (step550 p h) (sat_nil p)))
def c1839 : List Lit := [(75, true), (1, true), (72, true), (73, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c695, c551] c1839 (by decide) p (sat_cons (step695 p h) (sat_cons (step551 p h) (sat_nil p)))
def c1840 : List Lit := [(76, true), (74, false), (91, true)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c696, c553] c1840 (by decide) p (sat_cons (step696 p h) (sat_cons (step553 p h) (sat_nil p)))
def c1841 : List Lit := [(74, false), (2, true), (91, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c696, c554] c1841 (by decide) p (sat_cons (step696 p h) (sat_cons (step554 p h) (sat_nil p)))
def c1842 : List Lit := [(77, false), (76, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c697, c560] c1842 (by decide) p (sat_cons (step697 p h) (sat_cons (step560 p h) (sat_nil p)))
def c1843 : List Lit := [(77, false), (75, true)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c697, c561] c1843 (by decide) p (sat_cons (step697 p h) (sat_cons (step561 p h) (sat_nil p)))
def c1844 : List Lit := [(80, false), (81, true)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c698, c565] c1844 (by decide) p (sat_cons (step698 p h) (sat_cons (step565 p h) (sat_nil p)))
def c1845 : List Lit := [(82, false), (83, true)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c699, c568] c1845 (by decide) p (sat_cons (step699 p h) (sat_cons (step568 p h) (sat_nil p)))
def c1846 : List Lit := [(82, false), (76, true)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c699, c569] c1846 (by decide) p (sat_cons (step699 p h) (sat_cons (step569 p h) (sat_nil p)))
def c1847 : List Lit := [(84, false), (83, true)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c700, c572] c1847 (by decide) p (sat_cons (step700 p h) (sat_cons (step572 p h) (sat_nil p)))
def c1848 : List Lit := [(84, false), (81, true)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c700, c573] c1848 (by decide) p (sat_cons (step700 p h) (sat_cons (step573 p h) (sat_nil p)))
def c1849 : List Lit := [(86, false), (90, true)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c701, c579] c1849 (by decide) p (sat_cons (step701 p h) (sat_cons (step579 p h) (sat_nil p)))
def c1850 : List Lit := [(86, false), (85, true)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c701, c580] c1850 (by decide) p (sat_cons (step701 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1851 : List Lit := [(91, true), (92, false), (37, true)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c702, c597] c1851 (by decide) p (sat_cons (step702 p h) (sat_cons (step597 p h) (sat_nil p)))
def c1852 : List Lit := [(88, true), (92, false), (37, true)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c702, c598] c1852 (by decide) p (sat_cons (step702 p h) (sat_cons (step598 p h) (sat_nil p)))
def c1853 : List Lit := [(85, true), (40, true), (93, false)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c703, c600] c1853 (by decide) p (sat_cons (step703 p h) (sat_cons (step600 p h) (sat_nil p)))
def c1854 : List Lit := [(97, true), (95, false), (94, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c704, c607] c1854 (by decide) p (sat_cons (step704 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1855 : List Lit := [(96, true), (95, false), (94, true)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c704, c608] c1855 (by decide) p (sat_cons (step704 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1856 : List Lit := [(98, false), (91, true)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c705, c611] c1856 (by decide) p (sat_cons (step705 p h) (sat_cons (step611 p h) (sat_nil p)))
def c1857 : List Lit := [(97, true), (100, false), (99, true)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c706, c613] c1857 (by decide) p (sat_cons (step706 p h) (sat_cons (step613 p h) (sat_nil p)))
def c1858 : List Lit := [(96, true), (100, false), (99, true)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c706, c614] c1858 (by decide) p (sat_cons (step706 p h) (sat_cons (step614 p h) (sat_nil p)))
def c1859 : List Lit := [(105, true), (102, false), (52, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c707, c621] c1859 (by decide) p (sat_cons (step707 p h) (sat_cons (step621 p h) (sat_nil p)))
def c1860 : List Lit := [(101, true), (102, false), (52, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c707, c622] c1860 (by decide) p (sat_cons (step707 p h) (sat_cons (step622 p h) (sat_nil p)))
def c1861 : List Lit := [(113, true), (104, false), (103, true), (108, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c708, c625] c1861 (by decide) p (sat_cons (step708 p h) (sat_cons (step625 p h) (sat_nil p)))
def c1862 : List Lit := [(113, true), (105, true), (103, true), (104, false)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c708, c626] c1862 (by decide) p (sat_cons (step708 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1863 : List Lit := [(106, true), (107, false), (115, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c709, c636] c1863 (by decide) p (sat_cons (step709 p h) (sat_cons (step636 p h) (sat_nil p)))
def c1864 : List Lit := [(107, false), (115, true), (101, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c709, c637] c1864 (by decide) p (sat_cons (step709 p h) (sat_cons (step637 p h) (sat_nil p)))
def c1865 : List Lit := [(107, false), (106, true), (101, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c709, c638] c1865 (by decide) p (sat_cons (step709 p h) (sat_cons (step638 p h) (sat_nil p)))
def c1866 : List Lit := [(108, true), (109, false), (60, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c710, c643] c1866 (by decide) p (sat_cons (step710 p h) (sat_cons (step643 p h) (sat_nil p)))
def c1867 : List Lit := [(105, true), (109, false), (60, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c710, c644] c1867 (by decide) p (sat_cons (step710 p h) (sat_cons (step644 p h) (sat_nil p)))
def c1868 : List Lit := [(110, false), (113, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c711, c646] c1868 (by decide) p (sat_cons (step711 p h) (sat_cons (step646 p h) (sat_nil p)))
def c1869 : List Lit := [(111, false), (103, true), (64, true), (112, true)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c712, c649] c1869 (by decide) p (sat_cons (step712 p h) (sat_cons (step649 p h) (sat_nil p)))
def c1870 : List Lit := [(114, false), (106, true), (115, true)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c713, c653] c1870 (by decide) p (sat_cons (step713 p h) (sat_cons (step653 p h) (sat_nil p)))
def c1871 : List Lit := [(97, true), (67, true), (115, true), (117, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c714, c660] c1871 (by decide) p (sat_cons (step714 p h) (sat_cons (step660 p h) (sat_nil p)))
def c1872 : List Lit := [(112, true), (115, true), (118, false)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c715, c661] c1872 (by decide) p (sat_cons (step715 p h) (sat_cons (step661 p h) (sat_nil p)))
def c1873 : List Lit := [(115, true), (69, true), (118, false)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c715, c662] c1873 (by decide) p (sat_cons (step715 p h) (sat_cons (step662 p h) (sat_nil p)))
def c1874 : List Lit := [(112, true), (69, true), (118, false)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c715, c663] c1874 (by decide) p (sat_cons (step715 p h) (sat_cons (step663 p h) (sat_nil p)))
def c1875 : List Lit := [(119, false), (237, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1597, c719] c1875 (by decide) p (sat_cons (step1597 p h) (sat_cons (step719 p h) (sat_nil p)))
def c1876 : List Lit := [(239, false), (245, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1590, c725] c1876 (by decide) p (sat_cons (step1590 p h) (sat_cons (step725 p h) (sat_nil p)))
def c1877 : List Lit := [(126, false), (249, false)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1596, c730] c1877 (by decide) p (sat_cons (step1596 p h) (sat_cons (step730 p h) (sat_nil p)))
def c1878 : List Lit := [(253, false), (255, false)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c1595, c735] c1878 (by decide) p (sat_cons (step1595 p h) (sat_cons (step735 p h) (sat_nil p)))
def c1879 : List Lit := [(251, false), (257, false)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c1589, c739] c1879 (by decide) p (sat_cons (step1589 p h) (sat_cons (step739 p h) (sat_nil p)))
def c1880 : List Lit := [(247, false), (259, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c1582, c744] c1880 (by decide) p (sat_cons (step1582 p h) (sat_cons (step744 p h) (sat_nil p)))
def c1881 : List Lit := [(133, false), (263, false)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1594, c749] c1881 (by decide) p (sat_cons (step1594 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1882 : List Lit := [(265, false), (271, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c1588, c754] c1882 (by decide) p (sat_cons (step1588 p h) (sat_cons (step754 p h) (sat_nil p)))
def c1883 : List Lit := [(140, false), (141, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1598, c758] c1883 (by decide) p (sat_cons (step1598 p h) (sat_cons (step758 p h) (sat_nil p)))
def c1884 : List Lit := [(281, false), (283, false)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c1592, c766] c1884 (by decide) p (sat_cons (step1592 p h) (sat_cons (step766 p h) (sat_nil p)))
def c1885 : List Lit := [(279, false), (285, false)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1587, c770] c1885 (by decide) p (sat_cons (step1587 p h) (sat_cons (step770 p h) (sat_nil p)))
def c1886 : List Lit := [(273, false), (287, false)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1581, c775] c1886 (by decide) p (sat_cons (step1581 p h) (sat_cons (step775 p h) (sat_nil p)))
def c1887 : List Lit := [(261, false), (289, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c1577, c780] c1887 (by decide) p (sat_cons (step1577 p h) (sat_cons (step780 p h) (sat_nil p)))
def c1888 : List Lit := [(321, false), (327, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c1586, c801] c1888 (by decide) p (sat_cons (step1586 p h) (sat_cons (step801 p h) (sat_nil p)))
def c1889 : List Lit := [(291, false), (347, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c1573, c816] c1889 (by decide) p (sat_cons (step1573 p h) (sat_cons (step816 p h) (sat_nil p)))
end B112E158
