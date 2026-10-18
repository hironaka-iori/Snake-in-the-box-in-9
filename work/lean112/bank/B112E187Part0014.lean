import B112E187Part0013
namespace B112E187
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1913 : List Lit := [(1538, true), (349, true), (92, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c1898, c1899, c1897, c62, c1909, c1728, c1604, c1791, c525, c507, c504, c503, c1907, c722, c725, c1810, c746, c733, c738] c1913 (by decide) p (sat_cons (step1898 p h) (sat_cons (step1899 p h) (sat_cons (step1897 p h) (sat_cons (step62 p h) (sat_cons (step1909 p h) (sat_cons (step1728 p h) (sat_cons (step1604 p h) (sat_cons (step1791 p h) (sat_cons (step525 p h) (sat_cons (step507 p h) (sat_cons (step504 p h) (sat_cons (step503 p h) (sat_cons (step1907 p h) (sat_cons (step722 p h) (sat_cons (step725 p h) (sat_cons (step1810 p h) (sat_cons (step746 p h) (sat_cons (step733 p h) (sat_cons (step738 p h) (sat_nil p))))))))))))))))))))
def c1914 : List Lit := [(56, true), (349, true), (92, false)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c1898, c1899, c1897, c62, c1909, c1728, c1604, c1791, c525, c507, c504, c503, c1907, c722, c725, c747, c740, c523, c521, c512, c511, c732, c734, c738, c1894, c749] c1914 (by decide) p (sat_cons (step1898 p h) (sat_cons (step1899 p h) (sat_cons (step1897 p h) (sat_cons (step62 p h) (sat_cons (step1909 p h) (sat_cons (step1728 p h) (sat_cons (step1604 p h) (sat_cons (step1791 p h) (sat_cons (step525 p h) (sat_cons (step507 p h) (sat_cons (step504 p h) (sat_cons (step503 p h) (sat_cons (step1907 p h) (sat_cons (step722 p h) (sat_cons (step725 p h) (sat_cons (step747 p h) (sat_cons (step740 p h) (sat_cons (step523 p h) (sat_cons (step521 p h) (sat_cons (step512 p h) (sat_cons (step511 p h) (sat_cons (step732 p h) (sat_cons (step734 p h) (sat_cons (step738 p h) (sat_cons (step1894 p h) (sat_cons (step749 p h) (sat_nil p)))))))))))))))))))))))))))
def c1915 : List Lit := [(349, true), (1701, true), (92, false)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c1898, c1899, c1897, c1903, c1912, c62, c1909, c1728, c693, c1913, c762, c1534, c712, c1471, c467, c1336, c530, c495, c492, c490, c487, c1689, c1914, c1829] c1915 (by decide) p (sat_cons (step1898 p h) (sat_cons (step1899 p h) (sat_cons (step1897 p h) (sat_cons (step1903 p h) (sat_cons (step1912 p h) (sat_cons (step62 p h) (sat_cons (step1909 p h) (sat_cons (step1728 p h) (sat_cons (step693 p h) (sat_cons (step1913 p h) (sat_cons (step762 p h) (sat_cons (step1534 p h) (sat_cons (step712 p h) (sat_cons (step1471 p h) (sat_cons (step467 p h) (sat_cons (step1336 p h) (sat_cons (step530 p h) (sat_cons (step495 p h) (sat_cons (step492 p h) (sat_cons (step490 p h) (sat_cons (step487 p h) (sat_cons (step1689 p h) (sat_cons (step1914 p h) (sat_cons (step1829 p h) (sat_nil p)))))))))))))))))))))))))
def c1916 : List Lit := [(1701, true), (92, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c1898, c1899, c1897, c1901, c1442, c1448, c1912, c62, c1909, c1728, c693, c1915, c528, c1335, c1336, c495, c467, c492, c1471, c490, c685, c1534, c487, c777, c1474, c761, c1829, c712, c1689] c1916 (by decide) p (sat_cons (step1898 p h) (sat_cons (step1899 p h) (sat_cons (step1897 p h) (sat_cons (step1901 p h) (sat_cons (step1442 p h) (sat_cons (step1448 p h) (sat_cons (step1912 p h) (sat_cons (step62 p h) (sat_cons (step1909 p h) (sat_cons (step1728 p h) (sat_cons (step693 p h) (sat_cons (step1915 p h) (sat_cons (step528 p h) (sat_cons (step1335 p h) (sat_cons (step1336 p h) (sat_cons (step495 p h) (sat_cons (step467 p h) (sat_cons (step492 p h) (sat_cons (step1471 p h) (sat_cons (step490 p h) (sat_cons (step685 p h) (sat_cons (step1534 p h) (sat_cons (step487 p h) (sat_cons (step777 p h) (sat_cons (step1474 p h) (sat_cons (step761 p h) (sat_cons (step1829 p h) (sat_cons (step712 p h) (sat_cons (step1689 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1917 : List Lit := [(92, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c1899, c1898, c1897, c1515, c1448, c1901, c62, c1909, c1728, c693, c711, c757, c1916, c1372, c1623, c776, c1913, c685, c528, c1471, c1336, c467] c1917 (by decide) p (sat_cons (step1899 p h) (sat_cons (step1898 p h) (sat_cons (step1897 p h) (sat_cons (step1515 p h) (sat_cons (step1448 p h) (sat_cons (step1901 p h) (sat_cons (step62 p h) (sat_cons (step1909 p h) (sat_cons (step1728 p h) (sat_cons (step693 p h) (sat_cons (step711 p h) (sat_cons (step757 p h) (sat_cons (step1916 p h) (sat_cons (step1372 p h) (sat_cons (step1623 p h) (sat_cons (step776 p h) (sat_cons (step1913 p h) (sat_cons (step685 p h) (sat_cons (step528 p h) (sat_cons (step1471 p h) (sat_cons (step1336 p h) (sat_cons (step467 p h) (sat_nil p)))))))))))))))))))))))
def c1918 : List Lit := [(1632, true)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c1917, c866] c1918 (by decide) p (sat_cons (step1917 p h) (sat_cons (step866 p h) (sat_nil p)))
def c1919 : List Lit := [(1634, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c1918, c868] c1919 (by decide) p (sat_cons (step1918 p h) (sat_cons (step868 p h) (sat_nil p)))
def c1920 : List Lit := [(56, false), (94, false), (349, false)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c1901, c1917, c1902, c1448, c1515, c1905, c528, c1336, c467, c1471, c1640, c1791, c1335, c495, c492, c490, c487, c685, c1825, c1372, c776, c1725, c757, c1450, c710, c711, c1689, c693, c1730, c1744, c226, c228, c229, c230, c1733, c904] c1920 (by decide) p (sat_cons (step1901 p h) (sat_cons (step1917 p h) (sat_cons (step1902 p h) (sat_cons (step1448 p h) (sat_cons (step1515 p h) (sat_cons (step1905 p h) (sat_cons (step528 p h) (sat_cons (step1336 p h) (sat_cons (step467 p h) (sat_cons (step1471 p h) (sat_cons (step1640 p h) (sat_cons (step1791 p h) (sat_cons (step1335 p h) (sat_cons (step495 p h) (sat_cons (step492 p h) (sat_cons (step490 p h) (sat_cons (step487 p h) (sat_cons (step685 p h) (sat_cons (step1825 p h) (sat_cons (step1372 p h) (sat_cons (step776 p h) (sat_cons (step1725 p h) (sat_cons (step757 p h) (sat_cons (step1450 p h) (sat_cons (step710 p h) (sat_cons (step711 p h) (sat_cons (step1689 p h) (sat_cons (step693 p h) (sat_cons (step1730 p h) (sat_cons (step1744 p h) (sat_cons (step226 p h) (sat_cons (step228 p h) (sat_cons (step229 p h) (sat_cons (step230 p h) (sat_cons (step1733 p h) (sat_cons (step904 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1921 : List Lit := [(1633, false), (1681, true), (1636, true), (1524, true), (89, false), (87, false), (32, false)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c1899, c869, c872, c1078, c228, c259, c724] c1921 (by decide) p (sat_cons (step1899 p h) (sat_cons (step869 p h) (sat_cons (step872 p h) (sat_cons (step1078 p h) (sat_cons (step228 p h) (sat_cons (step259 p h) (sat_cons (step724 p h) (sat_nil p))))))))
def c1922 : List Lit := [(94, false), (349, false), (1598, false)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.TreeRup.prove_clause [c1442, c1902, c1897, c1901, c1670, c1919, c1917, c1918, c528, c533, c1347, c628, c623, c620, c607, c604, c599, c603, c602, c1336, c467, c1471, c685, c777, c1335, c497, c481, c472, c469, c495, c492, c490, c487, c1640, c1920, c732, c1474, c738, c1534, c758, c1725, c1660, c749, c1728, c1557, c710, c1372, c726, c46, c1689, c993, c821, c1892, c829, c1221, c977, c1364, c894, c1921, c867, c295, c294, c1078, c873, c871, c883, c238, c878] c1922 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1902 p h) (sat_cons (step1897 p h) (sat_cons (step1901 p h) (sat_cons (step1670 p h) (sat_cons (step1919 p h) (sat_cons (step1917 p h) (sat_cons (step1918 p h) (sat_cons (step528 p h) (sat_cons (step533 p h) (sat_cons (step1347 p h) (sat_cons (step628 p h) (sat_cons (step623 p h) (sat_cons (step620 p h) (sat_cons (step607 p h) (sat_cons (step604 p h) (sat_cons (step599 p h) (sat_cons (step603 p h) (sat_cons (step602 p h) (sat_cons (step1336 p h) (sat_cons (step467 p h) (sat_cons (step1471 p h) (sat_cons (step685 p h) (sat_cons (step777 p h) (sat_cons (step1335 p h) (sat_cons (step497 p h) (sat_cons (step481 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step495 p h) (sat_cons (step492 p h) (sat_cons (step490 p h) (sat_cons (step487 p h) (sat_cons (step1640 p h) (sat_cons (step1920 p h) (sat_cons (step732 p h) (sat_cons (step1474 p h) (sat_cons (step738 p h) (sat_cons (step1534 p h) (sat_cons (step758 p h) (sat_cons (step1725 p h) (sat_cons (step1660 p h) (sat_cons (step749 p h) (sat_cons (step1728 p h) (sat_cons (step1557 p h) (sat_cons (step710 p h) (sat_cons (step1372 p h) (sat_cons (step726 p h) (sat_cons (step46 p h) (sat_cons (step1689 p h) (sat_cons (step993 p h) (sat_cons (step821 p h) (sat_cons (step1892 p h) (sat_cons (step829 p h) (sat_cons (step1221 p h) (sat_cons (step977 p h) (sat_cons (step1364 p h) (sat_cons (step894 p h) (sat_cons (step1921 p h) (sat_cons (step867 p h) (sat_cons (step295 p h) (sat_cons (step294 p h) (sat_cons (step1078 p h) (sat_cons (step873 p h) (sat_cons (step871 p h) (sat_cons (step883 p h) (sat_cons (step238 p h) (sat_cons (step878 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1923 : List Lit := [(1538, false), (32, false), (349, false), (1598, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.TreeRup.prove_clause [c1442, c1901, c1517, c1898, c1670, c1902, c1917, c1899, c1922, c1911, c994, c1335, c497, c481, c472, c469, c44, c46, c993, c821, c829, c1221, c1274, c479, c477, c474, c53, c528, c533, c1347, c628, c623, c620, c607, c604, c599, c603, c602, c1336, c467, c1471, c685, c775, c1371, c777, c495, c758, c1725, c710, c1372, c1860, c1892, c977, c867, c869, c872, c1078, c238, c239, c264, c877, c904, c908, c1738, c913, c1360] c1923 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1901 p h) (sat_cons (step1517 p h) (sat_cons (step1898 p h) (sat_cons (step1670 p h) (sat_cons (step1902 p h) (sat_cons (step1917 p h) (sat_cons (step1899 p h) (sat_cons (step1922 p h) (sat_cons (step1911 p h) (sat_cons (step994 p h) (sat_cons (step1335 p h) (sat_cons (step497 p h) (sat_cons (step481 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step44 p h) (sat_cons (step46 p h) (sat_cons (step993 p h) (sat_cons (step821 p h) (sat_cons (step829 p h) (sat_cons (step1221 p h) (sat_cons (step1274 p h) (sat_cons (step479 p h) (sat_cons (step477 p h) (sat_cons (step474 p h) (sat_cons (step53 p h) (sat_cons (step528 p h) (sat_cons (step533 p h) (sat_cons (step1347 p h) (sat_cons (step628 p h) (sat_cons (step623 p h) (sat_cons (step620 p h) (sat_cons (step607 p h) (sat_cons (step604 p h) (sat_cons (step599 p h) (sat_cons (step603 p h) (sat_cons (step602 p h) (sat_cons (step1336 p h) (sat_cons (step467 p h) (sat_cons (step1471 p h) (sat_cons (step685 p h) (sat_cons (step775 p h) (sat_cons (step1371 p h) (sat_cons (step777 p h) (sat_cons (step495 p h) (sat_cons (step758 p h) (sat_cons (step1725 p h) (sat_cons (step710 p h) (sat_cons (step1372 p h) (sat_cons (step1860 p h) (sat_cons (step1892 p h) (sat_cons (step977 p h) (sat_cons (step867 p h) (sat_cons (step869 p h) (sat_cons (step872 p h) (sat_cons (step1078 p h) (sat_cons (step238 p h) (sat_cons (step239 p h) (sat_cons (step264 p h) (sat_cons (step877 p h) (sat_cons (step904 p h) (sat_cons (step908 p h) (sat_cons (step1738 p h) (sat_cons (step913 p h) (sat_cons (step1360 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1924 : List Lit := [(32, false), (349, false), (1598, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c1901, c1517, c1898, c1899, c1922, c1911, c994, c528, c1336, c467, c1471, c685, c775, c1371, c1335, c497, c481, c472, c469, c44, c46, c993, c1274, c1923, c1450, c1481, c228, c229, c230, c1742] c1924 (by decide) p (sat_cons (step1901 p h) (sat_cons (step1517 p h) (sat_cons (step1898 p h) (sat_cons (step1899 p h) (sat_cons (step1922 p h) (sat_cons (step1911 p h) (sat_cons (step994 p h) (sat_cons (step528 p h) (sat_cons (step1336 p h) (sat_cons (step467 p h) (sat_cons (step1471 p h) (sat_cons (step685 p h) (sat_cons (step775 p h) (sat_cons (step1371 p h) (sat_cons (step1335 p h) (sat_cons (step497 p h) (sat_cons (step481 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step44 p h) (sat_cons (step46 p h) (sat_cons (step993 p h) (sat_cons (step1274 p h) (sat_cons (step1923 p h) (sat_cons (step1450 p h) (sat_cons (step1481 p h) (sat_cons (step228 p h) (sat_cons (step229 p h) (sat_cons (step230 p h) (sat_cons (step1742 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1925 : List Lit := [(349, false), (1598, false)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.TreeRup.prove_clause [c1901, c1442, c1899, c1898, c1515, c1448, c1917, c1670, c528, c1335, c533, c1336, c495, c1347, c465, c467, c492, c494, c628, c462, c1471, c490, c486, c623, c459, c1640, c685, c487, c485, c618, c620, c458, c1791, c777, c615, c616, c607, c457, c761, c614, c612, c603, c604, c613, c611, c602, c599, c1922, c1911, c994, c1924, c693, c1534, c711, c712, c1450, c1474, c1481, c757, c1689, c1755, c867, c776, c69, c1334, c869, c1372, c1276, c507, c896, c505, c502, c94, c1889, c92, c1282, c821, c1273, c1892, c829, c36, c872, c1221, c191, c246, c977, c1086, c906, c949, c938, c915] c1925 (by decide) p (sat_cons (step1901 p h) (sat_cons (step1442 p h) (sat_cons (step1899 p h) (sat_cons (step1898 p h) (sat_cons (step1515 p h) (sat_cons (step1448 p h) (sat_cons (step1917 p h) (sat_cons (step1670 p h) (sat_cons (step528 p h) (sat_cons (step1335 p h) (sat_cons (step533 p h) (sat_cons (step1336 p h) (sat_cons (step495 p h) (sat_cons (step1347 p h) (sat_cons (step465 p h) (sat_cons (step467 p h) (sat_cons (step492 p h) (sat_cons (step494 p h) (sat_cons (step628 p h) (sat_cons (step462 p h) (sat_cons (step1471 p h) (sat_cons (step490 p h) (sat_cons (step486 p h) (sat_cons (step623 p h) (sat_cons (step459 p h) (sat_cons (step1640 p h) (sat_cons (step685 p h) (sat_cons (step487 p h) (sat_cons (step485 p h) (sat_cons (step618 p h) (sat_cons (step620 p h) (sat_cons (step458 p h) (sat_cons (step1791 p h) (sat_cons (step777 p h) (sat_cons (step615 p h) (sat_cons (step616 p h) (sat_cons (step607 p h) (sat_cons (step457 p h) (sat_cons (step761 p h) (sat_cons (step614 p h) (sat_cons (step612 p h) (sat_cons (step603 p h) (sat_cons (step604 p h) (sat_cons (step613 p h) (sat_cons (step611 p h) (sat_cons (step602 p h) (sat_cons (step599 p h) (sat_cons (step1922 p h) (sat_cons (step1911 p h) (sat_cons (step994 p h) (sat_cons (step1924 p h) (sat_cons (step693 p h) (sat_cons (step1534 p h) (sat_cons (step711 p h) (sat_cons (step712 p h) (sat_cons (step1450 p h) (sat_cons (step1474 p h) (sat_cons (step1481 p h) (sat_cons (step757 p h) (sat_cons (step1689 p h) (sat_cons (step1755 p h) (sat_cons (step867 p h) (sat_cons (step776 p h) (sat_cons (step69 p h) (sat_cons (step1334 p h) (sat_cons (step869 p h) (sat_cons (step1372 p h) (sat_cons (step1276 p h) (sat_cons (step507 p h) (sat_cons (step896 p h) (sat_cons (step505 p h) (sat_cons (step502 p h) (sat_cons (step94 p h) (sat_cons (step1889 p h) (sat_cons (step92 p h) (sat_cons (step1282 p h) (sat_cons (step821 p h) (sat_cons (step1273 p h) (sat_cons (step1892 p h) (sat_cons (step829 p h) (sat_cons (step36 p h) (sat_cons (step872 p h) (sat_cons (step1221 p h) (sat_cons (step191 p h) (sat_cons (step246 p h) (sat_cons (step977 p h) (sat_cons (step1086 p h) (sat_cons (step906 p h) (sat_cons (step949 p h) (sat_cons (step938 p h) (sat_cons (step915 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1926 : List Lit := [(1538, true), (32, true), (1598, false)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c1515, c1670, c1902, c1901, c1448, c1917, c1918, c693, c711, c757, c772, c1371, c1604, c1791, c1925, c525, c507, c505, c502, c523, c1450, c1474, c1889, c92, c1755, c821, c1825, c829, c1372, c1221, c776, c773, c978, c685, c761, c1365, c1471, c712, c467, c1336, c530, c495, c492, c490, c487, c1689, c291, c293, c292, c1813, c1795, c873, c1758, c982, c1749] c1926 (by decide) p (sat_cons (step1515 p h) (sat_cons (step1670 p h) (sat_cons (step1902 p h) (sat_cons (step1901 p h) (sat_cons (step1448 p h) (sat_cons (step1917 p h) (sat_cons (step1918 p h) (sat_cons (step693 p h) (sat_cons (step711 p h) (sat_cons (step757 p h) (sat_cons (step772 p h) (sat_cons (step1371 p h) (sat_cons (step1604 p h) (sat_cons (step1791 p h) (sat_cons (step1925 p h) (sat_cons (step525 p h) (sat_cons (step507 p h) (sat_cons (step505 p h) (sat_cons (step502 p h) (sat_cons (step523 p h) (sat_cons (step1450 p h) (sat_cons (step1474 p h) (sat_cons (step1889 p h) (sat_cons (step92 p h) (sat_cons (step1755 p h) (sat_cons (step821 p h) (sat_cons (step1825 p h) (sat_cons (step829 p h) (sat_cons (step1372 p h) (sat_cons (step1221 p h) (sat_cons (step776 p h) (sat_cons (step773 p h) (sat_cons (step978 p h) (sat_cons (step685 p h) (sat_cons (step761 p h) (sat_cons (step1365 p h) (sat_cons (step1471 p h) (sat_cons (step712 p h) (sat_cons (step467 p h) (sat_cons (step1336 p h) (sat_cons (step530 p h) (sat_cons (step495 p h) (sat_cons (step492 p h) (sat_cons (step490 p h) (sat_cons (step487 p h) (sat_cons (step1689 p h) (sat_cons (step291 p h) (sat_cons (step293 p h) (sat_cons (step292 p h) (sat_cons (step1813 p h) (sat_cons (step1795 p h) (sat_cons (step873 p h) (sat_cons (step1758 p h) (sat_cons (step982 p h) (sat_cons (step1749 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1927 : List Lit := [(49, false), (56, true), (94, false), (1681, true), (87, false), (39, false), (1548, false), (32, true), (170, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1899, c1918, c1917, c1364, c894, c1604, c1791, c1808, c734, c740, c747, c725, c722, c110, c259, c1078, c1806, c869, c883, c867, c873, c294] c1927 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1899 p h) (sat_cons (step1918 p h) (sat_cons (step1917 p h) (sat_cons (step1364 p h) (sat_cons (step894 p h) (sat_cons (step1604 p h) (sat_cons (step1791 p h) (sat_cons (step1808 p h) (sat_cons (step734 p h) (sat_cons (step740 p h) (sat_cons (step747 p h) (sat_cons (step725 p h) (sat_cons (step722 p h) (sat_cons (step110 p h) (sat_cons (step259 p h) (sat_cons (step1078 p h) (sat_cons (step1806 p h) (sat_cons (step869 p h) (sat_cons (step883 p h) (sat_cons (step867 p h) (sat_cons (step873 p h) (sat_cons (step294 p h) (sat_nil p))))))))))))))))))))))))
def c1928 : List Lit := [(94, false), (1681, true), (87, false), (39, false), (1701, true), (1548, false), (32, true), (170, true)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c1917, c1604, c1825, c732, c738, c749, c1927, c723, c1854, c725, c734, c747, c740] c1928 (by decide) p (sat_cons (step1917 p h) (sat_cons (step1604 p h) (sat_cons (step1825 p h) (sat_cons (step732 p h) (sat_cons (step738 p h) (sat_cons (step749 p h) (sat_cons (step1927 p h) (sat_cons (step723 p h) (sat_cons (step1854 p h) (sat_cons (step725 p h) (sat_cons (step734 p h) (sat_cons (step747 p h) (sat_cons (step740 p h) (sat_nil p))))))))))))))
def c1929 : List Lit := [(33, false), (29, false)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c1899, c1898, c49] c1929 (by decide) p (sat_cons (step1899 p h) (sat_cons (step1898 p h) (sat_cons (step49 p h) (sat_nil p))))
def c1930 : List Lit := [(89, true), (33, true), (153, true)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c1899, c53] c1930 (by decide) p (sat_cons (step1899 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1931 : List Lit := [(52, false), (50, false)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c1765, c1667] c1931 (by decide) p (sat_cons (step1765 p h) (sat_cons (step1667 p h) (sat_nil p)))
def c1932 : List Lit := [(187, true), (76, true), (50, true)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c1765, c153] c1932 (by decide) p (sat_cons (step1765 p h) (sat_cons (step153 p h) (sat_nil p)))
def c1933 : List Lit := [(90, true), (98, true), (32, true), (87, false), (80, true), (107, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c1669, c1295] c1933 (by decide) p (sat_cons (step1669 p h) (sat_cons (step1295 p h) (sat_nil p)))
def c1934 : List Lit := [(101, false), (108, false), (89, false)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c1899, c264] c1934 (by decide) p (sat_cons (step1899 p h) (sat_cons (step264 p h) (sat_nil p)))
def c1935 : List Lit := [(102, false), (101, true)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c1917, c1303] c1935 (by decide) p (sat_cons (step1917 p h) (sat_cons (step1303 p h) (sat_nil p)))
def c1936 : List Lit := [(110, false), (108, true)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c1917, c1307] c1936 (by decide) p (sat_cons (step1917 p h) (sat_cons (step1307 p h) (sat_nil p)))
def c1937 : List Lit := [(1461, false), (1490, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c1901, c685] c1937 (by decide) p (sat_cons (step1901 p h) (sat_cons (step685 p h) (sat_nil p)))
def c1938 : List Lit := [(1515, true), (1503, false)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c1515, c711] c1938 (by decide) p (sat_cons (step1515 p h) (sat_cons (step711 p h) (sat_nil p)))
def c1939 : List Lit := [(1526, false), (1534, false)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c1647, c750] c1939 (by decide) p (sat_cons (step1647 p h) (sat_cons (step750 p h) (sat_nil p)))
def c1940 : List Lit := [(1527, false), (1533, false)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c1647, c752] c1940 (by decide) p (sat_cons (step1647 p h) (sat_cons (step752 p h) (sat_nil p)))
def c1941 : List Lit := [(1547, true), (1538, false)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c1516, c754] c1941 (by decide) p (sat_cons (step1516 p h) (sat_cons (step754 p h) (sat_nil p)))
def c1942 : List Lit := [(1548, true), (1539, false)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c1516, c755] c1942 (by decide) p (sat_cons (step1516 p h) (sat_cons (step755 p h) (sat_nil p)))
def c1943 : List Lit := [(1515, false), (1547, true)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c1448, c757] c1943 (by decide) p (sat_cons (step1448 p h) (sat_cons (step757 p h) (sat_nil p)))
def c1944 : List Lit := [(1538, false), (1516, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c1903, c762] c1944 (by decide) p (sat_cons (step1903 p h) (sat_cons (step762 p h) (sat_nil p)))
def c1945 : List Lit := [(1565, true), (1547, false)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c1902, c772] c1945 (by decide) p (sat_cons (step1902 p h) (sat_cons (step772 p h) (sat_nil p)))
def c1946 : List Lit := [(1566, true), (1548, false)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c1902, c773] c1946 (by decide) p (sat_cons (step1902 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1947 : List Lit := [(1490, false), (1565, true)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c1517, c775] c1947 (by decide) p (sat_cons (step1517 p h) (sat_cons (step775 p h) (sat_nil p)))
def c1948 : List Lit := [(1490, false), (1548, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c1442, c777] c1948 (by decide) p (sat_cons (step1442 p h) (sat_cons (step777 p h) (sat_nil p)))
def c1949 : List Lit := [(85, true), (1606, true)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c1669, c825] c1949 (by decide) p (sat_cons (step1669 p h) (sat_cons (step825 p h) (sat_nil p)))
def c1950 : List Lit := [(1608, true), (1603, false)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c1670, c829] c1950 (by decide) p (sat_cons (step1670 p h) (sat_cons (step829 p h) (sat_nil p)))
def c1951 : List Lit := [(1604, false), (1609, true)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c1670, c832] c1951 (by decide) p (sat_cons (step1670 p h) (sat_cons (step832 p h) (sat_nil p)))
def c1952 : List Lit := [(1633, true), (93, true)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c1917, c867] c1952 (by decide) p (sat_cons (step1917 p h) (sat_cons (step867 p h) (sat_nil p)))
def c1953 : List Lit := [(1635, true), (90, true)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c1918, c871] c1953 (by decide) p (sat_cons (step1918 p h) (sat_cons (step871 p h) (sat_nil p)))
def c1954 : List Lit := [(1646, true), (1641, false)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c1919, c892] c1954 (by decide) p (sat_cons (step1919 p h) (sat_cons (step892 p h) (sat_nil p)))
def c1955 : List Lit := [(1647, true), (1642, false)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c1919, c893] c1955 (by decide) p (sat_cons (step1919 p h) (sat_cons (step893 p h) (sat_nil p)))
def c1956 : List Lit := [(1643, false), (1648, true)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c1919, c894] c1956 (by decide) p (sat_cons (step1919 p h) (sat_cons (step894 p h) (sat_nil p)))
def c1957 : List Lit := [(104, false), (114, false), (233, true), (90, true), (1636, true), (1681, true)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c1917, c1142] c1957 (by decide) p (sat_cons (step1917 p h) (sat_cons (step1142 p h) (sat_nil p)))
def c1958 : List Lit := [(85, true), (1609, true), (90, false), (209, true)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c1669, c1917, c1143] c1958 (by decide) p (sat_cons (step1669 p h) (sat_cons (step1917 p h) (sat_cons (step1143 p h) (sat_nil p))))
def c1959 : List Lit := [(104, false), (114, false), (233, true), (1648, true), (98, true), (1642, false), (95, true)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c1917, c1919, c1250] c1959 (by decide) p (sat_cons (step1917 p h) (sat_cons (step1919 p h) (sat_cons (step1250 p h) (sat_nil p))))
def c1960 : List Lit := [(109, true), (1655, true), (227, true)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c1917, c1384] c1960 (by decide) p (sat_cons (step1917 p h) (sat_cons (step1384 p h) (sat_nil p)))
def c1961 : List Lit := [(76, false), (1598, true)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c1765, c1537] c1961 (by decide) p (sat_cons (step1765 p h) (sat_cons (step1537 p h) (sat_nil p)))
def c1962 : List Lit := [(1526, true), (50, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c1765, c1666] c1962 (by decide) p (sat_cons (step1765 p h) (sat_cons (step1666 p h) (sat_nil p)))
def c1963 : List Lit := [(1648, true), (39, false), (94, false), (87, false), (56, false), (32, false)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c1918, c1723] c1963 (by decide) p (sat_cons (step1918 p h) (sat_cons (step1723 p h) (sat_nil p)))
def c1964 : List Lit := [(1566, true), (1538, false), (1461, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c1902, c1725] c1964 (by decide) p (sat_cons (step1902 p h) (sat_cons (step1725 p h) (sat_nil p)))
def c1965 : List Lit := [(33, false), (32, false)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c1897, c1728] c1965 (by decide) p (sat_cons (step1897 p h) (sat_cons (step1728 p h) (sat_nil p)))
def c1966 : List Lit := [(90, true), (1652, false), (93, true), (98, true), (94, false), (80, true), (56, false), (39, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c1905, c1733] c1966 (by decide) p (sat_cons (step1905 p h) (sat_cons (step1733 p h) (sat_nil p)))
def c1967 : List Lit := [(1656, false), (93, false), (1702, true), (1608, false), (98, true), (56, false), (94, false)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1771] c1967 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1771 p h) (sat_nil p)))
def c1968 : List Lit := [(1640, true), (101, true), (1681, true), (87, false), (49, false)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c1918, c1806] c1968 (by decide) p (sat_cons (step1918 p h) (sat_cons (step1806 p h) (sat_nil p)))
def c1969 : List Lit := [(94, false), (56, false), (1701, true)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c1917, c1825] c1969 (by decide) p (sat_cons (step1917 p h) (sat_cons (step1825 p h) (sat_nil p)))
def c1970 : List Lit := [(1598, true), (52, false), (1515, false)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c1901, c1864] c1970 (by decide) p (sat_cons (step1901 p h) (sat_cons (step1864 p h) (sat_nil p)))
def c1971 : List Lit := [(1636, false), (80, true), (1598, false), (228, true), (227, true), (1701, true)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c1917, c1892] c1971 (by decide) p (sat_cons (step1917 p h) (sat_cons (step1892 p h) (sat_nil p)))
def c1972 : List Lit := [(1533, true), (94, true), (175, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c737, c738, c735, c736, c732, c125, c128] c1972 (by decide) p (sat_cons (step737 p h) (sat_cons (step738 p h) (sat_cons (step735 p h) (sat_cons (step736 p h) (sat_cons (step732 p h) (sat_cons (step125 p h) (sat_cons (step128 p h) (sat_nil p))))))))
def c1973 : List Lit := [(49, false), (56, false), (37, false), (94, true), (263, false), (32, true)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c467, c1336, c528, c523, c519, c517, c513, c129, c525, c507, c505, c502, c1324, c462, c459, c458, c457, c1604, c1791, c94, c1889, c1282, c83, c1273, c1866, c1276, c1929, c36] c1973 (by decide) p (sat_cons (step467 p h) (sat_cons (step1336 p h) (sat_cons (step528 p h) (sat_cons (step523 p h) (sat_cons (step519 p h) (sat_cons (step517 p h) (sat_cons (step513 p h) (sat_cons (step129 p h) (sat_cons (step525 p h) (sat_cons (step507 p h) (sat_cons (step505 p h) (sat_cons (step502 p h) (sat_cons (step1324 p h) (sat_cons (step462 p h) (sat_cons (step459 p h) (sat_cons (step458 p h) (sat_cons (step457 p h) (sat_cons (step1604 p h) (sat_cons (step1791 p h) (sat_cons (step94 p h) (sat_cons (step1889 p h) (sat_cons (step1282 p h) (sat_cons (step83 p h) (sat_cons (step1273 p h) (sat_cons (step1866 p h) (sat_cons (step1276 p h) (sat_cons (step1929 p h) (sat_cons (step36 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1974 : List Lit := [(49, true), (94, true), (175, true), (1539, true)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1972, c749, c723, c1854, c725, c1878, c747] c1974 (by decide) p (sat_cons (step1972 p h) (sat_cons (step749 p h) (sat_cons (step723 p h) (sat_cons (step1854 p h) (sat_cons (step725 p h) (sat_cons (step1878 p h) (sat_cons (step747 p h) (sat_nil p))))))))
def c1975 : List Lit := [(101, true), (1681, true), (49, false), (94, true), (87, false), (216, true)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c1364, c1956, c1935, c1078, c1968, c869, c883, c1952, c873, c874, c318, c321] c1975 (by decide) p (sat_cons (step1364 p h) (sat_cons (step1956 p h) (sat_cons (step1935 p h) (sat_cons (step1078 p h) (sat_cons (step1968 p h) (sat_cons (step869 p h) (sat_cons (step883 p h) (sat_cons (step1952 p h) (sat_cons (step873 p h) (sat_cons (step874 p h) (sat_cons (step318 p h) (sat_cons (step321 p h) (sat_nil p)))))))))))))
def c1976 : List Lit := [(90, false), (83, false), (95, false), (93, false), (49, false), (94, true), (87, false), (1598, false), (209, true), (233, true), (1701, true)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c246, c245, c208, c904, c877, c1958, c912, c879, c1444, c1954, c981, c948, c1360, c935, c915, c1748, c906, c367, c377] c1976 (by decide) p (sat_cons (step246 p h) (sat_cons (step245 p h) (sat_cons (step208 p h) (sat_cons (step904 p h) (sat_cons (step877 p h) (sat_cons (step1958 p h) (sat_cons (step912 p h) (sat_cons (step879 p h) (sat_cons (step1444 p h) (sat_cons (step1954 p h) (sat_cons (step981 p h) (sat_cons (step948 p h) (sat_cons (step1360 p h) (sat_cons (step935 p h) (sat_cons (step915 p h) (sat_cons (step1748 p h) (sat_cons (step906 p h) (sat_cons (step367 p h) (sat_cons (step377 p h) (sat_nil p))))))))))))))))))))
end B112E187
