import B112E258Part0005
namespace B112E258
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1882 : List Lit := [(89, true), (95, true), (84, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c677, c464] c1882 (by decide) p (sat_cons (step677 p h) (sat_cons (step464 p h) (sat_nil p)))
def c1883 : List Lit := [(95, true), (83, true), (84, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c677, c465] c1883 (by decide) p (sat_cons (step677 p h) (sat_cons (step465 p h) (sat_nil p)))
def c1884 : List Lit := [(89, true), (83, true), (84, false)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c677, c466] c1884 (by decide) p (sat_cons (step677 p h) (sat_cons (step466 p h) (sat_nil p)))
def c1885 : List Lit := [(91, true), (85, false), (96, true), (68, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c678, c468] c1885 (by decide) p (sat_cons (step678 p h) (sat_cons (step468 p h) (sat_nil p)))
def c1886 : List Lit := [(26, true), (91, true), (85, false), (96, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c678, c469] c1886 (by decide) p (sat_cons (step678 p h) (sat_cons (step469 p h) (sat_nil p)))
def c1887 : List Lit := [(26, true), (85, false), (96, true), (68, true)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c678, c470] c1887 (by decide) p (sat_cons (step678 p h) (sat_cons (step470 p h) (sat_nil p)))
def c1888 : List Lit := [(26, true), (91, true), (68, true), (85, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c678, c471] c1888 (by decide) p (sat_cons (step678 p h) (sat_cons (step471 p h) (sat_nil p)))
def c1889 : List Lit := [(92, true), (97, true), (86, false), (83, true)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c679, c473] c1889 (by decide) p (sat_cons (step679 p h) (sat_cons (step473 p h) (sat_nil p)))
def c1890 : List Lit := [(97, true), (27, true), (86, false), (83, true)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c679, c474] c1890 (by decide) p (sat_cons (step679 p h) (sat_cons (step474 p h) (sat_nil p)))
def c1891 : List Lit := [(92, true), (27, true), (83, true), (86, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c679, c475] c1891 (by decide) p (sat_cons (step679 p h) (sat_cons (step475 p h) (sat_nil p)))
def c1892 : List Lit := [(91, true), (89, true), (87, true), (88, false)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c680, c490] c1892 (by decide) p (sat_cons (step680 p h) (sat_cons (step490 p h) (sat_nil p)))
def c1893 : List Lit := [(30, true), (91, true), (87, true), (88, false)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c680, c491] c1893 (by decide) p (sat_cons (step680 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1894 : List Lit := [(30, true), (89, true), (87, true), (88, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c680, c492] c1894 (by decide) p (sat_cons (step680 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1895 : List Lit := [(117, true), (34, true), (93, false), (74, true), (95, true)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c682, c520] c1895 (by decide) p (sat_cons (step682 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1896 : List Lit := [(97, true), (95, true), (94, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c683, c521] c1896 (by decide) p (sat_cons (step683 p h) (sat_cons (step521 p h) (sat_nil p)))
def c1897 : List Lit := [(97, true), (83, true), (94, false)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c683, c522] c1897 (by decide) p (sat_cons (step683 p h) (sat_cons (step522 p h) (sat_nil p)))
def c1898 : List Lit := [(95, true), (83, true), (94, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c683, c523] c1898 (by decide) p (sat_cons (step683 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1899 : List Lit := [(87, true), (100, true), (98, false)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c684, c542] c1899 (by decide) p (sat_cons (step684 p h) (sat_cons (step542 p h) (sat_nil p)))
def c1900 : List Lit := [(38, true), (100, true), (98, false)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c684, c543] c1900 (by decide) p (sat_cons (step684 p h) (sat_cons (step543 p h) (sat_nil p)))
def c1901 : List Lit := [(38, true), (87, true), (98, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c684, c544] c1901 (by decide) p (sat_cons (step684 p h) (sat_cons (step544 p h) (sat_nil p)))
def c1902 : List Lit := [(101, true), (95, true), (99, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c685, c546] c1902 (by decide) p (sat_cons (step685 p h) (sat_cons (step546 p h) (sat_nil p)))
def c1903 : List Lit := [(89, true), (101, true), (99, false)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c685, c547] c1903 (by decide) p (sat_cons (step685 p h) (sat_cons (step547 p h) (sat_nil p)))
def c1904 : List Lit := [(89, true), (95, true), (99, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c685, c548] c1904 (by decide) p (sat_cons (step685 p h) (sat_cons (step548 p h) (sat_nil p)))
def c1905 : List Lit := [(110, true), (102, false), (103, true), (64, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c686, c557] c1905 (by decide) p (sat_cons (step686 p h) (sat_cons (step557 p h) (sat_nil p)))
def c1906 : List Lit := [(42, true), (110, true), (102, false), (103, true)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c686, c558] c1906 (by decide) p (sat_cons (step686 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1907 : List Lit := [(42, true), (110, true), (102, false), (64, true)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c686, c559] c1907 (by decide) p (sat_cons (step686 p h) (sat_cons (step559 p h) (sat_nil p)))
def c1908 : List Lit := [(102, false), (42, true), (103, true), (64, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c686, c560] c1908 (by decide) p (sat_cons (step686 p h) (sat_cons (step560 p h) (sat_nil p)))
def c1909 : List Lit := [(106, true), (118, true), (105, false), (103, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c687, c569] c1909 (by decide) p (sat_cons (step687 p h) (sat_cons (step569 p h) (sat_nil p)))
def c1910 : List Lit := [(118, true), (105, false), (103, true), (75, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c687, c570] c1910 (by decide) p (sat_cons (step687 p h) (sat_cons (step570 p h) (sat_nil p)))
def c1911 : List Lit := [(122, true), (109, true), (80, true), (108, false)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c689, c574] c1911 (by decide) p (sat_cons (step689 p h) (sat_cons (step574 p h) (sat_nil p)))
def c1912 : List Lit := [(122, true), (104, true), (108, false), (80, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c689, c575] c1912 (by decide) p (sat_cons (step689 p h) (sat_cons (step575 p h) (sat_nil p)))
def c1913 : List Lit := [(109, true), (104, true), (80, true), (108, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c689, c576] c1913 (by decide) p (sat_cons (step689 p h) (sat_cons (step576 p h) (sat_nil p)))
def c1914 : List Lit := [(114, true), (111, false), (110, true), (83, true)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c690, c613] c1914 (by decide) p (sat_cons (step690 p h) (sat_cons (step613 p h) (sat_nil p)))
def c1915 : List Lit := [(54, true), (111, false), (110, true), (83, true)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c690, c614] c1915 (by decide) p (sat_cons (step690 p h) (sat_cons (step614 p h) (sat_nil p)))
def c1916 : List Lit := [(115, true), (118, true), (110, true), (112, false), (103, true)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c691, c615] c1916 (by decide) p (sat_cons (step691 p h) (sat_cons (step615 p h) (sat_nil p)))
def c1917 : List Lit := [(56, true), (118, true), (103, true), (110, true), (112, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c691, c616] c1917 (by decide) p (sat_cons (step691 p h) (sat_cons (step616 p h) (sat_nil p)))
def c1918 : List Lit := [(114, true), (115, true), (113, false), (87, true), (110, true)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c692, c617] c1918 (by decide) p (sat_cons (step692 p h) (sat_cons (step617 p h) (sat_nil p)))
def c1919 : List Lit := [(115, true), (57, true), (87, true), (113, false), (110, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c692, c618] c1919 (by decide) p (sat_cons (step692 p h) (sat_cons (step618 p h) (sat_nil p)))
def c1920 : List Lit := [(117, true), (116, false), (110, true), (118, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c693, c623] c1920 (by decide) p (sat_cons (step693 p h) (sat_cons (step623 p h) (sat_nil p)))
def c1921 : List Lit := [(118, true), (59, true), (110, true), (116, false)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c693, c624] c1921 (by decide) p (sat_cons (step693 p h) (sat_cons (step624 p h) (sat_nil p)))
def c1922 : List Lit := [(117, true), (59, true), (110, true), (116, false)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c693, c625] c1922 (by decide) p (sat_cons (step693 p h) (sat_cons (step625 p h) (sat_nil p)))
def c1923 : List Lit := [(117, true), (121, true), (119, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c694, c630] c1923 (by decide) p (sat_cons (step694 p h) (sat_cons (step630 p h) (sat_nil p)))
def c1924 : List Lit := [(60, true), (121, true), (119, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c694, c631] c1924 (by decide) p (sat_cons (step694 p h) (sat_cons (step631 p h) (sat_nil p)))
def c1925 : List Lit := [(117, true), (60, true), (119, false)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c694, c632] c1925 (by decide) p (sat_cons (step694 p h) (sat_cons (step632 p h) (sat_nil p)))
def c1926 : List Lit := [(120, false), (122, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c695, c633] c1926 (by decide) p (sat_cons (step695 p h) (sat_cons (step633 p h) (sat_nil p)))
def c1927 : List Lit := [(120, false), (114, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c695, c634] c1927 (by decide) p (sat_cons (step695 p h) (sat_cons (step634 p h) (sat_nil p)))
def c1928 : List Lit := [(249, false), (251, false)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c1527, c703] c1928 (by decide) p (sat_cons (step1527 p h) (sat_cons (step703 p h) (sat_nil p)))
def c1929 : List Lit := [(247, false), (253, false)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c1520, c707] c1929 (by decide) p (sat_cons (step1520 p h) (sat_cons (step707 p h) (sat_nil p)))
def c1930 : List Lit := [(255, false), (269, false)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c1512, c719] c1930 (by decide) p (sat_cons (step1512 p h) (sat_cons (step719 p h) (sat_nil p)))
def c1931 : List Lit := [(141, false), (142, false)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c1529, c724] c1931 (by decide) p (sat_cons (step1529 p h) (sat_cons (step724 p h) (sat_nil p)))
def c1932 : List Lit := [(275, false), (281, false)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c1519, c730] c1932 (by decide) p (sat_cons (step1519 p h) (sat_cons (step730 p h) (sat_nil p)))
def c1933 : List Lit := [(283, false), (297, false)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c1511, c744] c1933 (by decide) p (sat_cons (step1511 p h) (sat_cons (step744 p h) (sat_nil p)))
def c1934 : List Lit := [(271, false), (299, false)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c1505, c749] c1934 (by decide) p (sat_cons (step1505 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1935 : List Lit := [(315, false), (317, false)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c1524, c765] c1935 (by decide) p (sat_cons (step1524 p h) (sat_cons (step765 p h) (sat_nil p)))
def c1936 : List Lit := [(313, false), (327, false)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c1510, c774] c1936 (by decide) p (sat_cons (step1510 p h) (sat_cons (step774 p h) (sat_nil p)))
def c1937 : List Lit := [(347, false), (353, false)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c1516, c795] c1937 (by decide) p (sat_cons (step1516 p h) (sat_cons (step795 p h) (sat_nil p)))
def c1938 : List Lit := [(341, false), (355, false)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c1509, c799] c1938 (by decide) p (sat_cons (step1509 p h) (sat_cons (step799 p h) (sat_nil p)))
def c1939 : List Lit := [(329, false), (357, false)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c1504, c803] c1939 (by decide) p (sat_cons (step1504 p h) (sat_cons (step803 p h) (sat_nil p)))
def c1940 : List Lit := [(301, false), (359, false)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c1501, c808] c1940 (by decide) p (sat_cons (step1501 p h) (sat_cons (step808 p h) (sat_nil p)))
def c1941 : List Lit := [(375, false), (377, false)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c1523, c822] c1941 (by decide) p (sat_cons (step1523 p h) (sat_cons (step822 p h) (sat_nil p)))
def c1942 : List Lit := [(379, false), (385, false)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c1515, c830] c1942 (by decide) p (sat_cons (step1515 p h) (sat_cons (step830 p h) (sat_nil p)))
def c1943 : List Lit := [(373, false), (387, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c1508, c835] c1943 (by decide) p (sat_cons (step1508 p h) (sat_cons (step835 p h) (sat_nil p)))
def c1944 : List Lit := [(389, false), (417, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c1503, c853] c1944 (by decide) p (sat_cons (step1503 p h) (sat_cons (step853 p h) (sat_nil p)))
def c1945 : List Lit := [(439, false), (441, false)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c1522, c872] c1945 (by decide) p (sat_cons (step1522 p h) (sat_cons (step872 p h) (sat_nil p)))
end B112E258
