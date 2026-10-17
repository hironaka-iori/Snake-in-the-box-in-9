import B112E256Part0000
namespace B112E256
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1908 : List Lit := [(2, false), (921, true), (129, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c1845, c1261, c1238, c1235, c1257, c1251, c1243, c11, c243] c1908 (by decide) p (sat_cons (step1845 p h) (sat_cons (step1261 p h) (sat_cons (step1238 p h) (sat_cons (step1235 p h) (sat_cons (step1257 p h) (sat_cons (step1251 p h) (sat_cons (step1243 p h) (sat_cons (step11 p h) (sat_cons (step243 p h) (sat_nil p))))))))))
def c1909 : List Lit := [(993, false), (1037, true), (990, false), (106, false), (78, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c536, c1476, c533, c1479, c1485, c534, c1491, c1498, c1514, c1544, c1463, c1451, c1452, c1462, c1446, c1539, c1515, c1519, c1501, c1499, c1488, c1492, c1494, c1478, c565, c500, c496] c1909 (by decide) p (sat_cons (step536 p h) (sat_cons (step1476 p h) (sat_cons (step533 p h) (sat_cons (step1479 p h) (sat_cons (step1485 p h) (sat_cons (step534 p h) (sat_cons (step1491 p h) (sat_cons (step1498 p h) (sat_cons (step1514 p h) (sat_cons (step1544 p h) (sat_cons (step1463 p h) (sat_cons (step1451 p h) (sat_cons (step1452 p h) (sat_cons (step1462 p h) (sat_cons (step1446 p h) (sat_cons (step1539 p h) (sat_cons (step1515 p h) (sat_cons (step1519 p h) (sat_cons (step1501 p h) (sat_cons (step1499 p h) (sat_cons (step1488 p h) (sat_cons (step1492 p h) (sat_cons (step1494 p h) (sat_cons (step1478 p h) (sat_cons (step565 p h) (sat_cons (step500 p h) (sat_cons (step496 p h) (sat_nil p))))))))))))))))))))))))))))
def c1910 : List Lit := [(1059, false), (1096, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c1662, c1590, c1594, c1657, c1568, c1570, c1638, c1641, c1566, c1563, c1630, c1632, c1617, c1627, c1628, c1624, c1615, c768, c707, c607] c1910 (by decide) p (sat_cons (step1662 p h) (sat_cons (step1590 p h) (sat_cons (step1594 p h) (sat_cons (step1657 p h) (sat_cons (step1568 p h) (sat_cons (step1570 p h) (sat_cons (step1638 p h) (sat_cons (step1641 p h) (sat_cons (step1566 p h) (sat_cons (step1563 p h) (sat_cons (step1630 p h) (sat_cons (step1632 p h) (sat_cons (step1617 p h) (sat_cons (step1627 p h) (sat_cons (step1628 p h) (sat_cons (step1624 p h) (sat_cons (step1615 p h) (sat_cons (step768 p h) (sat_cons (step707 p h) (sat_cons (step607 p h) (sat_nil p)))))))))))))))))))))
def c1911 : List Lit := [(1047, true), (220, true), (94, true), (101, false)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c1562, c1563, c637, c605] c1911 (by decide) p (sat_cons (step1562 p h) (sat_cons (step1563 p h) (sat_cons (step637 p h) (sat_cons (step605 p h) (sat_nil p)))))
def c1912 : List Lit := [(103, false), (108, false), (111, false), (230, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c658, c687] c1912 (by decide) p (sat_cons (step658 p h) (sat_cons (step687 p h) (sat_nil p)))
def c1913 : List Lit := [(911, false), (956, true), (50, false), (940, false), (915, false), (111, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c1304, c1352, c1249, c1267, c1268, c1346, c1252, c1309, c1244, c1282, c341, c1279] c1913 (by decide) p (sat_cons (step1304 p h) (sat_cons (step1352 p h) (sat_cons (step1249 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step1346 p h) (sat_cons (step1252 p h) (sat_cons (step1309 p h) (sat_cons (step1244 p h) (sat_cons (step1282 p h) (sat_cons (step341 p h) (sat_cons (step1279 p h) (sat_nil p)))))))))))))
def c1914 : List Lit := [(23, false), (852, true), (6, false), (78, false)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c36, c46, c1104, c1098] c1914 (by decide) p (sat_cons (step36 p h) (sat_cons (step46 p h) (sat_cons (step1104 p h) (sat_cons (step1098 p h) (sat_nil p)))))
def c1915 : List Lit := [(923, true), (43, true), (53, false), (2, false), (41, true), (7, true)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c1845, c1847, c774, c1244, c1247, c1252, c1259, c1263, c1255, c1253, c1238, c1245, c1248, c1235, c243, c11, c835, c836, c846, c866, c902, c973, c967, c931, c927, c924, c920, c294, c295, c364, c72] c1915 (by decide) p (sat_cons (step1845 p h) (sat_cons (step1847 p h) (sat_cons (step774 p h) (sat_cons (step1244 p h) (sat_cons (step1247 p h) (sat_cons (step1252 p h) (sat_cons (step1259 p h) (sat_cons (step1263 p h) (sat_cons (step1255 p h) (sat_cons (step1253 p h) (sat_cons (step1238 p h) (sat_cons (step1245 p h) (sat_cons (step1248 p h) (sat_cons (step1235 p h) (sat_cons (step243 p h) (sat_cons (step11 p h) (sat_cons (step835 p h) (sat_cons (step836 p h) (sat_cons (step846 p h) (sat_cons (step866 p h) (sat_cons (step902 p h) (sat_cons (step973 p h) (sat_cons (step967 p h) (sat_cons (step931 p h) (sat_cons (step927 p h) (sat_cons (step924 p h) (sat_cons (step920 p h) (sat_cons (step294 p h) (sat_cons (step295 p h) (sat_cons (step364 p h) (sat_cons (step72 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1916 : List Lit := [(122, false), (1074, true), (124, false), (126, false), (121, true), (497, true)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c1080, c1062, c1060, c1057, c1078, c1075, c1067, c1066, c768, c708, c747, c1616, c725] c1916 (by decide) p (sat_cons (step1080 p h) (sat_cons (step1062 p h) (sat_cons (step1060 p h) (sat_cons (step1057 p h) (sat_cons (step1078 p h) (sat_cons (step1075 p h) (sat_cons (step1067 p h) (sat_cons (step1066 p h) (sat_cons (step768 p h) (sat_cons (step708 p h) (sat_cons (step747 p h) (sat_cons (step1616 p h) (sat_cons (step725 p h) (sat_nil p))))))))))))))
def c1917 : List Lit := [(105, false), (43, false), (113, false), (114, true), (232, true)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c662, c660] c1917 (by decide) p (sat_cons (step662 p h) (sat_cons (step660 p h) (sat_nil p)))
def c1918 : List Lit := [(20, true), (2, false), (38, true)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c1845, c9] c1918 (by decide) p (sat_cons (step1845 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1919 : List Lit := [(2, false), (38, true), (129, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c1845, c11] c1919 (by decide) p (sat_cons (step1845 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1920 : List Lit := [(20, true), (2, false), (129, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c1845, c12] c1920 (by decide) p (sat_cons (step1845 p h) (sat_cons (step12 p h) (sat_nil p)))
def c1921 : List Lit := [(3, false), (21, true)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c770, c13] c1921 (by decide) p (sat_cons (step770 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1922 : List Lit := [(3, false), (1, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c770, c14] c1922 (by decide) p (sat_cons (step770 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1923 : List Lit := [(8, false), (25, true), (43, true)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c773, c66] c1923 (by decide) p (sat_cons (step773 p h) (sat_cons (step66 p h) (sat_nil p)))
def c1924 : List Lit := [(8, false), (43, true), (5, true)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c773, c67] c1924 (by decide) p (sat_cons (step773 p h) (sat_cons (step67 p h) (sat_nil p)))
def c1925 : List Lit := [(8, false), (25, true), (5, true)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c773, c68] c1925 (by decide) p (sat_cons (step773 p h) (sat_cons (step68 p h) (sat_nil p)))
def c1926 : List Lit := [(44, true), (9, false), (18, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c774, c70] c1926 (by decide) p (sat_cons (step774 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1927 : List Lit := [(9, false), (44, true), (7, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c774, c71] c1927 (by decide) p (sat_cons (step774 p h) (sat_cons (step71 p h) (sat_nil p)))
def c1928 : List Lit := [(9, false), (18, true), (7, true)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c774, c72] c1928 (by decide) p (sat_cons (step774 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1929 : List Lit := [(12, false), (27, false), (10, false)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c535, c74] c1929 (by decide) p (sat_cons (step535 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1930 : List Lit := [(137, false), (27, false)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c535, c75] c1930 (by decide) p (sat_cons (step535 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1931 : List Lit := [(12, false), (30, true), (47, true)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c775, c83] c1931 (by decide) p (sat_cons (step775 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1932 : List Lit := [(12, false), (47, true), (10, true)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c775, c84] c1932 (by decide) p (sat_cons (step775 p h) (sat_cons (step84 p h) (sat_nil p)))
def c1933 : List Lit := [(12, false), (30, true), (10, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c775, c85] c1933 (by decide) p (sat_cons (step775 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1934 : List Lit := [(13, false), (49, true), (18, true)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c776, c87] c1934 (by decide) p (sat_cons (step776 p h) (sat_cons (step87 p h) (sat_nil p)))
def c1935 : List Lit := [(11, true), (13, false), (18, true)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c776, c88] c1935 (by decide) p (sat_cons (step776 p h) (sat_cons (step88 p h) (sat_nil p)))
def c1936 : List Lit := [(53, true), (16, false), (18, true), (33, true), (90, true)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c777, c112] c1936 (by decide) p (sat_cons (step777 p h) (sat_cons (step112 p h) (sat_nil p)))
def c1937 : List Lit := [(16, false), (53, true), (90, true), (14, true), (18, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c777, c113] c1937 (by decide) p (sat_cons (step777 p h) (sat_cons (step113 p h) (sat_nil p)))
def c1938 : List Lit := [(91, true), (34, true), (17, false), (18, true)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c778, c118] c1938 (by decide) p (sat_cons (step778 p h) (sat_cons (step118 p h) (sat_nil p)))
def c1939 : List Lit := [(20, false), (19, true)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c779, c141] c1939 (by decide) p (sat_cons (step779 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1940 : List Lit := [(20, false), (2, true)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c779, c142] c1940 (by decide) p (sat_cons (step779 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1941 : List Lit := [(22, false), (58, true)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c780, c148] c1941 (by decide) p (sat_cons (step780 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1942 : List Lit := [(22, false), (21, true)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c780, c149] c1942 (by decide) p (sat_cons (step780 p h) (sat_cons (step149 p h) (sat_nil p)))
def c1943 : List Lit := [(24, false), (60, true), (23, true)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c781, c155] c1943 (by decide) p (sat_cons (step781 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1944 : List Lit := [(60, true), (24, false), (7, true)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c781, c156] c1944 (by decide) p (sat_cons (step781 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1945 : List Lit := [(24, false), (23, true), (7, true)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c781, c157] c1945 (by decide) p (sat_cons (step781 p h) (sat_cons (step157 p h) (sat_nil p)))
def c1946 : List Lit := [(62, true), (34, true), (26, false)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c782, c164] c1946 (by decide) p (sat_cons (step782 p h) (sat_cons (step164 p h) (sat_nil p)))
def c1947 : List Lit := [(25, true), (34, true), (26, false)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c782, c165] c1947 (by decide) p (sat_cons (step782 p h) (sat_cons (step165 p h) (sat_nil p)))
def c1948 : List Lit := [(28, true), (27, false), (30, true), (10, true), (63, true)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c783, c176] c1948 (by decide) p (sat_cons (step783 p h) (sat_cons (step176 p h) (sat_nil p)))
def c1949 : List Lit := [(27, false), (19, true), (10, true), (30, true), (63, true)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c783, c177] c1949 (by decide) p (sat_cons (step783 p h) (sat_cons (step177 p h) (sat_nil p)))
def c1950 : List Lit := [(28, true), (29, false), (65, true)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c784, c185] c1950 (by decide) p (sat_cons (step784 p h) (sat_cons (step185 p h) (sat_nil p)))
def c1951 : List Lit := [(11, true), (29, false), (65, true)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c784, c186] c1951 (by decide) p (sat_cons (step784 p h) (sat_cons (step186 p h) (sat_nil p)))
def c1952 : List Lit := [(11, true), (28, true), (29, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c784, c187] c1952 (by decide) p (sat_cons (step784 p h) (sat_cons (step187 p h) (sat_nil p)))
def c1953 : List Lit := [(31, false), (34, true), (68, true)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c785, c197] c1953 (by decide) p (sat_cons (step785 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1954 : List Lit := [(34, true), (30, true), (31, false)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c785, c198] c1954 (by decide) p (sat_cons (step785 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1955 : List Lit := [(32, false), (70, true), (34, true)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c786, c200] c1955 (by decide) p (sat_cons (step786 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1956 : List Lit := [(32, false), (15, true), (34, true)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c786, c201] c1956 (by decide) p (sat_cons (step786 p h) (sat_cons (step201 p h) (sat_nil p)))
def c1957 : List Lit := [(34, true), (101, true), (18, true), (35, false)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c787, c221] c1957 (by decide) p (sat_cons (step787 p h) (sat_cons (step221 p h) (sat_nil p)))
def c1958 : List Lit := [(37, false), (36, true), (41, true)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c788, c240] c1958 (by decide) p (sat_cons (step788 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1959 : List Lit := [(1, true), (37, false), (41, true)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c788, c241] c1959 (by decide) p (sat_cons (step788 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1960 : List Lit := [(37, false), (36, true), (1, true)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c788, c242] c1960 (by decide) p (sat_cons (step788 p h) (sat_cons (step242 p h) (sat_nil p)))
def c1961 : List Lit := [(45, true), (38, false), (36, true), (42, true)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c789, c247] c1961 (by decide) p (sat_cons (step789 p h) (sat_cons (step247 p h) (sat_nil p)))
def c1962 : List Lit := [(45, true), (38, false), (2, true), (42, true)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c789, c248] c1962 (by decide) p (sat_cons (step789 p h) (sat_cons (step248 p h) (sat_nil p)))
def c1963 : List Lit := [(45, true), (38, false), (2, true), (36, true)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c789, c249] c1963 (by decide) p (sat_cons (step789 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1964 : List Lit := [(2, true), (38, false), (42, true), (36, true)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c789, c250] c1964 (by decide) p (sat_cons (step789 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1965 : List Lit := [(39, false), (57, true), (43, true), (47, true)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c790, c255] c1965 (by decide) p (sat_cons (step790 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1966 : List Lit := [(39, false), (57, true), (43, true), (36, true)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c790, c256] c1966 (by decide) p (sat_cons (step790 p h) (sat_cons (step256 p h) (sat_nil p)))
def c1967 : List Lit := [(39, false), (36, true), (43, true), (47, true)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c790, c257] c1967 (by decide) p (sat_cons (step790 p h) (sat_cons (step257 p h) (sat_nil p)))
def c1968 : List Lit := [(42, true), (36, true), (40, false), (43, true), (41, true)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c791, c268] c1968 (by decide) p (sat_cons (step791 p h) (sat_cons (step268 p h) (sat_nil p)))
def c1969 : List Lit := [(42, true), (36, true), (5, true), (43, true), (40, false)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c791, c269] c1969 (by decide) p (sat_cons (step791 p h) (sat_cons (step269 p h) (sat_nil p)))
def c1970 : List Lit := [(53, true), (111, true), (50, false), (41, true)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c794, c342] c1970 (by decide) p (sat_cons (step794 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1971 : List Lit := [(50, false), (14, true), (111, true), (53, true)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c794, c343] c1971 (by decide) p (sat_cons (step794 p h) (sat_cons (step343 p h) (sat_nil p)))
end B112E256
