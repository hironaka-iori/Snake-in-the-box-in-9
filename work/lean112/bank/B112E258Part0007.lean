import B112E258Part0006
namespace B112E258
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1946 : List Lit := [(437, false), (443, false)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c1514, c876] c1946 (by decide) p (sat_cons (step1514 p h) (sat_cons (step876 p h) (sat_nil p)))
def c1947 : List Lit := [(431, false), (445, false)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c1507, c880] c1947 (by decide) p (sat_cons (step1507 p h) (sat_cons (step880 p h) (sat_nil p)))
def c1948 : List Lit := [(461, false), (475, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c1506, c905] c1948 (by decide) p (sat_cons (step1506 p h) (sat_cons (step905 p h) (sat_nil p)))
def c1949 : List Lit := [(447, false), (477, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c1502, c909] c1949 (by decide) p (sat_cons (step1502 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1950 : List Lit := [(419, false), (479, false)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c1500, c914] c1950 (by decide) p (sat_cons (step1500 p h) (sat_cons (step914 p h) (sat_nil p)))
def c1951 : List Lit := [(361, false), (481, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c919, c917] c1951 (by decide) p (sat_cons (step919 p h) (sat_cons (step917 p h) (sat_nil p)))
def c1952 : List Lit := [(1568, false), (1600, true)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c1563, c1098] c1952 (by decide) p (sat_cons (step1563 p h) (sat_cons (step1098 p h) (sat_nil p)))
def c1953 : List Lit := [(1569, false), (1601, true)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c1563, c1103] c1953 (by decide) p (sat_cons (step1563 p h) (sat_cons (step1103 p h) (sat_nil p)))
def c1954 : List Lit := [(1570, false), (1602, true)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c1563, c1108] c1954 (by decide) p (sat_cons (step1563 p h) (sat_cons (step1108 p h) (sat_nil p)))
def c1955 : List Lit := [(1571, false), (1603, true)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c1563, c1111] c1955 (by decide) p (sat_cons (step1563 p h) (sat_cons (step1111 p h) (sat_nil p)))
def c1956 : List Lit := [(1618, true), (1544, false)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c1564, c1131] c1956 (by decide) p (sat_cons (step1564 p h) (sat_cons (step1131 p h) (sat_nil p)))
def c1957 : List Lit := [(1619, true), (1545, false)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c1564, c1137] c1957 (by decide) p (sat_cons (step1564 p h) (sat_cons (step1137 p h) (sat_nil p)))
def c1958 : List Lit := [(1620, true), (1546, false)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c1564, c1144] c1958 (by decide) p (sat_cons (step1564 p h) (sat_cons (step1144 p h) (sat_nil p)))
def c1959 : List Lit := [(1621, true), (1547, false)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c1564, c1150] c1959 (by decide) p (sat_cons (step1564 p h) (sat_cons (step1150 p h) (sat_nil p)))
def c1960 : List Lit := [(1622, true), (1548, false)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c1564, c1157] c1960 (by decide) p (sat_cons (step1564 p h) (sat_cons (step1157 p h) (sat_nil p)))
def c1961 : List Lit := [(1623, true), (1549, false)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c1564, c1162] c1961 (by decide) p (sat_cons (step1564 p h) (sat_cons (step1162 p h) (sat_nil p)))
def c1962 : List Lit := [(1624, true), (1550, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c1564, c1166] c1962 (by decide) p (sat_cons (step1564 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c1963 : List Lit := [(1665, false), (1673, true)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1250] c1963 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1250 p h) (sat_nil p)))
def c1964 : List Lit := [(1666, false), (1674, true)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1251] c1964 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1251 p h) (sat_nil p)))
def c1965 : List Lit := [(1667, false), (1675, true)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1252] c1965 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1252 p h) (sat_nil p)))
def c1966 : List Lit := [(1668, false), (1676, true)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1253] c1966 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1253 p h) (sat_nil p)))
def c1967 : List Lit := [(1669, false), (1677, true)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1254] c1967 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1254 p h) (sat_nil p)))
def c1968 : List Lit := [(1670, false), (1678, true)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1255] c1968 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1255 p h) (sat_nil p)))
def c1969 : List Lit := [(1732, true), (1699, false)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1364] c1969 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1364 p h) (sat_nil p)))
def c1970 : List Lit := [(1733, true), (1700, false)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1368] c1970 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1368 p h) (sat_nil p)))
def c1971 : List Lit := [(1734, true), (1701, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1372] c1971 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1372 p h) (sat_nil p)))
def c1972 : List Lit := [(1735, true), (1702, false)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1377] c1972 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1377 p h) (sat_nil p)))
def c1973 : List Lit := [(1703, false), (1736, true)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1382] c1973 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1382 p h) (sat_nil p)))
def c1974 : List Lit := [(1704, false), (1737, true)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1385] c1974 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1385 p h) (sat_nil p)))
def c1975 : List Lit := [(1734, false), (1750, true)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1388] c1975 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1388 p h) (sat_nil p)))
def c1976 : List Lit := [(1735, false), (1751, true)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1389] c1976 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1389 p h) (sat_nil p)))
def c1977 : List Lit := [(1736, false), (1752, true)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1390] c1977 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1390 p h) (sat_nil p)))
def c1978 : List Lit := [(1737, false), (1753, true)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1391] c1978 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1391 p h) (sat_nil p)))
def c1979 : List Lit := [(1738, false), (1754, true)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1392] c1979 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1392 p h) (sat_nil p)))
def c1980 : List Lit := [(1739, false), (1755, true)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1393] c1980 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1393 p h) (sat_nil p)))
def c1981 : List Lit := [(1675, false), (1750, true)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1407] c1981 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1407 p h) (sat_nil p)))
def c1982 : List Lit := [(1676, false), (1751, true)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1414] c1982 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1414 p h) (sat_nil p)))
def c1983 : List Lit := [(1677, false), (1752, true)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1421] c1983 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1421 p h) (sat_nil p)))
def c1984 : List Lit := [(1678, false), (1737, false)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c1566, c1432] c1984 (by decide) p (sat_cons (step1566 p h) (sat_cons (step1432 p h) (sat_nil p)))
def c1985 : List Lit := [(1679, false), (1754, true)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1433] c1985 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1433 p h) (sat_nil p)))
def c1986 : List Lit := [(1680, false), (1755, true)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1438] c1986 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1438 p h) (sat_nil p)))
def c1987 : List Lit := [(1617, false), (1758, false)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1442] c1987 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1442 p h) (sat_nil p)))
def c1988 : List Lit := [(1618, false), (1757, false)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1443] c1988 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1443 p h) (sat_nil p)))
def c1989 : List Lit := [(1619, false), (1756, false)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1444] c1989 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1444 p h) (sat_nil p)))
def c1990 : List Lit := [(1620, false), (1755, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1445] c1990 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1445 p h) (sat_nil p)))
def c1991 : List Lit := [(1621, false), (1754, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1446] c1991 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1446 p h) (sat_nil p)))
def c1992 : List Lit := [(1622, false), (1753, false)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1447] c1992 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1447 p h) (sat_nil p)))
def c1993 : List Lit := [(1623, false), (1752, false)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1448] c1993 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1448 p h) (sat_nil p)))
def c1994 : List Lit := [(1624, false), (1751, false)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1449] c1994 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1449 p h) (sat_nil p)))
def c1995 : List Lit := [(1625, false), (1750, false)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1450] c1995 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1450 p h) (sat_nil p)))
def c1996 : List Lit := [(1626, false), (1749, false)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1451] c1996 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1451 p h) (sat_nil p)))
def c1997 : List Lit := [(83, true), (1669, true), (1689, false), (99, false), (98, false), (90, false), (1701, false), (105, true), (79, true), (81, true), (1757, true), (1646, false), (64, true), (85, true)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1215, c1243, c1766, c1219, c1228, c1229, c1242, c1247, c1220, c1260, c1216, c486, c1426, c1211, c1877, c1374, c1775, c1732, c1378, c1298, c1318, c1300] c1997 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1215 p h) (sat_cons (step1243 p h) (sat_cons (step1766 p h) (sat_cons (step1219 p h) (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step1242 p h) (sat_cons (step1247 p h) (sat_cons (step1220 p h) (sat_cons (step1260 p h) (sat_cons (step1216 p h) (sat_cons (step486 p h) (sat_cons (step1426 p h) (sat_cons (step1211 p h) (sat_cons (step1877 p h) (sat_cons (step1374 p h) (sat_cons (step1775 p h) (sat_cons (step1732 p h) (sat_cons (step1378 p h) (sat_cons (step1298 p h) (sat_cons (step1318 p h) (sat_cons (step1300 p h) (sat_nil p))))))))))))))))))))))))
def c1998 : List Lit := [(1658, false), (83, false), (1678, true), (79, true), (81, true), (1642, false)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1215, c1192, c1261, c1243, c1228, c1229, c1242, c1247, c1221, c1267, c1216, c1197, c1211, c1172, c448, c1170] c1998 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1215 p h) (sat_cons (step1192 p h) (sat_cons (step1261 p h) (sat_cons (step1243 p h) (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step1242 p h) (sat_cons (step1247 p h) (sat_cons (step1221 p h) (sat_cons (step1267 p h) (sat_cons (step1216 p h) (sat_cons (step1197 p h) (sat_cons (step1211 p h) (sat_cons (step1172 p h) (sat_cons (step448 p h) (sat_cons (step1170 p h) (sat_nil p))))))))))))))))))
def c1999 : List Lit := [(86, false), (84, false), (83, false), (1678, true), (79, true), (81, true), (1642, false), (1661, false)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c451, c455, c1170, c1211, c1172, c1216, c1197, c1246, c1267] c1999 (by decide) p (sat_cons (step451 p h) (sat_cons (step455 p h) (sat_cons (step1170 p h) (sat_cons (step1211 p h) (sat_cons (step1172 p h) (sat_cons (step1216 p h) (sat_cons (step1197 p h) (sat_cons (step1246 p h) (sat_cons (step1267 p h) (sat_nil p))))))))))
def c2000 : List Lit := [(99, false), (98, false), (90, false), (1701, false), (105, true), (79, true), (1695, false), (93, true), (81, true), (1757, true), (1642, false), (1543, false), (64, true), (85, true), (67, false)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1215, c1192, c1217, c1225, c1778, c1287, c1289, c1725, c1430, c1261, c1997, c1998, c1219, c1999, c1221, c1226, c1242, c1247, c1267, c1216, c1197, c1211, c1172, c447, c1170] c2000 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1215 p h) (sat_cons (step1192 p h) (sat_cons (step1217 p h) (sat_cons (step1225 p h) (sat_cons (step1778 p h) (sat_cons (step1287 p h) (sat_cons (step1289 p h) (sat_cons (step1725 p h) (sat_cons (step1430 p h) (sat_cons (step1261 p h) (sat_cons (step1997 p h) (sat_cons (step1998 p h) (sat_cons (step1219 p h) (sat_cons (step1999 p h) (sat_cons (step1221 p h) (sat_cons (step1226 p h) (sat_cons (step1242 p h) (sat_cons (step1247 p h) (sat_cons (step1267 p h) (sat_cons (step1216 p h) (sat_cons (step1197 p h) (sat_cons (step1211 p h) (sat_cons (step1172 p h) (sat_cons (step447 p h) (sat_cons (step1170 p h) (sat_nil p)))))))))))))))))))))))))))
def c2001 : List Lit := [(82, false), (1668, false), (84, false), (83, false), (105, true), (1695, false), (93, true), (1757, true), (1642, false), (64, true), (67, false)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c456, c447, c1287, c1170, c1289, c1172, c1725, c1197, c1430, c1267] c2001 (by decide) p (sat_cons (step456 p h) (sat_cons (step447 p h) (sat_cons (step1287 p h) (sat_cons (step1170 p h) (sat_cons (step1289 p h) (sat_cons (step1172 p h) (sat_cons (step1725 p h) (sat_cons (step1197 p h) (sat_cons (step1430 p h) (sat_cons (step1267 p h) (sat_nil p)))))))))))
def c2002 : List Lit := [(1735, true), (1691, false), (1701, false), (103, false), (1688, false), (64, true), (67, false)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c1972, c1373, c1314, c1769, c1303] c2002 (by decide) p (sat_cons (step1972 p h) (sat_cons (step1373 p h) (sat_cons (step1314 p h) (sat_cons (step1769 p h) (sat_cons (step1303 p h) (sat_nil p))))))
def c2003 : List Lit := [(84, false), (83, false), (1678, true), (105, true), (79, true), (1695, false), (93, true), (81, true), (1757, true), (1642, false), (1657, false), (64, true), (67, false)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c1192, c1261, c1210, c1215, c1225, c1999, c1221, c1226, c1242, c1247, c2001, c1216, c1211] c2003 (by decide) p (sat_cons (step1192 p h) (sat_cons (step1261 p h) (sat_cons (step1210 p h) (sat_cons (step1215 p h) (sat_cons (step1225 p h) (sat_cons (step1999 p h) (sat_cons (step1221 p h) (sat_cons (step1226 p h) (sat_cons (step1242 p h) (sat_cons (step1247 p h) (sat_cons (step2001 p h) (sat_cons (step1216 p h) (sat_cons (step1211 p h) (sat_nil p))))))))))))))
def c2004 : List Lit := [(83, false), (1678, true), (105, true), (79, true), (1695, false), (93, true), (81, true), (1757, true), (1642, false), (64, true), (85, true), (67, false)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c1217, c2003, c1998, c1219] c2004 (by decide) p (sat_cons (step1217 p h) (sat_cons (step2003 p h) (sat_cons (step1998 p h) (sat_cons (step1219 p h) (sat_nil p)))))
def c2005 : List Lit := [(1668, false), (1735, false), (75, true), (1600, false), (64, true), (85, true), (69, true), (8, true), (65, false)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1532, c924, c1607, c1125, c1988, c1430, c1658, c1192, c1260, c1267, c1425, c1193, c1989, c1132, c1598, c931, c1597, c1729, c1181, c1179, c1189] c2005 (by decide) p (sat_cons (step1532 p h) (sat_cons (step924 p h) (sat_cons (step1607 p h) (sat_cons (step1125 p h) (sat_cons (step1988 p h) (sat_cons (step1430 p h) (sat_cons (step1658 p h) (sat_cons (step1192 p h) (sat_cons (step1260 p h) (sat_cons (step1267 p h) (sat_cons (step1425 p h) (sat_cons (step1193 p h) (sat_cons (step1989 p h) (sat_cons (step1132 p h) (sat_cons (step1598 p h) (sat_cons (step931 p h) (sat_cons (step1597 p h) (sat_cons (step1729 p h) (sat_cons (step1181 p h) (sat_cons (step1179 p h) (sat_cons (step1189 p h) (sat_nil p))))))))))))))))))))))
def c2006 : List Lit := [(1736, true), (110, false), (1724, false), (1691, false), (1701, false), (105, true), (1688, false)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c1374, c1378, c1732, c1314, c1298, c1303] c2006 (by decide) p (sat_cons (step1374 p h) (sat_cons (step1378 p h) (sat_cons (step1732 p h) (sat_cons (step1314 p h) (sat_cons (step1298 p h) (sat_cons (step1303 p h) (sat_nil p)))))))
def c2007 : List Lit := [(1736, false), (1667, false), (75, true), (1600, false), (64, true), (85, true), (69, true), (8, true), (65, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c1658, c1192, c1259, c1532, c924, c1607, c1125, c1988, c1419, c1426, c1989, c1132, c1598, c931, c1597, c1729, c1266, c1181, c1179, c1193, c1189] c2007 (by decide) p (sat_cons (step1658 p h) (sat_cons (step1192 p h) (sat_cons (step1259 p h) (sat_cons (step1532 p h) (sat_cons (step924 p h) (sat_cons (step1607 p h) (sat_cons (step1125 p h) (sat_cons (step1988 p h) (sat_cons (step1419 p h) (sat_cons (step1426 p h) (sat_cons (step1989 p h) (sat_cons (step1132 p h) (sat_cons (step1598 p h) (sat_cons (step931 p h) (sat_cons (step1597 p h) (sat_cons (step1729 p h) (sat_cons (step1266 p h) (sat_cons (step1181 p h) (sat_cons (step1179 p h) (sat_cons (step1193 p h) (sat_cons (step1189 p h) (sat_nil p))))))))))))))))))))))
def c2008 : List Lit := [(1724, false), (88, false), (82, false), (83, true), (1696, false), (1691, false), (1701, false), (105, true), (1736, true), (1686, false), (64, true)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1378, c2006, c1318, c1877, c1291, c482] c2008 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1378 p h) (sat_cons (step2006 p h) (sat_cons (step1318 p h) (sat_cons (step1877 p h) (sat_cons (step1291 p h) (sat_cons (step482 p h) (sat_nil p))))))))
def c2009 : List Lit := [(1691, false), (1701, false), (105, true), (103, false), (93, true), (81, true), (68, false), (65, false), (67, false)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c1286, c1288, c326, c332, c333, c1484, c1714, c320, c1217, c1225, c1210, c1772, c1215, c1241, c2007, c1973, c1315, c1771, c1299, c1532, c924, c1607, c1125, c1988, c1658, c1302, c2002, c1430, c2005, c2004, c1246, c1242, c1216, c1228, c1226, c1211, c1219, c1220, c1766, c2008, c1769, c1735, c1306, c1877, c1295, c483] c2009 (by decide) p (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step326 p h) (sat_cons (step332 p h) (sat_cons (step333 p h) (sat_cons (step1484 p h) (sat_cons (step1714 p h) (sat_cons (step320 p h) (sat_cons (step1217 p h) (sat_cons (step1225 p h) (sat_cons (step1210 p h) (sat_cons (step1772 p h) (sat_cons (step1215 p h) (sat_cons (step1241 p h) (sat_cons (step2007 p h) (sat_cons (step1973 p h) (sat_cons (step1315 p h) (sat_cons (step1771 p h) (sat_cons (step1299 p h) (sat_cons (step1532 p h) (sat_cons (step924 p h) (sat_cons (step1607 p h) (sat_cons (step1125 p h) (sat_cons (step1988 p h) (sat_cons (step1658 p h) (sat_cons (step1302 p h) (sat_cons (step2002 p h) (sat_cons (step1430 p h) (sat_cons (step2005 p h) (sat_cons (step2004 p h) (sat_cons (step1246 p h) (sat_cons (step1242 p h) (sat_cons (step1216 p h) (sat_cons (step1228 p h) (sat_cons (step1226 p h) (sat_cons (step1211 p h) (sat_cons (step1219 p h) (sat_cons (step1220 p h) (sat_cons (step1766 p h) (sat_cons (step2008 p h) (sat_cons (step1769 p h) (sat_cons (step1735 p h) (sat_cons (step1306 p h) (sat_cons (step1877 p h) (sat_cons (step1295 p h) (sat_cons (step483 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
end B112E258
