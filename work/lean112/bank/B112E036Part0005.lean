import B112E036Part0004
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1965 : List Lit := [(123, true), (126, false), (127, true)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c826, c762] c1965 (by decide) p (sat_cons (step826 p h) (sat_cons (step762 p h) (sat_nil p)))
def c1966 : List Lit := [(303, false), (309, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c1663, c856] c1966 (by decide) p (sat_cons (step1663 p h) (sat_cons (step856 p h) (sat_nil p)))
def c1967 : List Lit := [(297, false), (311, false)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c1658, c860] c1967 (by decide) p (sat_cons (step1658 p h) (sat_cons (step860 p h) (sat_nil p)))
def c1968 : List Lit := [(283, false), (313, false)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c1653, c864] c1968 (by decide) p (sat_cons (step1653 p h) (sat_cons (step864 p h) (sat_nil p)))
def c1969 : List Lit := [(176, false), (177, false)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c1670, c873] c1969 (by decide) p (sat_cons (step1670 p h) (sat_cons (step873 p h) (sat_nil p)))
def c1970 : List Lit := [(359, false), (373, false)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c1657, c890] c1970 (by decide) p (sat_cons (step1657 p h) (sat_cons (step890 p h) (sat_nil p)))
def c1971 : List Lit := [(345, false), (375, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c1652, c895] c1971 (by decide) p (sat_cons (step1652 p h) (sat_cons (step895 p h) (sat_nil p)))
def c1972 : List Lit := [(315, false), (377, false)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c1649, c899] c1972 (by decide) p (sat_cons (step1649 p h) (sat_cons (step899 p h) (sat_nil p)))
def c1973 : List Lit := [(196, false), (197, false)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c1669, c905] c1973 (by decide) p (sat_cons (step1669 p h) (sat_cons (step905 p h) (sat_nil p)))
def c1974 : List Lit := [(385, false), (391, false)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1661, c911] c1974 (by decide) p (sat_cons (step1661 p h) (sat_cons (step911 p h) (sat_nil p)))
def c1975 : List Lit := [(393, false), (407, false)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c1656, c919] c1975 (by decide) p (sat_cons (step1656 p h) (sat_cons (step919 p h) (sat_nil p)))
def c1976 : List Lit := [(409, false), (439, false)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c1651, c933] c1976 (by decide) p (sat_cons (step1651 p h) (sat_cons (step933 p h) (sat_nil p)))
def c1977 : List Lit := [(463, false), (465, false)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c1665, c950] c1977 (by decide) p (sat_cons (step1665 p h) (sat_cons (step950 p h) (sat_nil p)))
def c1978 : List Lit := [(461, false), (467, false)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c1660, c954] c1978 (by decide) p (sat_cons (step1660 p h) (sat_cons (step954 p h) (sat_nil p)))
def c1979 : List Lit := [(455, false), (469, false)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c1655, c958] c1979 (by decide) p (sat_cons (step1655 p h) (sat_cons (step958 p h) (sat_nil p)))
def c1980 : List Lit := [(247, false), (248, false)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c1668, c963] c1980 (by decide) p (sat_cons (step1668 p h) (sat_cons (step963 p h) (sat_nil p)))
def c1981 : List Lit := [(477, false), (483, false)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c1659, c969] c1981 (by decide) p (sat_cons (step1659 p h) (sat_cons (step969 p h) (sat_nil p)))
def c1982 : List Lit := [(485, false), (499, false)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1654, c980] c1982 (by decide) p (sat_cons (step1654 p h) (sat_cons (step980 p h) (sat_nil p)))
def c1983 : List Lit := [(471, false), (501, false)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c1650, c985] c1983 (by decide) p (sat_cons (step1650 p h) (sat_cons (step985 p h) (sat_nil p)))
def c1984 : List Lit := [(441, false), (503, false)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c1648, c990] c1984 (by decide) p (sat_cons (step1648 p h) (sat_cons (step990 p h) (sat_nil p)))
def c1985 : List Lit := [(379, false), (505, false)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c995, c993] c1985 (by decide) p (sat_cons (step995 p h) (sat_cons (step993 p h) (sat_nil p)))
def c1986 : List Lit := [(1586, false), (1591, true)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1713, c1065] c1986 (by decide) p (sat_cons (step1713 p h) (sat_cons (step1065 p h) (sat_nil p)))
def c1987 : List Lit := [(1563, false), (1599, true)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1077] c1987 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c1988 : List Lit := [(1564, false), (1600, true)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1082] c1988 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c1989 : List Lit := [(1565, false), (1601, true)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1086] c1989 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1086 p h) (sat_nil p)))
def c1990 : List Lit := [(1566, false), (1602, true)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1091] c1990 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1091 p h) (sat_nil p)))
def c1991 : List Lit := [(1567, false), (1603, true)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1097] c1991 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1097 p h) (sat_nil p)))
def c1992 : List Lit := [(1568, false), (1604, true)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1101] c1992 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c1993 : List Lit := [(1639, false), (1656, true)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1684, c1191] c1993 (by decide) p (sat_cons (step1684 p h) (sat_cons (step1191 p h) (sat_nil p)))
def c1994 : List Lit := [(1640, false), (1657, true)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c1684, c1196] c1994 (by decide) p (sat_cons (step1684 p h) (sat_cons (step1196 p h) (sat_nil p)))
def c1995 : List Lit := [(1641, false), (1658, true)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c1684, c1200] c1995 (by decide) p (sat_cons (step1684 p h) (sat_cons (step1200 p h) (sat_nil p)))
def c1996 : List Lit := [(1642, false), (1659, true)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c1684, c1203] c1996 (by decide) p (sat_cons (step1684 p h) (sat_cons (step1203 p h) (sat_nil p)))
def c1997 : List Lit := [(1627, false), (1665, true)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c1685, c1208] c1997 (by decide) p (sat_cons (step1685 p h) (sat_cons (step1208 p h) (sat_nil p)))
def c1998 : List Lit := [(1628, false), (1666, true)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c1685, c1214] c1998 (by decide) p (sat_cons (step1685 p h) (sat_cons (step1214 p h) (sat_nil p)))
def c1999 : List Lit := [(1629, false), (1667, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c1685, c1220] c1999 (by decide) p (sat_cons (step1685 p h) (sat_cons (step1220 p h) (sat_nil p)))
def c2000 : List Lit := [(1668, true), (1630, false)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1685, c1227] c2000 (by decide) p (sat_cons (step1685 p h) (sat_cons (step1227 p h) (sat_nil p)))
def c2001 : List Lit := [(1669, true), (1631, false)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c1685, c1233] c2001 (by decide) p (sat_cons (step1685 p h) (sat_cons (step1233 p h) (sat_nil p)))
def c2002 : List Lit := [(1670, true), (1632, false)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c1685, c1239] c2002 (by decide) p (sat_cons (step1685 p h) (sat_cons (step1239 p h) (sat_nil p)))
def c2003 : List Lit := [(1711, false), (1724, true)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c1679, c1310] c2003 (by decide) p (sat_cons (step1679 p h) (sat_cons (step1310 p h) (sat_nil p)))
def c2004 : List Lit := [(1712, false), (1725, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c1679, c1314] c2004 (by decide) p (sat_cons (step1679 p h) (sat_cons (step1314 p h) (sat_nil p)))
def c2005 : List Lit := [(1713, false), (1726, true)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1679, c1317] c2005 (by decide) p (sat_cons (step1679 p h) (sat_cons (step1317 p h) (sat_nil p)))
def c2006 : List Lit := [(1714, false), (1727, true)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c1679, c1320] c2006 (by decide) p (sat_cons (step1679 p h) (sat_cons (step1320 p h) (sat_nil p)))
def c2007 : List Lit := [(1756, true), (1747, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c1680, c1354] c2007 (by decide) p (sat_cons (step1680 p h) (sat_cons (step1354 p h) (sat_nil p)))
def c2008 : List Lit := [(1748, false), (1757, true)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c1680, c1355] c2008 (by decide) p (sat_cons (step1680 p h) (sat_cons (step1355 p h) (sat_nil p)))
def c2009 : List Lit := [(1749, false), (1758, true)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c1680, c1356] c2009 (by decide) p (sat_cons (step1680 p h) (sat_cons (step1356 p h) (sat_nil p)))
def c2010 : List Lit := [(1750, false), (1759, true)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c1680, c1357] c2010 (by decide) p (sat_cons (step1680 p h) (sat_cons (step1357 p h) (sat_nil p)))
def c2011 : List Lit := [(1751, false), (1760, true)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c1680, c1358] c2011 (by decide) p (sat_cons (step1680 p h) (sat_cons (step1358 p h) (sat_nil p)))
def c2012 : List Lit := [(1691, false), (1855, false)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1579] c2012 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1579 p h) (sat_nil p)))
def c2013 : List Lit := [(1692, false), (1854, false)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1580] c2013 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1580 p h) (sat_nil p)))
def c2014 : List Lit := [(1693, false), (1853, false)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1581] c2014 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1581 p h) (sat_nil p)))
def c2015 : List Lit := [(1694, false), (1852, false)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1582] c2015 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1582 p h) (sat_nil p)))
def c2016 : List Lit := [(1695, false), (1851, false)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1583] c2016 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1583 p h) (sat_nil p)))
def c2017 : List Lit := [(1696, false), (1850, false)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1584] c2017 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1584 p h) (sat_nil p)))
def c2018 : List Lit := [(1697, false), (1849, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1585] c2018 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1585 p h) (sat_nil p)))
def c2019 : List Lit := [(1651, true), (56, true)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c1166, c1184, c1181, c1168, c1172, c1742, c1170] c2019 (by decide) p (sat_cons (step1166 p h) (sat_cons (step1184 p h) (sat_cons (step1181 p h) (sat_cons (step1168 p h) (sat_cons (step1172 p h) (sat_cons (step1742 p h) (sat_cons (step1170 p h) (sat_nil p))))))))
def c2020 : List Lit := [(110, false), (50, false), (49, false), (39, false)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c238, c241, c1835] c2020 (by decide) p (sat_cons (step238 p h) (sat_cons (step241 p h) (sat_cons (step1835 p h) (sat_nil p))))
def c2021 : List Lit := [(11, true), (1566, true), (1547, false), (6, false), (37, false)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c1779, c1005, c1035, c1021, c1010, c1012, c1018, c23, c20, c1038, c1001, c1006] c2021 (by decide) p (sat_cons (step1779 p h) (sat_cons (step1005 p h) (sat_cons (step1035 p h) (sat_cons (step1021 p h) (sat_cons (step1010 p h) (sat_cons (step1012 p h) (sat_cons (step1018 p h) (sat_cons (step23 p h) (sat_cons (step20 p h) (sat_cons (step1038 p h) (sat_cons (step1001 p h) (sat_cons (step1006 p h) (sat_nil p)))))))))))))
def c2022 : List Lit := [(91, true), (89, true), (92, false), (101, true), (232, true), (35, true), (103, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c1912, c1911, c1628, c638] c2022 (by decide) p (sat_cons (step1912 p h) (sat_cons (step1911 p h) (sat_cons (step1628 p h) (sat_cons (step638 p h) (sat_nil p)))))
def c2023 : List Lit := [(1615, true), (31, true), (35, true), (89, true)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1112, c1107, c1104, c1105, c132, c1825] c2023 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1112 p h) (sat_cons (step1107 p h) (sat_cons (step1104 p h) (sat_cons (step1105 p h) (sat_cons (step132 p h) (sat_cons (step1825 p h) (sat_nil p))))))))
def c2024 : List Lit := [(52, true), (1657, true), (35, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c1994, c1159, c1156, c1157, c1158, c1856, c1857, c1192, c1607, c1178, c1169, c1173, c1172, c1171, c1181, c1742, c1167] c2024 (by decide) p (sat_cons (step1994 p h) (sat_cons (step1159 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step1158 p h) (sat_cons (step1856 p h) (sat_cons (step1857 p h) (sat_cons (step1192 p h) (sat_cons (step1607 p h) (sat_cons (step1178 p h) (sat_cons (step1169 p h) (sat_cons (step1173 p h) (sat_cons (step1172 p h) (sat_cons (step1171 p h) (sat_cons (step1181 p h) (sat_cons (step1742 p h) (sat_cons (step1167 p h) (sat_nil p))))))))))))))))))
def c2025 : List Lit := [(1639, true), (1668, true), (1616, false), (35, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1160, c1155, c1686, c1856, c1857, c1142, c1607, c1221, c1169, c1188, c1172, c1178, c1181, c1173, c1167, c1171, c1742] c2025 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1160 p h) (sat_cons (step1155 p h) (sat_cons (step1686 p h) (sat_cons (step1856 p h) (sat_cons (step1857 p h) (sat_cons (step1142 p h) (sat_cons (step1607 p h) (sat_cons (step1221 p h) (sat_cons (step1169 p h) (sat_cons (step1188 p h) (sat_cons (step1172 p h) (sat_cons (step1178 p h) (sat_cons (step1181 p h) (sat_cons (step1173 p h) (sat_cons (step1167 p h) (sat_cons (step1171 p h) (sat_cons (step1742 p h) (sat_nil p)))))))))))))))))))
def c2026 : List Lit := [(1668, true), (1612, false), (34, false), (35, true)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c1115, c1141, c1216, c2024, c2025, c1993, c1221, c1145, c1142, c1116, c1124, c1107, c1122, c141] c2026 (by decide) p (sat_cons (step1115 p h) (sat_cons (step1141 p h) (sat_cons (step1216 p h) (sat_cons (step2024 p h) (sat_cons (step2025 p h) (sat_cons (step1993 p h) (sat_cons (step1221 p h) (sat_cons (step1145 p h) (sat_cons (step1142 p h) (sat_cons (step1116 p h) (sat_cons (step1124 p h) (sat_cons (step1107 p h) (sat_cons (step1122 p h) (sat_cons (step141 p h) (sat_nil p)))))))))))))))
def c2027 : List Lit := [(61, true), (1651, true)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c1178, c1173, c1169, c1171, c1172, c1742, c1181, c1167] c2027 (by decide) p (sat_cons (step1178 p h) (sat_cons (step1173 p h) (sat_cons (step1169 p h) (sat_cons (step1171 p h) (sat_cons (step1172 p h) (sat_cons (step1742 p h) (sat_cons (step1181 p h) (sat_cons (step1167 p h) (sat_nil p)))))))))
def c2028 : List Lit := [(59, false), (54, false), (61, false)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c1868, c255] c2028 (by decide) p (sat_cons (step1868 p h) (sat_cons (step255 p h) (sat_nil p)))
end B112E036
