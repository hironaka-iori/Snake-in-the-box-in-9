import B112E052Inputs
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1990 : List Lit := [(13, true)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c2, c1] c1990 (by decide) p (sat_cons (step2 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1991 : List Lit := [(7, false), (6, false), (44, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c1990, c19] c1991 (by decide) p (sat_cons (step1990 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1992 : List Lit := [(7, false), (6, false), (79, false)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1990, c20] c1992 (by decide) p (sat_cons (step1990 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1993 : List Lit := [(7, false), (44, false), (79, false)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1990, c21] c1993 (by decide) p (sat_cons (step1990 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1994 : List Lit := [(140, true), (7, true), (11, true), (12, true)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c1990, c32] c1994 (by decide) p (sat_cons (step1990 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1995 : List Lit := [(10, false)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c974, c29] c1995 (by decide) p (sat_cons (step974 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1996 : List Lit := [(11, false)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c975, c30] c1996 (by decide) p (sat_cons (step975 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1997 : List Lit := [(12, false)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c976, c31] c1997 (by decide) p (sat_cons (step976 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1998 : List Lit := [(502, false)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c1246, c1243] c1998 (by decide) p (sat_cons (step1246 p h) (sat_cons (step1243 p h) (sat_nil p)))
def c1999 : List Lit := [(378, false)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c1246, c1245] c1999 (by decide) p (sat_cons (step1246 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c2000 : List Lit := [(500, false)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1998, c1239] c2000 (by decide) p (sat_cons (step1998 p h) (sat_cons (step1239 p h) (sat_nil p)))
def c2001 : List Lit := [(438, false)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c1998, c1242] c2001 (by decide) p (sat_cons (step1998 p h) (sat_cons (step1242 p h) (sat_nil p)))
def c2002 : List Lit := [(376, false)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c1999, c1136] c2002 (by decide) p (sat_cons (step1999 p h) (sat_cons (step1136 p h) (sat_nil p)))
def c2003 : List Lit := [(314, false)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c1999, c1139] c2003 (by decide) p (sat_cons (step1999 p h) (sat_cons (step1139 p h) (sat_nil p)))
def c2004 : List Lit := [(498, false)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c2000, c1234] c2004 (by decide) p (sat_cons (step2000 p h) (sat_cons (step1234 p h) (sat_nil p)))
def c2005 : List Lit := [(468, false)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c2000, c1237] c2005 (by decide) p (sat_cons (step2000 p h) (sat_cons (step1237 p h) (sat_nil p)))
def c2006 : List Lit := [(436, false)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c2001, c1182] c2006 (by decide) p (sat_cons (step2001 p h) (sat_cons (step1182 p h) (sat_nil p)))
def c2007 : List Lit := [(406, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c2001, c1185] c2007 (by decide) p (sat_cons (step2001 p h) (sat_cons (step1185 p h) (sat_nil p)))
def c2008 : List Lit := [(374, false)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c2002, c1131] c2008 (by decide) p (sat_cons (step2002 p h) (sat_cons (step1131 p h) (sat_nil p)))
def c2009 : List Lit := [(344, false)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c2002, c1134] c2009 (by decide) p (sat_cons (step2002 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c2010 : List Lit := [(312, false)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c2003, c1082] c2010 (by decide) p (sat_cons (step2003 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c2011 : List Lit := [(282, false)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c2003, c1085] c2011 (by decide) p (sat_cons (step2003 p h) (sat_cons (step1085 p h) (sat_nil p)))
def c2012 : List Lit := [(496, false)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c2004, c1229] c2012 (by decide) p (sat_cons (step2004 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c2013 : List Lit := [(482, false)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c2004, c1232] c2013 (by decide) p (sat_cons (step2004 p h) (sat_cons (step1232 p h) (sat_nil p)))
def c2014 : List Lit := [(452, false)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c2005, c1210] c2014 (by decide) p (sat_cons (step2005 p h) (sat_cons (step1210 p h) (sat_nil p)))
def c2015 : List Lit := [(434, false)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c2006, c1178] c2015 (by decide) p (sat_cons (step2006 p h) (sat_cons (step1178 p h) (sat_nil p)))
def c2016 : List Lit := [(404, false)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c2007, c1159] c2016 (by decide) p (sat_cons (step2007 p h) (sat_cons (step1159 p h) (sat_nil p)))
def c2017 : List Lit := [(358, false)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c2008, c1129] c2017 (by decide) p (sat_cons (step2008 p h) (sat_cons (step1129 p h) (sat_nil p)))
def c2018 : List Lit := [(342, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c2009, c1103] c2018 (by decide) p (sat_cons (step2009 p h) (sat_cons (step1103 p h) (sat_nil p)))
def c2019 : List Lit := [(328, false)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c2009, c1106] c2019 (by decide) p (sat_cons (step2009 p h) (sat_cons (step1106 p h) (sat_nil p)))
def c2020 : List Lit := [(310, false)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c2010, c1078] c2020 (by decide) p (sat_cons (step2010 p h) (sat_cons (step1078 p h) (sat_nil p)))
def c2021 : List Lit := [(280, false)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c2011, c1056] c2021 (by decide) p (sat_cons (step2011 p h) (sat_cons (step1056 p h) (sat_nil p)))
def c2022 : List Lit := [(266, false)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c2011, c1059] c2022 (by decide) p (sat_cons (step2011 p h) (sat_cons (step1059 p h) (sat_nil p)))
def c2023 : List Lit := [(444, false)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c2014, c1195] c2023 (by decide) p (sat_cons (step2014 p h) (sat_cons (step1195 p h) (sat_nil p)))
def c2024 : List Lit := [(396, false)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c2016, c1157] c2024 (by decide) p (sat_cons (step2016 p h) (sat_cons (step1157 p h) (sat_nil p)))
def c2025 : List Lit := [(308, false)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c2020, c1076] c2025 (by decide) p (sat_cons (step2020 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c2026 : List Lit := [(278, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c2021, c1052] c2026 (by decide) p (sat_cons (step2021 p h) (sat_cons (step1052 p h) (sat_nil p)))
def c2027 : List Lit := [(258, false)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c2022, c1040] c2027 (by decide) p (sat_cons (step2022 p h) (sat_cons (step1040 p h) (sat_nil p)))
def c2028 : List Lit := [(274, false)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c2026, c1050] c2028 (by decide) p (sat_cons (step2026 p h) (sat_cons (step1050 p h) (sat_nil p)))
def c2029 : List Lit := [(1551, true)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c1995, c1256] c2029 (by decide) p (sat_cons (step1995 p h) (sat_cons (step1256 p h) (sat_nil p)))
def c2030 : List Lit := [(8, true), (1552, true)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c1995, c1257] c2030 (by decide) p (sat_cons (step1995 p h) (sat_cons (step1257 p h) (sat_nil p)))
def c2031 : List Lit := [(1554, true)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c1996, c1997, c1258] c2031 (by decide) p (sat_cons (step1996 p h) (sat_cons (step1997 p h) (sat_cons (step1258 p h) (sat_nil p))))
def c2032 : List Lit := [(1556, true)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c2031, c1259] c2032 (by decide) p (sat_cons (step2031 p h) (sat_cons (step1259 p h) (sat_nil p)))
def c2033 : List Lit := [(1557, true)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c2029, c2031, c1260] c2033 (by decide) p (sat_cons (step2029 p h) (sat_cons (step2031 p h) (sat_cons (step1260 p h) (sat_nil p))))
def c2034 : List Lit := [(1552, false), (1558, true)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c2031, c1261] c2034 (by decide) p (sat_cons (step2031 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c2035 : List Lit := [(1560, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c2032, c1262] c2035 (by decide) p (sat_cons (step2032 p h) (sat_cons (step1262 p h) (sat_nil p)))
def c2036 : List Lit := [(1561, true)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1263] c2036 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1263 p h) (sat_nil p)))
def c2037 : List Lit := [(1547, false), (1562, true)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1265] c2037 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1265 p h) (sat_nil p)))
def c2038 : List Lit := [(1548, false), (1562, true)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c2032, c1267] c2038 (by decide) p (sat_cons (step2032 p h) (sat_cons (step1267 p h) (sat_nil p)))
def c2039 : List Lit := [(1548, false), (1563, true)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1268] c2039 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1268 p h) (sat_nil p)))
def c2040 : List Lit := [(1585, false), (1595, true)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c2035, c1315] c2040 (by decide) p (sat_cons (step2035 p h) (sat_cons (step1315 p h) (sat_nil p)))
def c2041 : List Lit := [(1587, false), (1597, true)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c2035, c1316] c2041 (by decide) p (sat_cons (step2035 p h) (sat_cons (step1316 p h) (sat_nil p)))
def c2042 : List Lit := [(1593, true)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1317] c2042 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1317 p h) (sat_nil p)))
def c2043 : List Lit := [(1583, false), (1594, true)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1318] c2043 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1318 p h) (sat_nil p)))
def c2044 : List Lit := [(1584, false), (1595, true)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1319] c2044 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1319 p h) (sat_nil p)))
def c2045 : List Lit := [(1585, false), (1596, true)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1320] c2045 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1320 p h) (sat_nil p)))
def c2046 : List Lit := [(1586, false), (1597, true)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1321] c2046 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1321 p h) (sat_nil p)))
def c2047 : List Lit := [(1587, false), (1598, true)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1322] c2047 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1322 p h) (sat_nil p)))
def c2048 : List Lit := [(1659, false), (1678, true)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c2042, c1470] c2048 (by decide) p (sat_cons (step2042 p h) (sat_cons (step1470 p h) (sat_nil p)))
def c2049 : List Lit := [(1661, false), (1680, true)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c2042, c1471] c2049 (by decide) p (sat_cons (step2042 p h) (sat_cons (step1471 p h) (sat_nil p)))
def c2050 : List Lit := [(1711, true)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c1006, c1560, c1564, c1552, c1554, c1538, c1550, c1546, c1535, c1536, c392, c354, c364] c2050 (by decide) p (sat_cons (step1006 p h) (sat_cons (step1560 p h) (sat_cons (step1564 p h) (sat_cons (step1552 p h) (sat_cons (step1554 p h) (sat_cons (step1538 p h) (sat_cons (step1550 p h) (sat_cons (step1546 p h) (sat_cons (step1535 p h) (sat_cons (step1536 p h) (sat_cons (step392 p h) (sat_cons (step354 p h) (sat_cons (step364 p h) (sat_nil p))))))))))))))
def c2051 : List Lit := [(1707, true), (1719, true)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c1007, c1583, c1582, c1552, c1554, c1549, c1547, c431, c418, c423] c2051 (by decide) p (sat_cons (step1007 p h) (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step1552 p h) (sat_cons (step1554 p h) (sat_cons (step1549 p h) (sat_cons (step1547 p h) (sat_cons (step431 p h) (sat_cons (step418 p h) (sat_cons (step423 p h) (sat_nil p)))))))))))
def c2052 : List Lit := [(78, false), (70, true), (71, false), (84, false)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c1006, c395, c365] c2052 (by decide) p (sat_cons (step1006 p h) (sat_cons (step395 p h) (sat_cons (step365 p h) (sat_nil p))))
def c2053 : List Lit := [(1719, true), (1712, true)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c1009, c1561, c1553, c1582, c1583, c2051, c1565, c1538, c1540, c1535, c1536, c1532, c327, c2052, c1550, c1551, c1555, c431, c1546, c437, c393] c2053 (by decide) p (sat_cons (step1009 p h) (sat_cons (step1561 p h) (sat_cons (step1553 p h) (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step2051 p h) (sat_cons (step1565 p h) (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step1535 p h) (sat_cons (step1536 p h) (sat_cons (step1532 p h) (sat_cons (step327 p h) (sat_cons (step2052 p h) (sat_cons (step1550 p h) (sat_cons (step1551 p h) (sat_cons (step1555 p h) (sat_cons (step431 p h) (sat_cons (step1546 p h) (sat_cons (step437 p h) (sat_cons (step393 p h) (sat_nil p))))))))))))))))))))))
end B112E052
