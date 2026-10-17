import B112E052Part0002
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2182 : List Lit := [(1572, true), (1569, false), (95, false), (90, false)]
theorem step2182 (p : Nat → Bool) (h : Constraints p) : clause p c2182 = true :=
  Snake9.LocalRup.prove_clause [c978, c1280, c2099, c1271, c50, c484] c2182 (by decide) p (sat_cons (step978 p h) (sat_cons (step1280 p h) (sat_cons (step2099 p h) (sat_cons (step1271 p h) (sat_cons (step50 p h) (sat_cons (step484 p h) (sat_nil p)))))))
def c2183 : List Lit := [(1721, true), (95, false), (101, true), (90, false)]
theorem step2183 (p : Nat → Bool) (h : Constraints p) : clause p c2183 = true :=
  Snake9.LocalRup.prove_clause [c1012, c1585, c2088, c500, c533] c2183 (by decide) p (sat_cons (step1012 p h) (sat_cons (step1585 p h) (sat_cons (step2088 p h) (sat_cons (step500 p h) (sat_cons (step533 p h) (sat_nil p))))))
def c2184 : List Lit := [(95, true), (1736, true), (1732, true)]
theorem step2184 (p : Nat → Bool) (h : Constraints p) : clause p c2184 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1603, c1599, c1601, c1602, c1605, c1615, c1596, c1588, c2102, c1586, c535, c573] c2184 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1603 p h) (sat_cons (step1599 p h) (sat_cons (step1601 p h) (sat_cons (step1602 p h) (sat_cons (step1605 p h) (sat_cons (step1615 p h) (sat_cons (step1596 p h) (sat_cons (step1588 p h) (sat_cons (step2102 p h) (sat_cons (step1586 p h) (sat_cons (step535 p h) (sat_cons (step573 p h) (sat_nil p))))))))))))))
def c2185 : List Lit := [(1721, true), (95, false), (1732, true), (122, false)]
theorem step2185 (p : Nat → Bool) (h : Constraints p) : clause p c2185 = true :=
  Snake9.LocalRup.prove_clause [c2138, c2175, c2183, c1966] c2185 (by decide) p (sat_cons (step2138 p h) (sat_cons (step2175 p h) (sat_cons (step2183 p h) (sat_cons (step1966 p h) (sat_nil p)))))
def c2186 : List Lit := [(78, false), (68, false), (67, false), (79, true)]
theorem step2186 (p : Nat → Bool) (h : Constraints p) : clause p c2186 = true :=
  Snake9.LocalRup.prove_clause [c1006, c365, c328] c2186 (by decide) p (sat_cons (step1006 p h) (sat_cons (step365 p h) (sat_cons (step328 p h) (sat_nil p))))
def c2187 : List Lit := [(1562, true), (72, false), (81, false), (68, false)]
theorem step2187 (p : Nat → Bool) (h : Constraints p) : clause p c2187 = true :=
  Snake9.LocalRup.prove_clause [c1004, c1264, c2037, c2034, c1253, c2030, c1247, c406, c349, c341] c2187 (by decide) p (sat_cons (step1004 p h) (sat_cons (step1264 p h) (sat_cons (step2037 p h) (sat_cons (step2034 p h) (sat_cons (step1253 p h) (sat_cons (step2030 p h) (sat_cons (step1247 p h) (sat_cons (step406 p h) (sat_cons (step349 p h) (sat_cons (step341 p h) (sat_nil p)))))))))))
def c2188 : List Lit := [(90, false), (1721, true), (95, false), (122, false)]
theorem step2188 (p : Nat → Bool) (h : Constraints p) : clause p c2188 = true :=
  Snake9.LocalRup.prove_clause [c2175, c2183, c1966] c2188 (by decide) p (sat_cons (step2175 p h) (sat_cons (step2183 p h) (sat_cons (step1966 p h) (sat_nil p))))
def c2189 : List Lit := [(1765, true), (96, true), (102, true), (1721, true), (122, false)]
theorem step2189 (p : Nat → Bool) (h : Constraints p) : clause p c2189 = true :=
  Snake9.LocalRup.prove_clause [c1017, c1686, c1688, c1586, c1585, c1697, c1695, c1687, c1690, c516, c634, c691, c658] c2189 (by decide) p (sat_cons (step1017 p h) (sat_cons (step1686 p h) (sat_cons (step1688 p h) (sat_cons (step1586 p h) (sat_cons (step1585 p h) (sat_cons (step1697 p h) (sat_cons (step1695 p h) (sat_cons (step1687 p h) (sat_cons (step1690 p h) (sat_cons (step516 p h) (sat_cons (step634 p h) (sat_cons (step691 p h) (sat_cons (step658 p h) (sat_nil p))))))))))))))
def c2190 : List Lit := [(35, false), (120, true), (1790, true), (114, true), (113, false), (122, false)]
theorem step2190 (p : Nat → Bool) (h : Constraints p) : clause p c2190 = true :=
  Snake9.LocalRup.prove_clause [c837, c836, c1741, c1738, c1749] c2190 (by decide) p (sat_cons (step837 p h) (sat_cons (step836 p h) (sat_cons (step1741 p h) (sat_cons (step1738 p h) (sat_cons (step1749 p h) (sat_nil p))))))
def c2191 : List Lit := [(1572, true), (18, true), (87, false), (95, false)]
theorem step2191 (p : Nat → Bool) (h : Constraints p) : clause p c2191 = true :=
  Snake9.LocalRup.prove_clause [c978, c1275, c1278, c1280, c2099, c1276, c1271, c52, c46] c2191 (by decide) p (sat_cons (step978 p h) (sat_cons (step1275 p h) (sat_cons (step1278 p h) (sat_cons (step1280 p h) (sat_cons (step2099 p h) (sat_cons (step1276 p h) (sat_cons (step1271 p h) (sat_cons (step52 p h) (sat_cons (step46 p h) (sat_nil p))))))))))
def c2192 : List Lit := [(1648, true), (1633, false), (86, false)]
theorem step2192 (p : Nat → Bool) (h : Constraints p) : clause p c2192 = true :=
  Snake9.LocalRup.prove_clause [c997, c1393, c1423, c1419, c1396, c1407, c1409, c1387, c1405, c1401, c217, c273, c271] c2192 (by decide) p (sat_cons (step997 p h) (sat_cons (step1393 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1396 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1387 p h) (sat_cons (step1405 p h) (sat_cons (step1401 p h) (sat_cons (step217 p h) (sat_cons (step273 p h) (sat_cons (step271 p h) (sat_nil p))))))))))))))
def c2193 : List Lit := [(1788, true), (114, true), (113, false), (122, false)]
theorem step2193 (p : Nat → Bool) (h : Constraints p) : clause p c2193 = true :=
  Snake9.LocalRup.prove_clause [c1736, c1747, c1745, c1738, c1740, c857] c2193 (by decide) p (sat_cons (step1736 p h) (sat_cons (step1747 p h) (sat_cons (step1745 p h) (sat_cons (step1738 p h) (sat_cons (step1740 p h) (sat_cons (step857 p h) (sat_nil p)))))))
def c2194 : List Lit := [(1586, true), (44, true), (17, true), (107, false), (1572, false), (1569, false), (122, false)]
theorem step2194 (p : Nat → Bool) (h : Constraints p) : clause p c2194 = true :=
  Snake9.LocalRup.prove_clause [c2068, c983, c1312, c1309, c1283, c1296, c2172, c1273, c673, c105, c98, c99, c1287] c2194 (by decide) p (sat_cons (step2068 p h) (sat_cons (step983 p h) (sat_cons (step1312 p h) (sat_cons (step1309 p h) (sat_cons (step1283 p h) (sat_cons (step1296 p h) (sat_cons (step2172 p h) (sat_cons (step1273 p h) (sat_cons (step673 p h) (sat_cons (step105 p h) (sat_cons (step98 p h) (sat_cons (step99 p h) (sat_cons (step1287 p h) (sat_nil p))))))))))))))
def c2195 : List Lit := [(1597, true), (44, false), (1572, false), (122, false)]
theorem step2195 (p : Nat → Bool) (h : Constraints p) : clause p c2195 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1308, c2046, c1325, c1309, c2037, c2172, c1251, c179, c1248] c2195 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1308 p h) (sat_cons (step2046 p h) (sat_cons (step1325 p h) (sat_cons (step1309 p h) (sat_cons (step2037 p h) (sat_cons (step2172 p h) (sat_cons (step1251 p h) (sat_cons (step179 p h) (sat_cons (step1248 p h) (sat_nil p)))))))))))
def c2196 : List Lit := [(26, false), (15, false), (1580, true)]
theorem step2196 (p : Nat → Bool) (h : Constraints p) : clause p c2196 = true :=
  Snake9.LocalRup.prove_clause [c2172, c1296, c98, c99, c1287] c2196 (by decide) p (sat_cons (step2172 p h) (sat_cons (step1296 p h) (sat_cons (step98 p h) (sat_cons (step99 p h) (sat_cons (step1287 p h) (sat_nil p))))))
def c2197 : List Lit := [(28, false), (30, false), (20, false)]
theorem step2197 (p : Nat → Bool) (h : Constraints p) : clause p c2197 = true :=
  Snake9.LocalRup.prove_clause [c984, c108, c110] c2197 (by decide) p (sat_cons (step984 p h) (sat_cons (step108 p h) (sat_cons (step110 p h) (sat_nil p))))
def c2198 : List Lit := [(1793, true), (123, false), (103, false), (106, true)]
theorem step2198 (p : Nat → Bool) (h : Constraints p) : clause p c2198 = true :=
  Snake9.LocalRup.prove_clause [c1030, c1753, c1754, c951, c953, c967] c2198 (by decide) p (sat_cons (step1030 p h) (sat_cons (step1753 p h) (sat_cons (step1754 p h) (sat_cons (step951 p h) (sat_cons (step953 p h) (sat_cons (step967 p h) (sat_nil p)))))))
def c2199 : List Lit := [(1789, true), (120, true), (114, true), (113, false), (122, false)]
theorem step2199 (p : Nat → Bool) (h : Constraints p) : clause p c2199 = true :=
  Snake9.LocalRup.prove_clause [c1739, c1736, c1746, c1748, c1741, c1738, c857] c2199 (by decide) p (sat_cons (step1739 p h) (sat_cons (step1736 p h) (sat_cons (step1746 p h) (sat_cons (step1748 p h) (sat_cons (step1741 p h) (sat_cons (step1738 p h) (sat_cons (step857 p h) (sat_nil p))))))))
def c2200 : List Lit := [(1795, true), (103, false), (106, true)]
theorem step2200 (p : Nat → Bool) (h : Constraints p) : clause p c2200 = true :=
  Snake9.LocalRup.prove_clause [c1756, c1758, c2198, c1750] c2200 (by decide) p (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step2198 p h) (sat_cons (step1750 p h) (sat_nil p)))))
def c2201 : List Lit := [(38, true), (74, true), (3, false)]
theorem step2201 (p : Nat → Bool) (h : Constraints p) : clause p c2201 = true :=
  Snake9.LocalRup.prove_clause [c970, c8] c2201 (by decide) p (sat_cons (step970 p h) (sat_cons (step8 p h) (sat_nil p)))
def c2202 : List Lit := [(9, true), (74, true), (3, false)]
theorem step2202 (p : Nat → Bool) (h : Constraints p) : clause p c2202 = true :=
  Snake9.LocalRup.prove_clause [c970, c9] c2202 (by decide) p (sat_cons (step970 p h) (sat_cons (step9 p h) (sat_nil p)))
def c2203 : List Lit := [(9, true), (38, true), (3, false)]
theorem step2203 (p : Nat → Bool) (h : Constraints p) : clause p c2203 = true :=
  Snake9.LocalRup.prove_clause [c970, c10] c2203 (by decide) p (sat_cons (step970 p h) (sat_cons (step10 p h) (sat_nil p)))
def c2204 : List Lit := [(4, true), (5, false), (6, true)]
theorem step2204 (p : Nat → Bool) (h : Constraints p) : clause p c2204 = true :=
  Snake9.LocalRup.prove_clause [c971, c14] c2204 (by decide) p (sat_cons (step971 p h) (sat_cons (step14 p h) (sat_nil p)))
def c2205 : List Lit := [(2, true), (5, false), (6, true)]
theorem step2205 (p : Nat → Bool) (h : Constraints p) : clause p c2205 = true :=
  Snake9.LocalRup.prove_clause [c971, c15] c2205 (by decide) p (sat_cons (step971 p h) (sat_cons (step15 p h) (sat_nil p)))
def c2206 : List Lit := [(4, true), (2, true), (5, false)]
theorem step2206 (p : Nat → Bool) (h : Constraints p) : clause p c2206 = true :=
  Snake9.LocalRup.prove_clause [c971, c16] c2206 (by decide) p (sat_cons (step971 p h) (sat_cons (step16 p h) (sat_nil p)))
def c2207 : List Lit := [(6, true), (79, true), (7, false), (44, true)]
theorem step2207 (p : Nat → Bool) (h : Constraints p) : clause p c2207 = true :=
  Snake9.LocalRup.prove_clause [c972, c22] c2207 (by decide) p (sat_cons (step972 p h) (sat_cons (step22 p h) (sat_nil p)))
def c2208 : List Lit := [(9, true), (80, true), (8, false)]
theorem step2208 (p : Nat → Bool) (h : Constraints p) : clause p c2208 = true :=
  Snake9.LocalRup.prove_clause [c973, c24] c2208 (by decide) p (sat_cons (step973 p h) (sat_cons (step24 p h) (sat_nil p)))
def c2209 : List Lit := [(4, true), (80, true), (8, false)]
theorem step2209 (p : Nat → Bool) (h : Constraints p) : clause p c2209 = true :=
  Snake9.LocalRup.prove_clause [c973, c25] c2209 (by decide) p (sat_cons (step973 p h) (sat_cons (step25 p h) (sat_nil p)))
def c2210 : List Lit := [(9, false), (8, true), (136, true)]
theorem step2210 (p : Nat → Bool) (h : Constraints p) : clause p c2210 = true :=
  Snake9.LocalRup.prove_clause [c1995, c27] c2210 (by decide) p (sat_cons (step1995 p h) (sat_cons (step27 p h) (sat_nil p)))
def c2211 : List Lit := [(9, false), (3, true), (136, true)]
theorem step2211 (p : Nat → Bool) (h : Constraints p) : clause p c2211 = true :=
  Snake9.LocalRup.prove_clause [c1995, c28] c2211 (by decide) p (sat_cons (step1995 p h) (sat_cons (step28 p h) (sat_nil p)))
def c2212 : List Lit := [(140, true), (7, true)]
theorem step2212 (p : Nat → Bool) (h : Constraints p) : clause p c2212 = true :=
  Snake9.LocalRup.prove_clause [c1996, c1997, c1994] c2212 (by decide) p (sat_cons (step1996 p h) (sat_cons (step1997 p h) (sat_cons (step1994 p h) (sat_nil p))))
def c2213 : List Lit := [(19, true), (15, false), (26, true)]
theorem step2213 (p : Nat → Bool) (h : Constraints p) : clause p c2213 = true :=
  Snake9.LocalRup.prove_clause [c977, c42] c2213 (by decide) p (sat_cons (step977 p h) (sat_cons (step42 p h) (sat_nil p)))
def c2214 : List Lit := [(14, true), (15, false), (26, true)]
theorem step2214 (p : Nat → Bool) (h : Constraints p) : clause p c2214 = true :=
  Snake9.LocalRup.prove_clause [c977, c43] c2214 (by decide) p (sat_cons (step977 p h) (sat_cons (step43 p h) (sat_nil p)))
def c2215 : List Lit := [(14, true), (19, true), (15, false)]
theorem step2215 (p : Nat → Bool) (h : Constraints p) : clause p c2215 = true :=
  Snake9.LocalRup.prove_clause [c977, c44] c2215 (by decide) p (sat_cons (step977 p h) (sat_cons (step44 p h) (sat_nil p)))
def c2216 : List Lit := [(17, false), (21, true), (88, true)]
theorem step2216 (p : Nat → Bool) (h : Constraints p) : clause p c2216 = true :=
  Snake9.LocalRup.prove_clause [c978, c50] c2216 (by decide) p (sat_cons (step978 p h) (sat_cons (step50 p h) (sat_nil p)))
def c2217 : List Lit := [(16, true), (17, false), (88, true)]
theorem step2217 (p : Nat → Bool) (h : Constraints p) : clause p c2217 = true :=
  Snake9.LocalRup.prove_clause [c978, c51] c2217 (by decide) p (sat_cons (step978 p h) (sat_cons (step51 p h) (sat_nil p)))
def c2218 : List Lit := [(16, true), (17, false), (21, true)]
theorem step2218 (p : Nat → Bool) (h : Constraints p) : clause p c2218 = true :=
  Snake9.LocalRup.prove_clause [c978, c52] c2218 (by decide) p (sat_cons (step978 p h) (sat_cons (step52 p h) (sat_nil p)))
def c2219 : List Lit := [(21, true), (18, false), (92, true)]
theorem step2219 (p : Nat → Bool) (h : Constraints p) : clause p c2219 = true :=
  Snake9.LocalRup.prove_clause [c979, c54] c2219 (by decide) p (sat_cons (step979 p h) (sat_cons (step54 p h) (sat_nil p)))
def c2220 : List Lit := [(19, true), (18, false), (92, true)]
theorem step2220 (p : Nat → Bool) (h : Constraints p) : clause p c2220 = true :=
  Snake9.LocalRup.prove_clause [c979, c55] c2220 (by decide) p (sat_cons (step979 p h) (sat_cons (step55 p h) (sat_nil p)))
def c2221 : List Lit := [(19, true), (18, false), (21, true)]
theorem step2221 (p : Nat → Bool) (h : Constraints p) : clause p c2221 = true :=
  Snake9.LocalRup.prove_clause [c979, c56] c2221 (by decide) p (sat_cons (step979 p h) (sat_cons (step56 p h) (sat_nil p)))
def c2222 : List Lit := [(29, true), (22, true), (20, false), (38, true), (21, true)]
theorem step2222 (p : Nat → Bool) (h : Constraints p) : clause p c2222 = true :=
  Snake9.LocalRup.prove_clause [c980, c67] c2222 (by decide) p (sat_cons (step980 p h) (sat_cons (step67 p h) (sat_nil p)))
def c2223 : List Lit := [(29, true), (22, true), (16, true), (20, false), (38, true)]
theorem step2223 (p : Nat → Bool) (h : Constraints p) : clause p c2223 = true :=
  Snake9.LocalRup.prove_clause [c980, c68] c2223 (by decide) p (sat_cons (step980 p h) (sat_cons (step68 p h) (sat_nil p)))
def c2224 : List Lit := [(16, true), (21, true), (22, true), (20, false), (38, true)]
theorem step2224 (p : Nat → Bool) (h : Constraints p) : clause p c2224 = true :=
  Snake9.LocalRup.prove_clause [c980, c69] c2224 (by decide) p (sat_cons (step980 p h) (sat_cons (step69 p h) (sat_nil p)))
def c2225 : List Lit := [(40, true), (97, true), (26, true), (24, false)]
theorem step2225 (p : Nat → Bool) (h : Constraints p) : clause p c2225 = true :=
  Snake9.LocalRup.prove_clause [c981, c90] c2225 (by decide) p (sat_cons (step981 p h) (sat_cons (step90 p h) (sat_nil p)))
def c2226 : List Lit := [(23, true), (97, true), (26, true), (24, false)]
theorem step2226 (p : Nat → Bool) (h : Constraints p) : clause p c2226 = true :=
  Snake9.LocalRup.prove_clause [c981, c91] c2226 (by decide) p (sat_cons (step981 p h) (sat_cons (step91 p h) (sat_nil p)))
def c2227 : List Lit := [(23, true), (40, true), (26, true), (24, false)]
theorem step2227 (p : Nat → Bool) (h : Constraints p) : clause p c2227 = true :=
  Snake9.LocalRup.prove_clause [c981, c92] c2227 (by decide) p (sat_cons (step981 p h) (sat_cons (step92 p h) (sat_nil p)))
def c2228 : List Lit := [(23, true), (26, true), (25, false)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c982, c94] c2228 (by decide) p (sat_cons (step982 p h) (sat_cons (step94 p h) (sat_nil p)))
def c2229 : List Lit := [(26, true), (14, true), (25, false)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c982, c95] c2229 (by decide) p (sat_cons (step982 p h) (sat_cons (step95 p h) (sat_nil p)))
def c2230 : List Lit := [(23, true), (14, true), (25, false)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c982, c96] c2230 (by decide) p (sat_cons (step982 p h) (sat_cons (step96 p h) (sat_nil p)))
def c2231 : List Lit := [(31, true), (27, false), (44, true), (101, true)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c983, c104] c2231 (by decide) p (sat_cons (step983 p h) (sat_cons (step104 p h) (sat_nil p)))
def c2232 : List Lit := [(44, true), (101, true), (27, false), (26, true)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c983, c105] c2232 (by decide) p (sat_cons (step983 p h) (sat_cons (step105 p h) (sat_nil p)))
def c2233 : List Lit := [(26, true), (31, true), (27, false), (101, true)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c983, c106] c2233 (by decide) p (sat_cons (step983 p h) (sat_cons (step106 p h) (sat_nil p)))
def c2234 : List Lit := [(31, true), (27, false), (26, true), (44, true)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c983, c107] c2234 (by decide) p (sat_cons (step983 p h) (sat_cons (step107 p h) (sat_nil p)))
def c2235 : List Lit := [(28, false), (29, true)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c984, c108] c2235 (by decide) p (sat_cons (step984 p h) (sat_cons (step108 p h) (sat_nil p)))
def c2236 : List Lit := [(28, false), (23, true)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c984, c109] c2236 (by decide) p (sat_cons (step984 p h) (sat_cons (step109 p h) (sat_nil p)))
def c2237 : List Lit := [(29, true), (31, true), (30, false), (106, true)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c985, c116] c2237 (by decide) p (sat_cons (step985 p h) (sat_cons (step116 p h) (sat_nil p)))
def c2238 : List Lit := [(31, true), (22, true), (30, false), (106, true)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c985, c117] c2238 (by decide) p (sat_cons (step985 p h) (sat_cons (step117 p h) (sat_nil p)))
def c2239 : List Lit := [(29, true), (22, true), (30, false), (106, true)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c985, c118] c2239 (by decide) p (sat_cons (step985 p h) (sat_cons (step118 p h) (sat_nil p)))
def c2240 : List Lit := [(29, true), (22, true), (31, true), (30, false)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c985, c119] c2240 (by decide) p (sat_cons (step985 p h) (sat_cons (step119 p h) (sat_nil p)))
def c2241 : List Lit := [(44, true), (35, false), (113, true)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c986, c144] c2241 (by decide) p (sat_cons (step986 p h) (sat_cons (step144 p h) (sat_nil p)))
def c2242 : List Lit := [(34, true), (35, false), (113, true)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c986, c145] c2242 (by decide) p (sat_cons (step986 p h) (sat_cons (step145 p h) (sat_nil p)))
def c2243 : List Lit := [(34, true), (35, false), (44, true)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c986, c146] c2243 (by decide) p (sat_cons (step986 p h) (sat_cons (step146 p h) (sat_nil p)))
def c2244 : List Lit := [(37, true), (38, true), (36, false)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c987, c147] c2244 (by decide) p (sat_cons (step987 p h) (sat_cons (step147 p h) (sat_nil p)))
def c2245 : List Lit := [(32, true), (38, true), (36, false)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c987, c148] c2245 (by decide) p (sat_cons (step987 p h) (sat_cons (step148 p h) (sat_nil p)))
end B112E052
