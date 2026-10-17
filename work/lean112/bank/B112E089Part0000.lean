import B112E089Inputs
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2012 : List Lit := [(80, false)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c1008, c766] c2012 (by decide) p (sat_cons (step1008 p h) (sat_cons (step766 p h) (sat_nil p)))
def c2013 : List Lit := [(82, false)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c1009, c771] c2013 (by decide) p (sat_cons (step1009 p h) (sat_cons (step771 p h) (sat_nil p)))
def c2014 : List Lit := [(490, false)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c1302, c1299] c2014 (by decide) p (sat_cons (step1302 p h) (sat_cons (step1299 p h) (sat_nil p)))
def c2015 : List Lit := [(368, false)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c1302, c1301] c2015 (by decide) p (sat_cons (step1302 p h) (sat_cons (step1301 p h) (sat_nil p)))
def c2016 : List Lit := [(488, false)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c2014, c1295] c2016 (by decide) p (sat_cons (step2014 p h) (sat_cons (step1295 p h) (sat_nil p)))
def c2017 : List Lit := [(428, false)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c2014, c1298] c2017 (by decide) p (sat_cons (step2014 p h) (sat_cons (step1298 p h) (sat_nil p)))
def c2018 : List Lit := [(366, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c2015, c1161] c2018 (by decide) p (sat_cons (step2015 p h) (sat_cons (step1161 p h) (sat_nil p)))
def c2019 : List Lit := [(306, false)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c2015, c1164] c2019 (by decide) p (sat_cons (step2015 p h) (sat_cons (step1164 p h) (sat_nil p)))
def c2020 : List Lit := [(486, false)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c2016, c1290] c2020 (by decide) p (sat_cons (step2016 p h) (sat_cons (step1290 p h) (sat_nil p)))
def c2021 : List Lit := [(456, false)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c2016, c1293] c2021 (by decide) p (sat_cons (step2016 p h) (sat_cons (step1293 p h) (sat_nil p)))
def c2022 : List Lit := [(426, false)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c2017, c1221] c2022 (by decide) p (sat_cons (step2017 p h) (sat_cons (step1221 p h) (sat_nil p)))
def c2023 : List Lit := [(396, false)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c2017, c1224] c2023 (by decide) p (sat_cons (step2017 p h) (sat_cons (step1224 p h) (sat_nil p)))
def c2024 : List Lit := [(364, false)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c2018, c1156] c2024 (by decide) p (sat_cons (step2018 p h) (sat_cons (step1156 p h) (sat_nil p)))
def c2025 : List Lit := [(334, false)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c2018, c1159] c2025 (by decide) p (sat_cons (step2018 p h) (sat_cons (step1159 p h) (sat_nil p)))
def c2026 : List Lit := [(304, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c2019, c1089] c2026 (by decide) p (sat_cons (step2019 p h) (sat_cons (step1089 p h) (sat_nil p)))
def c2027 : List Lit := [(276, false)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c2019, c1092] c2027 (by decide) p (sat_cons (step2019 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c2028 : List Lit := [(484, false)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c2020, c1285] c2028 (by decide) p (sat_cons (step2020 p h) (sat_cons (step1285 p h) (sat_nil p)))
def c2029 : List Lit := [(470, false)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c2020, c1288] c2029 (by decide) p (sat_cons (step2020 p h) (sat_cons (step1288 p h) (sat_nil p)))
def c2030 : List Lit := [(454, false)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c2021, c1251] c2030 (by decide) p (sat_cons (step2021 p h) (sat_cons (step1251 p h) (sat_nil p)))
def c2031 : List Lit := [(440, false)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c2021, c1254] c2031 (by decide) p (sat_cons (step2021 p h) (sat_cons (step1254 p h) (sat_nil p)))
def c2032 : List Lit := [(424, false)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c2022, c1218] c2032 (by decide) p (sat_cons (step2022 p h) (sat_cons (step1218 p h) (sat_nil p)))
def c2033 : List Lit := [(394, false)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c2023, c1196] c2033 (by decide) p (sat_cons (step2023 p h) (sat_cons (step1196 p h) (sat_nil p)))
def c2034 : List Lit := [(380, false)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c2023, c1199] c2034 (by decide) p (sat_cons (step2023 p h) (sat_cons (step1199 p h) (sat_nil p)))
def c2035 : List Lit := [(362, false)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c2024, c1151] c2035 (by decide) p (sat_cons (step2024 p h) (sat_cons (step1151 p h) (sat_nil p)))
def c2036 : List Lit := [(348, false)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c2024, c1154] c2036 (by decide) p (sat_cons (step2024 p h) (sat_cons (step1154 p h) (sat_nil p)))
def c2037 : List Lit := [(332, false)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c2025, c1122] c2037 (by decide) p (sat_cons (step2025 p h) (sat_cons (step1122 p h) (sat_nil p)))
def c2038 : List Lit := [(318, false)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c2025, c1125] c2038 (by decide) p (sat_cons (step2025 p h) (sat_cons (step1125 p h) (sat_nil p)))
def c2039 : List Lit := [(302, false)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c2026, c1085] c2039 (by decide) p (sat_cons (step2026 p h) (sat_cons (step1085 p h) (sat_nil p)))
def c2040 : List Lit := [(274, false)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c2027, c1062] c2040 (by decide) p (sat_cons (step2027 p h) (sat_cons (step1062 p h) (sat_nil p)))
def c2041 : List Lit := [(482, false)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c2028, c1280] c2041 (by decide) p (sat_cons (step2028 p h) (sat_cons (step1280 p h) (sat_nil p)))
def c2042 : List Lit := [(476, false)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c2028, c1283] c2042 (by decide) p (sat_cons (step2028 p h) (sat_cons (step1283 p h) (sat_nil p)))
def c2043 : List Lit := [(468, false)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c2029, c1263] c2043 (by decide) p (sat_cons (step2029 p h) (sat_cons (step1263 p h) (sat_nil p)))
def c2044 : List Lit := [(446, false)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c2030, c1249] c2044 (by decide) p (sat_cons (step2030 p h) (sat_cons (step1249 p h) (sat_nil p)))
def c2045 : List Lit := [(438, false)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c2031, c1235] c2045 (by decide) p (sat_cons (step2031 p h) (sat_cons (step1235 p h) (sat_nil p)))
def c2046 : List Lit := [(432, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c2031, c1238] c2046 (by decide) p (sat_cons (step2031 p h) (sat_cons (step1238 p h) (sat_nil p)))
def c2047 : List Lit := [(416, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c2032, c1216] c2047 (by decide) p (sat_cons (step2032 p h) (sat_cons (step1216 p h) (sat_nil p)))
def c2048 : List Lit := [(392, false)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1191] c2048 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1191 p h) (sat_nil p)))
def c2049 : List Lit := [(386, false)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1194] c2049 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1194 p h) (sat_nil p)))
def c2050 : List Lit := [(372, false)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c2034, c1176] c2050 (by decide) p (sat_cons (step2034 p h) (sat_cons (step1176 p h) (sat_nil p)))
def c2051 : List Lit := [(354, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c2035, c1149] c2051 (by decide) p (sat_cons (step2035 p h) (sat_cons (step1149 p h) (sat_nil p)))
def c2052 : List Lit := [(346, false)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1135] c2052 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1135 p h) (sat_nil p)))
def c2053 : List Lit := [(330, false)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c2037, c1117] c2053 (by decide) p (sat_cons (step2037 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c2054 : List Lit := [(324, false)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c2037, c1120] c2054 (by decide) p (sat_cons (step2037 p h) (sat_cons (step1120 p h) (sat_nil p)))
def c2055 : List Lit := [(310, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c2038, c1102] c2055 (by decide) p (sat_cons (step2038 p h) (sat_cons (step1102 p h) (sat_nil p)))
def c2056 : List Lit := [(300, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c2039, c1081] c2056 (by decide) p (sat_cons (step2039 p h) (sat_cons (step1081 p h) (sat_nil p)))
def c2057 : List Lit := [(272, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c2040, c1057] c2057 (by decide) p (sat_cons (step2040 p h) (sat_cons (step1057 p h) (sat_nil p)))
def c2058 : List Lit := [(266, false)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c2040, c1060] c2058 (by decide) p (sat_cons (step2040 p h) (sat_cons (step1060 p h) (sat_nil p)))
def c2059 : List Lit := [(474, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c2042, c1271] c2059 (by decide) p (sat_cons (step2042 p h) (sat_cons (step1271 p h) (sat_nil p)))
def c2060 : List Lit := [(390, false)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c2048, c1187] c2060 (by decide) p (sat_cons (step2048 p h) (sat_cons (step1187 p h) (sat_nil p)))
def c2061 : List Lit := [(342, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c2052, c1133] c2061 (by decide) p (sat_cons (step2052 p h) (sat_cons (step1133 p h) (sat_nil p)))
def c2062 : List Lit := [(328, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c2053, c1113] c2062 (by decide) p (sat_cons (step2053 p h) (sat_cons (step1113 p h) (sat_nil p)))
def c2063 : List Lit := [(270, false)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c2057, c1053] c2063 (by decide) p (sat_cons (step2057 p h) (sat_cons (step1053 p h) (sat_nil p)))
def c2064 : List Lit := [(264, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c2058, c1044] c2064 (by decide) p (sat_cons (step2058 p h) (sat_cons (step1044 p h) (sat_nil p)))
def c2065 : List Lit := [(262, false)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c2058, c1047] c2065 (by decide) p (sat_cons (step2058 p h) (sat_cons (step1047 p h) (sat_nil p)))
def c2066 : List Lit := [(126, true), (129, true), (132, true), (133, true), (134, true), (135, true), (137, true), (138, true), (139, true), (142, true), (146, true), (148, true), (149, true), (151, true), (153, true), (155, true), (156, true), (158, true), (163, true), (165, true), (166, true), (168, true), (169, true), (170, true), (171, true), (174, true), (175, true), (178, true), (180, true), (181, true), (185, true), (186, true), (188, true), (190, true), (191, true), (193, true), (196, true), (197, true), (199, true), (200, true), (203, true), (205, true), (209, true), (211, true), (213, true), (215, true), (218, true), (220, true), (222, true), (223, true), (226, true), (227, true), (228, true), (231, true), (235, true), (237, true), (239, true), (241, true), (243, true), (244, true), (246, true), (247, true)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.TreeRup.prove_clause [c970, c971, c972, c973, c974, c975, c976, c977, c978, c979, c980, c981, c982, c983, c984, c985, c986, c987, c988, c989, c990, c991, c992, c993, c994, c995, c996, c997, c998, c999, c1000, c1001, c1002, c1003, c1004, c1005, c1006, c1007, c1008, c1009, c1010, c1011, c1012, c1013, c1014, c1015, c1016, c1017, c1018, c1019, c1020, c1021, c1022, c1023, c1024, c1025, c1026, c1027, c1028, c1029, c1030, c1303] c2066 (by decide) p (sat_cons (step970 p h) (sat_cons (step971 p h) (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step974 p h) (sat_cons (step975 p h) (sat_cons (step976 p h) (sat_cons (step977 p h) (sat_cons (step978 p h) (sat_cons (step979 p h) (sat_cons (step980 p h) (sat_cons (step981 p h) (sat_cons (step982 p h) (sat_cons (step983 p h) (sat_cons (step984 p h) (sat_cons (step985 p h) (sat_cons (step986 p h) (sat_cons (step987 p h) (sat_cons (step988 p h) (sat_cons (step989 p h) (sat_cons (step990 p h) (sat_cons (step991 p h) (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step996 p h) (sat_cons (step997 p h) (sat_cons (step998 p h) (sat_cons (step999 p h) (sat_cons (step1000 p h) (sat_cons (step1001 p h) (sat_cons (step1002 p h) (sat_cons (step1003 p h) (sat_cons (step1004 p h) (sat_cons (step1005 p h) (sat_cons (step1006 p h) (sat_cons (step1007 p h) (sat_cons (step1008 p h) (sat_cons (step1009 p h) (sat_cons (step1010 p h) (sat_cons (step1011 p h) (sat_cons (step1012 p h) (sat_cons (step1013 p h) (sat_cons (step1014 p h) (sat_cons (step1015 p h) (sat_cons (step1016 p h) (sat_cons (step1017 p h) (sat_cons (step1018 p h) (sat_cons (step1019 p h) (sat_cons (step1020 p h) (sat_cons (step1021 p h) (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step1024 p h) (sat_cons (step1025 p h) (sat_cons (step1026 p h) (sat_cons (step1027 p h) (sat_cons (step1028 p h) (sat_cons (step1029 p h) (sat_cons (step1030 p h) (sat_cons (step1303 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2067 : List Lit := [(76, false), (1663, true)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1628, c1620, c1617, c1618, c1622, c1614, c654, c1615, c1632, c1609, c1606, c1611, c559, c707, c755, c640, c748, c1177, c1183, c1180, c1186, c1193] c2067 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1628 p h) (sat_cons (step1620 p h) (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step1622 p h) (sat_cons (step1614 p h) (sat_cons (step654 p h) (sat_cons (step1615 p h) (sat_cons (step1632 p h) (sat_cons (step1609 p h) (sat_cons (step1606 p h) (sat_cons (step1611 p h) (sat_cons (step559 p h) (sat_cons (step707 p h) (sat_cons (step755 p h) (sat_cons (step640 p h) (sat_cons (step748 p h) (sat_cons (step1177 p h) (sat_cons (step1183 p h) (sat_cons (step1180 p h) (sat_cons (step1186 p h) (sat_cons (step1193 p h) (sat_nil p))))))))))))))))))))))))
def c2068 : List Lit := [(193, true), (1663, true), (1593, true)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c1628, c1620, c1617, c1618, c1622, c1614, c654, c1632, c1611, c640, c642, c696, c645, c1464, c1462, c1470] c2068 (by decide) p (sat_cons (step1628 p h) (sat_cons (step1620 p h) (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step1622 p h) (sat_cons (step1614 p h) (sat_cons (step654 p h) (sat_cons (step1632 p h) (sat_cons (step1611 p h) (sat_cons (step640 p h) (sat_cons (step642 p h) (sat_cons (step696 p h) (sat_cons (step645 p h) (sat_cons (step1464 p h) (sat_cons (step1462 p h) (sat_cons (step1470 p h) (sat_nil p)))))))))))))))))
def c2069 : List Lit := [(1663, true), (1593, true)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c2023, c998, c1628, c1632, c1620, c1622, c1609, c1611, c1618, c1615, c1606, c1607, c559, c624, c527, c2068, c1177, c1180, c1192, c1198, c1173, c1174, c1172, c1166, c1169, c1165, c574, c539, c421, c425, c431] c2069 (by decide) p (sat_cons (step2023 p h) (sat_cons (step998 p h) (sat_cons (step1628 p h) (sat_cons (step1632 p h) (sat_cons (step1620 p h) (sat_cons (step1622 p h) (sat_cons (step1609 p h) (sat_cons (step1611 p h) (sat_cons (step1618 p h) (sat_cons (step1615 p h) (sat_cons (step1606 p h) (sat_cons (step1607 p h) (sat_cons (step559 p h) (sat_cons (step624 p h) (sat_cons (step527 p h) (sat_cons (step2068 p h) (sat_cons (step1177 p h) (sat_cons (step1180 p h) (sat_cons (step1192 p h) (sat_cons (step1198 p h) (sat_cons (step1173 p h) (sat_cons (step1174 p h) (sat_cons (step1172 p h) (sat_cons (step1166 p h) (sat_cons (step1169 p h) (sat_cons (step1165 p h) (sat_cons (step574 p h) (sat_cons (step539 p h) (sat_cons (step421 p h) (sat_cons (step425 p h) (sat_cons (step431 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2070 : List Lit := [(64, false), (66, false), (68, true), (65, true), (62, false), (72, false), (379, true)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c998, c1174, c1166, c1165, c1173, c1172, c1169, c527, c539, c574, c421, c425, c431] c2070 (by decide) p (sat_cons (step998 p h) (sat_cons (step1174 p h) (sat_cons (step1166 p h) (sat_cons (step1165 p h) (sat_cons (step1173 p h) (sat_cons (step1172 p h) (sat_cons (step1169 p h) (sat_cons (step527 p h) (sat_cons (step539 p h) (sat_cons (step574 p h) (sat_cons (step421 p h) (sat_cons (step425 p h) (sat_cons (step431 p h) (sat_nil p))))))))))))))
def c2071 : List Lit := [(1598, true), (59, true), (68, true), (72, false), (185, true)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1479, c473, c423] c2071 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step473 p h) (sat_cons (step423 p h) (sat_nil p)))))
def c2072 : List Lit := [(70, false), (72, false), (69, false), (1605, true)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c645, c646, c1462, c1475, c1469, c1483, c1494] c2072 (by decide) p (sat_cons (step645 p h) (sat_cons (step646 p h) (sat_cons (step1462 p h) (sat_cons (step1475 p h) (sat_cons (step1469 p h) (sat_cons (step1483 p h) (sat_cons (step1494 p h) (sat_nil p))))))))
def c2073 : List Lit := [(32, true), (28, false), (72, false), (1569, true)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1413, c1415, c1422, c167, c1417] c2073 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1413 p h) (sat_cons (step1415 p h) (sat_cons (step1422 p h) (sat_cons (step167 p h) (sat_cons (step1417 p h) (sat_nil p)))))))
def c2074 : List Lit := [(32, true), (75, true), (158, true), (1569, true)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c985, c1424, c1413, c1415, c193, c1422, c1417, c201, c199, c1964] c2074 (by decide) p (sat_cons (step985 p h) (sat_cons (step1424 p h) (sat_cons (step1413 p h) (sat_cons (step1415 p h) (sat_cons (step193 p h) (sat_cons (step1422 p h) (sat_cons (step1417 p h) (sat_cons (step201 p h) (sat_cons (step199 p h) (sat_cons (step1964 p h) (sat_nil p)))))))))))
def c2075 : List Lit := [(58, true), (1666, true), (1658, false), (60, true), (61, false), (185, true)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c1621, c1639, c1610, c472, c474, c1989, c1606, c1608, c1609, c619, c1635, c1615, c1624] c2075 (by decide) p (sat_cons (step1621 p h) (sat_cons (step1639 p h) (sat_cons (step1610 p h) (sat_cons (step472 p h) (sat_cons (step474 p h) (sat_cons (step1989 p h) (sat_cons (step1606 p h) (sat_cons (step1608 p h) (sat_cons (step1609 p h) (sat_cons (step619 p h) (sat_cons (step1635 p h) (sat_cons (step1615 p h) (sat_cons (step1624 p h) (sat_nil p))))))))))))))
end B112E089
