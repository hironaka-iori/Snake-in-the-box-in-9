import B112E057Inputs
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2025 : List Lit := [(66, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c965, c964] c2025 (by decide) p (sat_cons (step965 p h) (sat_cons (step964 p h) (sat_nil p)))
def c2026 : List Lit := [(61, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c996, c428] c2026 (by decide) p (sat_cons (step996 p h) (sat_cons (step428 p h) (sat_nil p)))
def c2027 : List Lit := [(65, false)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c998, c438] c2027 (by decide) p (sat_cons (step998 p h) (sat_cons (step438 p h) (sat_nil p)))
def c2028 : List Lit := [(67, false)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c999, c441] c2028 (by decide) p (sat_cons (step999 p h) (sat_cons (step441 p h) (sat_nil p)))
def c2029 : List Lit := [(502, false)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1259] c2029 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1259 p h) (sat_nil p)))
def c2030 : List Lit := [(378, false)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1261] c2030 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c2031 : List Lit := [(500, false)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c2029, c1255] c2031 (by decide) p (sat_cons (step2029 p h) (sat_cons (step1255 p h) (sat_nil p)))
def c2032 : List Lit := [(438, false)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c2029, c1258] c2032 (by decide) p (sat_cons (step2029 p h) (sat_cons (step1258 p h) (sat_nil p)))
def c2033 : List Lit := [(376, false)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c2030, c1134] c2033 (by decide) p (sat_cons (step2030 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c2034 : List Lit := [(314, false)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c2030, c1137] c2034 (by decide) p (sat_cons (step2030 p h) (sat_cons (step1137 p h) (sat_nil p)))
def c2035 : List Lit := [(498, false)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c2031, c1250] c2035 (by decide) p (sat_cons (step2031 p h) (sat_cons (step1250 p h) (sat_nil p)))
def c2036 : List Lit := [(468, false)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c2031, c1253] c2036 (by decide) p (sat_cons (step2031 p h) (sat_cons (step1253 p h) (sat_nil p)))
def c2037 : List Lit := [(436, false)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c2032, c1187] c2037 (by decide) p (sat_cons (step2032 p h) (sat_cons (step1187 p h) (sat_nil p)))
def c2038 : List Lit := [(406, false)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c2032, c1190] c2038 (by decide) p (sat_cons (step2032 p h) (sat_cons (step1190 p h) (sat_nil p)))
def c2039 : List Lit := [(374, false)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1129] c2039 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1129 p h) (sat_nil p)))
def c2040 : List Lit := [(344, false)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1132] c2040 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1132 p h) (sat_nil p)))
def c2041 : List Lit := [(312, false)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c2034, c1073] c2041 (by decide) p (sat_cons (step2034 p h) (sat_cons (step1073 p h) (sat_nil p)))
def c2042 : List Lit := [(282, false)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c2034, c1076] c2042 (by decide) p (sat_cons (step2034 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c2043 : List Lit := [(496, false)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c2035, c1245] c2043 (by decide) p (sat_cons (step2035 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c2044 : List Lit := [(482, false)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c2035, c1248] c2044 (by decide) p (sat_cons (step2035 p h) (sat_cons (step1248 p h) (sat_nil p)))
def c2045 : List Lit := [(466, false)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1215] c2045 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1215 p h) (sat_nil p)))
def c2046 : List Lit := [(452, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1218] c2046 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1218 p h) (sat_nil p)))
def c2047 : List Lit := [(420, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c2037, c1185] c2047 (by decide) p (sat_cons (step2037 p h) (sat_cons (step1185 p h) (sat_nil p)))
def c2048 : List Lit := [(404, false)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c2038, c1157] c2048 (by decide) p (sat_cons (step2038 p h) (sat_cons (step1157 p h) (sat_nil p)))
def c2049 : List Lit := [(390, false)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c2038, c1160] c2049 (by decide) p (sat_cons (step2038 p h) (sat_cons (step1160 p h) (sat_nil p)))
def c2050 : List Lit := [(372, false)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c2039, c1124] c2050 (by decide) p (sat_cons (step2039 p h) (sat_cons (step1124 p h) (sat_nil p)))
def c2051 : List Lit := [(358, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c2039, c1127] c2051 (by decide) p (sat_cons (step2039 p h) (sat_cons (step1127 p h) (sat_nil p)))
def c2052 : List Lit := [(342, false)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c2040, c1097] c2052 (by decide) p (sat_cons (step2040 p h) (sat_cons (step1097 p h) (sat_nil p)))
def c2053 : List Lit := [(296, false)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c2041, c1071] c2053 (by decide) p (sat_cons (step2041 p h) (sat_cons (step1071 p h) (sat_nil p)))
def c2054 : List Lit := [(480, false)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c2044, c1229] c2054 (by decide) p (sat_cons (step2044 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c2055 : List Lit := [(450, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c2046, c1200] c2055 (by decide) p (sat_cons (step2046 p h) (sat_cons (step1200 p h) (sat_nil p)))
def c2056 : List Lit := [(412, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c2047, c1173] c2056 (by decide) p (sat_cons (step2047 p h) (sat_cons (step1173 p h) (sat_nil p)))
def c2057 : List Lit := [(396, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c2048, c1155] c2057 (by decide) p (sat_cons (step2048 p h) (sat_cons (step1155 p h) (sat_nil p)))
def c2058 : List Lit := [(370, false)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1120] c2058 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1120 p h) (sat_nil p)))
def c2059 : List Lit := [(288, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c2053, c1057] c2059 (by decide) p (sat_cons (step2053 p h) (sat_cons (step1057 p h) (sat_nil p)))
def c2060 : List Lit := [(476, false)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c2054, c1227] c2060 (by decide) p (sat_cons (step2054 p h) (sat_cons (step1227 p h) (sat_nil p)))
def c2061 : List Lit := [(368, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c2058, c1118] c2061 (by decide) p (sat_cons (step2058 p h) (sat_cons (step1118 p h) (sat_nil p)))
def c2062 : List Lit := [(129, true), (130, true), (132, true), (135, true), (139, true), (140, true), (141, true), (143, true), (145, true), (147, true), (148, true), (150, true), (151, true), (154, true), (156, true), (158, true), (159, true), (161, true), (164, true), (165, true), (167, true), (168, true), (171, true), (172, true), (176, true), (179, true), (180, true), (182, true), (184, true), (185, true), (189, true), (190, true), (193, true), (195, true), (197, true), (198, true), (201, true), (203, true), (205, true), (207, true), (208, true), (211, true), (212, true), (215, true), (219, true), (220, true), (225, true), (226, true), (227, true), (229, true), (231, true), (233, true), (235, true), (237, true), (238, true), (242, true), (243, true), (244, true), (246, true), (247, true), (249, true), (251, true), (253, true)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.TreeRup.prove_clause [c966, c967, c968, c969, c970, c971, c972, c973, c974, c975, c976, c977, c978, c979, c980, c981, c982, c983, c984, c985, c986, c987, c988, c989, c990, c991, c992, c993, c994, c995, c996, c997, c998, c999, c1000, c1001, c1002, c1003, c1004, c1005, c1006, c1007, c1008, c1009, c1010, c1011, c1012, c1013, c1014, c1015, c1016, c1017, c1018, c1019, c1020, c1021, c1022, c1023, c1024, c1025, c1026, c1027, c1028, c1263] c2062 (by decide) p (sat_cons (step966 p h) (sat_cons (step967 p h) (sat_cons (step968 p h) (sat_cons (step969 p h) (sat_cons (step970 p h) (sat_cons (step971 p h) (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step974 p h) (sat_cons (step975 p h) (sat_cons (step976 p h) (sat_cons (step977 p h) (sat_cons (step978 p h) (sat_cons (step979 p h) (sat_cons (step980 p h) (sat_cons (step981 p h) (sat_cons (step982 p h) (sat_cons (step983 p h) (sat_cons (step984 p h) (sat_cons (step985 p h) (sat_cons (step986 p h) (sat_cons (step987 p h) (sat_cons (step988 p h) (sat_cons (step989 p h) (sat_cons (step990 p h) (sat_cons (step991 p h) (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step996 p h) (sat_cons (step997 p h) (sat_cons (step998 p h) (sat_cons (step999 p h) (sat_cons (step1000 p h) (sat_cons (step1001 p h) (sat_cons (step1002 p h) (sat_cons (step1003 p h) (sat_cons (step1004 p h) (sat_cons (step1005 p h) (sat_cons (step1006 p h) (sat_cons (step1007 p h) (sat_cons (step1008 p h) (sat_cons (step1009 p h) (sat_cons (step1010 p h) (sat_cons (step1011 p h) (sat_cons (step1012 p h) (sat_cons (step1013 p h) (sat_cons (step1014 p h) (sat_cons (step1015 p h) (sat_cons (step1016 p h) (sat_cons (step1017 p h) (sat_cons (step1018 p h) (sat_cons (step1019 p h) (sat_cons (step1020 p h) (sat_cons (step1021 p h) (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step1024 p h) (sat_cons (step1025 p h) (sat_cons (step1026 p h) (sat_cons (step1027 p h) (sat_cons (step1028 p h) (sat_cons (step1263 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2063 : List Lit := [(965, true)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c2026, c1454] c2063 (by decide) p (sat_cons (step2026 p h) (sat_cons (step1454 p h) (sat_nil p)))
def c2064 : List Lit := [(64, true), (966, true)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c2026, c1455] c2064 (by decide) p (sat_cons (step2026 p h) (sat_cons (step1455 p h) (sat_nil p)))
def c2065 : List Lit := [(967, true)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c2063, c1456] c2065 (by decide) p (sat_cons (step2063 p h) (sat_cons (step1456 p h) (sat_nil p)))
def c2066 : List Lit := [(963, false), (968, true)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c2063, c1458] c2066 (by decide) p (sat_cons (step2063 p h) (sat_cons (step1458 p h) (sat_nil p)))
def c2067 : List Lit := [(964, false), (969, true)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c2063, c1460] c2067 (by decide) p (sat_cons (step2063 p h) (sat_cons (step1460 p h) (sat_nil p)))
def c2068 : List Lit := [(971, true)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c2065, c1462] c2068 (by decide) p (sat_cons (step2065 p h) (sat_cons (step1462 p h) (sat_nil p)))
def c2069 : List Lit := [(959, false), (972, true)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c2065, c1465] c2069 (by decide) p (sat_cons (step2065 p h) (sat_cons (step1465 p h) (sat_nil p)))
def c2070 : List Lit := [(960, false), (973, true)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c2065, c1470] c2070 (by decide) p (sat_cons (step2065 p h) (sat_cons (step1470 p h) (sat_nil p)))
def c2071 : List Lit := [(961, false), (974, true)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c2065, c1474] c2071 (by decide) p (sat_cons (step2065 p h) (sat_cons (step1474 p h) (sat_nil p)))
def c2072 : List Lit := [(962, false), (975, true)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c2065, c1477] c2072 (by decide) p (sat_cons (step2065 p h) (sat_cons (step1477 p h) (sat_nil p)))
def c2073 : List Lit := [(949, false), (982, true)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1490] c2073 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1490 p h) (sat_nil p)))
def c2074 : List Lit := [(950, false), (983, true)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1495] c2074 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1495 p h) (sat_nil p)))
def c2075 : List Lit := [(951, false), (984, true)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1500] c2075 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1500 p h) (sat_nil p)))
def c2076 : List Lit := [(952, false), (985, true)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1504] c2076 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1504 p h) (sat_nil p)))
def c2077 : List Lit := [(1019, true)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c2028, c1541] c2077 (by decide) p (sat_cons (step2028 p h) (sat_cons (step1541 p h) (sat_nil p)))
def c2078 : List Lit := [(1020, true)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c2027, c2028, c1542] c2078 (by decide) p (sat_cons (step2027 p h) (sat_cons (step2028 p h) (sat_cons (step1542 p h) (sat_nil p))))
def c2079 : List Lit := [(1022, false), (1025, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c2077, c1546] c2079 (by decide) p (sat_cons (step2077 p h) (sat_cons (step1546 p h) (sat_nil p)))
def c2080 : List Lit := [(1024, true)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1547] c2080 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1547 p h) (sat_nil p)))
def c2081 : List Lit := [(1021, false), (1025, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1548] c2081 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1548 p h) (sat_nil p)))
def c2082 : List Lit := [(1022, false), (1026, true)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1549] c2082 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1549 p h) (sat_nil p)))
def c2083 : List Lit := [(1036, true)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c2080, c1564] c2083 (by decide) p (sat_cons (step2080 p h) (sat_cons (step1564 p h) (sat_nil p)))
def c2084 : List Lit := [(1031, false), (1037, true)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c2080, c1565] c2084 (by decide) p (sat_cons (step2080 p h) (sat_cons (step1565 p h) (sat_nil p)))
def c2085 : List Lit := [(1032, false), (1038, true)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c2080, c1566] c2085 (by decide) p (sat_cons (step2080 p h) (sat_cons (step1566 p h) (sat_nil p)))
def c2086 : List Lit := [(1033, false), (1039, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c2080, c1567] c2086 (by decide) p (sat_cons (step2080 p h) (sat_cons (step1567 p h) (sat_nil p)))
def c2087 : List Lit := [(1034, false), (1040, true)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c2080, c1568] c2087 (by decide) p (sat_cons (step2080 p h) (sat_cons (step1568 p h) (sat_nil p)))
def c2088 : List Lit := [(1063, false), (1073, true)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c2083, c1631] c2088 (by decide) p (sat_cons (step2083 p h) (sat_cons (step1631 p h) (sat_nil p)))
end B112E057
