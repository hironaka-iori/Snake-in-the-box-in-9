import B112E105Part0001
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2057 : List Lit := [(116, false), (114, true), (104, true), (123, false), (240, true), (107, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c801, c865] c2057 (by decide) p (sat_cons (step801 p h) (sat_cons (step865 p h) (sat_nil p)))
def c2058 : List Lit := [(121, false), (1748, true), (110, false)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c1712, c2056, c1705, c1714, c1708, c1709, c908] c2058 (by decide) p (sat_cons (step1712 p h) (sat_cons (step2056 p h) (sat_cons (step1705 p h) (sat_cons (step1714 p h) (sat_cons (step1708 p h) (sat_cons (step1709 p h) (sat_cons (step908 p h) (sat_nil p))))))))
def c2059 : List Lit := [(14, true), (2, false), (126, true), (32, true)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1932, c2] c2059 (by decide) p (sat_cons (step1932 p h) (sat_cons (step2 p h) (sat_nil p)))
def c2060 : List Lit := [(3, true), (2, false), (126, true), (32, true)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c1932, c3] c2060 (by decide) p (sat_cons (step1932 p h) (sat_cons (step3 p h) (sat_nil p)))
def c2061 : List Lit := [(14, true), (3, true), (126, true), (2, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c1932, c4] c2061 (by decide) p (sat_cons (step1932 p h) (sat_cons (step4 p h) (sat_nil p)))
def c2062 : List Lit := [(3, false), (4, true)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c944, c5] c2062 (by decide) p (sat_cons (step944 p h) (sat_cons (step5 p h) (sat_nil p)))
def c2063 : List Lit := [(3, false), (2, true)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c944, c6] c2063 (by decide) p (sat_cons (step944 p h) (sat_cons (step6 p h) (sat_nil p)))
def c2064 : List Lit := [(5, false), (16, false), (35, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c1929, c12] c2064 (by decide) p (sat_cons (step1929 p h) (sat_cons (step12 p h) (sat_nil p)))
def c2065 : List Lit := [(5, false), (16, true), (35, true)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c945, c13] c2065 (by decide) p (sat_cons (step945 p h) (sat_cons (step13 p h) (sat_nil p)))
def c2066 : List Lit := [(8, false), (6, true), (7, true)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c946, c20] c2066 (by decide) p (sat_cons (step946 p h) (sat_cons (step20 p h) (sat_nil p)))
def c2067 : List Lit := [(8, false), (4, true), (7, true)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c946, c21] c2067 (by decide) p (sat_cons (step946 p h) (sat_cons (step21 p h) (sat_nil p)))
def c2068 : List Lit := [(11, false), (6, true)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c947, c26] c2068 (by decide) p (sat_cons (step947 p h) (sat_cons (step26 p h) (sat_nil p)))
def c2069 : List Lit := [(16, true), (12, false), (22, true)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c948, c28] c2069 (by decide) p (sat_cons (step948 p h) (sat_cons (step28 p h) (sat_nil p)))
def c2070 : List Lit := [(12, false), (13, true), (22, true)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c948, c29] c2070 (by decide) p (sat_cons (step948 p h) (sat_cons (step29 p h) (sat_nil p)))
def c2071 : List Lit := [(16, true), (12, false), (13, true)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c948, c30] c2071 (by decide) p (sat_cons (step948 p h) (sat_cons (step30 p h) (sat_nil p)))
def c2072 : List Lit := [(14, false), (25, true), (17, true), (49, true)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c949, c40] c2072 (by decide) p (sat_cons (step949 p h) (sat_cons (step40 p h) (sat_nil p)))
def c2073 : List Lit := [(14, false), (25, true), (2, true), (49, true)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c949, c41] c2073 (by decide) p (sat_cons (step949 p h) (sat_cons (step41 p h) (sat_nil p)))
def c2074 : List Lit := [(14, false), (2, true), (17, true), (49, true)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c949, c42] c2074 (by decide) p (sat_cons (step949 p h) (sat_cons (step42 p h) (sat_nil p)))
def c2075 : List Lit := [(14, false), (25, true), (17, true), (2, true)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c949, c43] c2075 (by decide) p (sat_cons (step949 p h) (sat_cons (step43 p h) (sat_nil p)))
def c2076 : List Lit := [(27, true), (18, false), (20, true), (17, true)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c951, c58] c2076 (by decide) p (sat_cons (step951 p h) (sat_cons (step58 p h) (sat_nil p)))
def c2077 : List Lit := [(18, false), (16, true), (20, true), (27, true)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c951, c59] c2077 (by decide) p (sat_cons (step951 p h) (sat_cons (step59 p h) (sat_nil p)))
def c2078 : List Lit := [(18, false), (16, true), (17, true), (27, true)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c951, c60] c2078 (by decide) p (sat_cons (step951 p h) (sat_cons (step60 p h) (sat_nil p)))
def c2079 : List Lit := [(16, true), (18, false), (17, true), (20, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c951, c61] c2079 (by decide) p (sat_cons (step951 p h) (sat_cons (step61 p h) (sat_nil p)))
def c2080 : List Lit := [(21, false), (25, true), (22, true)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c953, c77] c2080 (by decide) p (sat_cons (step953 p h) (sat_cons (step77 p h) (sat_nil p)))
def c2081 : List Lit := [(23, true), (21, false), (22, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c953, c78] c2081 (by decide) p (sat_cons (step953 p h) (sat_cons (step78 p h) (sat_nil p)))
def c2082 : List Lit := [(26, false), (28, true)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c955, c111] c2082 (by decide) p (sat_cons (step955 p h) (sat_cons (step111 p h) (sat_nil p)))
def c2083 : List Lit := [(26, false), (23, true)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c955, c112] c2083 (by decide) p (sat_cons (step955 p h) (sat_cons (step112 p h) (sat_nil p)))
def c2084 : List Lit := [(28, true), (29, false), (20, true)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c956, c122] c2084 (by decide) p (sat_cons (step956 p h) (sat_cons (step122 p h) (sat_nil p)))
def c2085 : List Lit := [(29, false), (27, true), (20, true)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c956, c123] c2085 (by decide) p (sat_cons (step956 p h) (sat_cons (step123 p h) (sat_nil p)))
def c2086 : List Lit := [(30, false), (31, true), (33, true), (35, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c957, c127] c2086 (by decide) p (sat_cons (step957 p h) (sat_cons (step127 p h) (sat_nil p)))
def c2087 : List Lit := [(32, false), (33, true), (37, true), (49, true)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c958, c135] c2087 (by decide) p (sat_cons (step958 p h) (sat_cons (step135 p h) (sat_nil p)))
def c2088 : List Lit := [(32, false), (2, true), (37, true), (49, true)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c958, c136] c2088 (by decide) p (sat_cons (step958 p h) (sat_cons (step136 p h) (sat_nil p)))
def c2089 : List Lit := [(32, false), (33, true), (2, true), (49, true)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c958, c137] c2089 (by decide) p (sat_cons (step958 p h) (sat_cons (step137 p h) (sat_nil p)))
def c2090 : List Lit := [(36, false), (35, true), (54, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c960, c154] c2090 (by decide) p (sat_cons (step960 p h) (sat_cons (step154 p h) (sat_nil p)))
def c2091 : List Lit := [(36, false), (31, true), (35, true)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c960, c155] c2091 (by decide) p (sat_cons (step960 p h) (sat_cons (step155 p h) (sat_nil p)))
def c2092 : List Lit := [(44, true), (38, false), (33, true), (37, true)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c961, c165] c2092 (by decide) p (sat_cons (step961 p h) (sat_cons (step165 p h) (sat_nil p)))
def c2093 : List Lit := [(33, true), (38, false), (37, true), (35, true)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c961, c166] c2093 (by decide) p (sat_cons (step961 p h) (sat_cons (step166 p h) (sat_nil p)))
def c2094 : List Lit := [(39, false), (41, true)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c962, c167] c2094 (by decide) p (sat_cons (step962 p h) (sat_cons (step167 p h) (sat_nil p)))
def c2095 : List Lit := [(39, false), (40, true)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c962, c168] c2095 (by decide) p (sat_cons (step962 p h) (sat_cons (step168 p h) (sat_nil p)))
def c2096 : List Lit := [(42, false), (45, true), (61, true)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c963, c178] c2096 (by decide) p (sat_cons (step963 p h) (sat_cons (step178 p h) (sat_nil p)))
def c2097 : List Lit := [(42, false), (41, true), (61, true)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c963, c179] c2097 (by decide) p (sat_cons (step963 p h) (sat_cons (step179 p h) (sat_nil p)))
def c2098 : List Lit := [(46, false), (45, true)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c965, c189] c2098 (by decide) p (sat_cons (step965 p h) (sat_cons (step189 p h) (sat_nil p)))
def c2099 : List Lit := [(46, false), (44, true)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c965, c190] c2099 (by decide) p (sat_cons (step965 p h) (sat_cons (step190 p h) (sat_nil p)))
def c2100 : List Lit := [(47, false), (102, true), (52, true), (49, true)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c966, c195] c2100 (by decide) p (sat_cons (step966 p h) (sat_cons (step195 p h) (sat_nil p)))
def c2101 : List Lit := [(47, false), (48, true), (52, true), (102, true)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c966, c196] c2101 (by decide) p (sat_cons (step966 p h) (sat_cons (step196 p h) (sat_nil p)))
def c2102 : List Lit := [(47, false), (49, true), (48, true), (102, true)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c966, c197] c2102 (by decide) p (sat_cons (step966 p h) (sat_cons (step197 p h) (sat_nil p)))
def c2103 : List Lit := [(106, true), (33, true), (49, true), (50, false)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c967, c232] c2103 (by decide) p (sat_cons (step967 p h) (sat_cons (step232 p h) (sat_nil p)))
def c2104 : List Lit := [(51, false), (107, true), (56, true), (49, true), (61, true)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c968, c243] c2104 (by decide) p (sat_cons (step968 p h) (sat_cons (step243 p h) (sat_nil p)))
def c2105 : List Lit := [(51, false), (107, true), (49, true), (56, true), (48, true)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c968, c244] c2105 (by decide) p (sat_cons (step968 p h) (sat_cons (step244 p h) (sat_nil p)))
def c2106 : List Lit := [(53, false), (54, true), (52, true), (56, true)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c969, c259] c2106 (by decide) p (sat_cons (step969 p h) (sat_cons (step259 p h) (sat_nil p)))
def c2107 : List Lit := [(53, false), (54, true), (48, true), (56, true)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c969, c260] c2107 (by decide) p (sat_cons (step969 p h) (sat_cons (step260 p h) (sat_nil p)))
def c2108 : List Lit := [(53, false), (54, true), (52, true), (48, true)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c969, c261] c2108 (by decide) p (sat_cons (step969 p h) (sat_cons (step261 p h) (sat_nil p)))
def c2109 : List Lit := [(57, false), (54, true), (20, true), (113, true)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c971, c319] c2109 (by decide) p (sat_cons (step971 p h) (sat_cons (step319 p h) (sat_nil p)))
def c2110 : List Lit := [(22, true), (59, true), (115, true), (58, false), (60, true), (40, true)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c972, c340] c2110 (by decide) p (sat_cons (step972 p h) (sat_cons (step340 p h) (sat_nil p)))
def c2111 : List Lit := [(62, false), (60, true), (61, true)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c973, c363] c2111 (by decide) p (sat_cons (step973 p h) (sat_cons (step363 p h) (sat_nil p)))
def c2112 : List Lit := [(62, false), (59, true), (61, true)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c973, c364] c2112 (by decide) p (sat_cons (step973 p h) (sat_cons (step364 p h) (sat_nil p)))
def c2113 : List Lit := [(62, false), (60, true), (59, true)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c973, c365] c2113 (by decide) p (sat_cons (step973 p h) (sat_cons (step365 p h) (sat_nil p)))
def c2114 : List Lit := [(64, true), (63, false), (66, true)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c974, c367] c2114 (by decide) p (sat_cons (step974 p h) (sat_cons (step367 p h) (sat_nil p)))
def c2115 : List Lit := [(63, false), (66, true), (52, true)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c974, c368] c2115 (by decide) p (sat_cons (step974 p h) (sat_cons (step368 p h) (sat_nil p)))
def c2116 : List Lit := [(63, false), (64, true), (52, true)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c974, c369] c2116 (by decide) p (sat_cons (step974 p h) (sat_cons (step369 p h) (sat_nil p)))
def c2117 : List Lit := [(65, false), (64, true), (59, true)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c975, c377] c2117 (by decide) p (sat_cons (step975 p h) (sat_cons (step377 p h) (sat_nil p)))
def c2118 : List Lit := [(65, false), (64, true), (54, true)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c975, c378] c2118 (by decide) p (sat_cons (step975 p h) (sat_cons (step378 p h) (sat_nil p)))
def c2119 : List Lit := [(65, false), (59, true), (54, true)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c975, c379] c2119 (by decide) p (sat_cons (step975 p h) (sat_cons (step379 p h) (sat_nil p)))
def c2120 : List Lit := [(72, true), (67, false), (102, true)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c976, c389] c2120 (by decide) p (sat_cons (step976 p h) (sat_cons (step389 p h) (sat_nil p)))
end B112E105
