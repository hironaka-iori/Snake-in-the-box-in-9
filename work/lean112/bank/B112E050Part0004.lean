import B112E050Part0003
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2072 : List Lit := [(75, true), (58, true), (56, false), (64, true), (57, true)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c870, c196] c2072 (by decide) p (sat_cons (step870 p h) (sat_cons (step196 p h) (sat_nil p)))
def c2073 : List Lit := [(52, true), (64, true), (56, false), (57, true), (75, true)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c870, c197] c2073 (by decide) p (sat_cons (step870 p h) (sat_cons (step197 p h) (sat_nil p)))
def c2074 : List Lit := [(75, true), (58, true), (56, false), (57, true), (52, true)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c870, c198] c2074 (by decide) p (sat_cons (step870 p h) (sat_cons (step198 p h) (sat_nil p)))
def c2075 : List Lit := [(52, true), (64, true), (58, true), (57, true), (56, false)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c870, c199] c2075 (by decide) p (sat_cons (step870 p h) (sat_cons (step199 p h) (sat_nil p)))
def c2076 : List Lit := [(59, true), (61, true), (60, false)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c871, c218] c2076 (by decide) p (sat_cons (step871 p h) (sat_cons (step218 p h) (sat_nil p)))
def c2077 : List Lit := [(50, true), (61, true), (60, false)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c871, c219] c2077 (by decide) p (sat_cons (step871 p h) (sat_cons (step219 p h) (sat_nil p)))
def c2078 : List Lit := [(50, true), (59, true), (60, false)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c871, c220] c2078 (by decide) p (sat_cons (step871 p h) (sat_cons (step220 p h) (sat_nil p)))
def c2079 : List Lit := [(102, true), (80, true), (62, false), (67, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c872, c228] c2079 (by decide) p (sat_cons (step872 p h) (sat_cons (step228 p h) (sat_nil p)))
def c2080 : List Lit := [(102, true), (80, true), (62, false), (61, true)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c872, c229] c2080 (by decide) p (sat_cons (step872 p h) (sat_cons (step229 p h) (sat_nil p)))
def c2081 : List Lit := [(102, true), (67, true), (62, false), (61, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c872, c230] c2081 (by decide) p (sat_cons (step872 p h) (sat_cons (step230 p h) (sat_nil p)))
def c2082 : List Lit := [(80, true), (67, true), (62, false), (61, true)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c872, c231] c2082 (by decide) p (sat_cons (step872 p h) (sat_cons (step231 p h) (sat_nil p)))
def c2083 : List Lit := [(64, true), (81, true), (63, false)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c873, c233] c2083 (by decide) p (sat_cons (step873 p h) (sat_cons (step233 p h) (sat_nil p)))
def c2084 : List Lit := [(64, true), (59, true), (63, false)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c873, c234] c2084 (by decide) p (sat_cons (step873 p h) (sat_cons (step234 p h) (sat_nil p)))
def c2085 : List Lit := [(64, true), (65, false), (67, true), (106, true)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c874, c241] c2085 (by decide) p (sat_cons (step874 p h) (sat_cons (step241 p h) (sat_nil p)))
def c2086 : List Lit := [(65, false), (57, true), (67, true), (106, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c874, c242] c2086 (by decide) p (sat_cons (step874 p h) (sat_cons (step242 p h) (sat_nil p)))
def c2087 : List Lit := [(64, true), (65, false), (57, true), (106, true)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c874, c243] c2087 (by decide) p (sat_cons (step874 p h) (sat_cons (step243 p h) (sat_nil p)))
def c2088 : List Lit := [(64, true), (57, true), (67, true), (65, false)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c874, c244] c2088 (by decide) p (sat_cons (step874 p h) (sat_cons (step244 p h) (sat_nil p)))
def c2089 : List Lit := [(64, true), (66, false), (107, true), (67, true)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c875, c247] c2089 (by decide) p (sat_cons (step875 p h) (sat_cons (step247 p h) (sat_nil p)))
def c2090 : List Lit := [(66, false), (58, true), (107, true), (67, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c875, c248] c2090 (by decide) p (sat_cons (step875 p h) (sat_cons (step248 p h) (sat_nil p)))
def c2091 : List Lit := [(64, true), (58, true), (66, false), (107, true)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c875, c249] c2091 (by decide) p (sat_cons (step875 p h) (sat_cons (step249 p h) (sat_nil p)))
def c2092 : List Lit := [(64, true), (58, true), (67, true), (66, false)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c875, c250] c2092 (by decide) p (sat_cons (step875 p h) (sat_cons (step250 p h) (sat_nil p)))
def c2093 : List Lit := [(2, true), (71, true), (50, true), (68, false)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c876, c262] c2093 (by decide) p (sat_cons (step876 p h) (sat_cons (step262 p h) (sat_nil p)))
def c2094 : List Lit := [(71, true), (114, true), (80, true), (72, false)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c877, c281] c2094 (by decide) p (sat_cons (step877 p h) (sat_cons (step281 p h) (sat_nil p)))
def c2095 : List Lit := [(70, true), (114, true), (80, true), (72, false)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c877, c282] c2095 (by decide) p (sat_cons (step877 p h) (sat_cons (step282 p h) (sat_nil p)))
def c2096 : List Lit := [(71, true), (70, true), (72, false), (114, true)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c877, c283] c2096 (by decide) p (sat_cons (step877 p h) (sat_cons (step283 p h) (sat_nil p)))
def c2097 : List Lit := [(71, true), (70, true), (80, true), (72, false)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c877, c284] c2097 (by decide) p (sat_cons (step877 p h) (sat_cons (step284 p h) (sat_nil p)))
def c2098 : List Lit := [(75, true), (81, true), (73, false)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c878, c285] c2098 (by decide) p (sat_cons (step878 p h) (sat_cons (step285 p h) (sat_nil p)))
def c2099 : List Lit := [(74, true), (81, true), (73, false)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c878, c286] c2099 (by decide) p (sat_cons (step878 p h) (sat_cons (step286 p h) (sat_nil p)))
def c2100 : List Lit := [(74, true), (75, true), (73, false)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c878, c287] c2100 (by decide) p (sat_cons (step878 p h) (sat_cons (step287 p h) (sat_nil p)))
def c2101 : List Lit := [(77, true), (78, false), (70, true), (80, true)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c879, c301] c2101 (by decide) p (sat_cons (step879 p h) (sat_cons (step301 p h) (sat_nil p)))
def c2102 : List Lit := [(76, true), (78, false), (80, true), (70, true)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c879, c302] c2102 (by decide) p (sat_cons (step879 p h) (sat_cons (step302 p h) (sat_nil p)))
def c2103 : List Lit := [(77, true), (79, false), (80, true)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c880, c303] c2103 (by decide) p (sat_cons (step880 p h) (sat_cons (step303 p h) (sat_nil p)))
def c2104 : List Lit := [(71, true), (79, false), (80, true)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c880, c304] c2104 (by decide) p (sat_cons (step880 p h) (sat_cons (step304 p h) (sat_nil p)))
def c2105 : List Lit := [(77, true), (71, true), (79, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c880, c305] c2105 (by decide) p (sat_cons (step880 p h) (sat_cons (step305 p h) (sat_nil p)))
def c2106 : List Lit := [(84, true), (81, true), (82, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c881, c358] c2106 (by decide) p (sat_cons (step881 p h) (sat_cons (step358 p h) (sat_nil p)))
def c2107 : List Lit := [(84, true), (82, false), (76, true)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c881, c359] c2107 (by decide) p (sat_cons (step881 p h) (sat_cons (step359 p h) (sat_nil p)))
def c2108 : List Lit := [(81, true), (82, false), (76, true)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c881, c360] c2108 (by decide) p (sat_cons (step881 p h) (sat_cons (step360 p h) (sat_nil p)))
def c2109 : List Lit := [(74, true), (84, true), (125, true), (83, false)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c882, c363] c2109 (by decide) p (sat_cons (step882 p h) (sat_cons (step363 p h) (sat_nil p)))
def c2110 : List Lit := [(84, true), (80, true), (85, false)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c883, c366] c2110 (by decide) p (sat_cons (step883 p h) (sat_cons (step366 p h) (sat_nil p)))
def c2111 : List Lit := [(85, false), (84, true), (67, true)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c883, c367] c2111 (by decide) p (sat_cons (step883 p h) (sat_cons (step367 p h) (sat_nil p)))
def c2112 : List Lit := [(67, true), (80, true), (85, false)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c883, c368] c2112 (by decide) p (sat_cons (step883 p h) (sat_cons (step368 p h) (sat_nil p)))
def c2113 : List Lit := [(86, true), (50, true), (87, false), (90, true), (94, true)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c884, c377] c2113 (by decide) p (sat_cons (step884 p h) (sat_cons (step377 p h) (sat_nil p)))
def c2114 : List Lit := [(15, true), (86, true), (87, false), (90, true), (94, true)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c884, c378] c2114 (by decide) p (sat_cons (step884 p h) (sat_cons (step378 p h) (sat_nil p)))
def c2115 : List Lit := [(15, true), (90, true), (87, false), (94, true), (50, true)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c884, c379] c2115 (by decide) p (sat_cons (step884 p h) (sat_cons (step379 p h) (sat_nil p)))
def c2116 : List Lit := [(50, true), (15, true), (87, false), (94, true), (86, true)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c884, c380] c2116 (by decide) p (sat_cons (step884 p h) (sat_cons (step380 p h) (sat_nil p)))
def c2117 : List Lit := [(86, true), (90, true), (87, false), (15, true), (50, true)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c884, c381] c2117 (by decide) p (sat_cons (step884 p h) (sat_cons (step381 p h) (sat_nil p)))
def c2118 : List Lit := [(91, false), (90, true), (102, true), (114, true)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c885, c442] c2118 (by decide) p (sat_cons (step885 p h) (sat_cons (step442 p h) (sat_nil p)))
def c2119 : List Lit := [(89, true), (91, false), (102, true), (114, true)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c885, c443] c2119 (by decide) p (sat_cons (step885 p h) (sat_cons (step443 p h) (sat_nil p)))
def c2120 : List Lit := [(91, false), (90, true), (89, true), (114, true)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c885, c444] c2120 (by decide) p (sat_cons (step885 p h) (sat_cons (step444 p h) (sat_nil p)))
def c2121 : List Lit := [(89, true), (91, false), (90, true), (102, true)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c885, c445] c2121 (by decide) p (sat_cons (step885 p h) (sat_cons (step445 p h) (sat_nil p)))
def c2122 : List Lit := [(92, false), (94, true), (93, true)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c886, c446] c2122 (by decide) p (sat_cons (step886 p h) (sat_cons (step446 p h) (sat_nil p)))
def c2123 : List Lit := [(86, true), (92, false), (94, true)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c886, c447] c2123 (by decide) p (sat_cons (step886 p h) (sat_cons (step447 p h) (sat_nil p)))
def c2124 : List Lit := [(86, true), (92, false), (93, true)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c886, c448] c2124 (by decide) p (sat_cons (step886 p h) (sat_cons (step448 p h) (sat_nil p)))
def c2125 : List Lit := [(89, true), (57, true), (117, true), (93, true), (96, false), (106, true)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c887, c521] c2125 (by decide) p (sat_cons (step887 p h) (sat_cons (step521 p h) (sat_nil p)))
def c2126 : List Lit := [(89, true), (22, true), (96, false), (93, true), (106, true), (117, true)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c887, c522] c2126 (by decide) p (sat_cons (step887 p h) (sat_cons (step522 p h) (sat_nil p)))
def c2127 : List Lit := [(90, true), (118, true), (97, false), (23, true), (107, true), (94, true)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c888, c536] c2127 (by decide) p (sat_cons (step888 p h) (sat_cons (step536 p h) (sat_nil p)))
def c2128 : List Lit := [(99, true), (98, true), (102, true), (100, false), (106, true)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c889, c553] c2128 (by decide) p (sat_cons (step889 p h) (sat_cons (step553 p h) (sat_nil p)))
def c2129 : List Lit := [(99, true), (89, true), (106, true), (102, true), (100, false)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c889, c554] c2129 (by decide) p (sat_cons (step889 p h) (sat_cons (step554 p h) (sat_nil p)))
def c2130 : List Lit := [(89, true), (98, true), (100, false), (102, true), (106, true)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c889, c555] c2130 (by decide) p (sat_cons (step889 p h) (sat_cons (step555 p h) (sat_nil p)))
def c2131 : List Lit := [(99, true), (89, true), (98, true), (100, false), (106, true)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c889, c556] c2131 (by decide) p (sat_cons (step889 p h) (sat_cons (step556 p h) (sat_nil p)))
def c2132 : List Lit := [(99, true), (89, true), (98, true), (100, false), (102, true)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c889, c557] c2132 (by decide) p (sat_cons (step889 p h) (sat_cons (step557 p h) (sat_nil p)))
def c2133 : List Lit := [(99, true), (107, true), (101, false), (102, true)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c890, c559] c2133 (by decide) p (sat_cons (step890 p h) (sat_cons (step559 p h) (sat_nil p)))
def c2134 : List Lit := [(90, true), (107, true), (101, false), (102, true)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c890, c560] c2134 (by decide) p (sat_cons (step890 p h) (sat_cons (step560 p h) (sat_nil p)))
def c2135 : List Lit := [(99, true), (90, true), (101, false), (107, true)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c890, c561] c2135 (by decide) p (sat_cons (step890 p h) (sat_cons (step561 p h) (sat_nil p)))
end B112E050
