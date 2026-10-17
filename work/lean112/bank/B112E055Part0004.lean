import B112E055Part0003
namespace B112E055
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2198 : List Lit := [(75, true), (123, true), (87, false), (86, true), (16, true), (104, true)]
theorem step2198 (p : Nat → Bool) (h : Constraints p) : clause p c2198 = true :=
  Snake9.LocalRup.prove_clause [c999, c646] c2198 (by decide) p (sat_cons (step999 p h) (sat_cons (step646 p h) (sat_nil p)))
def c2199 : List Lit := [(87, false), (123, true), (89, true), (86, true), (75, true), (16, true)]
theorem step2199 (p : Nat → Bool) (h : Constraints p) : clause p c2199 = true :=
  Snake9.LocalRup.prove_clause [c999, c647] c2199 (by decide) p (sat_cons (step999 p h) (sat_cons (step647 p h) (sat_nil p)))
def c2200 : List Lit := [(75, true), (86, true), (87, false), (89, true), (104, true), (16, true)]
theorem step2200 (p : Nat → Bool) (h : Constraints p) : clause p c2200 = true :=
  Snake9.LocalRup.prove_clause [c999, c648] c2200 (by decide) p (sat_cons (step999 p h) (sat_cons (step648 p h) (sat_nil p)))
def c2201 : List Lit := [(88, false), (86, true), (89, true)]
theorem step2201 (p : Nat → Bool) (h : Constraints p) : clause p c2201 = true :=
  Snake9.LocalRup.prove_clause [c1000, c650] c2201 (by decide) p (sat_cons (step1000 p h) (sat_cons (step650 p h) (sat_nil p)))
def c2202 : List Lit := [(88, false), (89, true), (81, true)]
theorem step2202 (p : Nat → Bool) (h : Constraints p) : clause p c2202 = true :=
  Snake9.LocalRup.prove_clause [c1000, c651] c2202 (by decide) p (sat_cons (step1000 p h) (sat_cons (step651 p h) (sat_nil p)))
def c2203 : List Lit := [(88, false), (86, true), (81, true)]
theorem step2203 (p : Nat → Bool) (h : Constraints p) : clause p c2203 = true :=
  Snake9.LocalRup.prove_clause [c1000, c652] c2203 (by decide) p (sat_cons (step1000 p h) (sat_cons (step652 p h) (sat_nil p)))
def c2204 : List Lit := [(125, true), (106, true), (77, true), (82, true), (90, false), (18, true)]
theorem step2204 (p : Nat → Bool) (h : Constraints p) : clause p c2204 = true :=
  Snake9.LocalRup.prove_clause [c1001, c705] c2204 (by decide) p (sat_cons (step1001 p h) (sat_cons (step705 p h) (sat_nil p)))
def c2205 : List Lit := [(92, false), (94, true), (100, true)]
theorem step2205 (p : Nat → Bool) (h : Constraints p) : clause p c2205 = true :=
  Snake9.LocalRup.prove_clause [c1003, c727] c2205 (by decide) p (sat_cons (step1003 p h) (sat_cons (step727 p h) (sat_nil p)))
def c2206 : List Lit := [(93, true), (92, false), (100, true)]
theorem step2206 (p : Nat → Bool) (h : Constraints p) : clause p c2206 = true :=
  Snake9.LocalRup.prove_clause [c1003, c728] c2206 (by decide) p (sat_cons (step1003 p h) (sat_cons (step728 p h) (sat_nil p)))
def c2207 : List Lit := [(92, false), (93, true), (94, true)]
theorem step2207 (p : Nat → Bool) (h : Constraints p) : clause p c2207 = true :=
  Snake9.LocalRup.prove_clause [c1003, c729] c2207 (by decide) p (sat_cons (step1003 p h) (sat_cons (step729 p h) (sat_nil p)))
def c2208 : List Lit := [(95, false), (98, true), (71, true), (93, true)]
theorem step2208 (p : Nat → Bool) (h : Constraints p) : clause p c2208 = true :=
  Snake9.LocalRup.prove_clause [c1004, c745] c2208 (by decide) p (sat_cons (step1004 p h) (sat_cons (step745 p h) (sat_nil p)))
def c2209 : List Lit := [(95, false), (98, true), (23, true), (71, true)]
theorem step2209 (p : Nat → Bool) (h : Constraints p) : clause p c2209 = true :=
  Snake9.LocalRup.prove_clause [c1004, c746] c2209 (by decide) p (sat_cons (step1004 p h) (sat_cons (step746 p h) (sat_nil p)))
def c2210 : List Lit := [(23, true), (71, true), (95, false), (93, true)]
theorem step2210 (p : Nat → Bool) (h : Constraints p) : clause p c2210 = true :=
  Snake9.LocalRup.prove_clause [c1004, c747] c2210 (by decide) p (sat_cons (step1004 p h) (sat_cons (step747 p h) (sat_nil p)))
def c2211 : List Lit := [(96, false), (99, true)]
theorem step2211 (p : Nat → Bool) (h : Constraints p) : clause p c2211 = true :=
  Snake9.LocalRup.prove_clause [c1005, c748] c2211 (by decide) p (sat_cons (step1005 p h) (sat_cons (step748 p h) (sat_nil p)))
def c2212 : List Lit := [(96, false), (94, true)]
theorem step2212 (p : Nat → Bool) (h : Constraints p) : clause p c2212 = true :=
  Snake9.LocalRup.prove_clause [c1005, c749] c2212 (by decide) p (sat_cons (step1005 p h) (sat_cons (step749 p h) (sat_nil p)))
def c2213 : List Lit := [(97, false), (99, true), (77, true), (106, true)]
theorem step2213 (p : Nat → Bool) (h : Constraints p) : clause p c2213 = true :=
  Snake9.LocalRup.prove_clause [c1006, c754] c2213 (by decide) p (sat_cons (step1006 p h) (sat_cons (step754 p h) (sat_nil p)))
def c2214 : List Lit := [(97, false), (106, true), (98, true), (77, true)]
theorem step2214 (p : Nat → Bool) (h : Constraints p) : clause p c2214 = true :=
  Snake9.LocalRup.prove_clause [c1006, c755] c2214 (by decide) p (sat_cons (step1006 p h) (sat_cons (step755 p h) (sat_nil p)))
def c2215 : List Lit := [(97, false), (99, true), (77, true), (98, true)]
theorem step2215 (p : Nat → Bool) (h : Constraints p) : clause p c2215 = true :=
  Snake9.LocalRup.prove_clause [c1006, c756] c2215 (by decide) p (sat_cons (step1006 p h) (sat_cons (step756 p h) (sat_nil p)))
def c2216 : List Lit := [(101, false), (100, true), (104, true)]
theorem step2216 (p : Nat → Bool) (h : Constraints p) : clause p c2216 = true :=
  Snake9.LocalRup.prove_clause [c1007, c776] c2216 (by decide) p (sat_cons (step1007 p h) (sat_cons (step776 p h) (sat_nil p)))
def c2217 : List Lit := [(101, false), (104, true), (93, true)]
theorem step2217 (p : Nat → Bool) (h : Constraints p) : clause p c2217 = true :=
  Snake9.LocalRup.prove_clause [c1007, c777] c2217 (by decide) p (sat_cons (step1007 p h) (sat_cons (step777 p h) (sat_nil p)))
def c2218 : List Lit := [(93, true), (100, true), (101, false)]
theorem step2218 (p : Nat → Bool) (h : Constraints p) : clause p c2218 = true :=
  Snake9.LocalRup.prove_clause [c1007, c778] c2218 (by decide) p (sat_cons (step1007 p h) (sat_cons (step778 p h) (sat_nil p)))
def c2219 : List Lit := [(103, false), (102, true), (108, true)]
theorem step2219 (p : Nat → Bool) (h : Constraints p) : clause p c2219 = true :=
  Snake9.LocalRup.prove_clause [c1008, c787] c2219 (by decide) p (sat_cons (step1008 p h) (sat_cons (step787 p h) (sat_nil p)))
def c2220 : List Lit := [(103, false), (108, true), (85, true)]
theorem step2220 (p : Nat → Bool) (h : Constraints p) : clause p c2220 = true :=
  Snake9.LocalRup.prove_clause [c1008, c788] c2220 (by decide) p (sat_cons (step1008 p h) (sat_cons (step788 p h) (sat_nil p)))
def c2221 : List Lit := [(103, false), (102, true), (85, true)]
theorem step2221 (p : Nat → Bool) (h : Constraints p) : clause p c2221 = true :=
  Snake9.LocalRup.prove_clause [c1008, c789] c2221 (by decide) p (sat_cons (step1008 p h) (sat_cons (step789 p h) (sat_nil p)))
def c2222 : List Lit := [(105, false), (104, true), (108, true)]
theorem step2222 (p : Nat → Bool) (h : Constraints p) : clause p c2222 = true :=
  Snake9.LocalRup.prove_clause [c1009, c798] c2222 (by decide) p (sat_cons (step1009 p h) (sat_cons (step798 p h) (sat_nil p)))
def c2223 : List Lit := [(108, true), (105, false), (89, true)]
theorem step2223 (p : Nat → Bool) (h : Constraints p) : clause p c2223 = true :=
  Snake9.LocalRup.prove_clause [c1009, c799] c2223 (by decide) p (sat_cons (step1009 p h) (sat_cons (step799 p h) (sat_nil p)))
def c2224 : List Lit := [(105, false), (104, true), (89, true)]
theorem step2224 (p : Nat → Bool) (h : Constraints p) : clause p c2224 = true :=
  Snake9.LocalRup.prove_clause [c1009, c800] c2224 (by decide) p (sat_cons (step1009 p h) (sat_cons (step800 p h) (sat_nil p)))
def c2225 : List Lit := [(37, true), (107, false), (102, true), (106, true), (108, true)]
theorem step2225 (p : Nat → Bool) (h : Constraints p) : clause p c2225 = true :=
  Snake9.LocalRup.prove_clause [c1010, c821] c2225 (by decide) p (sat_cons (step1010 p h) (sat_cons (step821 p h) (sat_nil p)))
def c2226 : List Lit := [(37, true), (107, false), (99, true), (102, true), (108, true)]
theorem step2226 (p : Nat → Bool) (h : Constraints p) : clause p c2226 = true :=
  Snake9.LocalRup.prove_clause [c1010, c822] c2226 (by decide) p (sat_cons (step1010 p h) (sat_cons (step822 p h) (sat_nil p)))
def c2227 : List Lit := [(109, false), (118, true), (111, true)]
theorem step2227 (p : Nat → Bool) (h : Constraints p) : clause p c2227 = true :=
  Snake9.LocalRup.prove_clause [c1011, c834] c2227 (by decide) p (sat_cons (step1011 p h) (sat_cons (step834 p h) (sat_nil p)))
def c2228 : List Lit := [(110, true), (109, false), (118, true)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c1011, c835] c2228 (by decide) p (sat_cons (step1011 p h) (sat_cons (step835 p h) (sat_nil p)))
def c2229 : List Lit := [(109, false), (110, true), (111, true)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c1011, c836] c2229 (by decide) p (sat_cons (step1011 p h) (sat_cons (step836 p h) (sat_nil p)))
def c2230 : List Lit := [(115, true), (112, false), (71, true), (40, true)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c1012, c847] c2230 (by decide) p (sat_cons (step1012 p h) (sat_cons (step847 p h) (sat_nil p)))
def c2231 : List Lit := [(112, false), (110, true), (71, true), (40, true)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c1012, c848] c2231 (by decide) p (sat_cons (step1012 p h) (sat_cons (step848 p h) (sat_nil p)))
def c2232 : List Lit := [(113, false), (116, true), (45, true)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c1013, c850] c2232 (by decide) p (sat_cons (step1013 p h) (sat_cons (step850 p h) (sat_nil p)))
def c2233 : List Lit := [(111, true), (113, false), (45, true)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c1013, c851] c2233 (by decide) p (sat_cons (step1013 p h) (sat_cons (step851 p h) (sat_nil p)))
def c2234 : List Lit := [(114, false), (116, true), (125, true), (77, true)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c1014, c856] c2234 (by decide) p (sat_cons (step1014 p h) (sat_cons (step856 p h) (sat_nil p)))
def c2235 : List Lit := [(114, false), (125, true), (77, true), (115, true)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c1014, c857] c2235 (by decide) p (sat_cons (step1014 p h) (sat_cons (step857 p h) (sat_nil p)))
def c2236 : List Lit := [(114, false), (116, true), (77, true), (115, true)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c1014, c858] c2236 (by decide) p (sat_cons (step1014 p h) (sat_cons (step858 p h) (sat_nil p)))
def c2237 : List Lit := [(116, true), (117, false), (79, true), (115, true)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c1015, c879] c2237 (by decide) p (sat_cons (step1015 p h) (sat_cons (step879 p h) (sat_nil p)))
def c2238 : List Lit := [(119, false), (120, true), (118, true), (123, true)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c1016, c888] c2238 (by decide) p (sat_cons (step1016 p h) (sat_cons (step888 p h) (sat_nil p)))
def c2239 : List Lit := [(119, false), (110, true), (118, true), (123, true)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c1016, c889] c2239 (by decide) p (sat_cons (step1016 p h) (sat_cons (step889 p h) (sat_nil p)))
def c2240 : List Lit := [(119, false), (110, true), (118, true), (120, true)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c1016, c890] c2240 (by decide) p (sat_cons (step1016 p h) (sat_cons (step890 p h) (sat_nil p)))
def c2241 : List Lit := [(122, false), (127, true), (85, true), (52, true), (121, true)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c1017, c914] c2241 (by decide) p (sat_cons (step1017 p h) (sat_cons (step914 p h) (sat_nil p)))
def c2242 : List Lit := [(124, false), (120, true), (123, true), (127, true)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c1018, c925] c2242 (by decide) p (sat_cons (step1018 p h) (sat_cons (step925 p h) (sat_nil p)))
def c2243 : List Lit := [(124, false), (127, true), (89, true), (123, true)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c1018, c926] c2243 (by decide) p (sat_cons (step1018 p h) (sat_cons (step926 p h) (sat_nil p)))
def c2244 : List Lit := [(124, false), (120, true), (127, true), (89, true)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c1018, c927] c2244 (by decide) p (sat_cons (step1018 p h) (sat_cons (step927 p h) (sat_nil p)))
def c2245 : List Lit := [(130, false), (131, false)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c1996, c1022] c2245 (by decide) p (sat_cons (step1996 p h) (sat_cons (step1022 p h) (sat_nil p)))
def c2246 : List Lit := [(275, false), (277, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c1990, c1037] c2246 (by decide) p (sat_cons (step1990 p h) (sat_cons (step1037 p h) (sat_nil p)))
def c2247 : List Lit := [(273, false), (279, false)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c1974, c1041] c2247 (by decide) p (sat_cons (step1974 p h) (sat_cons (step1041 p h) (sat_nil p)))
def c2248 : List Lit := [(267, false), (281, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c1959, c1045] c2248 (by decide) p (sat_cons (step1959 p h) (sat_cons (step1045 p h) (sat_nil p)))
def c2249 : List Lit := [(285, false), (287, false)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c1989, c1051] c2249 (by decide) p (sat_cons (step1989 p h) (sat_cons (step1051 p h) (sat_nil p)))
def c2250 : List Lit := [(289, false), (295, false)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c1973, c1059] c2250 (by decide) p (sat_cons (step1973 p h) (sat_cons (step1059 p h) (sat_nil p)))
def c2251 : List Lit := [(299, false), (301, false)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c1988, c1065] c2251 (by decide) p (sat_cons (step1988 p h) (sat_cons (step1065 p h) (sat_nil p)))
def c2252 : List Lit := [(303, false), (309, false)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c1972, c1072] c2252 (by decide) p (sat_cons (step1972 p h) (sat_cons (step1072 p h) (sat_nil p)))
def c2253 : List Lit := [(297, false), (311, false)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c1958, c1077] c2253 (by decide) p (sat_cons (step1958 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c2254 : List Lit := [(283, false), (313, false)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c1951, c1082] c2254 (by decide) p (sat_cons (step1951 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c2255 : List Lit := [(321, false), (327, false)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c1971, c1094] c2255 (by decide) p (sat_cons (step1971 p h) (sat_cons (step1094 p h) (sat_nil p)))
def c2256 : List Lit := [(335, false), (341, false)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c1970, c1103] c2256 (by decide) p (sat_cons (step1970 p h) (sat_cons (step1103 p h) (sat_nil p)))
def c2257 : List Lit := [(329, false), (343, false)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c1957, c1107] c2257 (by decide) p (sat_cons (step1957 p h) (sat_cons (step1107 p h) (sat_nil p)))
def c2258 : List Lit := [(180, false), (181, false)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c1995, c1113] c2258 (by decide) p (sat_cons (step1995 p h) (sat_cons (step1113 p h) (sat_nil p)))
def c2259 : List Lit := [(353, false), (355, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c1987, c1117] c2259 (by decide) p (sat_cons (step1987 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c2260 : List Lit := [(361, false), (363, false)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c1986, c1126] c2260 (by decide) p (sat_cons (step1986 p h) (sat_cons (step1126 p h) (sat_nil p)))
def c2261 : List Lit := [(365, false), (371, false)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c1968, c1131] c2261 (by decide) p (sat_cons (step1968 p h) (sat_cons (step1131 p h) (sat_nil p)))
end B112E055
