import B112E089Part0003
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2268 : List Lit := [(7, true), (95, true), (81, false), (205, true)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c2012, c2013, c769] c2268 (by decide) p (sat_cons (step2012 p h) (sat_cons (step2013 p h) (sat_cons (step769 p h) (sat_nil p))))
def c2269 : List Lit := [(86, true), (7, true), (81, false), (205, true)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c2012, c2013, c770] c2269 (by decide) p (sat_cons (step2012 p h) (sat_cons (step2013 p h) (sat_cons (step770 p h) (sat_nil p))))
def c2270 : List Lit := [(83, false), (85, true), (87, true)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c1010, c773] c2270 (by decide) p (sat_cons (step1010 p h) (sat_cons (step773 p h) (sat_nil p)))
def c2271 : List Lit := [(87, true), (83, false), (79, true)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c1010, c774] c2271 (by decide) p (sat_cons (step1010 p h) (sat_cons (step774 p h) (sat_nil p)))
def c2272 : List Lit := [(83, false), (85, true), (79, true)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c1010, c775] c2272 (by decide) p (sat_cons (step1010 p h) (sat_cons (step775 p h) (sat_nil p)))
def c2273 : List Lit := [(84, false), (89, true)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c1011, c776] c2273 (by decide) p (sat_cons (step1011 p h) (sat_cons (step776 p h) (sat_nil p)))
def c2274 : List Lit := [(84, false), (85, true)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c1011, c777] c2274 (by decide) p (sat_cons (step1011 p h) (sat_cons (step777 p h) (sat_nil p)))
def c2275 : List Lit := [(86, false), (87, true)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c1012, c780] c2275 (by decide) p (sat_cons (step1012 p h) (sat_cons (step780 p h) (sat_nil p)))
def c2276 : List Lit := [(86, false), (81, true)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c1012, c781] c2276 (by decide) p (sat_cons (step1012 p h) (sat_cons (step781 p h) (sat_nil p)))
def c2277 : List Lit := [(25, true), (89, true)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c786, c784] c2277 (by decide) p (sat_cons (step786 p h) (sat_cons (step784 p h) (sat_nil p)))
def c2278 : List Lit := [(25, false), (89, false)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c787, c785] c2278 (by decide) p (sat_cons (step787 p h) (sat_cons (step785 p h) (sat_nil p)))
def c2279 : List Lit := [(90, false), (107, true), (91, true)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c1013, c790] c2279 (by decide) p (sat_cons (step1013 p h) (sat_cons (step790 p h) (sat_nil p)))
def c2280 : List Lit := [(79, true), (96, true), (102, true), (91, true), (92, false)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c1014, c810] c2280 (by decide) p (sat_cons (step1014 p h) (sat_cons (step810 p h) (sat_nil p)))
def c2281 : List Lit := [(93, false), (98, true)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c1015, c811] c2281 (by decide) p (sat_cons (step1015 p h) (sat_cons (step811 p h) (sat_nil p)))
def c2282 : List Lit := [(93, false), (94, true)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c1015, c812] c2282 (by decide) p (sat_cons (step1015 p h) (sat_cons (step812 p h) (sat_nil p)))
def c2283 : List Lit := [(96, true), (81, true), (91, true), (95, false)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c1016, c822] c2283 (by decide) p (sat_cons (step1016 p h) (sat_cons (step822 p h) (sat_nil p)))
def c2284 : List Lit := [(95, false), (42, true), (91, true), (96, true)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c1016, c823] c2284 (by decide) p (sat_cons (step1016 p h) (sat_cons (step823 p h) (sat_nil p)))
def c2285 : List Lit := [(95, false), (81, true), (42, true), (91, true)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1016, c824] c2285 (by decide) p (sat_cons (step1016 p h) (sat_cons (step824 p h) (sat_nil p)))
def c2286 : List Lit := [(97, false), (104, true), (44, true)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c1017, c832] c2286 (by decide) p (sat_cons (step1017 p h) (sat_cons (step832 p h) (sat_nil p)))
def c2287 : List Lit := [(100, false), (46, true), (102, true)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c1018, c843] c2287 (by decide) p (sat_cons (step1018 p h) (sat_cons (step843 p h) (sat_nil p)))
def c2288 : List Lit := [(99, true), (100, false), (46, true)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c1018, c844] c2288 (by decide) p (sat_cons (step1018 p h) (sat_cons (step844 p h) (sat_nil p)))
def c2289 : List Lit := [(101, false), (103, true), (102, true), (91, true)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1019, c849] c2289 (by decide) p (sat_cons (step1019 p h) (sat_cons (step849 p h) (sat_nil p)))
def c2290 : List Lit := [(99, true), (101, false), (91, true), (102, true)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c1019, c850] c2290 (by decide) p (sat_cons (step1019 p h) (sat_cons (step850 p h) (sat_nil p)))
def c2291 : List Lit := [(105, false), (123, true), (104, true)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c1020, c868] c2291 (by decide) p (sat_cons (step1020 p h) (sat_cons (step868 p h) (sat_nil p)))
def c2292 : List Lit := [(106, false), (104, true)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c1021, c869] c2292 (by decide) p (sat_cons (step1021 p h) (sat_cons (step869 p h) (sat_nil p)))
def c2293 : List Lit := [(106, false), (103, true)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c1021, c870] c2293 (by decide) p (sat_cons (step1021 p h) (sat_cons (step870 p h) (sat_nil p)))
def c2294 : List Lit := [(108, false), (56, true), (107, true)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1022, c878] c2294 (by decide) p (sat_cons (step1022 p h) (sat_cons (step878 p h) (sat_nil p)))
def c2295 : List Lit := [(109, false), (107, true), (91, true), (57, true)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c1023, c883] c2295 (by decide) p (sat_cons (step1023 p h) (sat_cons (step883 p h) (sat_nil p)))
def c2296 : List Lit := [(110, false), (107, true), (117, true)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c1024, c885] c2296 (by decide) p (sat_cons (step1024 p h) (sat_cons (step885 p h) (sat_nil p)))
def c2297 : List Lit := [(110, false), (111, true), (107, true)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1024, c886] c2297 (by decide) p (sat_cons (step1024 p h) (sat_cons (step886 p h) (sat_nil p)))
def c2298 : List Lit := [(113, true), (107, true), (120, true), (112, false)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c1025, c898] c2298 (by decide) p (sat_cons (step1025 p h) (sat_cons (step898 p h) (sat_nil p)))
def c2299 : List Lit := [(112, false), (113, true), (62, true), (120, true)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c1025, c899] c2299 (by decide) p (sat_cons (step1025 p h) (sat_cons (step899 p h) (sat_nil p)))
def c2300 : List Lit := [(112, false), (107, true), (62, true), (120, true)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c1025, c900] c2300 (by decide) p (sat_cons (step1025 p h) (sat_cons (step900 p h) (sat_nil p)))
def c2301 : List Lit := [(113, true), (107, true), (62, true), (112, false)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c1025, c901] c2301 (by decide) p (sat_cons (step1025 p h) (sat_cons (step901 p h) (sat_nil p)))
def c2302 : List Lit := [(111, true), (114, false), (115, true)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1026, c908] c2302 (by decide) p (sat_cons (step1026 p h) (sat_cons (step908 p h) (sat_nil p)))
def c2303 : List Lit := [(114, false), (115, true), (67, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c1026, c909] c2303 (by decide) p (sat_cons (step1026 p h) (sat_cons (step909 p h) (sat_nil p)))
def c2304 : List Lit := [(111, true), (114, false), (67, true)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1026, c910] c2304 (by decide) p (sat_cons (step1026 p h) (sat_cons (step910 p h) (sat_nil p)))
def c2305 : List Lit := [(116, false), (119, true), (72, true), (122, true)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c1027, c922] c2305 (by decide) p (sat_cons (step1027 p h) (sat_cons (step922 p h) (sat_nil p)))
def c2306 : List Lit := [(119, true), (116, false), (72, true), (102, true)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c1027, c923] c2306 (by decide) p (sat_cons (step1027 p h) (sat_cons (step923 p h) (sat_nil p)))
def c2307 : List Lit := [(118, false), (119, true), (123, true)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c1028, c929] c2307 (by decide) p (sat_cons (step1028 p h) (sat_cons (step929 p h) (sat_nil p)))
def c2308 : List Lit := [(118, false), (123, true), (117, true)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1028, c930] c2308 (by decide) p (sat_cons (step1028 p h) (sat_cons (step930 p h) (sat_nil p)))
def c2309 : List Lit := [(119, true), (118, false), (117, true)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c1028, c931] c2309 (by decide) p (sat_cons (step1028 p h) (sat_cons (step931 p h) (sat_nil p)))
def c2310 : List Lit := [(122, true), (120, true), (121, false)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c1029, c949] c2310 (by decide) p (sat_cons (step1029 p h) (sat_cons (step949 p h) (sat_nil p)))
def c2311 : List Lit := [(122, true), (121, false), (75, true)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c1029, c950] c2311 (by decide) p (sat_cons (step1029 p h) (sat_cons (step950 p h) (sat_nil p)))
def c2312 : List Lit := [(121, false), (75, true), (120, true)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c1029, c951] c2312 (by decide) p (sat_cons (step1029 p h) (sat_cons (step951 p h) (sat_nil p)))
def c2313 : List Lit := [(124, false), (119, true), (123, true), (115, true)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c1030, c969] c2313 (by decide) p (sat_cons (step1030 p h) (sat_cons (step969 p h) (sat_nil p)))
def c2314 : List Lit := [(132, false), (133, false)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c2065, c1039] c2314 (by decide) p (sat_cons (step2065 p h) (sat_cons (step1039 p h) (sat_nil p)))
def c2315 : List Lit := [(134, false), (135, false)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c2064, c1042] c2315 (by decide) p (sat_cons (step2064 p h) (sat_cons (step1042 p h) (sat_nil p)))
def c2316 : List Lit := [(261, false), (263, false)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c2058, c1046] c2316 (by decide) p (sat_cons (step2058 p h) (sat_cons (step1046 p h) (sat_nil p)))
def c2317 : List Lit := [(138, false), (139, false)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c2063, c1051] c2317 (by decide) p (sat_cons (step2063 p h) (sat_cons (step1051 p h) (sat_nil p)))
def c2318 : List Lit := [(267, false), (269, false)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c2057, c1055] c2318 (by decide) p (sat_cons (step2057 p h) (sat_cons (step1055 p h) (sat_nil p)))
def c2319 : List Lit := [(265, false), (271, false)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c2040, c1059] c2319 (by decide) p (sat_cons (step2040 p h) (sat_cons (step1059 p h) (sat_nil p)))
def c2320 : List Lit := [(259, false), (273, false)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c2027, c1064] c2320 (by decide) p (sat_cons (step2027 p h) (sat_cons (step1064 p h) (sat_nil p)))
def c2321 : List Lit := [(295, false), (297, false)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c2056, c1079] c2321 (by decide) p (sat_cons (step2056 p h) (sat_cons (step1079 p h) (sat_nil p)))
def c2322 : List Lit := [(293, false), (299, false)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c2039, c1083] c2322 (by decide) p (sat_cons (step2039 p h) (sat_cons (step1083 p h) (sat_nil p)))
def c2323 : List Lit := [(287, false), (301, false)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c2026, c1087] c2323 (by decide) p (sat_cons (step2026 p h) (sat_cons (step1087 p h) (sat_nil p)))
def c2324 : List Lit := [(275, false), (303, false)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c2019, c1091] c2324 (by decide) p (sat_cons (step2019 p h) (sat_cons (step1091 p h) (sat_nil p)))
def c2325 : List Lit := [(155, false), (307, false)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c2055, c1096] c2325 (by decide) p (sat_cons (step2055 p h) (sat_cons (step1096 p h) (sat_nil p)))
def c2326 : List Lit := [(309, false), (315, false)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c2038, c1101] c2326 (by decide) p (sat_cons (step2038 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c2327 : List Lit := [(319, false), (321, false)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c2054, c1107] c2327 (by decide) p (sat_cons (step2054 p h) (sat_cons (step1107 p h) (sat_nil p)))
def c2328 : List Lit := [(168, false), (169, false)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c2062, c1111] c2328 (by decide) p (sat_cons (step2062 p h) (sat_cons (step1111 p h) (sat_nil p)))
def c2329 : List Lit := [(325, false), (327, false)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c2053, c1115] c2329 (by decide) p (sat_cons (step2053 p h) (sat_cons (step1115 p h) (sat_nil p)))
def c2330 : List Lit := [(323, false), (329, false)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c2037, c1119] c2330 (by decide) p (sat_cons (step2037 p h) (sat_cons (step1119 p h) (sat_nil p)))
def c2331 : List Lit := [(317, false), (331, false)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c2025, c1124] c2331 (by decide) p (sat_cons (step2025 p h) (sat_cons (step1124 p h) (sat_nil p)))
end B112E089
