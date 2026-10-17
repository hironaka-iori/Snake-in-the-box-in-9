import B112E057Part0004
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2345 : List Lit := [(102, true), (84, true), (103, false)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c1018, c850] c2345 (by decide) p (sat_cons (step1018 p h) (sat_cons (step850 p h) (sat_nil p)))
def c2346 : List Lit := [(108, true), (104, true), (105, false)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c1019, c856] c2346 (by decide) p (sat_cons (step1019 p h) (sat_cons (step856 p h) (sat_nil p)))
def c2347 : List Lit := [(108, true), (105, false), (88, true)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c1019, c857] c2347 (by decide) p (sat_cons (step1019 p h) (sat_cons (step857 p h) (sat_nil p)))
def c2348 : List Lit := [(104, true), (105, false), (88, true)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c1019, c858] c2348 (by decide) p (sat_cons (step1019 p h) (sat_cons (step858 p h) (sat_nil p)))
def c2349 : List Lit := [(106, true), (108, true), (107, false), (37, true), (102, true)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c1020, c865] c2349 (by decide) p (sat_cons (step1020 p h) (sat_cons (step865 p h) (sat_nil p)))
def c2350 : List Lit := [(117, true), (109, false), (111, true)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c1021, c875] c2350 (by decide) p (sat_cons (step1021 p h) (sat_cons (step875 p h) (sat_nil p)))
def c2351 : List Lit := [(117, true), (110, true), (109, false)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c1021, c876] c2351 (by decide) p (sat_cons (step1021 p h) (sat_cons (step876 p h) (sat_nil p)))
def c2352 : List Lit := [(110, true), (109, false), (111, true)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c1021, c877] c2352 (by decide) p (sat_cons (step1021 p h) (sat_cons (step877 p h) (sat_nil p)))
def c2353 : List Lit := [(115, true), (110, true), (112, false), (70, true)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c1022, c888] c2353 (by decide) p (sat_cons (step1022 p h) (sat_cons (step888 p h) (sat_nil p)))
def c2354 : List Lit := [(110, true), (115, true), (112, false), (40, true)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c1022, c889] c2354 (by decide) p (sat_cons (step1022 p h) (sat_cons (step889 p h) (sat_nil p)))
def c2355 : List Lit := [(40, true), (115, true), (70, true), (112, false)]
theorem step2355 (p : Nat → Bool) (h : Constraints p) : clause p c2355 = true :=
  Snake9.LocalRup.prove_clause [c1022, c890] c2355 (by decide) p (sat_cons (step1022 p h) (sat_cons (step890 p h) (sat_nil p)))
def c2356 : List Lit := [(110, true), (40, true), (70, true), (112, false)]
theorem step2356 (p : Nat → Bool) (h : Constraints p) : clause p c2356 = true :=
  Snake9.LocalRup.prove_clause [c1022, c891] c2356 (by decide) p (sat_cons (step1022 p h) (sat_cons (step891 p h) (sat_nil p)))
def c2357 : List Lit := [(111, true), (116, true), (113, false)]
theorem step2357 (p : Nat → Bool) (h : Constraints p) : clause p c2357 = true :=
  Snake9.LocalRup.prove_clause [c1023, c893] c2357 (by decide) p (sat_cons (step1023 p h) (sat_cons (step893 p h) (sat_nil p)))
def c2358 : List Lit := [(116, true), (113, false), (45, true)]
theorem step2358 (p : Nat → Bool) (h : Constraints p) : clause p c2358 = true :=
  Snake9.LocalRup.prove_clause [c1023, c894] c2358 (by decide) p (sat_cons (step1023 p h) (sat_cons (step894 p h) (sat_nil p)))
def c2359 : List Lit := [(111, true), (113, false), (45, true)]
theorem step2359 (p : Nat → Bool) (h : Constraints p) : clause p c2359 = true :=
  Snake9.LocalRup.prove_clause [c1023, c895] c2359 (by decide) p (sat_cons (step1023 p h) (sat_cons (step895 p h) (sat_nil p)))
def c2360 : List Lit := [(124, true), (116, true), (76, true), (114, false)]
theorem step2360 (p : Nat → Bool) (h : Constraints p) : clause p c2360 = true :=
  Snake9.LocalRup.prove_clause [c1024, c899] c2360 (by decide) p (sat_cons (step1024 p h) (sat_cons (step899 p h) (sat_nil p)))
def c2361 : List Lit := [(124, true), (115, true), (114, false), (76, true)]
theorem step2361 (p : Nat → Bool) (h : Constraints p) : clause p c2361 = true :=
  Snake9.LocalRup.prove_clause [c1024, c900] c2361 (by decide) p (sat_cons (step1024 p h) (sat_cons (step900 p h) (sat_nil p)))
def c2362 : List Lit := [(115, true), (116, true), (76, true), (114, false)]
theorem step2362 (p : Nat → Bool) (h : Constraints p) : clause p c2362 = true :=
  Snake9.LocalRup.prove_clause [c1024, c901] c2362 (by decide) p (sat_cons (step1024 p h) (sat_cons (step901 p h) (sat_nil p)))
def c2363 : List Lit := [(117, true), (122, true), (118, false), (119, true)]
theorem step2363 (p : Nat → Bool) (h : Constraints p) : clause p c2363 = true :=
  Snake9.LocalRup.prove_clause [c1025, c918] c2363 (by decide) p (sat_cons (step1025 p h) (sat_cons (step918 p h) (sat_nil p)))
def c2364 : List Lit := [(110, true), (122, true), (119, true), (118, false)]
theorem step2364 (p : Nat → Bool) (h : Constraints p) : clause p c2364 = true :=
  Snake9.LocalRup.prove_clause [c1025, c919] c2364 (by decide) p (sat_cons (step1025 p h) (sat_cons (step919 p h) (sat_nil p)))
def c2365 : List Lit := [(110, true), (122, true), (117, true), (118, false)]
theorem step2365 (p : Nat → Bool) (h : Constraints p) : clause p c2365 = true :=
  Snake9.LocalRup.prove_clause [c1025, c920] c2365 (by decide) p (sat_cons (step1025 p h) (sat_cons (step920 p h) (sat_nil p)))
def c2366 : List Lit := [(110, true), (117, true), (118, false), (119, true)]
theorem step2366 (p : Nat → Bool) (h : Constraints p) : clause p c2366 = true :=
  Snake9.LocalRup.prove_clause [c1025, c921] c2366 (by decide) p (sat_cons (step1025 p h) (sat_cons (step921 p h) (sat_nil p)))
def c2367 : List Lit := [(120, true), (84, true), (119, true), (121, false), (126, true)]
theorem step2367 (p : Nat → Bool) (h : Constraints p) : clause p c2367 = true :=
  Snake9.LocalRup.prove_clause [c1026, c930] c2367 (by decide) p (sat_cons (step1026 p h) (sat_cons (step930 p h) (sat_nil p)))
def c2368 : List Lit := [(120, true), (119, true), (121, false), (52, true), (126, true)]
theorem step2368 (p : Nat → Bool) (h : Constraints p) : clause p c2368 = true :=
  Snake9.LocalRup.prove_clause [c1026, c931] c2368 (by decide) p (sat_cons (step1026 p h) (sat_cons (step931 p h) (sat_nil p)))
def c2369 : List Lit := [(120, true), (126, true), (84, true), (121, false), (52, true)]
theorem step2369 (p : Nat → Bool) (h : Constraints p) : clause p c2369 = true :=
  Snake9.LocalRup.prove_clause [c1026, c932] c2369 (by decide) p (sat_cons (step1026 p h) (sat_cons (step932 p h) (sat_nil p)))
def c2370 : List Lit := [(84, true), (126, true), (52, true), (121, false), (119, true)]
theorem step2370 (p : Nat → Bool) (h : Constraints p) : clause p c2370 = true :=
  Snake9.LocalRup.prove_clause [c1026, c933] c2370 (by decide) p (sat_cons (step1026 p h) (sat_cons (step933 p h) (sat_nil p)))
def c2371 : List Lit := [(120, true), (119, true), (84, true), (121, false), (52, true)]
theorem step2371 (p : Nat → Bool) (h : Constraints p) : clause p c2371 = true :=
  Snake9.LocalRup.prove_clause [c1026, c934] c2371 (by decide) p (sat_cons (step1026 p h) (sat_cons (step934 p h) (sat_nil p)))
def c2372 : List Lit := [(126, true), (122, true), (123, false), (119, true)]
theorem step2372 (p : Nat → Bool) (h : Constraints p) : clause p c2372 = true :=
  Snake9.LocalRup.prove_clause [c1027, c945] c2372 (by decide) p (sat_cons (step1027 p h) (sat_cons (step945 p h) (sat_nil p)))
def c2373 : List Lit := [(126, true), (122, true), (88, true), (123, false)]
theorem step2373 (p : Nat → Bool) (h : Constraints p) : clause p c2373 = true :=
  Snake9.LocalRup.prove_clause [c1027, c946] c2373 (by decide) p (sat_cons (step1027 p h) (sat_cons (step946 p h) (sat_nil p)))
def c2374 : List Lit := [(126, true), (119, true), (123, false), (88, true)]
theorem step2374 (p : Nat → Bool) (h : Constraints p) : clause p c2374 = true :=
  Snake9.LocalRup.prove_clause [c1027, c947] c2374 (by decide) p (sat_cons (step1027 p h) (sat_cons (step947 p h) (sat_nil p)))
def c2375 : List Lit := [(119, true), (122, true), (88, true), (123, false)]
theorem step2375 (p : Nat → Bool) (h : Constraints p) : clause p c2375 = true :=
  Snake9.LocalRup.prove_clause [c1027, c948] c2375 (by decide) p (sat_cons (step1027 p h) (sat_cons (step948 p h) (sat_nil p)))
def c2376 : List Lit := [(120, true), (124, true), (126, true), (125, false), (116, true)]
theorem step2376 (p : Nat → Bool) (h : Constraints p) : clause p c2376 = true :=
  Snake9.LocalRup.prove_clause [c1028, c956] c2376 (by decide) p (sat_cons (step1028 p h) (sat_cons (step956 p h) (sat_nil p)))
def c2377 : List Lit := [(124, true), (120, true), (55, true), (126, true), (125, false)]
theorem step2377 (p : Nat → Bool) (h : Constraints p) : clause p c2377 = true :=
  Snake9.LocalRup.prove_clause [c1028, c957] c2377 (by decide) p (sat_cons (step1028 p h) (sat_cons (step957 p h) (sat_nil p)))
def c2378 : List Lit := [(265, false), (279, false)]
theorem step2378 (p : Nat → Bool) (h : Constraints p) : clause p c2378 = true :=
  Snake9.LocalRup.prove_clause [c2042, c1044] c2378 (by decide) p (sat_cons (step2042 p h) (sat_cons (step1044 p h) (sat_nil p)))
def c2379 : List Lit := [(283, false), (285, false)]
theorem step2379 (p : Nat → Bool) (h : Constraints p) : clause p c2379 = true :=
  Snake9.LocalRup.prove_clause [c2059, c1049] c2379 (by decide) p (sat_cons (step2059 p h) (sat_cons (step1049 p h) (sat_nil p)))
def c2380 : List Lit := [(295, false), (309, false)]
theorem step2380 (p : Nat → Bool) (h : Constraints p) : clause p c2380 = true :=
  Snake9.LocalRup.prove_clause [c2041, c1070] c2380 (by decide) p (sat_cons (step2041 p h) (sat_cons (step1070 p h) (sat_nil p)))
def c2381 : List Lit := [(281, false), (311, false)]
theorem step2381 (p : Nat → Bool) (h : Constraints p) : clause p c2381 = true :=
  Snake9.LocalRup.prove_clause [c2034, c1075] c2381 (by decide) p (sat_cons (step2034 p h) (sat_cons (step1075 p h) (sat_nil p)))
def c2382 : List Lit := [(333, false), (339, false)]
theorem step2382 (p : Nat → Bool) (h : Constraints p) : clause p c2382 = true :=
  Snake9.LocalRup.prove_clause [c2052, c1095] c2382 (by decide) p (sat_cons (step2052 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c2383 : List Lit := [(327, false), (341, false)]
theorem step2383 (p : Nat → Bool) (h : Constraints p) : clause p c2383 = true :=
  Snake9.LocalRup.prove_clause [c2040, c1099] c2383 (by decide) p (sat_cons (step2040 p h) (sat_cons (step1099 p h) (sat_nil p)))
def c2384 : List Lit := [(349, false), (355, false)]
theorem step2384 (p : Nat → Bool) (h : Constraints p) : clause p c2384 = true :=
  Snake9.LocalRup.prove_clause [c2051, c1109] c2384 (by decide) p (sat_cons (step2051 p h) (sat_cons (step1109 p h) (sat_nil p)))
def c2385 : List Lit := [(189, false), (190, false)]
theorem step2385 (p : Nat → Bool) (h : Constraints p) : clause p c2385 = true :=
  Snake9.LocalRup.prove_clause [c2061, c1116] c2385 (by decide) p (sat_cons (step2061 p h) (sat_cons (step1116 p h) (sat_nil p)))
def c2386 : List Lit := [(363, false), (369, false)]
theorem step2386 (p : Nat → Bool) (h : Constraints p) : clause p c2386 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1122] c2386 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1122 p h) (sat_nil p)))
def c2387 : List Lit := [(357, false), (371, false)]
theorem step2387 (p : Nat → Bool) (h : Constraints p) : clause p c2387 = true :=
  Snake9.LocalRup.prove_clause [c2039, c1126] c2387 (by decide) p (sat_cons (step2039 p h) (sat_cons (step1126 p h) (sat_nil p)))
def c2388 : List Lit := [(343, false), (373, false)]
theorem step2388 (p : Nat → Bool) (h : Constraints p) : clause p c2388 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1131] c2388 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1131 p h) (sat_nil p)))
def c2389 : List Lit := [(313, false), (375, false)]
theorem step2389 (p : Nat → Bool) (h : Constraints p) : clause p c2389 = true :=
  Snake9.LocalRup.prove_clause [c2030, c1136] c2389 (by decide) p (sat_cons (step2030 p h) (sat_cons (step1136 p h) (sat_nil p)))
def c2390 : List Lit := [(381, false), (387, false)]
theorem step2390 (p : Nat → Bool) (h : Constraints p) : clause p c2390 = true :=
  Snake9.LocalRup.prove_clause [c2049, c1144] c2390 (by decide) p (sat_cons (step2049 p h) (sat_cons (step1144 p h) (sat_nil p)))
def c2391 : List Lit := [(391, false), (393, false)]
theorem step2391 (p : Nat → Bool) (h : Constraints p) : clause p c2391 = true :=
  Snake9.LocalRup.prove_clause [c2057, c1149] c2391 (by decide) p (sat_cons (step2057 p h) (sat_cons (step1149 p h) (sat_nil p)))
def c2392 : List Lit := [(395, false), (401, false)]
theorem step2392 (p : Nat → Bool) (h : Constraints p) : clause p c2392 = true :=
  Snake9.LocalRup.prove_clause [c2048, c1154] c2392 (by decide) p (sat_cons (step2048 p h) (sat_cons (step1154 p h) (sat_nil p)))
def c2393 : List Lit := [(389, false), (403, false)]
theorem step2393 (p : Nat → Bool) (h : Constraints p) : clause p c2393 = true :=
  Snake9.LocalRup.prove_clause [c2038, c1159] c2393 (by decide) p (sat_cons (step2038 p h) (sat_cons (step1159 p h) (sat_nil p)))
def c2394 : List Lit := [(407, false), (409, false)]
theorem step2394 (p : Nat → Bool) (h : Constraints p) : clause p c2394 = true :=
  Snake9.LocalRup.prove_clause [c2056, c1165] c2394 (by decide) p (sat_cons (step2056 p h) (sat_cons (step1165 p h) (sat_nil p)))
def c2395 : List Lit := [(411, false), (417, false)]
theorem step2395 (p : Nat → Bool) (h : Constraints p) : clause p c2395 = true :=
  Snake9.LocalRup.prove_clause [c2047, c1172] c2395 (by decide) p (sat_cons (step2047 p h) (sat_cons (step1172 p h) (sat_nil p)))
def c2396 : List Lit := [(419, false), (433, false)]
theorem step2396 (p : Nat → Bool) (h : Constraints p) : clause p c2396 = true :=
  Snake9.LocalRup.prove_clause [c2037, c1184] c2396 (by decide) p (sat_cons (step2037 p h) (sat_cons (step1184 p h) (sat_nil p)))
def c2397 : List Lit := [(405, false), (435, false)]
theorem step2397 (p : Nat → Bool) (h : Constraints p) : clause p c2397 = true :=
  Snake9.LocalRup.prove_clause [c2032, c1189] c2397 (by decide) p (sat_cons (step2032 p h) (sat_cons (step1189 p h) (sat_nil p)))
def c2398 : List Lit := [(445, false), (447, false)]
theorem step2398 (p : Nat → Bool) (h : Constraints p) : clause p c2398 = true :=
  Snake9.LocalRup.prove_clause [c2055, c1198] c2398 (by decide) p (sat_cons (step2055 p h) (sat_cons (step1198 p h) (sat_nil p)))
def c2399 : List Lit := [(443, false), (449, false)]
theorem step2399 (p : Nat → Bool) (h : Constraints p) : clause p c2399 = true :=
  Snake9.LocalRup.prove_clause [c2046, c1202] c2399 (by decide) p (sat_cons (step2046 p h) (sat_cons (step1202 p h) (sat_nil p)))
def c2400 : List Lit := [(457, false), (463, false)]
theorem step2400 (p : Nat → Bool) (h : Constraints p) : clause p c2400 = true :=
  Snake9.LocalRup.prove_clause [c2045, c1213] c2400 (by decide) p (sat_cons (step2045 p h) (sat_cons (step1213 p h) (sat_nil p)))
def c2401 : List Lit := [(451, false), (465, false)]
theorem step2401 (p : Nat → Bool) (h : Constraints p) : clause p c2401 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1217] c2401 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1217 p h) (sat_nil p)))
def c2402 : List Lit := [(242, false), (243, false)]
theorem step2402 (p : Nat → Bool) (h : Constraints p) : clause p c2402 = true :=
  Snake9.LocalRup.prove_clause [c2060, c1223] c2402 (by decide) p (sat_cons (step2060 p h) (sat_cons (step1223 p h) (sat_nil p)))
def c2403 : List Lit := [(473, false), (479, false)]
theorem step2403 (p : Nat → Bool) (h : Constraints p) : clause p c2403 = true :=
  Snake9.LocalRup.prove_clause [c2044, c1231] c2403 (by decide) p (sat_cons (step2044 p h) (sat_cons (step1231 p h) (sat_nil p)))
def c2404 : List Lit := [(487, false), (493, false)]
theorem step2404 (p : Nat → Bool) (h : Constraints p) : clause p c2404 = true :=
  Snake9.LocalRup.prove_clause [c2043, c1243] c2404 (by decide) p (sat_cons (step2043 p h) (sat_cons (step1243 p h) (sat_nil p)))
def c2405 : List Lit := [(481, false), (495, false)]
theorem step2405 (p : Nat → Bool) (h : Constraints p) : clause p c2405 = true :=
  Snake9.LocalRup.prove_clause [c2035, c1247] c2405 (by decide) p (sat_cons (step2035 p h) (sat_cons (step1247 p h) (sat_nil p)))
def c2406 : List Lit := [(467, false), (497, false)]
theorem step2406 (p : Nat → Bool) (h : Constraints p) : clause p c2406 = true :=
  Snake9.LocalRup.prove_clause [c2031, c1252] c2406 (by decide) p (sat_cons (step2031 p h) (sat_cons (step1252 p h) (sat_nil p)))
def c2407 : List Lit := [(437, false), (499, false)]
theorem step2407 (p : Nat → Bool) (h : Constraints p) : clause p c2407 = true :=
  Snake9.LocalRup.prove_clause [c2029, c1257] c2407 (by decide) p (sat_cons (step2029 p h) (sat_cons (step1257 p h) (sat_nil p)))
def c2408 : List Lit := [(377, false), (501, false)]
theorem step2408 (p : Nat → Bool) (h : Constraints p) : clause p c2408 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1260] c2408 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_nil p)))
end B112E057
