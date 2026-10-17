import B112E052Part0005
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2374 : List Lit := [(119, true), (120, false), (121, true)]
theorem step2374 (p : Nat → Bool) (h : Constraints p) : clause p c2374 = true :=
  Snake9.LocalRup.prove_clause [c1026, c903] c2374 (by decide) p (sat_cons (step1026 p h) (sat_cons (step903 p h) (sat_nil p)))
def c2375 : List Lit := [(121, true), (113, true), (101, true), (122, false), (79, true)]
theorem step2375 (p : Nat → Bool) (h : Constraints p) : clause p c2375 = true :=
  Snake9.LocalRup.prove_clause [c1027, c920] c2375 (by decide) p (sat_cons (step1027 p h) (sat_cons (step920 p h) (sat_nil p)))
def c2376 : List Lit := [(44, true), (121, true), (101, true), (122, false), (113, true)]
theorem step2376 (p : Nat → Bool) (h : Constraints p) : clause p c2376 = true :=
  Snake9.LocalRup.prove_clause [c1027, c921] c2376 (by decide) p (sat_cons (step1027 p h) (sat_cons (step921 p h) (sat_nil p)))
def c2377 : List Lit := [(121, true), (44, true), (79, true), (122, false), (113, true)]
theorem step2377 (p : Nat → Bool) (h : Constraints p) : clause p c2377 = true :=
  Snake9.LocalRup.prove_clause [c1027, c922] c2377 (by decide) p (sat_cons (step1027 p h) (sat_cons (step922 p h) (sat_nil p)))
def c2378 : List Lit := [(79, true), (44, true), (121, true), (101, true), (122, false)]
theorem step2378 (p : Nat → Bool) (h : Constraints p) : clause p c2378 = true :=
  Snake9.LocalRup.prove_clause [c1027, c923] c2378 (by decide) p (sat_cons (step1027 p h) (sat_cons (step923 p h) (sat_nil p)))
def c2379 : List Lit := [(44, true), (113, true), (79, true), (101, true), (122, false)]
theorem step2379 (p : Nat → Bool) (h : Constraints p) : clause p c2379 = true :=
  Snake9.LocalRup.prove_clause [c1027, c924] c2379 (by decide) p (sat_cons (step1027 p h) (sat_cons (step924 p h) (sat_nil p)))
def c2380 : List Lit := [(119, true), (124, true), (123, false), (125, true)]
theorem step2380 (p : Nat → Bool) (h : Constraints p) : clause p c2380 = true :=
  Snake9.LocalRup.prove_clause [c1028, c929] c2380 (by decide) p (sat_cons (step1028 p h) (sat_cons (step929 p h) (sat_nil p)))
def c2381 : List Lit := [(124, true), (80, true), (125, true), (123, false)]
theorem step2381 (p : Nat → Bool) (h : Constraints p) : clause p c2381 = true :=
  Snake9.LocalRup.prove_clause [c1028, c930] c2381 (by decide) p (sat_cons (step1028 p h) (sat_cons (step930 p h) (sat_nil p)))
def c2382 : List Lit := [(119, true), (80, true), (125, true), (123, false)]
theorem step2382 (p : Nat → Bool) (h : Constraints p) : clause p c2382 = true :=
  Snake9.LocalRup.prove_clause [c1028, c931] c2382 (by decide) p (sat_cons (step1028 p h) (sat_cons (step931 p h) (sat_nil p)))
def c2383 : List Lit := [(119, true), (124, true), (80, true), (123, false)]
theorem step2383 (p : Nat → Bool) (h : Constraints p) : clause p c2383 = true :=
  Snake9.LocalRup.prove_clause [c1028, c932] c2383 (by decide) p (sat_cons (step1028 p h) (sat_cons (step932 p h) (sat_nil p)))
def c2384 : List Lit := [(116, true), (105, true), (126, false), (125, true)]
theorem step2384 (p : Nat → Bool) (h : Constraints p) : clause p c2384 = true :=
  Snake9.LocalRup.prove_clause [c1029, c959] c2384 (by decide) p (sat_cons (step1029 p h) (sat_cons (step959 p h) (sat_nil p)))
def c2385 : List Lit := [(48, true), (116, true), (125, true), (126, false)]
theorem step2385 (p : Nat → Bool) (h : Constraints p) : clause p c2385 = true :=
  Snake9.LocalRup.prove_clause [c1029, c960] c2385 (by decide) p (sat_cons (step1029 p h) (sat_cons (step960 p h) (sat_nil p)))
def c2386 : List Lit := [(48, true), (105, true), (126, false), (125, true)]
theorem step2386 (p : Nat → Bool) (h : Constraints p) : clause p c2386 = true :=
  Snake9.LocalRup.prove_clause [c1029, c961] c2386 (by decide) p (sat_cons (step1029 p h) (sat_cons (step961 p h) (sat_nil p)))
def c2387 : List Lit := [(48, true), (116, true), (105, true), (126, false)]
theorem step2387 (p : Nat → Bool) (h : Constraints p) : clause p c2387 = true :=
  Snake9.LocalRup.prove_clause [c1029, c962] c2387 (by decide) p (sat_cons (step1029 p h) (sat_cons (step962 p h) (sat_nil p)))
def c2388 : List Lit := [(117, true), (124, true), (125, true), (127, false)]
theorem step2388 (p : Nat → Bool) (h : Constraints p) : clause p c2388 = true :=
  Snake9.LocalRup.prove_clause [c1030, c966] c2388 (by decide) p (sat_cons (step1030 p h) (sat_cons (step966 p h) (sat_nil p)))
def c2389 : List Lit := [(124, true), (125, true), (106, true), (127, false)]
theorem step2389 (p : Nat → Bool) (h : Constraints p) : clause p c2389 = true :=
  Snake9.LocalRup.prove_clause [c1030, c967] c2389 (by decide) p (sat_cons (step1030 p h) (sat_cons (step967 p h) (sat_nil p)))
def c2390 : List Lit := [(117, true), (125, true), (127, false), (106, true)]
theorem step2390 (p : Nat → Bool) (h : Constraints p) : clause p c2390 = true :=
  Snake9.LocalRup.prove_clause [c1030, c968] c2390 (by decide) p (sat_cons (step1030 p h) (sat_cons (step968 p h) (sat_nil p)))
def c2391 : List Lit := [(117, true), (124, true), (127, false), (106, true)]
theorem step2391 (p : Nat → Bool) (h : Constraints p) : clause p c2391 = true :=
  Snake9.LocalRup.prove_clause [c1030, c969] c2391 (by decide) p (sat_cons (step1030 p h) (sat_cons (step969 p h) (sat_nil p)))
def c2392 : List Lit := [(129, false), (255, false)]
theorem step2392 (p : Nat → Bool) (h : Constraints p) : clause p c2392 = true :=
  Snake9.LocalRup.prove_clause [c2027, c1034] c2392 (by decide) p (sat_cons (step2027 p h) (sat_cons (step1034 p h) (sat_nil p)))
def c2393 : List Lit := [(257, false), (263, false)]
theorem step2393 (p : Nat → Bool) (h : Constraints p) : clause p c2393 = true :=
  Snake9.LocalRup.prove_clause [c2022, c1039] c2393 (by decide) p (sat_cons (step2022 p h) (sat_cons (step1039 p h) (sat_nil p)))
def c2394 : List Lit := [(140, false), (141, false)]
theorem step2394 (p : Nat → Bool) (h : Constraints p) : clause p c2394 = true :=
  Snake9.LocalRup.prove_clause [c2028, c1045] c2394 (by decide) p (sat_cons (step2028 p h) (sat_cons (step1045 p h) (sat_nil p)))
def c2395 : List Lit := [(273, false), (275, false)]
theorem step2395 (p : Nat → Bool) (h : Constraints p) : clause p c2395 = true :=
  Snake9.LocalRup.prove_clause [c2026, c1049] c2395 (by decide) p (sat_cons (step2026 p h) (sat_cons (step1049 p h) (sat_nil p)))
def c2396 : List Lit := [(271, false), (277, false)]
theorem step2396 (p : Nat → Bool) (h : Constraints p) : clause p c2396 = true :=
  Snake9.LocalRup.prove_clause [c2021, c1054] c2396 (by decide) p (sat_cons (step2021 p h) (sat_cons (step1054 p h) (sat_nil p)))
def c2397 : List Lit := [(265, false), (279, false)]
theorem step2397 (p : Nat → Bool) (h : Constraints p) : clause p c2397 = true :=
  Snake9.LocalRup.prove_clause [c2011, c1058] c2397 (by decide) p (sat_cons (step2011 p h) (sat_cons (step1058 p h) (sat_nil p)))
def c2398 : List Lit := [(303, false), (305, false)]
theorem step2398 (p : Nat → Bool) (h : Constraints p) : clause p c2398 = true :=
  Snake9.LocalRup.prove_clause [c2025, c1074] c2398 (by decide) p (sat_cons (step2025 p h) (sat_cons (step1074 p h) (sat_nil p)))
def c2399 : List Lit := [(295, false), (309, false)]
theorem step2399 (p : Nat → Bool) (h : Constraints p) : clause p c2399 = true :=
  Snake9.LocalRup.prove_clause [c2010, c1080] c2399 (by decide) p (sat_cons (step2010 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c2400 : List Lit := [(281, false), (311, false)]
theorem step2400 (p : Nat → Bool) (h : Constraints p) : clause p c2400 = true :=
  Snake9.LocalRup.prove_clause [c2003, c1084] c2400 (by decide) p (sat_cons (step2003 p h) (sat_cons (step1084 p h) (sat_nil p)))
def c2401 : List Lit := [(319, false), (325, false)]
theorem step2401 (p : Nat → Bool) (h : Constraints p) : clause p c2401 = true :=
  Snake9.LocalRup.prove_clause [c2019, c1092] c2401 (by decide) p (sat_cons (step2019 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c2402 : List Lit := [(333, false), (339, false)]
theorem step2402 (p : Nat → Bool) (h : Constraints p) : clause p c2402 = true :=
  Snake9.LocalRup.prove_clause [c2018, c1101] c2402 (by decide) p (sat_cons (step2018 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c2403 : List Lit := [(327, false), (341, false)]
theorem step2403 (p : Nat → Bool) (h : Constraints p) : clause p c2403 = true :=
  Snake9.LocalRup.prove_clause [c2009, c1105] c2403 (by decide) p (sat_cons (step2009 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c2404 : List Lit := [(349, false), (355, false)]
theorem step2404 (p : Nat → Bool) (h : Constraints p) : clause p c2404 = true :=
  Snake9.LocalRup.prove_clause [c2017, c1114] c2404 (by decide) p (sat_cons (step2017 p h) (sat_cons (step1114 p h) (sat_nil p)))
def c2405 : List Lit := [(357, false), (371, false)]
theorem step2405 (p : Nat → Bool) (h : Constraints p) : clause p c2405 = true :=
  Snake9.LocalRup.prove_clause [c2008, c1128] c2405 (by decide) p (sat_cons (step2008 p h) (sat_cons (step1128 p h) (sat_nil p)))
def c2406 : List Lit := [(343, false), (373, false)]
theorem step2406 (p : Nat → Bool) (h : Constraints p) : clause p c2406 = true :=
  Snake9.LocalRup.prove_clause [c2002, c1133] c2406 (by decide) p (sat_cons (step2002 p h) (sat_cons (step1133 p h) (sat_nil p)))
def c2407 : List Lit := [(313, false), (375, false)]
theorem step2407 (p : Nat → Bool) (h : Constraints p) : clause p c2407 = true :=
  Snake9.LocalRup.prove_clause [c1999, c1138] c2407 (by decide) p (sat_cons (step1999 p h) (sat_cons (step1138 p h) (sat_nil p)))
def c2408 : List Lit := [(391, false), (393, false)]
theorem step2408 (p : Nat → Bool) (h : Constraints p) : clause p c2408 = true :=
  Snake9.LocalRup.prove_clause [c2024, c1151] c2408 (by decide) p (sat_cons (step2024 p h) (sat_cons (step1151 p h) (sat_nil p)))
def c2409 : List Lit := [(395, false), (401, false)]
theorem step2409 (p : Nat → Bool) (h : Constraints p) : clause p c2409 = true :=
  Snake9.LocalRup.prove_clause [c2016, c1156] c2409 (by decide) p (sat_cons (step2016 p h) (sat_cons (step1156 p h) (sat_nil p)))
def c2410 : List Lit := [(389, false), (403, false)]
theorem step2410 (p : Nat → Bool) (h : Constraints p) : clause p c2410 = true :=
  Snake9.LocalRup.prove_clause [c2007, c1161] c2410 (by decide) p (sat_cons (step2007 p h) (sat_cons (step1161 p h) (sat_nil p)))
def c2411 : List Lit := [(425, false), (431, false)]
theorem step2411 (p : Nat → Bool) (h : Constraints p) : clause p c2411 = true :=
  Snake9.LocalRup.prove_clause [c2015, c1176] c2411 (by decide) p (sat_cons (step2015 p h) (sat_cons (step1176 p h) (sat_nil p)))
def c2412 : List Lit := [(419, false), (433, false)]
theorem step2412 (p : Nat → Bool) (h : Constraints p) : clause p c2412 = true :=
  Snake9.LocalRup.prove_clause [c2006, c1180] c2412 (by decide) p (sat_cons (step2006 p h) (sat_cons (step1180 p h) (sat_nil p)))
def c2413 : List Lit := [(405, false), (435, false)]
theorem step2413 (p : Nat → Bool) (h : Constraints p) : clause p c2413 = true :=
  Snake9.LocalRup.prove_clause [c2001, c1184] c2413 (by decide) p (sat_cons (step2001 p h) (sat_cons (step1184 p h) (sat_nil p)))
def c2414 : List Lit := [(439, false), (441, false)]
theorem step2414 (p : Nat → Bool) (h : Constraints p) : clause p c2414 = true :=
  Snake9.LocalRup.prove_clause [c2023, c1190] c2414 (by decide) p (sat_cons (step2023 p h) (sat_cons (step1190 p h) (sat_nil p)))
def c2415 : List Lit := [(451, false), (465, false)]
theorem step2415 (p : Nat → Bool) (h : Constraints p) : clause p c2415 = true :=
  Snake9.LocalRup.prove_clause [c2005, c1209] c2415 (by decide) p (sat_cons (step2005 p h) (sat_cons (step1209 p h) (sat_nil p)))
def c2416 : List Lit := [(473, false), (479, false)]
theorem step2416 (p : Nat → Bool) (h : Constraints p) : clause p c2416 = true :=
  Snake9.LocalRup.prove_clause [c2013, c1220] c2416 (by decide) p (sat_cons (step2013 p h) (sat_cons (step1220 p h) (sat_nil p)))
def c2417 : List Lit := [(487, false), (493, false)]
theorem step2417 (p : Nat → Bool) (h : Constraints p) : clause p c2417 = true :=
  Snake9.LocalRup.prove_clause [c2012, c1227] c2417 (by decide) p (sat_cons (step2012 p h) (sat_cons (step1227 p h) (sat_nil p)))
def c2418 : List Lit := [(481, false), (495, false)]
theorem step2418 (p : Nat → Bool) (h : Constraints p) : clause p c2418 = true :=
  Snake9.LocalRup.prove_clause [c2004, c1231] c2418 (by decide) p (sat_cons (step2004 p h) (sat_cons (step1231 p h) (sat_nil p)))
def c2419 : List Lit := [(467, false), (497, false)]
theorem step2419 (p : Nat → Bool) (h : Constraints p) : clause p c2419 = true :=
  Snake9.LocalRup.prove_clause [c2000, c1236] c2419 (by decide) p (sat_cons (step2000 p h) (sat_cons (step1236 p h) (sat_nil p)))
def c2420 : List Lit := [(437, false), (499, false)]
theorem step2420 (p : Nat → Bool) (h : Constraints p) : clause p c2420 = true :=
  Snake9.LocalRup.prove_clause [c1998, c1241] c2420 (by decide) p (sat_cons (step1998 p h) (sat_cons (step1241 p h) (sat_nil p)))
def c2421 : List Lit := [(377, false), (501, false)]
theorem step2421 (p : Nat → Bool) (h : Constraints p) : clause p c2421 = true :=
  Snake9.LocalRup.prove_clause [c1246, c1244] c2421 (by decide) p (sat_cons (step1246 p h) (sat_cons (step1244 p h) (sat_nil p)))
def c2422 : List Lit := [(1571, false), (1584, true)]
theorem step2422 (p : Nat → Bool) (h : Constraints p) : clause p c2422 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1303] c2422 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1303 p h) (sat_nil p)))
def c2423 : List Lit := [(1572, false), (1585, true)]
theorem step2423 (p : Nat → Bool) (h : Constraints p) : clause p c2423 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1308] c2423 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1308 p h) (sat_nil p)))
def c2424 : List Lit := [(1573, false), (1586, true)]
theorem step2424 (p : Nat → Bool) (h : Constraints p) : clause p c2424 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1312] c2424 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1312 p h) (sat_nil p)))
def c2425 : List Lit := [(1574, false), (1587, true)]
theorem step2425 (p : Nat → Bool) (h : Constraints p) : clause p c2425 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1314] c2425 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1314 p h) (sat_nil p)))
def c2426 : List Lit := [(1562, false), (1595, true)]
theorem step2426 (p : Nat → Bool) (h : Constraints p) : clause p c2426 = true :=
  Snake9.LocalRup.prove_clause [c2069, c1323] c2426 (by decide) p (sat_cons (step2069 p h) (sat_cons (step1323 p h) (sat_nil p)))
def c2427 : List Lit := [(1596, true), (1563, false)]
theorem step2427 (p : Nat → Bool) (h : Constraints p) : clause p c2427 = true :=
  Snake9.LocalRup.prove_clause [c2069, c1328] c2427 (by decide) p (sat_cons (step2069 p h) (sat_cons (step1328 p h) (sat_nil p)))
def c2428 : List Lit := [(1597, true), (1564, false)]
theorem step2428 (p : Nat → Bool) (h : Constraints p) : clause p c2428 = true :=
  Snake9.LocalRup.prove_clause [c2069, c1333] c2428 (by decide) p (sat_cons (step2069 p h) (sat_cons (step1333 p h) (sat_nil p)))
def c2429 : List Lit := [(1598, true), (1565, false)]
theorem step2429 (p : Nat → Bool) (h : Constraints p) : clause p c2429 = true :=
  Snake9.LocalRup.prove_clause [c2069, c1339] c2429 (by decide) p (sat_cons (step2069 p h) (sat_cons (step1339 p h) (sat_nil p)))
def c2430 : List Lit := [(1647, false), (1656, true)]
theorem step2430 (p : Nat → Bool) (h : Constraints p) : clause p c2430 = true :=
  Snake9.LocalRup.prove_clause [c2066, c1437] c2430 (by decide) p (sat_cons (step2066 p h) (sat_cons (step1437 p h) (sat_nil p)))
def c2431 : List Lit := [(1648, false), (1657, true)]
theorem step2431 (p : Nat → Bool) (h : Constraints p) : clause p c2431 = true :=
  Snake9.LocalRup.prove_clause [c2066, c1438] c2431 (by decide) p (sat_cons (step2066 p h) (sat_cons (step1438 p h) (sat_nil p)))
def c2432 : List Lit := [(1649, false), (1658, true)]
theorem step2432 (p : Nat → Bool) (h : Constraints p) : clause p c2432 = true :=
  Snake9.LocalRup.prove_clause [c2066, c1439] c2432 (by decide) p (sat_cons (step2066 p h) (sat_cons (step1439 p h) (sat_nil p)))
def c2433 : List Lit := [(1650, false), (1659, true)]
theorem step2433 (p : Nat → Bool) (h : Constraints p) : clause p c2433 = true :=
  Snake9.LocalRup.prove_clause [c2066, c1440] c2433 (by decide) p (sat_cons (step2066 p h) (sat_cons (step1440 p h) (sat_nil p)))
def c2434 : List Lit := [(1651, false), (1660, true)]
theorem step2434 (p : Nat → Bool) (h : Constraints p) : clause p c2434 = true :=
  Snake9.LocalRup.prove_clause [c2066, c1441] c2434 (by decide) p (sat_cons (step2066 p h) (sat_cons (step1441 p h) (sat_nil p)))
def c2435 : List Lit := [(1652, false), (1661, true)]
theorem step2435 (p : Nat → Bool) (h : Constraints p) : clause p c2435 = true :=
  Snake9.LocalRup.prove_clause [c2066, c1442] c2435 (by decide) p (sat_cons (step2066 p h) (sat_cons (step1442 p h) (sat_nil p)))
def c2436 : List Lit := [(1656, false), (1676, true)]
theorem step2436 (p : Nat → Bool) (h : Constraints p) : clause p c2436 = true :=
  Snake9.LocalRup.prove_clause [c2070, c1473] c2436 (by decide) p (sat_cons (step2070 p h) (sat_cons (step1473 p h) (sat_nil p)))
def c2437 : List Lit := [(1657, false), (1677, true)]
theorem step2437 (p : Nat → Bool) (h : Constraints p) : clause p c2437 = true :=
  Snake9.LocalRup.prove_clause [c2070, c1474] c2437 (by decide) p (sat_cons (step2070 p h) (sat_cons (step1474 p h) (sat_nil p)))
end B112E052
