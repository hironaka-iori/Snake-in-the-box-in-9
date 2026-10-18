import B112E260Part0004
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2423 : List Lit := [(117, true), (93, false), (96, true)]
theorem step2423 (p : Nat → Bool) (h : Constraints p) : clause p c2423 = true :=
  Snake9.LocalRup.prove_clause [c862, c621] c2423 (by decide) p (sat_cons (step862 p h) (sat_cons (step621 p h) (sat_nil p)))
def c2424 : List Lit := [(117, true), (93, false), (79, true)]
theorem step2424 (p : Nat → Bool) (h : Constraints p) : clause p c2424 = true :=
  Snake9.LocalRup.prove_clause [c862, c622] c2424 (by decide) p (sat_cons (step862 p h) (sat_cons (step622 p h) (sat_nil p)))
def c2425 : List Lit := [(95, false), (96, true), (21, true)]
theorem step2425 (p : Nat → Bool) (h : Constraints p) : clause p c2425 = true :=
  Snake9.LocalRup.prove_clause [c864, c645] c2425 (by decide) p (sat_cons (step864 p h) (sat_cons (step645 p h) (sat_nil p)))
def c2426 : List Lit := [(82, true), (95, false), (21, true)]
theorem step2426 (p : Nat → Bool) (h : Constraints p) : clause p c2426 = true :=
  Snake9.LocalRup.prove_clause [c864, c646] c2426 (by decide) p (sat_cons (step864 p h) (sat_cons (step646 p h) (sat_nil p)))
def c2427 : List Lit := [(97, false), (86, true)]
theorem step2427 (p : Nat → Bool) (h : Constraints p) : clause p c2427 = true :=
  Snake9.LocalRup.prove_clause [c865, c664] c2427 (by decide) p (sat_cons (step865 p h) (sat_cons (step664 p h) (sat_nil p)))
def c2428 : List Lit := [(126, true), (98, true), (99, false)]
theorem step2428 (p : Nat → Bool) (h : Constraints p) : clause p c2428 = true :=
  Snake9.LocalRup.prove_clause [c866, c671] c2428 (by decide) p (sat_cons (step866 p h) (sat_cons (step671 p h) (sat_nil p)))
def c2429 : List Lit := [(99, false), (126, true), (96, true)]
theorem step2429 (p : Nat → Bool) (h : Constraints p) : clause p c2429 = true :=
  Snake9.LocalRup.prove_clause [c866, c672] c2429 (by decide) p (sat_cons (step866 p h) (sat_cons (step672 p h) (sat_nil p)))
def c2430 : List Lit := [(99, false), (98, true), (96, true)]
theorem step2430 (p : Nat → Bool) (h : Constraints p) : clause p c2430 = true :=
  Snake9.LocalRup.prove_clause [c866, c673] c2430 (by decide) p (sat_cons (step866 p h) (sat_cons (step673 p h) (sat_nil p)))
def c2431 : List Lit := [(101, false), (127, true), (96, true)]
theorem step2431 (p : Nat → Bool) (h : Constraints p) : clause p c2431 = true :=
  Snake9.LocalRup.prove_clause [c867, c680] c2431 (by decide) p (sat_cons (step867 p h) (sat_cons (step680 p h) (sat_nil p)))
def c2432 : List Lit := [(101, false), (100, true), (96, true)]
theorem step2432 (p : Nat → Bool) (h : Constraints p) : clause p c2432 = true :=
  Snake9.LocalRup.prove_clause [c867, c681] c2432 (by decide) p (sat_cons (step867 p h) (sat_cons (step681 p h) (sat_nil p)))
def c2433 : List Lit := [(102, false), (103, true), (108, true), (105, true)]
theorem step2433 (p : Nat → Bool) (h : Constraints p) : clause p c2433 = true :=
  Snake9.LocalRup.prove_clause [c868, c685] c2433 (by decide) p (sat_cons (step868 p h) (sat_cons (step685 p h) (sat_nil p)))
def c2434 : List Lit := [(107, false), (82, true)]
theorem step2434 (p : Nat → Bool) (h : Constraints p) : clause p c2434 = true :=
  Snake9.LocalRup.prove_clause [c871, c722] c2434 (by decide) p (sat_cons (step871 p h) (sat_cons (step722 p h) (sat_nil p)))
def c2435 : List Lit := [(113, true), (112, false), (49, true)]
theorem step2435 (p : Nat → Bool) (h : Constraints p) : clause p c2435 = true :=
  Snake9.LocalRup.prove_clause [c873, c737] c2435 (by decide) p (sat_cons (step873 p h) (sat_cons (step737 p h) (sat_nil p)))
def c2436 : List Lit := [(114, false), (105, true), (50, true)]
theorem step2436 (p : Nat → Bool) (h : Constraints p) : clause p c2436 = true :=
  Snake9.LocalRup.prove_clause [c874, c743] c2436 (by decide) p (sat_cons (step874 p h) (sat_cons (step743 p h) (sat_nil p)))
def c2437 : List Lit := [(117, true), (116, false), (56, true)]
theorem step2437 (p : Nat → Bool) (h : Constraints p) : clause p c2437 = true :=
  Snake9.LocalRup.prove_clause [c875, c747] c2437 (by decide) p (sat_cons (step875 p h) (sat_cons (step747 p h) (sat_nil p)))
def c2438 : List Lit := [(124, true), (118, false), (105, true)]
theorem step2438 (p : Nat → Bool) (h : Constraints p) : clause p c2438 = true :=
  Snake9.LocalRup.prove_clause [c876, c751] c2438 (by decide) p (sat_cons (step876 p h) (sat_cons (step751 p h) (sat_nil p)))
def c2439 : List Lit := [(118, false), (119, true), (105, true)]
theorem step2439 (p : Nat → Bool) (h : Constraints p) : clause p c2439 = true :=
  Snake9.LocalRup.prove_clause [c876, c752] c2439 (by decide) p (sat_cons (step876 p h) (sat_cons (step752 p h) (sat_nil p)))
def c2440 : List Lit := [(126, true), (117, true), (96, true), (120, false), (127, true)]
theorem step2440 (p : Nat → Bool) (h : Constraints p) : clause p c2440 = true :=
  Snake9.LocalRup.prove_clause [c877, c768] c2440 (by decide) p (sat_cons (step877 p h) (sat_cons (step768 p h) (sat_nil p)))
def c2441 : List Lit := [(117, true), (120, false), (96, true), (119, true), (127, true)]
theorem step2441 (p : Nat → Bool) (h : Constraints p) : clause p c2441 = true :=
  Snake9.LocalRup.prove_clause [c877, c769] c2441 (by decide) p (sat_cons (step877 p h) (sat_cons (step769 p h) (sat_nil p)))
def c2442 : List Lit := [(117, true), (126, true), (96, true), (120, false), (119, true)]
theorem step2442 (p : Nat → Bool) (h : Constraints p) : clause p c2442 = true :=
  Snake9.LocalRup.prove_clause [c877, c770] c2442 (by decide) p (sat_cons (step877 p h) (sat_cons (step770 p h) (sat_nil p)))
def c2443 : List Lit := [(124, true), (122, true), (121, false), (108, true)]
theorem step2443 (p : Nat → Bool) (h : Constraints p) : clause p c2443 = true :=
  Snake9.LocalRup.prove_clause [c878, c774] c2443 (by decide) p (sat_cons (step878 p h) (sat_cons (step774 p h) (sat_nil p)))
def c2444 : List Lit := [(124, true), (122, true), (121, false), (60, true)]
theorem step2444 (p : Nat → Bool) (h : Constraints p) : clause p c2444 = true :=
  Snake9.LocalRup.prove_clause [c878, c775] c2444 (by decide) p (sat_cons (step878 p h) (sat_cons (step775 p h) (sat_nil p)))
def c2445 : List Lit := [(128, false), (255, false)]
theorem step2445 (p : Nat → Bool) (h : Constraints p) : clause p c2445 = true :=
  Snake9.LocalRup.prove_clause [c2149, c884] c2445 (by decide) p (sat_cons (step2149 p h) (sat_cons (step884 p h) (sat_nil p)))
def c2446 : List Lit := [(133, false), (134, false)]
theorem step2446 (p : Nat → Bool) (h : Constraints p) : clause p c2446 = true :=
  Snake9.LocalRup.prove_clause [c2154, c888] c2446 (by decide) p (sat_cons (step2154 p h) (sat_cons (step888 p h) (sat_nil p)))
def c2447 : List Lit := [(257, false), (263, false)]
theorem step2447 (p : Nat → Bool) (h : Constraints p) : clause p c2447 = true :=
  Snake9.LocalRup.prove_clause [c2134, c895] c2447 (by decide) p (sat_cons (step2134 p h) (sat_cons (step895 p h) (sat_nil p)))
def c2448 : List Lit := [(273, false), (275, false)]
theorem step2448 (p : Nat → Bool) (h : Constraints p) : clause p c2448 = true :=
  Snake9.LocalRup.prove_clause [c2147, c903] c2448 (by decide) p (sat_cons (step2147 p h) (sat_cons (step903 p h) (sat_nil p)))
def c2449 : List Lit := [(271, false), (277, false)]
theorem step2449 (p : Nat → Bool) (h : Constraints p) : clause p c2449 = true :=
  Snake9.LocalRup.prove_clause [c2133, c907] c2449 (by decide) p (sat_cons (step2133 p h) (sat_cons (step907 p h) (sat_nil p)))
def c2450 : List Lit := [(265, false), (279, false)]
theorem step2450 (p : Nat → Bool) (h : Constraints p) : clause p c2450 = true :=
  Snake9.LocalRup.prove_clause [c2120, c911] c2450 (by decide) p (sat_cons (step2120 p h) (sat_cons (step911 p h) (sat_nil p)))
def c2451 : List Lit := [(287, false), (293, false)]
theorem step2451 (p : Nat → Bool) (h : Constraints p) : clause p c2451 = true :=
  Snake9.LocalRup.prove_clause [c2132, c920] c2451 (by decide) p (sat_cons (step2132 p h) (sat_cons (step920 p h) (sat_nil p)))
def c2452 : List Lit := [(297, false), (299, false)]
theorem step2452 (p : Nat → Bool) (h : Constraints p) : clause p c2452 = true :=
  Snake9.LocalRup.prove_clause [c2146, c925] c2452 (by decide) p (sat_cons (step2146 p h) (sat_cons (step925 p h) (sat_nil p)))
def c2453 : List Lit := [(303, false), (305, false)]
theorem step2453 (p : Nat → Bool) (h : Constraints p) : clause p c2453 = true :=
  Snake9.LocalRup.prove_clause [c2145, c930] c2453 (by decide) p (sat_cons (step2145 p h) (sat_cons (step930 p h) (sat_nil p)))
def c2454 : List Lit := [(301, false), (307, false)]
theorem step2454 (p : Nat → Bool) (h : Constraints p) : clause p c2454 = true :=
  Snake9.LocalRup.prove_clause [c2131, c934] c2454 (by decide) p (sat_cons (step2131 p h) (sat_cons (step934 p h) (sat_nil p)))
def c2455 : List Lit := [(295, false), (309, false)]
theorem step2455 (p : Nat → Bool) (h : Constraints p) : clause p c2455 = true :=
  Snake9.LocalRup.prove_clause [c2119, c939] c2455 (by decide) p (sat_cons (step2119 p h) (sat_cons (step939 p h) (sat_nil p)))
def c2456 : List Lit := [(281, false), (311, false)]
theorem step2456 (p : Nat → Bool) (h : Constraints p) : clause p c2456 = true :=
  Snake9.LocalRup.prove_clause [c2112, c944] c2456 (by decide) p (sat_cons (step2112 p h) (sat_cons (step944 p h) (sat_nil p)))
def c2457 : List Lit := [(315, false), (317, false)]
theorem step2457 (p : Nat → Bool) (h : Constraints p) : clause p c2457 = true :=
  Snake9.LocalRup.prove_clause [c2144, c950] c2457 (by decide) p (sat_cons (step2144 p h) (sat_cons (step950 p h) (sat_nil p)))
def c2458 : List Lit := [(319, false), (325, false)]
theorem step2458 (p : Nat → Bool) (h : Constraints p) : clause p c2458 = true :=
  Snake9.LocalRup.prove_clause [c2130, c955] c2458 (by decide) p (sat_cons (step2130 p h) (sat_cons (step955 p h) (sat_nil p)))
def c2459 : List Lit := [(335, false), (337, false)]
theorem step2459 (p : Nat → Bool) (h : Constraints p) : clause p c2459 = true :=
  Snake9.LocalRup.prove_clause [c2143, c965] c2459 (by decide) p (sat_cons (step2143 p h) (sat_cons (step965 p h) (sat_nil p)))
def c2460 : List Lit := [(333, false), (339, false)]
theorem step2460 (p : Nat → Bool) (h : Constraints p) : clause p c2460 = true :=
  Snake9.LocalRup.prove_clause [c2129, c969] c2460 (by decide) p (sat_cons (step2129 p h) (sat_cons (step969 p h) (sat_nil p)))
def c2461 : List Lit := [(327, false), (341, false)]
theorem step2461 (p : Nat → Bool) (h : Constraints p) : clause p c2461 = true :=
  Snake9.LocalRup.prove_clause [c2118, c973] c2461 (by decide) p (sat_cons (step2118 p h) (sat_cons (step973 p h) (sat_nil p)))
def c2462 : List Lit := [(345, false), (347, false)]
theorem step2462 (p : Nat → Bool) (h : Constraints p) : clause p c2462 = true :=
  Snake9.LocalRup.prove_clause [c2142, c981] c2462 (by decide) p (sat_cons (step2142 p h) (sat_cons (step981 p h) (sat_nil p)))
def c2463 : List Lit := [(343, false), (373, false)]
theorem step2463 (p : Nat → Bool) (h : Constraints p) : clause p c2463 = true :=
  Snake9.LocalRup.prove_clause [c2111, c998] c2463 (by decide) p (sat_cons (step2111 p h) (sat_cons (step998 p h) (sat_nil p)))
def c2464 : List Lit := [(313, false), (375, false)]
theorem step2464 (p : Nat → Bool) (h : Constraints p) : clause p c2464 = true :=
  Snake9.LocalRup.prove_clause [c2108, c1003] c2464 (by decide) p (sat_cons (step2108 p h) (sat_cons (step1003 p h) (sat_nil p)))
def c2465 : List Lit := [(191, false), (379, false)]
theorem step2465 (p : Nat → Bool) (h : Constraints p) : clause p c2465 = true :=
  Snake9.LocalRup.prove_clause [c2141, c1008] c2465 (by decide) p (sat_cons (step2141 p h) (sat_cons (step1008 p h) (sat_nil p)))
def c2466 : List Lit := [(194, false), (195, false)]
theorem step2466 (p : Nat → Bool) (h : Constraints p) : clause p c2466 = true :=
  Snake9.LocalRup.prove_clause [c2153, c1011] c2466 (by decide) p (sat_cons (step2153 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c2467 : List Lit := [(383, false), (385, false)]
theorem step2467 (p : Nat → Bool) (h : Constraints p) : clause p c2467 = true :=
  Snake9.LocalRup.prove_clause [c2140, c1015] c2467 (by decide) p (sat_cons (step2140 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c2468 : List Lit := [(381, false), (387, false)]
theorem step2468 (p : Nat → Bool) (h : Constraints p) : clause p c2468 = true :=
  Snake9.LocalRup.prove_clause [c2127, c1020] c2468 (by decide) p (sat_cons (step2127 p h) (sat_cons (step1020 p h) (sat_nil p)))
def c2469 : List Lit := [(200, false), (201, false)]
theorem step2469 (p : Nat → Bool) (h : Constraints p) : clause p c2469 = true :=
  Snake9.LocalRup.prove_clause [c2152, c1025] c2469 (by decide) p (sat_cons (step2152 p h) (sat_cons (step1025 p h) (sat_nil p)))
def c2470 : List Lit := [(391, false), (393, false)]
theorem step2470 (p : Nat → Bool) (h : Constraints p) : clause p c2470 = true :=
  Snake9.LocalRup.prove_clause [c2139, c1029] c2470 (by decide) p (sat_cons (step2139 p h) (sat_cons (step1029 p h) (sat_nil p)))
def c2471 : List Lit := [(395, false), (401, false)]
theorem step2471 (p : Nat → Bool) (h : Constraints p) : clause p c2471 = true :=
  Snake9.LocalRup.prove_clause [c2126, c1034] c2471 (by decide) p (sat_cons (step2126 p h) (sat_cons (step1034 p h) (sat_nil p)))
def c2472 : List Lit := [(389, false), (403, false)]
theorem step2472 (p : Nat → Bool) (h : Constraints p) : clause p c2472 = true :=
  Snake9.LocalRup.prove_clause [c2116, c1039] c2472 (by decide) p (sat_cons (step2116 p h) (sat_cons (step1039 p h) (sat_nil p)))
def c2473 : List Lit := [(421, false), (423, false)]
theorem step2473 (p : Nat → Bool) (h : Constraints p) : clause p c2473 = true :=
  Snake9.LocalRup.prove_clause [c2138, c1056] c2473 (by decide) p (sat_cons (step2138 p h) (sat_cons (step1056 p h) (sat_nil p)))
def c2474 : List Lit := [(419, false), (433, false)]
theorem step2474 (p : Nat → Bool) (h : Constraints p) : clause p c2474 = true :=
  Snake9.LocalRup.prove_clause [c2115, c1062] c2474 (by decide) p (sat_cons (step2115 p h) (sat_cons (step1062 p h) (sat_nil p)))
def c2475 : List Lit := [(405, false), (435, false)]
theorem step2475 (p : Nat → Bool) (h : Constraints p) : clause p c2475 = true :=
  Snake9.LocalRup.prove_clause [c2110, c1066] c2475 (by decide) p (sat_cons (step2110 p h) (sat_cons (step1066 p h) (sat_nil p)))
def c2476 : List Lit := [(443, false), (449, false)]
theorem step2476 (p : Nat → Bool) (h : Constraints p) : clause p c2476 = true :=
  Snake9.LocalRup.prove_clause [c2124, c1078] c2476 (by decide) p (sat_cons (step2124 p h) (sat_cons (step1078 p h) (sat_nil p)))
def c2477 : List Lit := [(237, false), (238, false)]
theorem step2477 (p : Nat → Bool) (h : Constraints p) : clause p c2477 = true :=
  Snake9.LocalRup.prove_clause [c2151, c1084] c2477 (by decide) p (sat_cons (step2151 p h) (sat_cons (step1084 p h) (sat_nil p)))
def c2478 : List Lit := [(459, false), (461, false)]
theorem step2478 (p : Nat → Bool) (h : Constraints p) : clause p c2478 = true :=
  Snake9.LocalRup.prove_clause [c2137, c1088] c2478 (by decide) p (sat_cons (step2137 p h) (sat_cons (step1088 p h) (sat_nil p)))
def c2479 : List Lit := [(451, false), (465, false)]
theorem step2479 (p : Nat → Bool) (h : Constraints p) : clause p c2479 = true :=
  Snake9.LocalRup.prove_clause [c2114, c1095] c2479 (by decide) p (sat_cons (step2114 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c2480 : List Lit := [(469, false), (471, false)]
theorem step2480 (p : Nat → Bool) (h : Constraints p) : clause p c2480 = true :=
  Snake9.LocalRup.prove_clause [c2136, c1101] c2480 (by decide) p (sat_cons (step2136 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c2481 : List Lit := [(473, false), (479, false)]
theorem step2481 (p : Nat → Bool) (h : Constraints p) : clause p c2481 = true :=
  Snake9.LocalRup.prove_clause [c2122, c1108] c2481 (by decide) p (sat_cons (step2122 p h) (sat_cons (step1108 p h) (sat_nil p)))
def c2482 : List Lit := [(253, false), (254, false)]
theorem step2482 (p : Nat → Bool) (h : Constraints p) : clause p c2482 = true :=
  Snake9.LocalRup.prove_clause [c2150, c1115] c2482 (by decide) p (sat_cons (step2150 p h) (sat_cons (step1115 p h) (sat_nil p)))
def c2483 : List Lit := [(489, false), (491, false)]
theorem step2483 (p : Nat → Bool) (h : Constraints p) : clause p c2483 = true :=
  Snake9.LocalRup.prove_clause [c2135, c1119] c2483 (by decide) p (sat_cons (step2135 p h) (sat_cons (step1119 p h) (sat_nil p)))
def c2484 : List Lit := [(487, false), (493, false)]
theorem step2484 (p : Nat → Bool) (h : Constraints p) : clause p c2484 = true :=
  Snake9.LocalRup.prove_clause [c2121, c1123] c2484 (by decide) p (sat_cons (step2121 p h) (sat_cons (step1123 p h) (sat_nil p)))
def c2485 : List Lit := [(481, false), (495, false)]
theorem step2485 (p : Nat → Bool) (h : Constraints p) : clause p c2485 = true :=
  Snake9.LocalRup.prove_clause [c2113, c1127] c2485 (by decide) p (sat_cons (step2113 p h) (sat_cons (step1127 p h) (sat_nil p)))
def c2486 : List Lit := [(467, false), (497, false)]
theorem step2486 (p : Nat → Bool) (h : Constraints p) : clause p c2486 = true :=
  Snake9.LocalRup.prove_clause [c2109, c1132] c2486 (by decide) p (sat_cons (step2109 p h) (sat_cons (step1132 p h) (sat_nil p)))
end B112E260
