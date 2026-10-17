import B112E007Part0025
namespace B112E007
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2964 : List Lit := [(1584, true), (1579, false)]
theorem step2964 (p : Nat → Bool) (h : Constraints p) : clause p c2964 = true :=
  Snake9.LocalRup.prove_clause [c2485, c1064] c2964 (by decide) p (sat_cons (step2485 p h) (sat_cons (step1064 p h) (sat_nil p)))
def c2965 : List Lit := [(1599, false), (70, false), (1614, true), (81, true), (52, false)]
theorem step2965 (p : Nat → Bool) (h : Constraints p) : clause p c2965 = true :=
  Snake9.LocalRup.prove_clause [c2485, c1644] c2965 (by decide) p (sat_cons (step2485 p h) (sat_cons (step1644 p h) (sat_nil p)))
def c2966 : List Lit := [(70, false), (1613, true), (106, false), (81, true), (1599, false)]
theorem step2966 (p : Nat → Bool) (h : Constraints p) : clause p c2966 = true :=
  Snake9.LocalRup.prove_clause [c2485, c1637] c2966 (by decide) p (sat_cons (step2485 p h) (sat_cons (step1637 p h) (sat_nil p)))
def c2967 : List Lit := [(101, false), (106, true), (81, true)]
theorem step2967 (p : Nat → Bool) (h : Constraints p) : clause p c2967 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1522] c2967 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1522 p h) (sat_nil p)))
def c2968 : List Lit := [(50, false), (55, true), (52, true), (81, true)]
theorem step2968 (p : Nat → Bool) (h : Constraints p) : clause p c2968 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1481] c2968 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1481 p h) (sat_nil p)))
def c2969 : List Lit := [(50, false), (51, true), (52, true), (55, true)]
theorem step2969 (p : Nat → Bool) (h : Constraints p) : clause p c2969 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1483] c2969 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1483 p h) (sat_nil p)))
def c2970 : List Lit := [(77, false), (70, false), (1580, true), (52, false)]
theorem step2970 (p : Nat → Bool) (h : Constraints p) : clause p c2970 = true :=
  Snake9.LocalRup.prove_clause [c2613, c1657] c2970 (by decide) p (sat_cons (step2613 p h) (sat_cons (step1657 p h) (sat_nil p)))
def c2971 : List Lit := [(70, false), (68, true), (52, true), (77, true), (106, true)]
theorem step2971 (p : Nat → Bool) (h : Constraints p) : clause p c2971 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1500] c2971 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1500 p h) (sat_nil p)))
def c2972 : List Lit := [(1544, false), (29, false), (1611, false), (1470, false), (1459, false), (21, false), (1625, false)]
theorem step2972 (p : Nat → Bool) (h : Constraints p) : clause p c2972 = true :=
  Snake9.LocalRup.prove_clause [c2610, c2010] c2972 (by decide) p (sat_cons (step2610 p h) (sat_cons (step2010 p h) (sat_nil p)))
def c2973 : List Lit := [(63, false), (68, true)]
theorem step2973 (p : Nat → Bool) (h : Constraints p) : clause p c2973 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1495] c2973 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1495 p h) (sat_nil p)))
def c2974 : List Lit := [(1682, true), (1611, false)]
theorem step2974 (p : Nat → Bool) (h : Constraints p) : clause p c2974 = true :=
  Snake9.LocalRup.prove_clause [c2612, c1232] c2974 (by decide) p (sat_cons (step2612 p h) (sat_cons (step1232 p h) (sat_nil p)))
def c2975 : List Lit := [(12, true), (55, true), (73, false)]
theorem step2975 (p : Nat → Bool) (h : Constraints p) : clause p c2975 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1504] c2975 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1504 p h) (sat_nil p)))
def c2976 : List Lit := [(1490, false), (1543, false)]
theorem step2976 (p : Nat → Bool) (h : Constraints p) : clause p c2976 = true :=
  Snake9.LocalRup.prove_clause [c2617, c1040] c2976 (by decide) p (sat_cons (step2617 p h) (sat_cons (step1040 p h) (sat_nil p)))
def c2977 : List Lit := [(1640, false), (1668, true)]
theorem step2977 (p : Nat → Bool) (h : Constraints p) : clause p c2977 = true :=
  Snake9.LocalRup.prove_clause [c2611, c1221] c2977 (by decide) p (sat_cons (step2611 p h) (sat_cons (step1221 p h) (sat_nil p)))
def c2978 : List Lit := [(1626, false), (106, true), (1628, false), (1668, true)]
theorem step2978 (p : Nat → Bool) (h : Constraints p) : clause p c2978 = true :=
  Snake9.LocalRup.prove_clause [c2610, c1748] c2978 (by decide) p (sat_cons (step2610 p h) (sat_cons (step1748 p h) (sat_nil p)))
def c2979 : List Lit := [(102, true), (463, true), (106, true), (1628, false), (1668, true)]
theorem step2979 (p : Nat → Bool) (h : Constraints p) : clause p c2979 = true :=
  Snake9.LocalRup.prove_clause [c2610, c1826] c2979 (by decide) p (sat_cons (step2610 p h) (sat_cons (step1826 p h) (sat_nil p)))
def c2980 : List Lit := [(1629, false), (1625, false), (1668, true), (106, true)]
theorem step2980 (p : Nat → Bool) (h : Constraints p) : clause p c2980 = true :=
  Snake9.LocalRup.prove_clause [c2610, c1835] c2980 (by decide) p (sat_cons (step2610 p h) (sat_cons (step1835 p h) (sat_nil p)))
def c2981 : List Lit := [(1657, true), (1645, false)]
theorem step2981 (p : Nat → Bool) (h : Constraints p) : clause p c2981 = true :=
  Snake9.LocalRup.prove_clause [c2610, c1194] c2981 (by decide) p (sat_cons (step2610 p h) (sat_cons (step1194 p h) (sat_nil p)))
def c2982 : List Lit := [(86, false), (58, false), (98, false), (1530, true), (94, false)]
theorem step2982 (p : Nat → Bool) (h : Constraints p) : clause p c2982 = true :=
  Snake9.LocalRup.prove_clause [c2641, c1412] c2982 (by decide) p (sat_cons (step2641 p h) (sat_cons (step1412 p h) (sat_nil p)))
def c2983 : List Lit := [(1529, true), (55, true)]
theorem step2983 (p : Nat → Bool) (h : Constraints p) : clause p c2983 = true :=
  Snake9.LocalRup.prove_clause [c2641, c1358] c2983 (by decide) p (sat_cons (step2641 p h) (sat_cons (step1358 p h) (sat_nil p)))
def c2984 : List Lit := [(50, false), (51, true), (55, true), (81, true)]
theorem step2984 (p : Nat → Bool) (h : Constraints p) : clause p c2984 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1482] c2984 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1482 p h) (sat_nil p)))
def c2985 : List Lit := [(77, true), (55, true), (73, false)]
theorem step2985 (p : Nat → Bool) (h : Constraints p) : clause p c2985 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1503] c2985 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1503 p h) (sat_nil p)))
def c2986 : List Lit := [(82, true), (94, false), (95, true), (85, false), (83, false)]
theorem step2986 (p : Nat → Bool) (h : Constraints p) : clause p c2986 = true :=
  Snake9.LocalRup.prove_clause [c2643, c1385] c2986 (by decide) p (sat_cons (step2643 p h) (sat_cons (step1385 p h) (sat_nil p)))
def c2987 : List Lit := [(82, true), (84, true), (85, false), (95, true)]
theorem step2987 (p : Nat → Bool) (h : Constraints p) : clause p c2987 = true :=
  Snake9.LocalRup.prove_clause [c2643, c359] c2987 (by decide) p (sat_cons (step2643 p h) (sat_cons (step359 p h) (sat_nil p)))
def c2988 : List Lit := [(84, true), (19, true), (82, true), (85, false)]
theorem step2988 (p : Nat → Bool) (h : Constraints p) : clause p c2988 = true :=
  Snake9.LocalRup.prove_clause [c2643, c362] c2988 (by decide) p (sat_cons (step2643 p h) (sat_cons (step362 p h) (sat_nil p)))
def c2989 : List Lit := [(80, true), (18, true), (89, true), (84, true), (83, false)]
theorem step2989 (p : Nat → Bool) (h : Constraints p) : clause p c2989 = true :=
  Snake9.LocalRup.prove_clause [c2644, c347] c2989 (by decide) p (sat_cons (step2644 p h) (sat_cons (step347 p h) (sat_nil p)))
def c2990 : List Lit := [(63, true), (10, true), (69, true), (68, false), (70, true)]
theorem step2990 (p : Nat → Bool) (h : Constraints p) : clause p c2990 = true :=
  Snake9.LocalRup.prove_clause [c2649, c256] c2990 (by decide) p (sat_cons (step2649 p h) (sat_cons (step256 p h) (sat_nil p)))
def c2991 : List Lit := [(102, false), (1599, true), (208, true), (1626, true), (81, false)]
theorem step2991 (p : Nat → Bool) (h : Constraints p) : clause p c2991 = true :=
  Snake9.LocalRup.prove_clause [c2643, c1603] c2991 (by decide) p (sat_cons (step2643 p h) (sat_cons (step1603 p h) (sat_nil p)))
def c2992 : List Lit := [(107, false), (118, false), (102, false), (1643, false), (1668, true), (1628, false), (463, true)]
theorem step2992 (p : Nat → Bool) (h : Constraints p) : clause p c2992 = true :=
  Snake9.LocalRup.prove_clause [c2610, c1864] c2992 (by decide) p (sat_cons (step2610 p h) (sat_cons (step1864 p h) (sat_nil p)))
def c2993 : List Lit := [(72, true), (66, false)]
theorem step2993 (p : Nat → Bool) (h : Constraints p) : clause p c2993 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1497] c2993 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1497 p h) (sat_nil p)))
def c2994 : List Lit := [(71, true), (70, true), (72, false)]
theorem step2994 (p : Nat → Bool) (h : Constraints p) : clause p c2994 = true :=
  Snake9.LocalRup.prove_clause [c2648, c285] c2994 (by decide) p (sat_cons (step2648 p h) (sat_cons (step285 p h) (sat_nil p)))
def c2995 : List Lit := [(91, false), (25, false), (1666, true), (92, false)]
theorem step2995 (p : Nat → Bool) (h : Constraints p) : clause p c2995 = true :=
  Snake9.LocalRup.prove_clause [c2610, c1447] c2995 (by decide) p (sat_cons (step2610 p h) (sat_cons (step1447 p h) (sat_nil p)))
def c2996 : List Lit := [(1646, false), (1658, true)]
theorem step2996 (p : Nat → Bool) (h : Constraints p) : clause p c2996 = true :=
  Snake9.LocalRup.prove_clause [c2610, c1197] c2996 (by decide) p (sat_cons (step2610 p h) (sat_cons (step1197 p h) (sat_nil p)))
def c2997 : List Lit := [(82, true), (19, true), (85, false), (95, true)]
theorem step2997 (p : Nat → Bool) (h : Constraints p) : clause p c2997 = true :=
  Snake9.LocalRup.prove_clause [c2643, c361] c2997 (by decide) p (sat_cons (step2643 p h) (sat_cons (step361 p h) (sat_nil p)))
def c2998 : List Lit := [(64, true), (1570, true)]
theorem step2998 (p : Nat → Bool) (h : Constraints p) : clause p c2998 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1043] c2998 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1043 p h) (sat_nil p)))
def c2999 : List Lit := [(1616, false), (1687, true)]
theorem step2999 (p : Nat → Bool) (h : Constraints p) : clause p c2999 = true :=
  Snake9.LocalRup.prove_clause [c2612, c1257] c2999 (by decide) p (sat_cons (step2612 p h) (sat_cons (step1257 p h) (sat_nil p)))
def c3000 : List Lit := [(73, true), (1583, true)]
theorem step3000 (p : Nat → Bool) (h : Constraints p) : clause p c3000 = true :=
  Snake9.LocalRup.prove_clause [c2613, c1449] c3000 (by decide) p (sat_cons (step2613 p h) (sat_cons (step1449 p h) (sat_nil p)))
def c3001 : List Lit := [(73, true), (77, false), (70, true)]
theorem step3001 (p : Nat → Bool) (h : Constraints p) : clause p c3001 = true :=
  Snake9.LocalRup.prove_clause [c2646, c304] c3001 (by decide) p (sat_cons (step2646 p h) (sat_cons (step304 p h) (sat_nil p)))
def c3002 : List Lit := [(8, true), (64, false), (69, true)]
theorem step3002 (p : Nat → Bool) (h : Constraints p) : clause p c3002 = true :=
  Snake9.LocalRup.prove_clause [c2650, c238] c3002 (by decide) p (sat_cons (step2650 p h) (sat_cons (step238 p h) (sat_nil p)))
def c3003 : List Lit := [(63, true), (64, false), (69, true)]
theorem step3003 (p : Nat → Bool) (h : Constraints p) : clause p c3003 = true :=
  Snake9.LocalRup.prove_clause [c2650, c237] c3003 (by decide) p (sat_cons (step2650 p h) (sat_cons (step237 p h) (sat_nil p)))
def c3004 : List Lit := [(8, true), (63, true), (64, false)]
theorem step3004 (p : Nat → Bool) (h : Constraints p) : clause p c3004 = true :=
  Snake9.LocalRup.prove_clause [c2650, c239] c3004 (by decide) p (sat_cons (step2650 p h) (sat_cons (step239 p h) (sat_nil p)))
def c3005 : List Lit := [(69, true), (78, true), (76, false)]
theorem step3005 (p : Nat → Bool) (h : Constraints p) : clause p c3005 = true :=
  Snake9.LocalRup.prove_clause [c2647, c300] c3005 (by decide) p (sat_cons (step2647 p h) (sat_cons (step300 p h) (sat_nil p)))
def c3006 : List Lit := [(96, true), (59, false), (53, true)]
theorem step3006 (p : Nat → Bool) (h : Constraints p) : clause p c3006 = true :=
  Snake9.LocalRup.prove_clause [c2641, c226] c3006 (by decide) p (sat_cons (step2641 p h) (sat_cons (step226 p h) (sat_nil p)))
def c3007 : List Lit := [(59, false), (53, true), (60, true)]
theorem step3007 (p : Nat → Bool) (h : Constraints p) : clause p c3007 = true :=
  Snake9.LocalRup.prove_clause [c2641, c227] c3007 (by decide) p (sat_cons (step2641 p h) (sat_cons (step227 p h) (sat_nil p)))
def c3008 : List Lit := [(96, true), (59, false), (60, true)]
theorem step3008 (p : Nat → Bool) (h : Constraints p) : clause p c3008 = true :=
  Snake9.LocalRup.prove_clause [c2641, c225] c3008 (by decide) p (sat_cons (step2641 p h) (sat_cons (step225 p h) (sat_nil p)))
def c3009 : List Lit := [(78, true), (77, false), (70, true)]
theorem step3009 (p : Nat → Bool) (h : Constraints p) : clause p c3009 = true :=
  Snake9.LocalRup.prove_clause [c2646, c303] c3009 (by decide) p (sat_cons (step2646 p h) (sat_cons (step303 p h) (sat_nil p)))
def c3010 : List Lit := [(66, true), (70, true), (72, false)]
theorem step3010 (p : Nat → Bool) (h : Constraints p) : clause p c3010 = true :=
  Snake9.LocalRup.prove_clause [c2648, c287] c3010 (by decide) p (sat_cons (step2648 p h) (sat_cons (step287 p h) (sat_nil p)))
def c3011 : List Lit := [(66, true), (67, false)]
theorem step3011 (p : Nat → Bool) (h : Constraints p) : clause p c3011 = true :=
  Snake9.LocalRup.prove_clause [c2638, c252] c3011 (by decide) p (sat_cons (step2638 p h) (sat_cons (step252 p h) (sat_nil p)))
def c3012 : List Lit := [(80, true), (84, true), (101, true), (50, true), (81, false), (16, true), (88, true)]
theorem step3012 (p : Nat → Bool) (h : Constraints p) : clause p c3012 = true :=
  Snake9.LocalRup.prove_clause [c2645, c326] c3012 (by decide) p (sat_cons (step2645 p h) (sat_cons (step326 p h) (sat_nil p)))
def c3013 : List Lit := [(80, true), (101, true), (88, true), (81, false), (84, true), (82, true), (50, true)]
theorem step3013 (p : Nat → Bool) (h : Constraints p) : clause p c3013 = true :=
  Snake9.LocalRup.prove_clause [c2645, c324] c3013 (by decide) p (sat_cons (step2645 p h) (sat_cons (step324 p h) (sat_nil p)))
def c3014 : List Lit := [(87, true), (96, true), (88, true), (86, false), (80, true)]
theorem step3014 (p : Nat → Bool) (h : Constraints p) : clause p c3014 = true :=
  Snake9.LocalRup.prove_clause [c2642, c364] c3014 (by decide) p (sat_cons (step2642 p h) (sat_cons (step364 p h) (sat_nil p)))
def c3015 : List Lit := [(67, true), (1579, true)]
theorem step3015 (p : Nat → Bool) (h : Constraints p) : clause p c3015 = true :=
  Snake9.LocalRup.prove_clause [c2635, c1374] c3015 (by decide) p (sat_cons (step2635 p h) (sat_cons (step1374 p h) (sat_nil p)))
def c3016 : List Lit := [(75, true), (74, false)]
theorem step3016 (p : Nat → Bool) (h : Constraints p) : clause p c3016 = true :=
  Snake9.LocalRup.prove_clause [c2635, c294] c3016 (by decide) p (sat_cons (step2635 p h) (sat_cons (step294 p h) (sat_nil p)))
def c3017 : List Lit := [(79, true), (74, false)]
theorem step3017 (p : Nat → Bool) (h : Constraints p) : clause p c3017 = true :=
  Snake9.LocalRup.prove_clause [c2635, c293] c3017 (by decide) p (sat_cons (step2635 p h) (sat_cons (step293 p h) (sat_nil p)))
def c3018 : List Lit := [(1583, true), (70, false), (106, false)]
theorem step3018 (p : Nat → Bool) (h : Constraints p) : clause p c3018 = true :=
  Snake9.LocalRup.prove_clause [c2613, c1411] c3018 (by decide) p (sat_cons (step2613 p h) (sat_cons (step1411 p h) (sat_nil p)))
def c3019 : List Lit := [(1612, true), (107, true), (88, true), (102, false), (224, true), (106, false), (1598, false)]
theorem step3019 (p : Nat → Bool) (h : Constraints p) : clause p c3019 = true :=
  Snake9.LocalRup.prove_clause [c2613, c1425] c3019 (by decide) p (sat_cons (step2613 p h) (sat_cons (step1425 p h) (sat_nil p)))
def c3020 : List Lit := [(70, false), (1612, true), (52, false), (1598, false)]
theorem step3020 (p : Nat → Bool) (h : Constraints p) : clause p c3020 = true :=
  Snake9.LocalRup.prove_clause [c2613, c2482, c1417] c3020 (by decide) p (sat_cons (step2613 p h) (sat_cons (step2482 p h) (sat_cons (step1417 p h) (sat_nil p))))
def c3021 : List Lit := [(1666, true), (1625, false), (106, true)]
theorem step3021 (p : Nat → Bool) (h : Constraints p) : clause p c3021 = true :=
  Snake9.LocalRup.prove_clause [c2610, c1680] c3021 (by decide) p (sat_cons (step2610 p h) (sat_cons (step1680 p h) (sat_nil p)))
def c3022 : List Lit := [(1626, false), (1666, true)]
theorem step3022 (p : Nat → Bool) (h : Constraints p) : clause p c3022 = true :=
  Snake9.LocalRup.prove_clause [c2610, c2019] c3022 (by decide) p (sat_cons (step2610 p h) (sat_cons (step2019 p h) (sat_nil p)))
def c3023 : List Lit := [(1684, true), (1613, false)]
theorem step3023 (p : Nat → Bool) (h : Constraints p) : clause p c3023 = true :=
  Snake9.LocalRup.prove_clause [c2612, c1244] c3023 (by decide) p (sat_cons (step2612 p h) (sat_cons (step1244 p h) (sat_nil p)))
def c3024 : List Lit := [(1629, false), (1626, false), (1668, true)]
theorem step3024 (p : Nat → Bool) (h : Constraints p) : clause p c3024 = true :=
  Snake9.LocalRup.prove_clause [c2610, c1399] c3024 (by decide) p (sat_cons (step2610 p h) (sat_cons (step1399 p h) (sat_nil p)))
def c3025 : List Lit := [(1488, false), (1545, false)]
theorem step3025 (p : Nat → Bool) (h : Constraints p) : clause p c3025 = true :=
  Snake9.LocalRup.prove_clause [c2617, c1033] c3025 (by decide) p (sat_cons (step2617 p h) (sat_cons (step1033 p h) (sat_nil p)))
def c3026 : List Lit := [(10, false), (1583, true), (70, true)]
theorem step3026 (p : Nat → Bool) (h : Constraints p) : clause p c3026 = true :=
  Snake9.LocalRup.prove_clause [c2613, c2648, c1601] c3026 (by decide) p (sat_cons (step2613 p h) (sat_cons (step2648 p h) (sat_cons (step1601 p h) (sat_nil p))))
def c3027 : List Lit := [(63, false), (64, true)]
theorem step3027 (p : Nat → Bool) (h : Constraints p) : clause p c3027 = true :=
  Snake9.LocalRup.prove_clause [c2482, c1496] c3027 (by decide) p (sat_cons (step2482 p h) (sat_cons (step1496 p h) (sat_nil p)))
end B112E007
