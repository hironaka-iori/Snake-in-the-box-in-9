import B112E096Part0024
namespace B112E096
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2636 : List Lit := [(104, false), (105, true), (1680, true), (1566, false)]
theorem step2636 (p : Nat → Bool) (h : Constraints p) : clause p c2636 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2632, c2635, c852, c1104, c1247, c1246, c1017, c793, c1229, c1977, c1133, c219, c943, c796, c785, c983, c802, c788, c813, c834, c839, c979, c2528, c949, c854, c2072] c2636 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2632 p h) (sat_cons (step2635 p h) (sat_cons (step852 p h) (sat_cons (step1104 p h) (sat_cons (step1247 p h) (sat_cons (step1246 p h) (sat_cons (step1017 p h) (sat_cons (step793 p h) (sat_cons (step1229 p h) (sat_cons (step1977 p h) (sat_cons (step1133 p h) (sat_cons (step219 p h) (sat_cons (step943 p h) (sat_cons (step796 p h) (sat_cons (step785 p h) (sat_cons (step983 p h) (sat_cons (step802 p h) (sat_cons (step788 p h) (sat_cons (step813 p h) (sat_cons (step834 p h) (sat_cons (step839 p h) (sat_cons (step979 p h) (sat_cons (step2528 p h) (sat_cons (step949 p h) (sat_cons (step854 p h) (sat_cons (step2072 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2637 : List Lit := [(105, true), (1680, true), (1566, false)]
theorem step2637 (p : Nat → Bool) (h : Constraints p) : clause p c2637 = true :=
  Snake9.LocalRup.prove_clause [c2623, c1229, c1135, c833, c975, c2632, c2635, c852, c1104, c2636, c1955, c950, c944, c2072, c979, c854, c838, c2528] c2637 (by decide) p (sat_cons (step2623 p h) (sat_cons (step1229 p h) (sat_cons (step1135 p h) (sat_cons (step833 p h) (sat_cons (step975 p h) (sat_cons (step2632 p h) (sat_cons (step2635 p h) (sat_cons (step852 p h) (sat_cons (step1104 p h) (sat_cons (step2636 p h) (sat_cons (step1955 p h) (sat_cons (step950 p h) (sat_cons (step944 p h) (sat_cons (step2072 p h) (sat_cons (step979 p h) (sat_cons (step854 p h) (sat_cons (step838 p h) (sat_cons (step2528 p h) (sat_nil p)))))))))))))))))))
def c2638 : List Lit := [(1650, true), (116, true), (96, false), (1631, false)]
theorem step2638 (p : Nat → Bool) (h : Constraints p) : clause p c2638 = true :=
  Snake9.LocalRup.prove_clause [c2623, c2569, c1717, c891, c2442, c882, c387] c2638 (by decide) p (sat_cons (step2623 p h) (sat_cons (step2569 p h) (sat_cons (step1717 p h) (sat_cons (step891 p h) (sat_cons (step2442 p h) (sat_cons (step882 p h) (sat_cons (step387 p h) (sat_nil p))))))))
def c2639 : List Lit := [(102, false), (96, false), (1680, true), (1566, false)]
theorem step2639 (p : Nat → Bool) (h : Constraints p) : clause p c2639 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2557, c2623, c2637, c357, c368, c366, c1018, c367, c2014, c881, c2638, c934, c2590, c979, c853, c838, c2528] c2639 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2557 p h) (sat_cons (step2623 p h) (sat_cons (step2637 p h) (sat_cons (step357 p h) (sat_cons (step368 p h) (sat_cons (step366 p h) (sat_cons (step1018 p h) (sat_cons (step367 p h) (sat_cons (step2014 p h) (sat_cons (step881 p h) (sat_cons (step2638 p h) (sat_cons (step934 p h) (sat_cons (step2590 p h) (sat_cons (step979 p h) (sat_cons (step853 p h) (sat_cons (step838 p h) (sat_cons (step2528 p h) (sat_nil p)))))))))))))))))))
def c2640 : List Lit := [(1659, true), (104, false), (102, true), (96, false), (105, false)]
theorem step2640 (p : Nat → Bool) (h : Constraints p) : clause p c2640 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c1642, c852, c1516, c1093, c938, c2467, c1714] c2640 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step1642 p h) (sat_cons (step852 p h) (sat_cons (step1516 p h) (sat_cons (step1093 p h) (sat_cons (step938 p h) (sat_cons (step2467 p h) (sat_cons (step1714 p h) (sat_nil p))))))))))
def c2641 : List Lit := [(1625, true), (1600, true), (66, true), (102, true), (96, false)]
theorem step2641 (p : Nat → Bool) (h : Constraints p) : clause p c2641 = true :=
  Snake9.LocalRup.prove_clause [c2623, c852, c2254, c2597, c854, c838, c2528] c2641 (by decide) p (sat_cons (step2623 p h) (sat_cons (step852 p h) (sat_cons (step2254 p h) (sat_cons (step2597 p h) (sat_cons (step854 p h) (sat_cons (step838 p h) (sat_cons (step2528 p h) (sat_nil p))))))))
def c2642 : List Lit := [(1649, true), (109, false), (96, false), (1640, false), (1630, false)]
theorem step2642 (p : Nat → Bool) (h : Constraints p) : clause p c2642 = true :=
  Snake9.LocalRup.prove_clause [c2623, c1380, c2442] c2642 (by decide) p (sat_cons (step2623 p h) (sat_cons (step1380 p h) (sat_cons (step2442 p h) (sat_nil p))))
def c2643 : List Lit := [(1649, true), (104, false), (1630, false), (105, false), (1640, false), (96, false)]
theorem step2643 (p : Nat → Bool) (h : Constraints p) : clause p c2643 = true :=
  Snake9.LocalRup.prove_clause [c1714, c2642] c2643 (by decide) p (sat_cons (step1714 p h) (sat_cons (step2642 p h) (sat_nil p)))
def c2644 : List Lit := [(104, false), (96, false), (1680, true), (1566, false)]
theorem step2644 (p : Nat → Bool) (h : Constraints p) : clause p c2644 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2639, c2637, c1093, c1642, c1769, c2640, c979, c834, c2641, c2643, c945, c975, c1315, c833, c2528, c2598, c854] c2644 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2639 p h) (sat_cons (step2637 p h) (sat_cons (step1093 p h) (sat_cons (step1642 p h) (sat_cons (step1769 p h) (sat_cons (step2640 p h) (sat_cons (step979 p h) (sat_cons (step834 p h) (sat_cons (step2641 p h) (sat_cons (step2643 p h) (sat_cons (step945 p h) (sat_cons (step975 p h) (sat_cons (step1315 p h) (sat_cons (step833 p h) (sat_cons (step2528 p h) (sat_cons (step2598 p h) (sat_cons (step854 p h) (sat_nil p))))))))))))))))))))
def c2645 : List Lit := [(1600, false), (104, true), (1650, true), (102, true), (96, false), (105, false), (1680, true)]
theorem step2645 (p : Nat → Bool) (h : Constraints p) : clause p c2645 = true :=
  Snake9.LocalRup.prove_clause [c2623, c2577, c852, c1516, c1093, c979, c2468, c938, c1717, c1712, c881, c371] c2645 (by decide) p (sat_cons (step2623 p h) (sat_cons (step2577 p h) (sat_cons (step852 p h) (sat_cons (step1516 p h) (sat_cons (step1093 p h) (sat_cons (step979 p h) (sat_cons (step2468 p h) (sat_cons (step938 p h) (sat_cons (step1717 p h) (sat_cons (step1712 p h) (sat_cons (step881 p h) (sat_cons (step371 p h) (sat_nil p)))))))))))))
def c2646 : List Lit := [(109, false), (1649, true), (104, true), (96, false), (105, false)]
theorem step2646 (p : Nat → Bool) (h : Constraints p) : clause p c2646 = true :=
  Snake9.LocalRup.prove_clause [c2623, c2577, c1093, c2442, c2642, c387, c388, c897, c882, c893, c371, c901, c881, c921, c891] c2646 (by decide) p (sat_cons (step2623 p h) (sat_cons (step2577 p h) (sat_cons (step1093 p h) (sat_cons (step2442 p h) (sat_cons (step2642 p h) (sat_cons (step387 p h) (sat_cons (step388 p h) (sat_cons (step897 p h) (sat_cons (step882 p h) (sat_cons (step893 p h) (sat_cons (step371 p h) (sat_cons (step901 p h) (sat_cons (step881 p h) (sat_cons (step921 p h) (sat_cons (step891 p h) (sat_nil p))))))))))))))))
def c2647 : List Lit := [(1649, true), (104, true), (1650, true), (96, false), (105, false)]
theorem step2647 (p : Nat → Bool) (h : Constraints p) : clause p c2647 = true :=
  Snake9.LocalRup.prove_clause [c2623, c2577, c1093, c2646, c1717, c1712, c881, c371] c2647 (by decide) p (sat_cons (step2623 p h) (sat_cons (step2577 p h) (sat_cons (step1093 p h) (sat_cons (step2646 p h) (sat_cons (step1717 p h) (sat_cons (step1712 p h) (sat_cons (step881 p h) (sat_cons (step371 p h) (sat_nil p)))))))))
def c2648 : List Lit := [(66, false), (104, true), (1650, true), (96, false), (105, false)]
theorem step2648 (p : Nat → Bool) (h : Constraints p) : clause p c2648 = true :=
  Snake9.LocalRup.prove_clause [c2577, c360, c359, c2638, c881] c2648 (by decide) p (sat_cons (step2577 p h) (sat_cons (step360 p h) (sat_cons (step359 p h) (sat_cons (step2638 p h) (sat_cons (step881 p h) (sat_nil p))))))
def c2649 : List Lit := [(96, false), (1680, true), (1566, false)]
theorem step2649 (p : Nat → Bool) (h : Constraints p) : clause p c2649 = true :=
  Snake9.LocalRup.prove_clause [c2623, c2637, c2639, c852, c2590, c2644, c2645, c834, c2647, c2648, c2641, c945, c975, c1315, c833, c2528, c2598, c854] c2649 (by decide) p (sat_cons (step2623 p h) (sat_cons (step2637 p h) (sat_cons (step2639 p h) (sat_cons (step852 p h) (sat_cons (step2590 p h) (sat_cons (step2644 p h) (sat_cons (step2645 p h) (sat_cons (step834 p h) (sat_cons (step2647 p h) (sat_cons (step2648 p h) (sat_cons (step2641 p h) (sat_cons (step945 p h) (sat_cons (step975 p h) (sat_cons (step1315 p h) (sat_cons (step833 p h) (sat_cons (step2528 p h) (sat_cons (step2598 p h) (sat_cons (step854 p h) (sat_nil p)))))))))))))))))))
def c2650 : List Lit := [(109, false), (1649, true), (104, false), (1680, true), (1566, false)]
theorem step2650 (p : Nat → Bool) (h : Constraints p) : clause p c2650 = true :=
  Snake9.LocalRup.prove_clause [c2624, c2577, c2623, c1314, c970, c2637, c1093, c1730, c956, c871, c1020, c1248, c370, c366, c2649, c849, c2524, c2506, c401, c400, c854, c2072, c862, c859, c950, c851, c875, c975, c847, c833, c841, c842, c808, c207, c804, c793, c795, c802, c243, c796, c1250, c1132, c246] c2650 (by decide) p (sat_cons (step2624 p h) (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step1314 p h) (sat_cons (step970 p h) (sat_cons (step2637 p h) (sat_cons (step1093 p h) (sat_cons (step1730 p h) (sat_cons (step956 p h) (sat_cons (step871 p h) (sat_cons (step1020 p h) (sat_cons (step1248 p h) (sat_cons (step370 p h) (sat_cons (step366 p h) (sat_cons (step2649 p h) (sat_cons (step849 p h) (sat_cons (step2524 p h) (sat_cons (step2506 p h) (sat_cons (step401 p h) (sat_cons (step400 p h) (sat_cons (step854 p h) (sat_cons (step2072 p h) (sat_cons (step862 p h) (sat_cons (step859 p h) (sat_cons (step950 p h) (sat_cons (step851 p h) (sat_cons (step875 p h) (sat_cons (step975 p h) (sat_cons (step847 p h) (sat_cons (step833 p h) (sat_cons (step841 p h) (sat_cons (step842 p h) (sat_cons (step808 p h) (sat_cons (step207 p h) (sat_cons (step804 p h) (sat_cons (step793 p h) (sat_cons (step795 p h) (sat_cons (step802 p h) (sat_cons (step243 p h) (sat_cons (step796 p h) (sat_cons (step1250 p h) (sat_cons (step1132 p h) (sat_cons (step246 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c2651 : List Lit := [(1588, false), (104, false), (1680, true), (1566, false)]
theorem step2651 (p : Nat → Bool) (h : Constraints p) : clause p c2651 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2637, c1093, c1730, c2649, c366, c852, c1104, c944, c979, c1769, c833, c838, c975, c2528, c950, c854, c2072] c2651 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2637 p h) (sat_cons (step1093 p h) (sat_cons (step1730 p h) (sat_cons (step2649 p h) (sat_cons (step366 p h) (sat_cons (step852 p h) (sat_cons (step1104 p h) (sat_cons (step944 p h) (sat_cons (step979 p h) (sat_cons (step1769 p h) (sat_cons (step833 p h) (sat_cons (step838 p h) (sat_cons (step975 p h) (sat_cons (step2528 p h) (sat_cons (step950 p h) (sat_cons (step854 p h) (sat_cons (step2072 p h) (sat_nil p))))))))))))))))))))
def c2652 : List Lit := [(1649, true), (104, false), (1680, true), (1566, false)]
theorem step2652 (p : Nat → Bool) (h : Constraints p) : clause p c2652 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2651, c808, c1702, c2637, c1093, c1730, c2649, c366, c852, c1104, c944, c1769, c348, c370, c1642, c1689, c921, c889, c2650, c883, c884, c888, c917, c900, c902, c898, c893, c430, c1276, c1776, c1315, c2016, c2528, c950, c854, c2072] c2652 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2651 p h) (sat_cons (step808 p h) (sat_cons (step1702 p h) (sat_cons (step2637 p h) (sat_cons (step1093 p h) (sat_cons (step1730 p h) (sat_cons (step2649 p h) (sat_cons (step366 p h) (sat_cons (step852 p h) (sat_cons (step1104 p h) (sat_cons (step944 p h) (sat_cons (step1769 p h) (sat_cons (step348 p h) (sat_cons (step370 p h) (sat_cons (step1642 p h) (sat_cons (step1689 p h) (sat_cons (step921 p h) (sat_cons (step889 p h) (sat_cons (step2650 p h) (sat_cons (step883 p h) (sat_cons (step884 p h) (sat_cons (step888 p h) (sat_cons (step917 p h) (sat_cons (step900 p h) (sat_cons (step902 p h) (sat_cons (step898 p h) (sat_cons (step893 p h) (sat_cons (step430 p h) (sat_cons (step1276 p h) (sat_cons (step1776 p h) (sat_cons (step1315 p h) (sat_cons (step2016 p h) (sat_cons (step2528 p h) (sat_cons (step950 p h) (sat_cons (step854 p h) (sat_cons (step2072 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c2653 : List Lit := [(104, false), (1680, true), (1566, false)]
theorem step2653 (p : Nat → Bool) (h : Constraints p) : clause p c2653 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2649, c2637, c366, c1769, c852, c757, c1104, c2652, c2012, c945, c854, c975, c2528, c1315] c2653 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2649 p h) (sat_cons (step2637 p h) (sat_cons (step366 p h) (sat_cons (step1769 p h) (sat_cons (step852 p h) (sat_cons (step757 p h) (sat_cons (step1104 p h) (sat_cons (step2652 p h) (sat_cons (step2012 p h) (sat_cons (step945 p h) (sat_cons (step854 p h) (sat_cons (step975 p h) (sat_cons (step2528 p h) (sat_cons (step1315 p h) (sat_nil p)))))))))))))))))
def c2654 : List Lit := [(102, false), (1680, true), (1566, false)]
theorem step2654 (p : Nat → Bool) (h : Constraints p) : clause p c2654 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2653, c2649, c1784, c2637, c357, c368, c1018, c367, c2014, c881, c833, c1396, c975, c938, c945, c979, c1104, c838, c853, c2528] c2654 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2653 p h) (sat_cons (step2649 p h) (sat_cons (step1784 p h) (sat_cons (step2637 p h) (sat_cons (step357 p h) (sat_cons (step368 p h) (sat_cons (step1018 p h) (sat_cons (step367 p h) (sat_cons (step2014 p h) (sat_cons (step881 p h) (sat_cons (step833 p h) (sat_cons (step1396 p h) (sat_cons (step975 p h) (sat_cons (step938 p h) (sat_cons (step945 p h) (sat_cons (step979 p h) (sat_cons (step1104 p h) (sat_cons (step838 p h) (sat_cons (step853 p h) (sat_cons (step2528 p h) (sat_nil p)))))))))))))))))))))))
def c2655 : List Lit := [(1618, false), (1680, true), (1566, false)]
theorem step2655 (p : Nat → Bool) (h : Constraints p) : clause p c2655 = true :=
  Snake9.LocalRup.prove_clause [c2624, c2623, c2577, c1314, c970, c2637, c2653, c2278, c956, c871, c2649, c2072, c2077, c862, c950, c2512, c851, c975, c833, c808, c812, c788, c785, c2501, c2503, c802, c213, c796] c2655 (by decide) p (sat_cons (step2624 p h) (sat_cons (step2623 p h) (sat_cons (step2577 p h) (sat_cons (step1314 p h) (sat_cons (step970 p h) (sat_cons (step2637 p h) (sat_cons (step2653 p h) (sat_cons (step2278 p h) (sat_cons (step956 p h) (sat_cons (step871 p h) (sat_cons (step2649 p h) (sat_cons (step2072 p h) (sat_cons (step2077 p h) (sat_cons (step862 p h) (sat_cons (step950 p h) (sat_cons (step2512 p h) (sat_cons (step851 p h) (sat_cons (step975 p h) (sat_cons (step833 p h) (sat_cons (step808 p h) (sat_cons (step812 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_cons (step2501 p h) (sat_cons (step2503 p h) (sat_cons (step802 p h) (sat_cons (step213 p h) (sat_cons (step796 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2656 : List Lit := [(109, false), (1649, true), (99, false), (104, true), (105, false)]
theorem step2656 (p : Nat → Bool) (h : Constraints p) : clause p c2656 = true :=
  Snake9.LocalRup.prove_clause [c2623, c2577, c1093, c401, c2506, c418, c420, c2524, c882, c896, c371, c899, c881, c921, c891] c2656 (by decide) p (sat_cons (step2623 p h) (sat_cons (step2577 p h) (sat_cons (step1093 p h) (sat_cons (step401 p h) (sat_cons (step2506 p h) (sat_cons (step418 p h) (sat_cons (step420 p h) (sat_cons (step2524 p h) (sat_cons (step882 p h) (sat_cons (step896 p h) (sat_cons (step371 p h) (sat_cons (step899 p h) (sat_cons (step881 p h) (sat_cons (step921 p h) (sat_cons (step891 p h) (sat_nil p))))))))))))))))
def c2657 : List Lit := [(1649, true), (99, false), (1600, true), (1625, false), (104, true), (105, false)]
theorem step2657 (p : Nat → Bool) (h : Constraints p) : clause p c2657 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2656, c1641, c881, c359, c2528, c1315, c838, c1764, c808, c1702] c2657 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2656 p h) (sat_cons (step1641 p h) (sat_cons (step881 p h) (sat_cons (step359 p h) (sat_cons (step2528 p h) (sat_cons (step1315 p h) (sat_cons (step838 p h) (sat_cons (step1764 p h) (sat_cons (step808 p h) (sat_cons (step1702 p h) (sat_nil p)))))))))))))
def c2658 : List Lit := [(1680, true), (1566, false)]
theorem step2658 (p : Nat → Bool) (h : Constraints p) : clause p c2658 = true :=
  Snake9.LocalRup.prove_clause [c2624, c2577, c2623, c1314, c970, c2637, c2649, c849, c2653, c2278, c2654, c852, c1104, c858, c944, c979, c2655, c854, c2657, c951, c1669, c945, c870, c794, c975, c861, c801, c833, c1779, c851, c812, c808, c788, c804, c785, c795, c2503, c212] c2658 (by decide) p (sat_cons (step2624 p h) (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step1314 p h) (sat_cons (step970 p h) (sat_cons (step2637 p h) (sat_cons (step2649 p h) (sat_cons (step849 p h) (sat_cons (step2653 p h) (sat_cons (step2278 p h) (sat_cons (step2654 p h) (sat_cons (step852 p h) (sat_cons (step1104 p h) (sat_cons (step858 p h) (sat_cons (step944 p h) (sat_cons (step979 p h) (sat_cons (step2655 p h) (sat_cons (step854 p h) (sat_cons (step2657 p h) (sat_cons (step951 p h) (sat_cons (step1669 p h) (sat_cons (step945 p h) (sat_cons (step870 p h) (sat_cons (step794 p h) (sat_cons (step975 p h) (sat_cons (step861 p h) (sat_cons (step801 p h) (sat_cons (step833 p h) (sat_cons (step1779 p h) (sat_cons (step851 p h) (sat_cons (step812 p h) (sat_cons (step808 p h) (sat_cons (step788 p h) (sat_cons (step804 p h) (sat_cons (step785 p h) (sat_cons (step795 p h) (sat_cons (step2503 p h) (sat_cons (step212 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c2659 : List Lit := [(96, false), (1566, false)]
theorem step2659 (p : Nat → Bool) (h : Constraints p) : clause p c2659 = true :=
  Snake9.LocalRup.prove_clause [c2623, c2577, c2625, c2658, c1324, c2412, c2326, c347, c852, c1516, c348, c349, c881, c1705, c2507, c350, c342, c1375, c2491, c2638, c659, c939, c680, c681, c2496, c1355, c2641, c1299, c946, c723, c2499, c737, c833, c1702, c808] c2659 (by decide) p (sat_cons (step2623 p h) (sat_cons (step2577 p h) (sat_cons (step2625 p h) (sat_cons (step2658 p h) (sat_cons (step1324 p h) (sat_cons (step2412 p h) (sat_cons (step2326 p h) (sat_cons (step347 p h) (sat_cons (step852 p h) (sat_cons (step1516 p h) (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step881 p h) (sat_cons (step1705 p h) (sat_cons (step2507 p h) (sat_cons (step350 p h) (sat_cons (step342 p h) (sat_cons (step1375 p h) (sat_cons (step2491 p h) (sat_cons (step2638 p h) (sat_cons (step659 p h) (sat_cons (step939 p h) (sat_cons (step680 p h) (sat_cons (step681 p h) (sat_cons (step2496 p h) (sat_cons (step1355 p h) (sat_cons (step2641 p h) (sat_cons (step1299 p h) (sat_cons (step946 p h) (sat_cons (step723 p h) (sat_cons (step2499 p h) (sat_cons (step737 p h) (sat_cons (step833 p h) (sat_cons (step1702 p h) (sat_cons (step808 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c2660 : List Lit := [(1579, true), (1618, false), (1566, false)]
theorem step2660 (p : Nat → Bool) (h : Constraints p) : clause p c2660 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2658, c1324, c2412, c2326, c348, c1491, c2659, c2072, c951, c2499, c833, c808, c1702, c737, c2329, c760, c816, c789, c2014, c1315, c1314, c2509, c957, c849, c859, c875, c347, c852, c1104, c945, c969, c1325, c342, c757, c793, c794, c2501, c207, c2091, c2359, c2511, c1668, c1540, c317, c752, c749] c2660 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2658 p h) (sat_cons (step1324 p h) (sat_cons (step2412 p h) (sat_cons (step2326 p h) (sat_cons (step348 p h) (sat_cons (step1491 p h) (sat_cons (step2659 p h) (sat_cons (step2072 p h) (sat_cons (step951 p h) (sat_cons (step2499 p h) (sat_cons (step833 p h) (sat_cons (step808 p h) (sat_cons (step1702 p h) (sat_cons (step737 p h) (sat_cons (step2329 p h) (sat_cons (step760 p h) (sat_cons (step816 p h) (sat_cons (step789 p h) (sat_cons (step2014 p h) (sat_cons (step1315 p h) (sat_cons (step1314 p h) (sat_cons (step2509 p h) (sat_cons (step957 p h) (sat_cons (step849 p h) (sat_cons (step859 p h) (sat_cons (step875 p h) (sat_cons (step347 p h) (sat_cons (step852 p h) (sat_cons (step1104 p h) (sat_cons (step945 p h) (sat_cons (step969 p h) (sat_cons (step1325 p h) (sat_cons (step342 p h) (sat_cons (step757 p h) (sat_cons (step793 p h) (sat_cons (step794 p h) (sat_cons (step2501 p h) (sat_cons (step207 p h) (sat_cons (step2091 p h) (sat_cons (step2359 p h) (sat_cons (step2511 p h) (sat_cons (step1668 p h) (sat_cons (step1540 p h) (sat_cons (step317 p h) (sat_cons (step752 p h) (sat_cons (step749 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c2661 : List Lit := [(1618, false), (1566, false)]
theorem step2661 (p : Nat → Bool) (h : Constraints p) : clause p c2661 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2624, c2659, c1314, c2509, c2658, c1324, c2412, c2326, c348, c1491, c957, c871, c2072, c862, c951, c851, c2499, c833, c808, c2660, c801, c802, c812, c796, c788, c785, c786, c2503, c213] c2661 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2624 p h) (sat_cons (step2659 p h) (sat_cons (step1314 p h) (sat_cons (step2509 p h) (sat_cons (step2658 p h) (sat_cons (step1324 p h) (sat_cons (step2412 p h) (sat_cons (step2326 p h) (sat_cons (step348 p h) (sat_cons (step1491 p h) (sat_cons (step957 p h) (sat_cons (step871 p h) (sat_cons (step2072 p h) (sat_cons (step862 p h) (sat_cons (step951 p h) (sat_cons (step851 p h) (sat_cons (step2499 p h) (sat_cons (step833 p h) (sat_cons (step808 p h) (sat_cons (step2660 p h) (sat_cons (step801 p h) (sat_cons (step802 p h) (sat_cons (step812 p h) (sat_cons (step796 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step2503 p h) (sat_cons (step213 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2662 : List Lit := [(109, false), (1566, false)]
theorem step2662 (p : Nat → Bool) (h : Constraints p) : clause p c2662 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2658, c1324, c2412, c2326, c347, c852, c2659, c1104, c342, c2661, c854, c2528, c1315, c2499, c946, c348, c349, c881, c350, c401, c2506, c418, c420, c882, c898, c891, c900, c922] c2662 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2658 p h) (sat_cons (step1324 p h) (sat_cons (step2412 p h) (sat_cons (step2326 p h) (sat_cons (step347 p h) (sat_cons (step852 p h) (sat_cons (step2659 p h) (sat_cons (step1104 p h) (sat_cons (step342 p h) (sat_cons (step2661 p h) (sat_cons (step854 p h) (sat_cons (step2528 p h) (sat_cons (step1315 p h) (sat_cons (step2499 p h) (sat_cons (step946 p h) (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step881 p h) (sat_cons (step350 p h) (sat_cons (step401 p h) (sat_cons (step2506 p h) (sat_cons (step418 p h) (sat_cons (step420 p h) (sat_cons (step882 p h) (sat_cons (step898 p h) (sat_cons (step891 p h) (sat_cons (step900 p h) (sat_cons (step922 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2663 : List Lit := [(1566, false)]
theorem step2663 (p : Nat → Bool) (h : Constraints p) : clause p c2663 = true :=
  Snake9.LocalRup.prove_clause [c2577, c2623, c2624, c2658, c1324, c2412, c2326, c1705, c348, c342, c350, c349, c347, c1491, c2507, c897, c881, c852, c899, c2659, c1104, c1407, c2661, c854, c2528, c1315, c838, c2499, c808, c951, c946, c870, c926, c861, c892, c851, c2662, c884, c1884, c2512, c812, c788, c785, c2501, c2503, c802, c213, c796] c2663 (by decide) p (sat_cons (step2577 p h) (sat_cons (step2623 p h) (sat_cons (step2624 p h) (sat_cons (step2658 p h) (sat_cons (step1324 p h) (sat_cons (step2412 p h) (sat_cons (step2326 p h) (sat_cons (step1705 p h) (sat_cons (step348 p h) (sat_cons (step342 p h) (sat_cons (step350 p h) (sat_cons (step349 p h) (sat_cons (step347 p h) (sat_cons (step1491 p h) (sat_cons (step2507 p h) (sat_cons (step897 p h) (sat_cons (step881 p h) (sat_cons (step852 p h) (sat_cons (step899 p h) (sat_cons (step2659 p h) (sat_cons (step1104 p h) (sat_cons (step1407 p h) (sat_cons (step2661 p h) (sat_cons (step854 p h) (sat_cons (step2528 p h) (sat_cons (step1315 p h) (sat_cons (step838 p h) (sat_cons (step2499 p h) (sat_cons (step808 p h) (sat_cons (step951 p h) (sat_cons (step946 p h) (sat_cons (step870 p h) (sat_cons (step926 p h) (sat_cons (step861 p h) (sat_cons (step892 p h) (sat_cons (step851 p h) (sat_cons (step2662 p h) (sat_cons (step884 p h) (sat_cons (step1884 p h) (sat_cons (step2512 p h) (sat_cons (step812 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_cons (step2501 p h) (sat_cons (step2503 p h) (sat_cons (step802 p h) (sat_cons (step213 p h) (sat_cons (step796 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c2664 : List Lit := [(66, true)]
theorem step2664 (p : Nat → Bool) (h : Constraints p) : clause p c2664 = true :=
  Snake9.LocalRup.prove_clause [c2663, c2513] c2664 (by decide) p (sat_cons (step2663 p h) (sat_cons (step2513 p h) (sat_nil p)))
def c2665 : List Lit := [(105, true)]
theorem step2665 (p : Nat → Bool) (h : Constraints p) : clause p c2665 = true :=
  Snake9.LocalRup.prove_clause [c2664, c1229] c2665 (by decide) p (sat_cons (step2664 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c2666 : List Lit := [(65, true)]
theorem step2666 (p : Nat → Bool) (h : Constraints p) : clause p c2666 = true :=
  Snake9.LocalRup.prove_clause [c2664, c1230] c2666 (by decide) p (sat_cons (step2664 p h) (sat_cons (step1230 p h) (sat_nil p)))
def c2667 : List Lit := [(104, false)]
theorem step2667 (p : Nat → Bool) (h : Constraints p) : clause p c2667 = true :=
  Snake9.LocalRup.prove_clause [c2664, c2665, c2577, c358] c2667 (by decide) p (sat_cons (step2664 p h) (sat_cons (step2665 p h) (sat_cons (step2577 p h) (sat_cons (step358 p h) (sat_nil p)))))
def c2668 : List Lit := [(116, false)]
theorem step2668 (p : Nat → Bool) (h : Constraints p) : clause p c2668 = true :=
  Snake9.LocalRup.prove_clause [c2664, c2577, c2665, c360] c2668 (by decide) p (sat_cons (step2664 p h) (sat_cons (step2577 p h) (sat_cons (step2665 p h) (sat_cons (step360 p h) (sat_nil p)))))
def c2669 : List Lit := [(102, false)]
theorem step2669 (p : Nat → Bool) (h : Constraints p) : clause p c2669 = true :=
  Snake9.LocalRup.prove_clause [c2664, c2665, c2577, c357] c2669 (by decide) p (sat_cons (step2664 p h) (sat_cons (step2665 p h) (sat_cons (step2577 p h) (sat_cons (step357 p h) (sat_nil p)))))
def c2670 : List Lit := [(41, false)]
theorem step2670 (p : Nat → Bool) (h : Constraints p) : clause p c2670 = true :=
  Snake9.LocalRup.prove_clause [c2664, c2665, c2577, c342] c2670 (by decide) p (sat_cons (step2664 p h) (sat_cons (step2665 p h) (sat_cons (step2577 p h) (sat_cons (step342 p h) (sat_nil p)))))
def c2671 : List Lit := [(107, false)]
theorem step2671 (p : Nat → Bool) (h : Constraints p) : clause p c2671 = true :=
  Snake9.LocalRup.prove_clause [c2664, c2665, c2577, c359] c2671 (by decide) p (sat_cons (step2664 p h) (sat_cons (step2665 p h) (sat_cons (step2577 p h) (sat_cons (step359 p h) (sat_nil p)))))
def c2672 : List Lit := [(1565, true)]
theorem step2672 (p : Nat → Bool) (h : Constraints p) : clause p c2672 = true :=
  Snake9.LocalRup.prove_clause [c2664, c2560] c2672 (by decide) p (sat_cons (step2664 p h) (sat_cons (step2560 p h) (sat_nil p)))
def c2673 : List Lit := [(1538, true)]
theorem step2673 (p : Nat → Bool) (h : Constraints p) : clause p c2673 = true :=
  Snake9.LocalRup.prove_clause [c2670, c2326] c2673 (by decide) p (sat_cons (step2670 p h) (sat_cons (step2326 p h) (sat_nil p)))
def c2674 : List Lit := [(1486, true)]
theorem step2674 (p : Nat → Bool) (h : Constraints p) : clause p c2674 = true :=
  Snake9.LocalRup.prove_clause [c2670, c2623, c1159] c2674 (by decide) p (sat_cons (step2670 p h) (sat_cons (step2623 p h) (sat_cons (step1159 p h) (sat_nil p))))
def c2675 : List Lit := [(1631, true)]
theorem step2675 (p : Nat → Bool) (h : Constraints p) : clause p c2675 = true :=
  Snake9.LocalRup.prove_clause [c2671, c2667, c881] c2675 (by decide) p (sat_cons (step2671 p h) (sat_cons (step2667 p h) (sat_cons (step881 p h) (sat_nil p))))
def c2676 : List Lit := [(1597, true)]
theorem step2676 (p : Nat → Bool) (h : Constraints p) : clause p c2676 = true :=
  Snake9.LocalRup.prove_clause [c2672, c1313] c2676 (by decide) p (sat_cons (step2672 p h) (sat_cons (step1313 p h) (sat_nil p)))
def c2677 : List Lit := [(1680, false)]
theorem step2677 (p : Nat → Bool) (h : Constraints p) : clause p c2677 = true :=
  Snake9.LocalRup.prove_clause [c2673, c1324] c2677 (by decide) p (sat_cons (step2673 p h) (sat_cons (step1324 p h) (sat_nil p)))
def c2678 : List Lit := [(1649, true)]
theorem step2678 (p : Nat → Bool) (h : Constraints p) : clause p c2678 = true :=
  Snake9.LocalRup.prove_clause [c2675, c2668, c1396] c2678 (by decide) p (sat_cons (step2675 p h) (sat_cons (step2668 p h) (sat_cons (step1396 p h) (sat_nil p))))
def c2679 : List Lit := [(1662, false)]
theorem step2679 (p : Nat → Bool) (h : Constraints p) : clause p c2679 = true :=
  Snake9.LocalRup.prove_clause [c2677, c2676, c966] c2679 (by decide) p (sat_cons (step2677 p h) (sat_cons (step2676 p h) (sat_cons (step966 p h) (sat_nil p))))
def c2680 : List Lit := [(1627, false)]
theorem step2680 (p : Nat → Bool) (h : Constraints p) : clause p c2680 = true :=
  Snake9.LocalRup.prove_clause [c2678, c2679, c957] c2680 (by decide) p (sat_cons (step2678 p h) (sat_cons (step2679 p h) (sat_cons (step957 p h) (sat_nil p))))
def c2681 : List Lit := [(1622, false)]
theorem step2681 (p : Nat → Bool) (h : Constraints p) : clause p c2681 = true :=
  Snake9.LocalRup.prove_clause [c2680, c2624, c871] c2681 (by decide) p (sat_cons (step2680 p h) (sat_cons (step2624 p h) (sat_cons (step871 p h) (sat_nil p))))
def c2682 : List Lit := [(1618, false), (96, false)]
theorem step2682 (p : Nat → Bool) (h : Constraints p) : clause p c2682 = true :=
  Snake9.LocalRup.prove_clause [c2675, c2668, c2679, c2624, c2663, c2674, c2677, c2577, c2494, c2489, c760, c1117, c723, c2638, c952, c870, c2254, c859, c946, c850, c2551, c808, c1754, c2512, c812, c788, c785, c2501, c2503, c802, c213, c796] c2682 (by decide) p (sat_cons (step2675 p h) (sat_cons (step2668 p h) (sat_cons (step2679 p h) (sat_cons (step2624 p h) (sat_cons (step2663 p h) (sat_cons (step2674 p h) (sat_cons (step2677 p h) (sat_cons (step2577 p h) (sat_cons (step2494 p h) (sat_cons (step2489 p h) (sat_cons (step760 p h) (sat_cons (step1117 p h) (sat_cons (step723 p h) (sat_cons (step2638 p h) (sat_cons (step952 p h) (sat_cons (step870 p h) (sat_cons (step2254 p h) (sat_cons (step859 p h) (sat_cons (step946 p h) (sat_cons (step850 p h) (sat_cons (step2551 p h) (sat_cons (step808 p h) (sat_cons (step1754 p h) (sat_cons (step2512 p h) (sat_cons (step812 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_cons (step2501 p h) (sat_cons (step2503 p h) (sat_cons (step802 p h) (sat_cons (step213 p h) (sat_cons (step796 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c2683 : List Lit := [(99, false)]
theorem step2683 (p : Nat → Bool) (h : Constraints p) : clause p c2683 = true :=
  Snake9.LocalRup.prove_clause [c2663, c2623, c2666, c1738, c1751, c765, c2497, c758] c2683 (by decide) p (sat_cons (step2663 p h) (sat_cons (step2623 p h) (sat_cons (step2666 p h) (sat_cons (step1738 p h) (sat_cons (step1751 p h) (sat_cons (step765 p h) (sat_cons (step2497 p h) (sat_cons (step758 p h) (sat_nil p)))))))))
def c2684 : List Lit := [(1618, true)]
theorem step2684 (p : Nat → Bool) (h : Constraints p) : clause p c2684 = true :=
  Snake9.LocalRup.prove_clause [c2683, c2669, c854] c2684 (by decide) p (sat_cons (step2683 p h) (sat_cons (step2669 p h) (sat_cons (step854 p h) (sat_nil p))))
def c2685 : List Lit := [(1625, true)]
theorem step2685 (p : Nat → Bool) (h : Constraints p) : clause p c2685 = true :=
  Snake9.LocalRup.prove_clause [c2684, c2254] c2685 (by decide) p (sat_cons (step2684 p h) (sat_cons (step2254 p h) (sat_nil p)))
def c2686 : List Lit := [(1616, false)]
theorem step2686 (p : Nat → Bool) (h : Constraints p) : clause p c2686 = true :=
  Snake9.LocalRup.prove_clause [c2684, c2681, c862] c2686 (by decide) p (sat_cons (step2684 p h) (sat_cons (step2681 p h) (sat_cons (step862 p h) (sat_nil p))))
def c2687 : List Lit := [(96, false)]
theorem step2687 (p : Nat → Bool) (h : Constraints p) : clause p c2687 = true :=
  Snake9.LocalRup.prove_clause [c2684, c2682] c2687 (by decide) p (sat_cons (step2684 p h) (sat_cons (step2682 p h) (sat_nil p)))
def c2688 : List Lit := [(93, true)]
theorem step2688 (p : Nat → Bool) (h : Constraints p) : clause p c2688 = true :=
  Snake9.LocalRup.prove_clause [c2686, c2687, c851] c2688 (by decide) p (sat_cons (step2686 p h) (sat_cons (step2687 p h) (sat_cons (step851 p h) (sat_nil p))))
def c2689 : List Lit := [(1626, true)]
theorem step2689 (p : Nat → Bool) (h : Constraints p) : clause p c2689 = true :=
  Snake9.LocalRup.prove_clause [c2687, c2684, c2072] c2689 (by decide) p (sat_cons (step2687 p h) (sat_cons (step2684 p h) (sat_cons (step2072 p h) (sat_nil p))))
def c2690 : List Lit := [(1575, false)]
theorem step2690 (p : Nat → Bool) (h : Constraints p) : clause p c2690 = true :=
  Snake9.LocalRup.prove_clause [c2687, c2623, c2684, c2663, c2675, c2665, c2577, c2677, c2678, c2685, c2083] c2690 (by decide) p (sat_cons (step2687 p h) (sat_cons (step2623 p h) (sat_cons (step2684 p h) (sat_cons (step2663 p h) (sat_cons (step2675 p h) (sat_cons (step2665 p h) (sat_cons (step2577 p h) (sat_cons (step2677 p h) (sat_cons (step2678 p h) (sat_cons (step2685 p h) (sat_cons (step2083 p h) (sat_nil p))))))))))))
def c2691 : List Lit := [(1661, true)]
theorem step2691 (p : Nat → Bool) (h : Constraints p) : clause p c2691 = true :=
  Snake9.LocalRup.prove_clause [c2689, c2678, c951] c2691 (by decide) p (sat_cons (step2689 p h) (sat_cons (step2678 p h) (sat_cons (step951 p h) (sat_nil p))))
def c2692 : List Lit := [(1573, false)]
theorem step2692 (p : Nat → Bool) (h : Constraints p) : clause p c2692 = true :=
  Snake9.LocalRup.prove_clause [c2690, c788] c2692 (by decide) p (sat_cons (step2690 p h) (sat_cons (step788 p h) (sat_nil p)))
def c2693 : List Lit := [(1598, false)]
theorem step2693 (p : Nat → Bool) (h : Constraints p) : clause p c2693 = true :=
  Snake9.LocalRup.prove_clause [c2691, c2677, c970] c2693 (by decide) p (sat_cons (step2691 p h) (sat_cons (step2677 p h) (sat_cons (step970 p h) (sat_nil p))))
def c2694 : List Lit := [(78, true)]
theorem step2694 (p : Nat → Bool) (h : Constraints p) : clause p c2694 = true :=
  Snake9.LocalRup.prove_clause [c2692, c785] c2694 (by decide) p (sat_cons (step2692 p h) (sat_cons (step785 p h) (sat_nil p)))
def c2695 : List Lit := [(77, true)]
theorem step2695 (p : Nat → Bool) (h : Constraints p) : clause p c2695 = true :=
  Snake9.LocalRup.prove_clause [c2692, c786] c2695 (by decide) p (sat_cons (step2692 p h) (sat_cons (step786 p h) (sat_nil p)))
def c2696 : List Lit := [(1579, true)]
theorem step2696 (p : Nat → Bool) (h : Constraints p) : clause p c2696 = true :=
  Snake9.LocalRup.prove_clause [c2692, c2501] c2696 (by decide) p (sat_cons (step2692 p h) (sat_cons (step2501 p h) (sat_nil p)))
def c2697 : List Lit := [(1588, false)]
theorem step2697 (p : Nat → Bool) (h : Constraints p) : clause p c2697 = true :=
  Snake9.LocalRup.prove_clause [c2693, c2691, c2577, c2665, c2623, c2296] c2697 (by decide) p (sat_cons (step2693 p h) (sat_cons (step2691 p h) (sat_cons (step2577 p h) (sat_cons (step2665 p h) (sat_cons (step2623 p h) (sat_cons (step2296 p h) (sat_nil p)))))))
def c2698 : List Lit := [(83, true)]
theorem step2698 (p : Nat → Bool) (h : Constraints p) : clause p c2698 = true :=
  Snake9.LocalRup.prove_clause [c2694, c2695, c2503] c2698 (by decide) p (sat_cons (step2694 p h) (sat_cons (step2695 p h) (sat_cons (step2503 p h) (sat_nil p))))
def c2699 : List Lit := [(1584, false)]
theorem step2699 (p : Nat → Bool) (h : Constraints p) : clause p c2699 = true :=
  Snake9.LocalRup.prove_clause [c2697, c808] c2699 (by decide) p (sat_cons (step2697 p h) (sat_cons (step808 p h) (sat_nil p)))
end B112E096
