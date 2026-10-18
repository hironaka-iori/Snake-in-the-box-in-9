import B112E159Inputs
namespace B112E159
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1005 : List Lit := [(11, true)]
theorem step1005 (p : Nat → Bool) (h : Constraints p) : clause p c1005 = true :=
  Snake9.LocalRup.prove_clause [c17, c16] c1005 (by decide) p (sat_cons (step17 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1006 : List Lit := [(9, false), (6, false), (8, false)]
theorem step1006 (p : Nat → Bool) (h : Constraints p) : clause p c1006 = true :=
  Snake9.LocalRup.prove_clause [c1005, c19] c1006 (by decide) p (sat_cons (step1005 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1007 : List Lit := [(9, false), (6, false), (83, false)]
theorem step1007 (p : Nat → Bool) (h : Constraints p) : clause p c1007 = true :=
  Snake9.LocalRup.prove_clause [c1005, c20] c1007 (by decide) p (sat_cons (step1005 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1008 : List Lit := [(10, false), (8, false), (52, false)]
theorem step1008 (p : Nat → Bool) (h : Constraints p) : clause p c1008 = true :=
  Snake9.LocalRup.prove_clause [c1005, c21] c1008 (by decide) p (sat_cons (step1005 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1009 : List Lit := [(9, false), (10, false)]
theorem step1009 (p : Nat → Bool) (h : Constraints p) : clause p c1009 = true :=
  Snake9.LocalRup.prove_clause [c1005, c17, c23] c1009 (by decide) p (sat_cons (step1005 p h) (sat_cons (step17 p h) (sat_cons (step23 p h) (sat_nil p))))
def c1010 : List Lit := [(129, true), (9, true), (10, true)]
theorem step1010 (p : Nat → Bool) (h : Constraints p) : clause p c1010 = true :=
  Snake9.LocalRup.prove_clause [c1005, c24] c1010 (by decide) p (sat_cons (step1005 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1011 : List Lit := [(1, false)]
theorem step1011 (p : Nat → Bool) (h : Constraints p) : clause p c1011 = true :=
  Snake9.LocalRup.prove_clause [c390, c1] c1011 (by decide) p (sat_cons (step390 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1012 : List Lit := [(54, false)]
theorem step1012 (p : Nat → Bool) (h : Constraints p) : clause p c1012 = true :=
  Snake9.LocalRup.prove_clause [c410, c261] c1012 (by decide) p (sat_cons (step410 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1013 : List Lit := [(466, false)]
theorem step1013 (p : Nat → Bool) (h : Constraints p) : clause p c1013 = true :=
  Snake9.LocalRup.prove_clause [c566, c563] c1013 (by decide) p (sat_cons (step566 p h) (sat_cons (step563 p h) (sat_nil p)))
def c1014 : List Lit := [(350, false)]
theorem step1014 (p : Nat → Bool) (h : Constraints p) : clause p c1014 = true :=
  Snake9.LocalRup.prove_clause [c566, c565] c1014 (by decide) p (sat_cons (step566 p h) (sat_cons (step565 p h) (sat_nil p)))
def c1015 : List Lit := [(406, false)]
theorem step1015 (p : Nat → Bool) (h : Constraints p) : clause p c1015 = true :=
  Snake9.LocalRup.prove_clause [c1013, c562] c1015 (by decide) p (sat_cons (step1013 p h) (sat_cons (step562 p h) (sat_nil p)))
def c1016 : List Lit := [(348, false)]
theorem step1016 (p : Nat → Bool) (h : Constraints p) : clause p c1016 = true :=
  Snake9.LocalRup.prove_clause [c1014, c505] c1016 (by decide) p (sat_cons (step1014 p h) (sat_cons (step505 p h) (sat_nil p)))
def c1017 : List Lit := [(292, false)]
theorem step1017 (p : Nat → Bool) (h : Constraints p) : clause p c1017 = true :=
  Snake9.LocalRup.prove_clause [c1014, c508] c1017 (by decide) p (sat_cons (step1014 p h) (sat_cons (step508 p h) (sat_nil p)))
def c1018 : List Lit := [(404, false)]
theorem step1018 (p : Nat → Bool) (h : Constraints p) : clause p c1018 = true :=
  Snake9.LocalRup.prove_clause [c1015, c527] c1018 (by decide) p (sat_cons (step1015 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1019 : List Lit := [(376, false)]
theorem step1019 (p : Nat → Bool) (h : Constraints p) : clause p c1019 = true :=
  Snake9.LocalRup.prove_clause [c1015, c529] c1019 (by decide) p (sat_cons (step1015 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1020 : List Lit := [(346, false)]
theorem step1020 (p : Nat → Bool) (h : Constraints p) : clause p c1020 = true :=
  Snake9.LocalRup.prove_clause [c1016, c502] c1020 (by decide) p (sat_cons (step1016 p h) (sat_cons (step502 p h) (sat_nil p)))
def c1021 : List Lit := [(318, false)]
theorem step1021 (p : Nat → Bool) (h : Constraints p) : clause p c1021 = true :=
  Snake9.LocalRup.prove_clause [c1016, c504] c1021 (by decide) p (sat_cons (step1016 p h) (sat_cons (step504 p h) (sat_nil p)))
def c1022 : List Lit := [(262, false)]
theorem step1022 (p : Nat → Bool) (h : Constraints p) : clause p c1022 = true :=
  Snake9.LocalRup.prove_clause [c1017, c466] c1022 (by decide) p (sat_cons (step1017 p h) (sat_cons (step466 p h) (sat_nil p)))
def c1023 : List Lit := [(362, false)]
theorem step1023 (p : Nat → Bool) (h : Constraints p) : clause p c1023 = true :=
  Snake9.LocalRup.prove_clause [c1019, c516] c1023 (by decide) p (sat_cons (step1019 p h) (sat_cons (step516 p h) (sat_nil p)))
def c1024 : List Lit := [(344, false)]
theorem step1024 (p : Nat → Bool) (h : Constraints p) : clause p c1024 = true :=
  Snake9.LocalRup.prove_clause [c1020, c499] c1024 (by decide) p (sat_cons (step1020 p h) (sat_cons (step499 p h) (sat_nil p)))
def c1025 : List Lit := [(316, false)]
theorem step1025 (p : Nat → Bool) (h : Constraints p) : clause p c1025 = true :=
  Snake9.LocalRup.prove_clause [c1021, c478] c1025 (by decide) p (sat_cons (step1021 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1026 : List Lit := [(248, false)]
theorem step1026 (p : Nat → Bool) (h : Constraints p) : clause p c1026 = true :=
  Snake9.LocalRup.prove_clause [c1022, c449] c1026 (by decide) p (sat_cons (step1022 p h) (sat_cons (step449 p h) (sat_nil p)))
def c1027 : List Lit := [(342, false)]
theorem step1027 (p : Nat → Bool) (h : Constraints p) : clause p c1027 = true :=
  Snake9.LocalRup.prove_clause [c1024, c495] c1027 (by decide) p (sat_cons (step1024 p h) (sat_cons (step495 p h) (sat_nil p)))
def c1028 : List Lit := [(314, false)]
theorem step1028 (p : Nat → Bool) (h : Constraints p) : clause p c1028 = true :=
  Snake9.LocalRup.prove_clause [c1025, c476] c1028 (by decide) p (sat_cons (step1025 p h) (sat_cons (step476 p h) (sat_nil p)))
def c1029 : List Lit := [(312, false)]
theorem step1029 (p : Nat → Bool) (h : Constraints p) : clause p c1029 = true :=
  Snake9.LocalRup.prove_clause [c1028, c474] c1029 (by decide) p (sat_cons (step1028 p h) (sat_cons (step474 p h) (sat_nil p)))
def c1030 : List Lit := [(803, true)]
theorem step1030 (p : Nat → Bool) (h : Constraints p) : clause p c1030 = true :=
  Snake9.LocalRup.prove_clause [c1011, c570] c1030 (by decide) p (sat_cons (step1011 p h) (sat_cons (step570 p h) (sat_nil p)))
def c1031 : List Lit := [(801, false), (804, true)]
theorem step1031 (p : Nat → Bool) (h : Constraints p) : clause p c1031 = true :=
  Snake9.LocalRup.prove_clause [c1011, c571] c1031 (by decide) p (sat_cons (step1011 p h) (sat_cons (step571 p h) (sat_nil p)))
def c1032 : List Lit := [(802, false), (805, true)]
theorem step1032 (p : Nat → Bool) (h : Constraints p) : clause p c1032 = true :=
  Snake9.LocalRup.prove_clause [c1011, c572] c1032 (by decide) p (sat_cons (step1011 p h) (sat_cons (step572 p h) (sat_nil p)))
def c1033 : List Lit := [(814, true)]
theorem step1033 (p : Nat → Bool) (h : Constraints p) : clause p c1033 = true :=
  Snake9.LocalRup.prove_clause [c1030, c580] c1033 (by decide) p (sat_cons (step1030 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1034 : List Lit := [(810, false), (815, true)]
theorem step1034 (p : Nat → Bool) (h : Constraints p) : clause p c1034 = true :=
  Snake9.LocalRup.prove_clause [c1030, c581] c1034 (by decide) p (sat_cons (step1030 p h) (sat_cons (step581 p h) (sat_nil p)))
def c1035 : List Lit := [(811, false), (816, true)]
theorem step1035 (p : Nat → Bool) (h : Constraints p) : clause p c1035 = true :=
  Snake9.LocalRup.prove_clause [c1030, c582] c1035 (by decide) p (sat_cons (step1030 p h) (sat_cons (step582 p h) (sat_nil p)))
def c1036 : List Lit := [(835, false), (843, true)]
theorem step1036 (p : Nat → Bool) (h : Constraints p) : clause p c1036 = true :=
  Snake9.LocalRup.prove_clause [c1033, c625] c1036 (by decide) p (sat_cons (step1033 p h) (sat_cons (step625 p h) (sat_nil p)))
def c1037 : List Lit := [(885, true)]
theorem step1037 (p : Nat → Bool) (h : Constraints p) : clause p c1037 = true :=
  Snake9.LocalRup.prove_clause [c1012, c697] c1037 (by decide) p (sat_cons (step1012 p h) (sat_cons (step697 p h) (sat_nil p)))
def c1038 : List Lit := [(55, true), (886, true)]
theorem step1038 (p : Nat → Bool) (h : Constraints p) : clause p c1038 = true :=
  Snake9.LocalRup.prove_clause [c1012, c698] c1038 (by decide) p (sat_cons (step1012 p h) (sat_cons (step698 p h) (sat_nil p)))
def c1039 : List Lit := [(887, true)]
theorem step1039 (p : Nat → Bool) (h : Constraints p) : clause p c1039 = true :=
  Snake9.LocalRup.prove_clause [c1037, c699] c1039 (by decide) p (sat_cons (step1037 p h) (sat_cons (step699 p h) (sat_nil p)))
def c1040 : List Lit := [(883, false), (888, true)]
theorem step1040 (p : Nat → Bool) (h : Constraints p) : clause p c1040 = true :=
  Snake9.LocalRup.prove_clause [c1037, c701] c1040 (by decide) p (sat_cons (step1037 p h) (sat_cons (step701 p h) (sat_nil p)))
def c1041 : List Lit := [(884, false), (889, true)]
theorem step1041 (p : Nat → Bool) (h : Constraints p) : clause p c1041 = true :=
  Snake9.LocalRup.prove_clause [c1037, c704] c1041 (by decide) p (sat_cons (step1037 p h) (sat_cons (step704 p h) (sat_nil p)))
def c1042 : List Lit := [(879, false), (892, true)]
theorem step1042 (p : Nat → Bool) (h : Constraints p) : clause p c1042 = true :=
  Snake9.LocalRup.prove_clause [c1039, c709] c1042 (by decide) p (sat_cons (step1039 p h) (sat_cons (step709 p h) (sat_nil p)))
def c1043 : List Lit := [(880, false), (893, true)]
theorem step1043 (p : Nat → Bool) (h : Constraints p) : clause p c1043 = true :=
  Snake9.LocalRup.prove_clause [c1039, c713] c1043 (by decide) p (sat_cons (step1039 p h) (sat_cons (step713 p h) (sat_nil p)))
def c1044 : List Lit := [(881, false), (894, true)]
theorem step1044 (p : Nat → Bool) (h : Constraints p) : clause p c1044 = true :=
  Snake9.LocalRup.prove_clause [c1039, c717] c1044 (by decide) p (sat_cons (step1039 p h) (sat_cons (step717 p h) (sat_nil p)))
def c1045 : List Lit := [(882, false), (895, true)]
theorem step1045 (p : Nat → Bool) (h : Constraints p) : clause p c1045 = true :=
  Snake9.LocalRup.prove_clause [c1039, c721] c1045 (by decide) p (sat_cons (step1039 p h) (sat_cons (step721 p h) (sat_nil p)))
def c1046 : List Lit := [(25, false), (22, false), (27, true), (143, true)]
theorem step1046 (p : Nat → Bool) (h : Constraints p) : clause p c1046 = true :=
  Snake9.LocalRup.prove_clause [c87, c88, c989] c1046 (by decide) p (sat_cons (step87 p h) (sat_cons (step88 p h) (sat_cons (step989 p h) (sat_nil p))))
def c1047 : List Lit := [(27, true), (25, false), (143, true), (26, true)]
theorem step1047 (p : Nat → Bool) (h : Constraints p) : clause p c1047 = true :=
  Snake9.LocalRup.prove_clause [c399, c88, c1046, c82] c1047 (by decide) p (sat_cons (step399 p h) (sat_cons (step88 p h) (sat_cons (step1046 p h) (sat_cons (step82 p h) (sat_nil p)))))
def c1048 : List Lit := [(808, true)]
theorem step1048 (p : Nat → Bool) (h : Constraints p) : clause p c1048 = true :=
  Snake9.LocalRup.prove_clause [c574, c575, c1009] c1048 (by decide) p (sat_cons (step574 p h) (sat_cons (step575 p h) (sat_cons (step1009 p h) (sat_nil p))))
def c1049 : List Lit := [(810, true)]
theorem step1049 (p : Nat → Bool) (h : Constraints p) : clause p c1049 = true :=
  Snake9.LocalRup.prove_clause [c1048, c577] c1049 (by decide) p (sat_cons (step1048 p h) (sat_cons (step577 p h) (sat_nil p)))
def c1050 : List Lit := [(815, true)]
theorem step1050 (p : Nat → Bool) (h : Constraints p) : clause p c1050 = true :=
  Snake9.LocalRup.prove_clause [c1049, c1034] c1050 (by decide) p (sat_cons (step1049 p h) (sat_cons (step1034 p h) (sat_nil p)))
def c1051 : List Lit := [(836, true), (828, false), (14, true), (20, false), (21, false)]
theorem step1051 (p : Nat → Bool) (h : Constraints p) : clause p c1051 = true :=
  Snake9.LocalRup.prove_clause [c601, c588, c590, c619, c615, c591, c604, c589, c596, c64] c1051 (by decide) p (sat_cons (step601 p h) (sat_cons (step588 p h) (sat_cons (step590 p h) (sat_cons (step619 p h) (sat_cons (step615 p h) (sat_cons (step591 p h) (sat_cons (step604 p h) (sat_cons (step589 p h) (sat_cons (step596 p h) (sat_cons (step64 p h) (sat_nil p)))))))))))
def c1052 : List Lit := [(1024, true), (94, false), (95, false)]
theorem step1052 (p : Nat → Bool) (h : Constraints p) : clause p c1052 = true :=
  Snake9.LocalRup.prove_clause [c432, c911, c913, c908, c909, c905, c906, c388, c330, c364, c366] c1052 (by decide) p (sat_cons (step432 p h) (sat_cons (step911 p h) (sat_cons (step913 p h) (sat_cons (step908 p h) (sat_cons (step909 p h) (sat_cons (step905 p h) (sat_cons (step906 p h) (sat_cons (step388 p h) (sat_cons (step330 p h) (sat_cons (step364 p h) (sat_cons (step366 p h) (sat_nil p))))))))))))
def c1053 : List Lit := [(84, false), (88, false), (98, false)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true :=
  Snake9.LocalRup.prove_clause [c421, c300, c317] c1053 (by decide) p (sat_cons (step421 p h) (sat_cons (step300 p h) (sat_cons (step317 p h) (sat_nil p))))
def c1054 : List Lit := [(816, true), (40, true), (52, false)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true :=
  Snake9.LocalRup.prove_clause [c1049, c1048, c393, c1035, c583, c578, c579, c1031, c573, c567, c10, c9, c12, c1008, c576] c1054 (by decide) p (sat_cons (step1049 p h) (sat_cons (step1048 p h) (sat_cons (step393 p h) (sat_cons (step1035 p h) (sat_cons (step583 p h) (sat_cons (step578 p h) (sat_cons (step579 p h) (sat_cons (step1031 p h) (sat_cons (step573 p h) (sat_cons (step567 p h) (sat_cons (step10 p h) (sat_cons (step9 p h) (sat_cons (step12 p h) (sat_cons (step1008 p h) (sat_cons (step576 p h) (sat_nil p))))))))))))))))
def c1055 : List Lit := [(811, true), (40, true), (52, false)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true :=
  Snake9.LocalRup.prove_clause [c1048, c393, c578, c579, c573, c10, c9, c1008, c1006, c576] c1055 (by decide) p (sat_cons (step1048 p h) (sat_cons (step393 p h) (sat_cons (step578 p h) (sat_cons (step579 p h) (sat_cons (step573 p h) (sat_cons (step10 p h) (sat_cons (step9 p h) (sat_cons (step1008 p h) (sat_cons (step1006 p h) (sat_cons (step576 p h) (sat_nil p)))))))))))
def c1056 : List Lit := [(97, true), (848, true), (857, false), (822, false), (18, false), (830, false), (20, false), (111, true), (112, false), (51, true), (116, false), (52, false), (115, false), (1024, false), (88, false), (94, false), (98, false), (1000, true), (1006, false)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true :=
  Snake9.TreeRup.prove_clause [c427, c423, c392, c391, c1011, c566, c428, c430, c977, c426, c694, c1040, c1053, c826, c828, c833, c339, c315, c871, c38, c46, c40, c594, c656, c623, c658, c639, c671, c1054, c634, c1055, c584, c1031, c567, c568, c6, c7, c978, c5, c681, c3, c688, c435, c710, c436, c439, c447, c464, c506, c564, c559, c557, c558, c555, c556, c541, c553, c546, c539, c552, c545, c538, c549, c543, c537, c384, c361, c345, c346, c350, c349, c894, c733, c348, c903, c778, c355, c925, c973, c378, c938, c337, c954, c344, c847, c796, c804, c801] c1056 (by decide) p (sat_cons (step427 p h) (sat_cons (step423 p h) (sat_cons (step392 p h) (sat_cons (step391 p h) (sat_cons (step1011 p h) (sat_cons (step566 p h) (sat_cons (step428 p h) (sat_cons (step430 p h) (sat_cons (step977 p h) (sat_cons (step426 p h) (sat_cons (step694 p h) (sat_cons (step1040 p h) (sat_cons (step1053 p h) (sat_cons (step826 p h) (sat_cons (step828 p h) (sat_cons (step833 p h) (sat_cons (step339 p h) (sat_cons (step315 p h) (sat_cons (step871 p h) (sat_cons (step38 p h) (sat_cons (step46 p h) (sat_cons (step40 p h) (sat_cons (step594 p h) (sat_cons (step656 p h) (sat_cons (step623 p h) (sat_cons (step658 p h) (sat_cons (step639 p h) (sat_cons (step671 p h) (sat_cons (step1054 p h) (sat_cons (step634 p h) (sat_cons (step1055 p h) (sat_cons (step584 p h) (sat_cons (step1031 p h) (sat_cons (step567 p h) (sat_cons (step568 p h) (sat_cons (step6 p h) (sat_cons (step7 p h) (sat_cons (step978 p h) (sat_cons (step5 p h) (sat_cons (step681 p h) (sat_cons (step3 p h) (sat_cons (step688 p h) (sat_cons (step435 p h) (sat_cons (step710 p h) (sat_cons (step436 p h) (sat_cons (step439 p h) (sat_cons (step447 p h) (sat_cons (step464 p h) (sat_cons (step506 p h) (sat_cons (step564 p h) (sat_cons (step559 p h) (sat_cons (step557 p h) (sat_cons (step558 p h) (sat_cons (step555 p h) (sat_cons (step556 p h) (sat_cons (step541 p h) (sat_cons (step553 p h) (sat_cons (step546 p h) (sat_cons (step539 p h) (sat_cons (step552 p h) (sat_cons (step545 p h) (sat_cons (step538 p h) (sat_cons (step549 p h) (sat_cons (step543 p h) (sat_cons (step537 p h) (sat_cons (step384 p h) (sat_cons (step361 p h) (sat_cons (step345 p h) (sat_cons (step346 p h) (sat_cons (step350 p h) (sat_cons (step349 p h) (sat_cons (step894 p h) (sat_cons (step733 p h) (sat_cons (step348 p h) (sat_cons (step903 p h) (sat_cons (step778 p h) (sat_cons (step355 p h) (sat_cons (step925 p h) (sat_cons (step973 p h) (sat_cons (step378 p h) (sat_cons (step938 p h) (sat_cons (step337 p h) (sat_cons (step954 p h) (sat_cons (step344 p h) (sat_cons (step847 p h) (sat_cons (step796 p h) (sat_cons (step804 p h) (sat_cons (step801 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1057 : List Lit := [(848, true), (857, false), (822, false), (18, false), (830, false), (20, false), (111, true), (112, false), (51, true), (116, false), (52, false), (115, false), (1024, false), (88, false), (94, false), (98, false), (1000, true), (1006, false)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true :=
  Snake9.TreeRup.prove_clause [c423, c392, c391, c1011, c566, c428, c430, c977, c694, c1040, c1053, c826, c828, c833, c843, c1056, c331, c1000, c871, c316, c38, c46, c40, c594, c1054, c1055, c623, c634, c639, c584, c1031, c567, c568, c6, c7, c978, c5, c681, c3, c688, c435, c710, c436, c439, c447, c464, c506, c564, c559, c557, c558, c555, c556, c541, c553, c546, c539, c552, c545, c538, c549, c543, c537, c384, c361, c345, c346, c350, c349, c348, c894, c355, c903, c357, c925, c657, c938, c659, c950, c672, c974, c739, c779] c1057 (by decide) p (sat_cons (step423 p h) (sat_cons (step392 p h) (sat_cons (step391 p h) (sat_cons (step1011 p h) (sat_cons (step566 p h) (sat_cons (step428 p h) (sat_cons (step430 p h) (sat_cons (step977 p h) (sat_cons (step694 p h) (sat_cons (step1040 p h) (sat_cons (step1053 p h) (sat_cons (step826 p h) (sat_cons (step828 p h) (sat_cons (step833 p h) (sat_cons (step843 p h) (sat_cons (step1056 p h) (sat_cons (step331 p h) (sat_cons (step1000 p h) (sat_cons (step871 p h) (sat_cons (step316 p h) (sat_cons (step38 p h) (sat_cons (step46 p h) (sat_cons (step40 p h) (sat_cons (step594 p h) (sat_cons (step1054 p h) (sat_cons (step1055 p h) (sat_cons (step623 p h) (sat_cons (step634 p h) (sat_cons (step639 p h) (sat_cons (step584 p h) (sat_cons (step1031 p h) (sat_cons (step567 p h) (sat_cons (step568 p h) (sat_cons (step6 p h) (sat_cons (step7 p h) (sat_cons (step978 p h) (sat_cons (step5 p h) (sat_cons (step681 p h) (sat_cons (step3 p h) (sat_cons (step688 p h) (sat_cons (step435 p h) (sat_cons (step710 p h) (sat_cons (step436 p h) (sat_cons (step439 p h) (sat_cons (step447 p h) (sat_cons (step464 p h) (sat_cons (step506 p h) (sat_cons (step564 p h) (sat_cons (step559 p h) (sat_cons (step557 p h) (sat_cons (step558 p h) (sat_cons (step555 p h) (sat_cons (step556 p h) (sat_cons (step541 p h) (sat_cons (step553 p h) (sat_cons (step546 p h) (sat_cons (step539 p h) (sat_cons (step552 p h) (sat_cons (step545 p h) (sat_cons (step538 p h) (sat_cons (step549 p h) (sat_cons (step543 p h) (sat_cons (step537 p h) (sat_cons (step384 p h) (sat_cons (step361 p h) (sat_cons (step345 p h) (sat_cons (step346 p h) (sat_cons (step350 p h) (sat_cons (step349 p h) (sat_cons (step348 p h) (sat_cons (step894 p h) (sat_cons (step355 p h) (sat_cons (step903 p h) (sat_cons (step357 p h) (sat_cons (step925 p h) (sat_cons (step657 p h) (sat_cons (step938 p h) (sat_cons (step659 p h) (sat_cons (step950 p h) (sat_cons (step672 p h) (sat_cons (step974 p h) (sat_cons (step739 p h) (sat_cons (step779 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1058 : List Lit := [(101, false), (110, true), (108, false), (1013, true)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true :=
  Snake9.LocalRup.prove_clause [c428, c345, c350, c349, c894] c1058 (by decide) p (sat_cons (step428 p h) (sat_cons (step345 p h) (sat_cons (step350 p h) (sat_cons (step349 p h) (sat_cons (step894 p h) (sat_nil p))))))
def c1059 : List Lit := [(99, false), (88, false), (98, false)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true :=
  Snake9.LocalRup.prove_clause [c427, c339, c331] c1059 (by decide) p (sat_cons (step427 p h) (sat_cons (step339 p h) (sat_cons (step331 p h) (sat_nil p))))
def c1060 : List Lit := [(104, true), (1017, true), (101, false)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true :=
  Snake9.LocalRup.prove_clause [c430, c903, c893, c894, c901, c896, c356, c347] c1060 (by decide) p (sat_cons (step430 p h) (sat_cons (step903 p h) (sat_cons (step893 p h) (sat_cons (step894 p h) (sat_cons (step901 p h) (sat_cons (step896 p h) (sat_cons (step356 p h) (sat_cons (step347 p h) (sat_nil p)))))))))
def c1061 : List Lit := [(970, true), (963, false)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true :=
  Snake9.LocalRup.prove_clause [c420, c828, c834, c836, c831, c819, c823, c824, c813, c297, c294] c1061 (by decide) p (sat_cons (step420 p h) (sat_cons (step828 p h) (sat_cons (step834 p h) (sat_cons (step836 p h) (sat_cons (step831 p h) (sat_cons (step819 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step813 p h) (sat_cons (step297 p h) (sat_cons (step294 p h) (sat_nil p))))))))))))
def c1062 : List Lit := [(903, true), (864, false), (28, true), (19, true), (30, true), (21, false), (888, false), (94, false)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true :=
  Snake9.LocalRup.prove_clause [c401, c644, c647, c671, c706, c738, c733, c676, c710, c648, c650, c688, c646, c680, c120, c99, c113] c1062 (by decide) p (sat_cons (step401 p h) (sat_cons (step644 p h) (sat_cons (step647 p h) (sat_cons (step671 p h) (sat_cons (step706 p h) (sat_cons (step738 p h) (sat_cons (step733 p h) (sat_cons (step676 p h) (sat_cons (step710 p h) (sat_cons (step648 p h) (sat_cons (step650 p h) (sat_cons (step688 p h) (sat_cons (step646 p h) (sat_cons (step680 p h) (sat_cons (step120 p h) (sat_cons (step99 p h) (sat_cons (step113 p h) (sat_nil p))))))))))))))))))
def c1063 : List Lit := [(1016, true), (101, false)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true :=
  Snake9.LocalRup.prove_clause [c430, c898, c900, c896, c892, c356, c347] c1063 (by decide) p (sat_cons (step430 p h) (sat_cons (step898 p h) (sat_cons (step900 p h) (sat_cons (step896 p h) (sat_cons (step892 p h) (sat_cons (step356 p h) (sat_cons (step347 p h) (sat_nil p))))))))
def c1064 : List Lit := [(16, true), (88, false), (98, false)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true :=
  Snake9.LocalRup.prove_clause [c423, c315, c316, c1000] c1064 (by decide) p (sat_cons (step423 p h) (sat_cons (step315 p h) (sat_cons (step316 p h) (sat_cons (step1000 p h) (sat_nil p)))))
def c1065 : List Lit := [(18, false), (830, false), (14, true), (20, false), (21, false), (111, true), (112, false), (51, true), (116, false), (52, false), (115, false), (1024, false), (88, false), (94, false), (98, false), (1000, true), (1006, false)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true :=
  Snake9.LocalRup.prove_clause [c977, c694, c1040, c1064, c1053, c826, c1061, c844, c1059, c871, c1063, c921, c937, c953, c974, c70, c64, c986, c644, c589, c647, c1057, c783, c40, c45, c656, c1062, c658] c1065 (by decide) p (sat_cons (step977 p h) (sat_cons (step694 p h) (sat_cons (step1040 p h) (sat_cons (step1064 p h) (sat_cons (step1053 p h) (sat_cons (step826 p h) (sat_cons (step1061 p h) (sat_cons (step844 p h) (sat_cons (step1059 p h) (sat_cons (step871 p h) (sat_cons (step1063 p h) (sat_cons (step921 p h) (sat_cons (step937 p h) (sat_cons (step953 p h) (sat_cons (step974 p h) (sat_cons (step70 p h) (sat_cons (step64 p h) (sat_cons (step986 p h) (sat_cons (step644 p h) (sat_cons (step589 p h) (sat_cons (step647 p h) (sat_cons (step1057 p h) (sat_cons (step783 p h) (sat_cons (step40 p h) (sat_cons (step45 p h) (sat_cons (step656 p h) (sat_cons (step1062 p h) (sat_cons (step658 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1066 : List Lit := [(857, true), (20, false), (21, false), (52, false), (94, false), (98, false)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true :=
  Snake9.LocalRup.prove_clause [c400, c401, c647, c649, c644, c645, c115, c114, c343, c101, c111, c74] c1066 (by decide) p (sat_cons (step400 p h) (sat_cons (step401 p h) (sat_cons (step647 p h) (sat_cons (step649 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step115 p h) (sat_cons (step114 p h) (sat_cons (step343 p h) (sat_cons (step101 p h) (sat_cons (step111 p h) (sat_cons (step74 p h) (sat_nil p)))))))))))))
def c1067 : List Lit := [(855, true), (896, true), (20, false), (21, false), (118, true), (117, false), (94, false), (98, false)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true :=
  Snake9.LocalRup.prove_clause [c434, c401, c386, c385, c998, c644, c645, c115, c114, c253, c251, c343, c696, c684, c110, c111, c1041, c99, c62, c719, c682, c692] c1067 (by decide) p (sat_cons (step434 p h) (sat_cons (step401 p h) (sat_cons (step386 p h) (sat_cons (step385 p h) (sat_cons (step998 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step115 p h) (sat_cons (step114 p h) (sat_cons (step253 p h) (sat_cons (step251 p h) (sat_cons (step343 p h) (sat_cons (step696 p h) (sat_cons (step684 p h) (sat_cons (step110 p h) (sat_cons (step111 p h) (sat_cons (step1041 p h) (sat_cons (step99 p h) (sat_cons (step62 p h) (sat_cons (step719 p h) (sat_cons (step682 p h) (sat_cons (step692 p h) (sat_nil p)))))))))))))))))))))))
def c1068 : List Lit := [(30, false), (37, true), (831, false), (14, true), (857, false), (20, false), (21, false), (118, true), (1022, true), (926, true), (98, false)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true :=
  Snake9.LocalRup.prove_clause [c434, c1050, c408, c656, c658, c671, c908, c386, c385, c998, c909, c67, c253, c251, c589, c696, c684, c591, c1041, c686, c620, c711, c629, c774, c735, c740, c715, c672, c687, c659, c661, c685, c657, c653, c174, c372, c231] c1068 (by decide) p (sat_cons (step434 p h) (sat_cons (step1050 p h) (sat_cons (step408 p h) (sat_cons (step656 p h) (sat_cons (step658 p h) (sat_cons (step671 p h) (sat_cons (step908 p h) (sat_cons (step386 p h) (sat_cons (step385 p h) (sat_cons (step998 p h) (sat_cons (step909 p h) (sat_cons (step67 p h) (sat_cons (step253 p h) (sat_cons (step251 p h) (sat_cons (step589 p h) (sat_cons (step696 p h) (sat_cons (step684 p h) (sat_cons (step591 p h) (sat_cons (step1041 p h) (sat_cons (step686 p h) (sat_cons (step620 p h) (sat_cons (step711 p h) (sat_cons (step629 p h) (sat_cons (step774 p h) (sat_cons (step735 p h) (sat_cons (step740 p h) (sat_cons (step715 p h) (sat_cons (step672 p h) (sat_cons (step687 p h) (sat_cons (step659 p h) (sat_cons (step661 p h) (sat_cons (step685 p h) (sat_cons (step657 p h) (sat_cons (step653 p h) (sat_cons (step174 p h) (sat_cons (step372 p h) (sat_cons (step231 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
end B112E159
