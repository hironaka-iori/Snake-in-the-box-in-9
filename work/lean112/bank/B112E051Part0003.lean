import B112E051Part0002
namespace B112E051
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1011 : List Lit := [(56, true), (96, true), (75, true), (57, false)]
theorem step1011 (p : Nat → Bool) (h : Constraints p) : clause p c1011 = true :=
  Snake9.LocalRup.prove_clause [c317, c141] c1011 (by decide) p (sat_cons (step317 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1012 : List Lit := [(52, true), (96, true), (75, true), (57, false)]
theorem step1012 (p : Nat → Bool) (h : Constraints p) : clause p c1012 = true :=
  Snake9.LocalRup.prove_clause [c317, c142] c1012 (by decide) p (sat_cons (step317 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1013 : List Lit := [(60, true), (62, true), (58, false)]
theorem step1013 (p : Nat → Bool) (h : Constraints p) : clause p c1013 = true :=
  Snake9.LocalRup.prove_clause [c318, c143] c1013 (by decide) p (sat_cons (step318 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1014 : List Lit := [(100, true), (60, true), (59, false)]
theorem step1014 (p : Nat → Bool) (h : Constraints p) : clause p c1014 = true :=
  Snake9.LocalRup.prove_clause [c319, c145] c1014 (by decide) p (sat_cons (step319 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1015 : List Lit := [(61, true), (60, true), (59, false)]
theorem step1015 (p : Nat → Bool) (h : Constraints p) : clause p c1015 = true :=
  Snake9.LocalRup.prove_clause [c319, c146] c1015 (by decide) p (sat_cons (step319 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1016 : List Lit := [(64, false), (63, true)]
theorem step1016 (p : Nat → Bool) (h : Constraints p) : clause p c1016 = true :=
  Snake9.LocalRup.prove_clause [c320, c154] c1016 (by decide) p (sat_cons (step320 p h) (sat_cons (step154 p h) (sat_nil p)))
def c1017 : List Lit := [(64, false), (62, true)]
theorem step1017 (p : Nat → Bool) (h : Constraints p) : clause p c1017 = true :=
  Snake9.LocalRup.prove_clause [c320, c155] c1017 (by decide) p (sat_cons (step320 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1018 : List Lit := [(72, false), (75, true), (68, true)]
theorem step1018 (p : Nat → Bool) (h : Constraints p) : clause p c1018 = true :=
  Snake9.LocalRup.prove_clause [c321, c168] c1018 (by decide) p (sat_cons (step321 p h) (sat_cons (step168 p h) (sat_nil p)))
def c1019 : List Lit := [(82, true), (73, false), (69, true), (75, true)]
theorem step1019 (p : Nat → Bool) (h : Constraints p) : clause p c1019 = true :=
  Snake9.LocalRup.prove_clause [c322, c169] c1019 (by decide) p (sat_cons (step322 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1020 : List Lit := [(79, true), (76, false), (77, true)]
theorem step1020 (p : Nat → Bool) (h : Constraints p) : clause p c1020 = true :=
  Snake9.LocalRup.prove_clause [c324, c196] c1020 (by decide) p (sat_cons (step324 p h) (sat_cons (step196 p h) (sat_nil p)))
def c1021 : List Lit := [(78, false), (68, true)]
theorem step1021 (p : Nat → Bool) (h : Constraints p) : clause p c1021 = true :=
  Snake9.LocalRup.prove_clause [c325, c200] c1021 (by decide) p (sat_cons (step325 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1022 : List Lit := [(82, true), (81, false), (83, true)]
theorem step1022 (p : Nat → Bool) (h : Constraints p) : clause p c1022 = true :=
  Snake9.LocalRup.prove_clause [c326, c206] c1022 (by decide) p (sat_cons (step326 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1023 : List Lit := [(79, true), (81, false), (83, true)]
theorem step1023 (p : Nat → Bool) (h : Constraints p) : clause p c1023 = true :=
  Snake9.LocalRup.prove_clause [c326, c207] c1023 (by decide) p (sat_cons (step326 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1024 : List Lit := [(98, true), (86, false), (87, true), (84, true), (89, true)]
theorem step1024 (p : Nat → Bool) (h : Constraints p) : clause p c1024 = true :=
  Snake9.LocalRup.prove_clause [c327, c221] c1024 (by decide) p (sat_cons (step327 p h) (sat_cons (step221 p h) (sat_nil p)))
def c1025 : List Lit := [(92, true), (93, false), (96, true)]
theorem step1025 (p : Nat → Bool) (h : Constraints p) : clause p c1025 = true :=
  Snake9.LocalRup.prove_clause [c328, c243] c1025 (by decide) p (sat_cons (step328 p h) (sat_cons (step243 p h) (sat_nil p)))
def c1026 : List Lit := [(93, false), (87, true), (96, true)]
theorem step1026 (p : Nat → Bool) (h : Constraints p) : clause p c1026 = true :=
  Snake9.LocalRup.prove_clause [c328, c244] c1026 (by decide) p (sat_cons (step328 p h) (sat_cons (step244 p h) (sat_nil p)))
def c1027 : List Lit := [(92, true), (93, false), (87, true)]
theorem step1027 (p : Nat → Bool) (h : Constraints p) : clause p c1027 = true :=
  Snake9.LocalRup.prove_clause [c328, c245] c1027 (by decide) p (sat_cons (step328 p h) (sat_cons (step245 p h) (sat_nil p)))
def c1028 : List Lit := [(94, true), (92, true), (96, true), (95, false), (88, true)]
theorem step1028 (p : Nat → Bool) (h : Constraints p) : clause p c1028 = true :=
  Snake9.LocalRup.prove_clause [c329, c253] c1028 (by decide) p (sat_cons (step329 p h) (sat_cons (step253 p h) (sat_nil p)))
def c1029 : List Lit := [(102, true), (100, true), (97, false), (84, true)]
theorem step1029 (p : Nat → Bool) (h : Constraints p) : clause p c1029 = true :=
  Snake9.LocalRup.prove_clause [c330, c261] c1029 (by decide) p (sat_cons (step330 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1030 : List Lit := [(98, true), (102, true), (97, false), (84, true)]
theorem step1030 (p : Nat → Bool) (h : Constraints p) : clause p c1030 = true :=
  Snake9.LocalRup.prove_clause [c330, c262] c1030 (by decide) p (sat_cons (step330 p h) (sat_cons (step262 p h) (sat_nil p)))
def c1031 : List Lit := [(98, true), (100, true), (97, false), (84, true)]
theorem step1031 (p : Nat → Bool) (h : Constraints p) : clause p c1031 = true :=
  Snake9.LocalRup.prove_clause [c330, c263] c1031 (by decide) p (sat_cons (step330 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1032 : List Lit := [(99, false), (98, true)]
theorem step1032 (p : Nat → Bool) (h : Constraints p) : clause p c1032 = true :=
  Snake9.LocalRup.prove_clause [c331, c266] c1032 (by decide) p (sat_cons (step331 p h) (sat_cons (step266 p h) (sat_nil p)))
def c1033 : List Lit := [(99, false), (87, true)]
theorem step1033 (p : Nat → Bool) (h : Constraints p) : clause p c1033 = true :=
  Snake9.LocalRup.prove_clause [c331, c267] c1033 (by decide) p (sat_cons (step331 p h) (sat_cons (step267 p h) (sat_nil p)))
def c1034 : List Lit := [(111, false), (110, true)]
theorem step1034 (p : Nat → Bool) (h : Constraints p) : clause p c1034 = true :=
  Snake9.LocalRup.prove_clause [c332, c281] c1034 (by decide) p (sat_cons (step332 p h) (sat_cons (step281 p h) (sat_nil p)))
def c1035 : List Lit := [(111, false), (107, true)]
theorem step1035 (p : Nat → Bool) (h : Constraints p) : clause p c1035 = true :=
  Snake9.LocalRup.prove_clause [c332, c282] c1035 (by decide) p (sat_cons (step332 p h) (sat_cons (step282 p h) (sat_nil p)))
def c1036 : List Lit := [(112, false), (110, true)]
theorem step1036 (p : Nat → Bool) (h : Constraints p) : clause p c1036 = true :=
  Snake9.LocalRup.prove_clause [c333, c283] c1036 (by decide) p (sat_cons (step333 p h) (sat_cons (step283 p h) (sat_nil p)))
def c1037 : List Lit := [(112, false), (94, true)]
theorem step1037 (p : Nat → Bool) (h : Constraints p) : clause p c1037 = true :=
  Snake9.LocalRup.prove_clause [c333, c284] c1037 (by decide) p (sat_cons (step333 p h) (sat_cons (step284 p h) (sat_nil p)))
def c1038 : List Lit := [(106, true), (115, true)]
theorem step1038 (p : Nat → Bool) (h : Constraints p) : clause p c1038 = true :=
  Snake9.LocalRup.prove_clause [c286, c285] c1038 (by decide) p (sat_cons (step286 p h) (sat_cons (step285 p h) (sat_nil p)))
def c1039 : List Lit := [(116, true), (100, true), (114, false)]
theorem step1039 (p : Nat → Bool) (h : Constraints p) : clause p c1039 = true :=
  Snake9.LocalRup.prove_clause [c334, c287] c1039 (by decide) p (sat_cons (step334 p h) (sat_cons (step287 p h) (sat_nil p)))
def c1040 : List Lit := [(275, false), (277, false)]
theorem step1040 (p : Nat → Bool) (h : Constraints p) : clause p c1040 = true :=
  Snake9.LocalRup.prove_clause [c829, c378] c1040 (by decide) p (sat_cons (step829 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1041 : List Lit := [(273, false), (279, false)]
theorem step1041 (p : Nat → Bool) (h : Constraints p) : clause p c1041 = true :=
  Snake9.LocalRup.prove_clause [c825, c382] c1041 (by decide) p (sat_cons (step825 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1042 : List Lit := [(269, false), (281, false)]
theorem step1042 (p : Nat → Bool) (h : Constraints p) : clause p c1042 = true :=
  Snake9.LocalRup.prove_clause [c823, c387] c1042 (by decide) p (sat_cons (step823 p h) (sat_cons (step387 p h) (sat_nil p)))
def c1043 : List Lit := [(257, false), (283, false)]
theorem step1043 (p : Nat → Bool) (h : Constraints p) : clause p c1043 = true :=
  Snake9.LocalRup.prove_clause [c821, c392] c1043 (by decide) p (sat_cons (step821 p h) (sat_cons (step392 p h) (sat_nil p)))
def c1044 : List Lit := [(323, false), (337, false)]
theorem step1044 (p : Nat → Bool) (h : Constraints p) : clause p c1044 = true :=
  Snake9.LocalRup.prove_clause [c822, c414] c1044 (by decide) p (sat_cons (step822 p h) (sat_cons (step414 p h) (sat_nil p)))
def c1045 : List Lit := [(311, false), (339, false)]
theorem step1045 (p : Nat → Bool) (h : Constraints p) : clause p c1045 = true :=
  Snake9.LocalRup.prove_clause [c820, c418] c1045 (by decide) p (sat_cons (step820 p h) (sat_cons (step418 p h) (sat_nil p)))
def c1046 : List Lit := [(285, false), (341, false)]
theorem step1046 (p : Nat → Bool) (h : Constraints p) : clause p c1046 = true :=
  Snake9.LocalRup.prove_clause [c819, c422] c1046 (by decide) p (sat_cons (step819 p h) (sat_cons (step422 p h) (sat_nil p)))
def c1047 : List Lit := [(343, false), (457, false)]
theorem step1047 (p : Nat → Bool) (h : Constraints p) : clause p c1047 = true :=
  Snake9.LocalRup.prove_clause [c461, c459] c1047 (by decide) p (sat_cons (step461 p h) (sat_cons (step459 p h) (sat_nil p)))
def c1048 : List Lit := [(857, false), (869, true)]
theorem step1048 (p : Nat → Bool) (h : Constraints p) : clause p c1048 = true :=
  Snake9.LocalRup.prove_clause [c940, c596] c1048 (by decide) p (sat_cons (step940 p h) (sat_cons (step596 p h) (sat_nil p)))
def c1049 : List Lit := [(858, false), (870, true)]
theorem step1049 (p : Nat → Bool) (h : Constraints p) : clause p c1049 = true :=
  Snake9.LocalRup.prove_clause [c940, c599] c1049 (by decide) p (sat_cons (step940 p h) (sat_cons (step599 p h) (sat_nil p)))
def c1050 : List Lit := [(849, false), (877, true)]
theorem step1050 (p : Nat → Bool) (h : Constraints p) : clause p c1050 = true :=
  Snake9.LocalRup.prove_clause [c941, c607] c1050 (by decide) p (sat_cons (step941 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1051 : List Lit := [(850, false), (878, true)]
theorem step1051 (p : Nat → Bool) (h : Constraints p) : clause p c1051 = true :=
  Snake9.LocalRup.prove_clause [c941, c610] c1051 (by decide) p (sat_cons (step941 p h) (sat_cons (step610 p h) (sat_nil p)))
def c1052 : List Lit := [(851, false), (879, true)]
theorem step1052 (p : Nat → Bool) (h : Constraints p) : clause p c1052 = true :=
  Snake9.LocalRup.prove_clause [c941, c613] c1052 (by decide) p (sat_cons (step941 p h) (sat_cons (step613 p h) (sat_nil p)))
def c1053 : List Lit := [(894, true), (824, false)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true :=
  Snake9.LocalRup.prove_clause [c942, c620] c1053 (by decide) p (sat_cons (step942 p h) (sat_cons (step620 p h) (sat_nil p)))
def c1054 : List Lit := [(825, false), (895, true)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true :=
  Snake9.LocalRup.prove_clause [c942, c623] c1054 (by decide) p (sat_cons (step942 p h) (sat_cons (step623 p h) (sat_nil p)))
def c1055 : List Lit := [(928, false), (940, true)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true :=
  Snake9.LocalRup.prove_clause [c841, c681] c1055 (by decide) p (sat_cons (step841 p h) (sat_cons (step681 p h) (sat_nil p)))
def c1056 : List Lit := [(929, false), (941, true)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true :=
  Snake9.LocalRup.prove_clause [c841, c684] c1056 (by decide) p (sat_cons (step841 p h) (sat_cons (step684 p h) (sat_nil p)))
def c1057 : List Lit := [(930, false), (942, true)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true :=
  Snake9.LocalRup.prove_clause [c841, c686] c1057 (by decide) p (sat_cons (step841 p h) (sat_cons (step686 p h) (sat_nil p)))
def c1058 : List Lit := [(941, false), (949, true)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true :=
  Snake9.LocalRup.prove_clause [c851, c688] c1058 (by decide) p (sat_cons (step851 p h) (sat_cons (step688 p h) (sat_nil p)))
def c1059 : List Lit := [(942, false), (950, true)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true :=
  Snake9.LocalRup.prove_clause [c851, c689] c1059 (by decide) p (sat_cons (step851 p h) (sat_cons (step689 p h) (sat_nil p)))
def c1060 : List Lit := [(949, true), (921, false)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true :=
  Snake9.LocalRup.prove_clause [c842, c694] c1060 (by decide) p (sat_cons (step842 p h) (sat_cons (step694 p h) (sat_nil p)))
def c1061 : List Lit := [(922, false), (950, true)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true :=
  Snake9.LocalRup.prove_clause [c842, c698] c1061 (by decide) p (sat_cons (step842 p h) (sat_cons (step698 p h) (sat_nil p)))
def c1062 : List Lit := [(999, false), (1008, true)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true :=
  Snake9.LocalRup.prove_clause [c882, c776] c1062 (by decide) p (sat_cons (step882 p h) (sat_cons (step776 p h) (sat_nil p)))
def c1063 : List Lit := [(1000, false), (1009, true)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true :=
  Snake9.LocalRup.prove_clause [c882, c777] c1063 (by decide) p (sat_cons (step882 p h) (sat_cons (step777 p h) (sat_nil p)))
def c1064 : List Lit := [(976, false), (1008, true)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true :=
  Snake9.LocalRup.prove_clause [c879, c784] c1064 (by decide) p (sat_cons (step879 p h) (sat_cons (step784 p h) (sat_nil p)))
def c1065 : List Lit := [(977, false), (1009, true)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true :=
  Snake9.LocalRup.prove_clause [c879, c788] c1065 (by decide) p (sat_cons (step879 p h) (sat_cons (step788 p h) (sat_nil p)))
def c1066 : List Lit := [(1026, true), (949, false)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true :=
  Snake9.LocalRup.prove_clause [c887, c790] c1066 (by decide) p (sat_cons (step887 p h) (sat_cons (step790 p h) (sat_nil p)))
def c1067 : List Lit := [(952, false), (1029, true)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true :=
  Snake9.LocalRup.prove_clause [c887, c797] c1067 (by decide) p (sat_cons (step887 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1068 : List Lit := [(894, false), (1029, false)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true :=
  Snake9.LocalRup.prove_clause [c801, c798] c1068 (by decide) p (sat_cons (step801 p h) (sat_cons (step798 p h) (sat_nil p)))
def c1069 : List Lit := [(895, false), (1028, false)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true :=
  Snake9.LocalRup.prove_clause [c801, c799] c1069 (by decide) p (sat_cons (step801 p h) (sat_cons (step799 p h) (sat_nil p)))
def c1070 : List Lit := [(897, false), (1026, false)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true :=
  Snake9.LocalRup.prove_clause [c801, c800] c1070 (by decide) p (sat_cons (step801 p h) (sat_cons (step800 p h) (sat_nil p)))
def c1071 : List Lit := [(838, false), (878, true)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true :=
  Snake9.LocalRup.prove_clause [c570, c966, c608, c574, c1048, c576] c1071 (by decide) p (sat_cons (step570 p h) (sat_cons (step966 p h) (sat_cons (step608 p h) (sat_cons (step574 p h) (sat_cons (step1048 p h) (sat_cons (step576 p h) (sat_nil p)))))))
def c1072 : List Lit := [(25, true), (810, true), (75, false), (895, true)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true :=
  Snake9.TreeRup.prove_clause [c508, c934, c548, c566, c510, c503, c505, c984, c73, c670, c963, c929, c502, c506, c979, c981, c58, c371, c372, c381, c384, c1042, c389, c369, c421, c1046, c366, c367, c1047, c415, c365, c362, c458, c413, c55, c443, c406, c976, c432, c405, c49, c431, c404, c56, c430, c965, c636, c429, c619, c1071, c549, c543, c544, c946, c618, c1068, c1067, c949, c663, c950, c637, c163, c1021, c666, c675, c935, c682, c176, c700, c837] c1072 (by decide) p (sat_cons (step508 p h) (sat_cons (step934 p h) (sat_cons (step548 p h) (sat_cons (step566 p h) (sat_cons (step510 p h) (sat_cons (step503 p h) (sat_cons (step505 p h) (sat_cons (step984 p h) (sat_cons (step73 p h) (sat_cons (step670 p h) (sat_cons (step963 p h) (sat_cons (step929 p h) (sat_cons (step502 p h) (sat_cons (step506 p h) (sat_cons (step979 p h) (sat_cons (step981 p h) (sat_cons (step58 p h) (sat_cons (step371 p h) (sat_cons (step372 p h) (sat_cons (step381 p h) (sat_cons (step384 p h) (sat_cons (step1042 p h) (sat_cons (step389 p h) (sat_cons (step369 p h) (sat_cons (step421 p h) (sat_cons (step1046 p h) (sat_cons (step366 p h) (sat_cons (step367 p h) (sat_cons (step1047 p h) (sat_cons (step415 p h) (sat_cons (step365 p h) (sat_cons (step362 p h) (sat_cons (step458 p h) (sat_cons (step413 p h) (sat_cons (step55 p h) (sat_cons (step443 p h) (sat_cons (step406 p h) (sat_cons (step976 p h) (sat_cons (step432 p h) (sat_cons (step405 p h) (sat_cons (step49 p h) (sat_cons (step431 p h) (sat_cons (step404 p h) (sat_cons (step56 p h) (sat_cons (step430 p h) (sat_cons (step965 p h) (sat_cons (step636 p h) (sat_cons (step429 p h) (sat_cons (step619 p h) (sat_cons (step1071 p h) (sat_cons (step549 p h) (sat_cons (step543 p h) (sat_cons (step544 p h) (sat_cons (step946 p h) (sat_cons (step618 p h) (sat_cons (step1068 p h) (sat_cons (step1067 p h) (sat_cons (step949 p h) (sat_cons (step663 p h) (sat_cons (step950 p h) (sat_cons (step637 p h) (sat_cons (step163 p h) (sat_cons (step1021 p h) (sat_cons (step666 p h) (sat_cons (step675 p h) (sat_cons (step935 p h) (sat_cons (step682 p h) (sat_cons (step176 p h) (sat_cons (step700 p h) (sat_cons (step837 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1073 : List Lit := [(795, true), (21, true), (786, false)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true :=
  Snake9.LocalRup.prove_clause [c484, c906, c908, c478, c969, c845] c1073 (by decide) p (sat_cons (step484 p h) (sat_cons (step906 p h) (sat_cons (step908 p h) (sat_cons (step478 p h) (sat_cons (step969 p h) (sat_cons (step845 p h) (sat_nil p)))))))
def c1074 : List Lit := [(810, true), (75, false), (824, true), (895, true)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true :=
  Snake9.LocalRup.prove_clause [c510, c502, c963, c470, c1072, c64, c975, c494, c497, c518, c538, c1073, c943, c947, c500, c404, c904, c405, c471, c406, c480, c413, c489, c415, c467, c1046, c969, c391, c876] c1074 (by decide) p (sat_cons (step510 p h) (sat_cons (step502 p h) (sat_cons (step963 p h) (sat_cons (step470 p h) (sat_cons (step1072 p h) (sat_cons (step64 p h) (sat_cons (step975 p h) (sat_cons (step494 p h) (sat_cons (step497 p h) (sat_cons (step518 p h) (sat_cons (step538 p h) (sat_cons (step1073 p h) (sat_cons (step943 p h) (sat_cons (step947 p h) (sat_cons (step500 p h) (sat_cons (step404 p h) (sat_cons (step904 p h) (sat_cons (step405 p h) (sat_cons (step471 p h) (sat_cons (step406 p h) (sat_cons (step480 p h) (sat_cons (step413 p h) (sat_cons (step489 p h) (sat_cons (step415 p h) (sat_cons (step467 p h) (sat_cons (step1046 p h) (sat_cons (step969 p h) (sat_cons (step391 p h) (sat_cons (step876 p h) (sat_nil p))))))))))))))))))))))))))))))
end B112E051
