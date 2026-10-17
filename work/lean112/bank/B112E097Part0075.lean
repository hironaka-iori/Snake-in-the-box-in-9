import B112E097Part0074
namespace B112E097
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6395 : List Lit := [(81, false), (122, true), (123, false), (1055, false), (1085, true), (57, false)]
theorem step6395 (p : Nat → Bool) (h : Constraints p) : clause p c6395 = true :=
  Snake9.LocalRup.prove_clause [c6279, c5989, c2247, c655, c654, c4607, c1321] c6395 (by decide) p (sat_cons (step6279 p h) (sat_cons (step5989 p h) (sat_cons (step2247 p h) (sat_cons (step655 p h) (sat_cons (step654 p h) (sat_cons (step4607 p h) (sat_cons (step1321 p h) (sat_nil p))))))))
def c6396 : List Lit := [(123, false), (1055, false), (81, false), (1085, true), (57, false)]
theorem step6396 (p : Nat → Bool) (h : Constraints p) : clause p c6396 = true :=
  Snake9.LocalRup.prove_clause [c6279, c657, c6395] c6396 (by decide) p (sat_cons (step6279 p h) (sat_cons (step657 p h) (sat_cons (step6395 p h) (sat_nil p))))
def c6397 : List Lit := [(907, true), (81, false), (882, true), (960, true), (1085, true), (88, true), (57, false)]
theorem step6397 (p : Nat → Bool) (h : Constraints p) : clause p c6397 = true :=
  Snake9.LocalRup.prove_clause [c6279, c5989, c6069, c4227, c6396, c6116, c6108, c2687] c6397 (by decide) p (sat_cons (step6279 p h) (sat_cons (step5989 p h) (sat_cons (step6069 p h) (sat_cons (step4227 p h) (sat_cons (step6396 p h) (sat_cons (step6116 p h) (sat_cons (step6108 p h) (sat_cons (step2687 p h) (sat_nil p)))))))))
def c6398 : List Lit := [(881, true), (1021, true), (1005, false), (920, false), (52, true)]
theorem step6398 (p : Nat → Bool) (h : Constraints p) : clause p c6398 = true :=
  Snake9.LocalRup.prove_clause [c6277, c1197, c1251, c2080, c1058, c1048, c1042, c6364, c5722, c1997, c6373, c1638, c1816, c930, c932, c742, c927, c925, c743, c747, c764, c786, c832, c1996, c914, c6351, c1246, c1202, c1176, c1168, c1169, c4238, c4402, c237, c1166, c3006, c1140, c6136] c6398 (by decide) p (sat_cons (step6277 p h) (sat_cons (step1197 p h) (sat_cons (step1251 p h) (sat_cons (step2080 p h) (sat_cons (step1058 p h) (sat_cons (step1048 p h) (sat_cons (step1042 p h) (sat_cons (step6364 p h) (sat_cons (step5722 p h) (sat_cons (step1997 p h) (sat_cons (step6373 p h) (sat_cons (step1638 p h) (sat_cons (step1816 p h) (sat_cons (step930 p h) (sat_cons (step932 p h) (sat_cons (step742 p h) (sat_cons (step927 p h) (sat_cons (step925 p h) (sat_cons (step743 p h) (sat_cons (step747 p h) (sat_cons (step764 p h) (sat_cons (step786 p h) (sat_cons (step832 p h) (sat_cons (step1996 p h) (sat_cons (step914 p h) (sat_cons (step6351 p h) (sat_cons (step1246 p h) (sat_cons (step1202 p h) (sat_cons (step1176 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step4238 p h) (sat_cons (step4402 p h) (sat_cons (step237 p h) (sat_cons (step1166 p h) (sat_cons (step3006 p h) (sat_cons (step1140 p h) (sat_cons (step6136 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c6399 : List Lit := [(81, false), (907, true), (960, true), (1085, true), (88, true), (57, false)]
theorem step6399 (p : Nat → Bool) (h : Constraints p) : clause p c6399 = true :=
  Snake9.LocalRup.prove_clause [c5989, c6279, c5858, c6069, c4227, c6397, c6396, c1121, c2311, c1081, c2000] c6399 (by decide) p (sat_cons (step5989 p h) (sat_cons (step6279 p h) (sat_cons (step5858 p h) (sat_cons (step6069 p h) (sat_cons (step4227 p h) (sat_cons (step6397 p h) (sat_cons (step6396 p h) (sat_cons (step1121 p h) (sat_cons (step2311 p h) (sat_cons (step1081 p h) (sat_cons (step2000 p h) (sat_nil p))))))))))))
def c6400 : List Lit := [(88, true), (55, true), (52, true)]
theorem step6400 (p : Nat → Bool) (h : Constraints p) : clause p c6400 = true :=
  Snake9.LocalRup.prove_clause [c6369, c5858, c6280, c6277, c2080, c1058, c1039, c1048, c1042, c1050, c1041, c5722, c1134, c6364, c6372, c6382, c6392, c1186, c6393, c6394, c2031, c6014, c6043, c1436, c2032, c6398, c1115, c1087, c6399, c1172, c1174, c4405, c1202, c4402, c1246, c1139, c1165, c1162, c1140, c1149, c6136, c1141] c6400 (by decide) p (sat_cons (step6369 p h) (sat_cons (step5858 p h) (sat_cons (step6280 p h) (sat_cons (step6277 p h) (sat_cons (step2080 p h) (sat_cons (step1058 p h) (sat_cons (step1039 p h) (sat_cons (step1048 p h) (sat_cons (step1042 p h) (sat_cons (step1050 p h) (sat_cons (step1041 p h) (sat_cons (step5722 p h) (sat_cons (step1134 p h) (sat_cons (step6364 p h) (sat_cons (step6372 p h) (sat_cons (step6382 p h) (sat_cons (step6392 p h) (sat_cons (step1186 p h) (sat_cons (step6393 p h) (sat_cons (step6394 p h) (sat_cons (step2031 p h) (sat_cons (step6014 p h) (sat_cons (step6043 p h) (sat_cons (step1436 p h) (sat_cons (step2032 p h) (sat_cons (step6398 p h) (sat_cons (step1115 p h) (sat_cons (step1087 p h) (sat_cons (step6399 p h) (sat_cons (step1172 p h) (sat_cons (step1174 p h) (sat_cons (step4405 p h) (sat_cons (step1202 p h) (sat_cons (step4402 p h) (sat_cons (step1246 p h) (sat_cons (step1139 p h) (sat_cons (step1165 p h) (sat_cons (step1162 p h) (sat_cons (step1140 p h) (sat_cons (step1149 p h) (sat_cons (step6136 p h) (sat_cons (step1141 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c6401 : List Lit := [(88, false), (52, true)]
theorem step6401 (p : Nat → Bool) (h : Constraints p) : clause p c6401 = true :=
  Snake9.LocalRup.prove_clause [c6277, c6369, c5858, c5989, c4151, c1885, c6364, c1845, c1846, c5983, c1830, c2730, c2031, c943, c1081, c6043, c947, c1436, c2032, c4473, c1121, c1087, c1644, c6350, c2687, c229, c5609, c5621, c932, c1638, c985, c1717, c969, c945, c959, c2336] c6401 (by decide) p (sat_cons (step6277 p h) (sat_cons (step6369 p h) (sat_cons (step5858 p h) (sat_cons (step5989 p h) (sat_cons (step4151 p h) (sat_cons (step1885 p h) (sat_cons (step6364 p h) (sat_cons (step1845 p h) (sat_cons (step1846 p h) (sat_cons (step5983 p h) (sat_cons (step1830 p h) (sat_cons (step2730 p h) (sat_cons (step2031 p h) (sat_cons (step943 p h) (sat_cons (step1081 p h) (sat_cons (step6043 p h) (sat_cons (step947 p h) (sat_cons (step1436 p h) (sat_cons (step2032 p h) (sat_cons (step4473 p h) (sat_cons (step1121 p h) (sat_cons (step1087 p h) (sat_cons (step1644 p h) (sat_cons (step6350 p h) (sat_cons (step2687 p h) (sat_cons (step229 p h) (sat_cons (step5609 p h) (sat_cons (step5621 p h) (sat_cons (step932 p h) (sat_cons (step1638 p h) (sat_cons (step985 p h) (sat_cons (step1717 p h) (sat_cons (step969 p h) (sat_cons (step945 p h) (sat_cons (step959 p h) (sat_cons (step2336 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c6402 : List Lit := [(54, true), (52, true)]
theorem step6402 (p : Nat → Bool) (h : Constraints p) : clause p c6402 = true :=
  Snake9.LocalRup.prove_clause [c6277, c6401, c6400, c1891, c1889, c1560, c1029, c2080, c1058, c1040, c1800, c1047, c1025, c1062, c1034] c6402 (by decide) p (sat_cons (step6277 p h) (sat_cons (step6401 p h) (sat_cons (step6400 p h) (sat_cons (step1891 p h) (sat_cons (step1889 p h) (sat_cons (step1560 p h) (sat_cons (step1029 p h) (sat_cons (step2080 p h) (sat_cons (step1058 p h) (sat_cons (step1040 p h) (sat_cons (step1800 p h) (sat_cons (step1047 p h) (sat_cons (step1025 p h) (sat_cons (step1062 p h) (sat_cons (step1034 p h) (sat_nil p))))))))))))))))
def c6403 : List Lit := [(1106, true), (907, true), (960, true), (52, true)]
theorem step6403 (p : Nat → Bool) (h : Constraints p) : clause p c6403 = true :=
  Snake9.LocalRup.prove_clause [c6369, c6277, c6401, c6400, c1889, c6402, c224, c1145, c1147, c6382, c6364, c6014, c1437, c6399, c1172, c1174, c1202, c1246, c2322, c1162, c6136, c1137] c6403 (by decide) p (sat_cons (step6369 p h) (sat_cons (step6277 p h) (sat_cons (step6401 p h) (sat_cons (step6400 p h) (sat_cons (step1889 p h) (sat_cons (step6402 p h) (sat_cons (step224 p h) (sat_cons (step1145 p h) (sat_cons (step1147 p h) (sat_cons (step6382 p h) (sat_cons (step6364 p h) (sat_cons (step6014 p h) (sat_cons (step1437 p h) (sat_cons (step6399 p h) (sat_cons (step1172 p h) (sat_cons (step1174 p h) (sat_cons (step1202 p h) (sat_cons (step1246 p h) (sat_cons (step2322 p h) (sat_cons (step1162 p h) (sat_cons (step6136 p h) (sat_cons (step1137 p h) (sat_nil p)))))))))))))))))))))))
def c6404 : List Lit := [(907, true), (960, true), (52, true)]
theorem step6404 (p : Nat → Bool) (h : Constraints p) : clause p c6404 = true :=
  Snake9.LocalRup.prove_clause [c5859, c5858, c5989, c6277, c6401, c6400, c1889, c6402, c224, c1145, c225, c1186, c6372, c6364, c1015, c6403, c2031, c1120, c6394, c4583, c2297, c1081, c1114, c1643, c1997, c4603, c1717, c1638, c2687, c6242, c945, c932, c6079, c954, c955, c925, c1246, c1198, c1194, c1184, c6234, c5398, c993, c1017, c995] c6404 (by decide) p (sat_cons (step5859 p h) (sat_cons (step5858 p h) (sat_cons (step5989 p h) (sat_cons (step6277 p h) (sat_cons (step6401 p h) (sat_cons (step6400 p h) (sat_cons (step1889 p h) (sat_cons (step6402 p h) (sat_cons (step224 p h) (sat_cons (step1145 p h) (sat_cons (step225 p h) (sat_cons (step1186 p h) (sat_cons (step6372 p h) (sat_cons (step6364 p h) (sat_cons (step1015 p h) (sat_cons (step6403 p h) (sat_cons (step2031 p h) (sat_cons (step1120 p h) (sat_cons (step6394 p h) (sat_cons (step4583 p h) (sat_cons (step2297 p h) (sat_cons (step1081 p h) (sat_cons (step1114 p h) (sat_cons (step1643 p h) (sat_cons (step1997 p h) (sat_cons (step4603 p h) (sat_cons (step1717 p h) (sat_cons (step1638 p h) (sat_cons (step2687 p h) (sat_cons (step6242 p h) (sat_cons (step945 p h) (sat_cons (step932 p h) (sat_cons (step6079 p h) (sat_cons (step954 p h) (sat_cons (step955 p h) (sat_cons (step925 p h) (sat_cons (step1246 p h) (sat_cons (step1198 p h) (sat_cons (step1194 p h) (sat_cons (step1184 p h) (sat_cons (step6234 p h) (sat_cons (step5398 p h) (sat_cons (step993 p h) (sat_cons (step1017 p h) (sat_cons (step995 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c6405 : List Lit := [(960, true), (52, true)]
theorem step6405 (p : Nat → Bool) (h : Constraints p) : clause p c6405 = true :=
  Snake9.TreeRup.prove_clause [c5858, c6280, c6277, c6401, c6402, c6382, c1197, c6400, c1889, c224, c1145, c225, c1891, c1560, c6372, c1183, c4151, c1884, c6364, c5722, c6404, c2215, c1087, c2031, c1115, c6014, c1643, c1997, c6373, c1251, c1717, c1638, c1816, c1160, c945, c930, c932, c6079, c742, c1153, c927, c925, c1246, c743, c1198, c1202, c747, c1192, c1176, c764, c1187, c1169, c786, c385, c237, c832, c1986, c1895, c1918, c1996, c826, c914, c823, c825, c870, c820, c812, c850, c818, c811, c840, c842, c815, c808, c838, c835, c836, c266, c1887, c160, c162, c257, c1900, c170, c1143, c277, c294] c6405 (by decide) p (sat_cons (step5858 p h) (sat_cons (step6280 p h) (sat_cons (step6277 p h) (sat_cons (step6401 p h) (sat_cons (step6402 p h) (sat_cons (step6382 p h) (sat_cons (step1197 p h) (sat_cons (step6400 p h) (sat_cons (step1889 p h) (sat_cons (step224 p h) (sat_cons (step1145 p h) (sat_cons (step225 p h) (sat_cons (step1891 p h) (sat_cons (step1560 p h) (sat_cons (step6372 p h) (sat_cons (step1183 p h) (sat_cons (step4151 p h) (sat_cons (step1884 p h) (sat_cons (step6364 p h) (sat_cons (step5722 p h) (sat_cons (step6404 p h) (sat_cons (step2215 p h) (sat_cons (step1087 p h) (sat_cons (step2031 p h) (sat_cons (step1115 p h) (sat_cons (step6014 p h) (sat_cons (step1643 p h) (sat_cons (step1997 p h) (sat_cons (step6373 p h) (sat_cons (step1251 p h) (sat_cons (step1717 p h) (sat_cons (step1638 p h) (sat_cons (step1816 p h) (sat_cons (step1160 p h) (sat_cons (step945 p h) (sat_cons (step930 p h) (sat_cons (step932 p h) (sat_cons (step6079 p h) (sat_cons (step742 p h) (sat_cons (step1153 p h) (sat_cons (step927 p h) (sat_cons (step925 p h) (sat_cons (step1246 p h) (sat_cons (step743 p h) (sat_cons (step1198 p h) (sat_cons (step1202 p h) (sat_cons (step747 p h) (sat_cons (step1192 p h) (sat_cons (step1176 p h) (sat_cons (step764 p h) (sat_cons (step1187 p h) (sat_cons (step1169 p h) (sat_cons (step786 p h) (sat_cons (step385 p h) (sat_cons (step237 p h) (sat_cons (step832 p h) (sat_cons (step1986 p h) (sat_cons (step1895 p h) (sat_cons (step1918 p h) (sat_cons (step1996 p h) (sat_cons (step826 p h) (sat_cons (step914 p h) (sat_cons (step823 p h) (sat_cons (step825 p h) (sat_cons (step870 p h) (sat_cons (step820 p h) (sat_cons (step812 p h) (sat_cons (step850 p h) (sat_cons (step818 p h) (sat_cons (step811 p h) (sat_cons (step840 p h) (sat_cons (step842 p h) (sat_cons (step815 p h) (sat_cons (step808 p h) (sat_cons (step838 p h) (sat_cons (step835 p h) (sat_cons (step836 p h) (sat_cons (step266 p h) (sat_cons (step1887 p h) (sat_cons (step160 p h) (sat_cons (step162 p h) (sat_cons (step257 p h) (sat_cons (step1900 p h) (sat_cons (step170 p h) (sat_cons (step1143 p h) (sat_cons (step277 p h) (sat_cons (step294 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c6406 : List Lit := [(88, true), (52, true)]
theorem step6406 (p : Nat → Bool) (h : Constraints p) : clause p c6406 = true :=
  Snake9.LocalRup.prove_clause [c6369, c5989, c6280, c6372, c6400, c1183, c1889, c1190, c6402, c224, c1145, c1147, c1158, c4205, c6405, c2032, c1436, c1427, c6043, c6394, c2031] c6406 (by decide) p (sat_cons (step6369 p h) (sat_cons (step5989 p h) (sat_cons (step6280 p h) (sat_cons (step6372 p h) (sat_cons (step6400 p h) (sat_cons (step1183 p h) (sat_cons (step1889 p h) (sat_cons (step1190 p h) (sat_cons (step6402 p h) (sat_cons (step224 p h) (sat_cons (step1145 p h) (sat_cons (step1147 p h) (sat_cons (step1158 p h) (sat_cons (step4205 p h) (sat_cons (step6405 p h) (sat_cons (step2032 p h) (sat_cons (step1436 p h) (sat_cons (step1427 p h) (sat_cons (step6043 p h) (sat_cons (step6394 p h) (sat_cons (step2031 p h) (sat_nil p))))))))))))))))))))))
def c6407 : List Lit := [(52, true)]
theorem step6407 (p : Nat → Bool) (h : Constraints p) : clause p c6407 = true :=
  Snake9.LocalRup.prove_clause [c6401, c6406] c6407 (by decide) p (sat_cons (step6401 p h) (sat_cons (step6406 p h) (sat_nil p)))
def c6408 : List Lit := [(7, false)]
theorem step6408 (p : Nat → Bool) (h : Constraints p) : clause p c6408 = true :=
  Snake9.LocalRup.prove_clause [c6407, c6277, c2787] c6408 (by decide) p (sat_cons (step6407 p h) (sat_cons (step6277 p h) (sat_cons (step2787 p h) (sat_nil p))))
def c6409 : List Lit := [(86, false)]
theorem step6409 (p : Nat → Bool) (h : Constraints p) : clause p c6409 = true :=
  Snake9.LocalRup.prove_clause [c6407, c6334] c6409 (by decide) p (sat_cons (step6407 p h) (sat_cons (step6334 p h) (sat_nil p)))
def c6410 : List Lit := [(2, false)]
theorem step6410 (p : Nat → Bool) (h : Constraints p) : clause p c6410 = true :=
  Snake9.LocalRup.prove_clause [c6408, c1815] c6410 (by decide) p (sat_cons (step6408 p h) (sat_cons (step1815 p h) (sat_nil p)))
def c6411 : List Lit := [(838, true)]
theorem step6411 (p : Nat → Bool) (h : Constraints p) : clause p c6411 = true :=
  Snake9.LocalRup.prove_clause [c6408, c924] c6411 (by decide) p (sat_cons (step6408 p h) (sat_cons (step924 p h) (sat_nil p)))
def c6412 : List Lit := [(881, true)]
theorem step6412 (p : Nat → Bool) (h : Constraints p) : clause p c6412 = true :=
  Snake9.LocalRup.prove_clause [c6410, c6373] c6412 (by decide) p (sat_cons (step6410 p h) (sat_cons (step6373 p h) (sat_nil p)))
def c6413 : List Lit := [(842, true)]
theorem step6413 (p : Nat → Bool) (h : Constraints p) : clause p c6413 = true :=
  Snake9.LocalRup.prove_clause [c6411, c932] c6413 (by decide) p (sat_cons (step6411 p h) (sat_cons (step932 p h) (sat_nil p)))
def c6414 : List Lit := [(849, true)]
theorem step6414 (p : Nat → Bool) (h : Constraints p) : clause p c6414 = true :=
  Snake9.LocalRup.prove_clause [c6413, c1638] c6414 (by decide) p (sat_cons (step6413 p h) (sat_cons (step1638 p h) (sat_nil p)))
def c6415 : List Lit := [(959, true)]
theorem step6415 (p : Nat → Bool) (h : Constraints p) : clause p c6415 = true :=
  Snake9.LocalRup.prove_clause [c5859, c6412, c5989, c5858, c1120, c1114, c4583, c1081] c6415 (by decide) p (sat_cons (step5859 p h) (sat_cons (step6412 p h) (sat_cons (step5989 p h) (sat_cons (step5858 p h) (sat_cons (step1120 p h) (sat_cons (step1114 p h) (sat_cons (step4583 p h) (sat_cons (step1081 p h) (sat_nil p)))))))))
def c6416 : List Lit := [(1106, false)]
theorem step6416 (p : Nat → Bool) (h : Constraints p) : clause p c6416 = true :=
  Snake9.LocalRup.prove_clause [c6415, c2031] c6416 (by decide) p (sat_cons (step6415 p h) (sat_cons (step2031 p h) (sat_nil p)))
def c6417 : List Lit := [(1021, false)]
theorem step6417 (p : Nat → Bool) (h : Constraints p) : clause p c6417 = true :=
  Snake9.LocalRup.prove_clause [c6416, c6014] c6417 (by decide) p (sat_cons (step6416 p h) (sat_cons (step6014 p h) (sat_nil p)))
def c6418 : List Lit := [(1084, true)]
theorem step6418 (p : Nat → Bool) (h : Constraints p) : clause p c6418 = true :=
  Snake9.LocalRup.prove_clause [c6416, c6043] c6418 (by decide) p (sat_cons (step6416 p h) (sat_cons (step6043 p h) (sat_nil p)))
def c6419 : List Lit := [(1085, false)]
theorem step6419 (p : Nat → Bool) (h : Constraints p) : clause p c6419 = true :=
  Snake9.LocalRup.prove_clause [c6416, c6369, c1437] c6419 (by decide) p (sat_cons (step6416 p h) (sat_cons (step6369 p h) (sat_cons (step1437 p h) (sat_nil p))))
def c6420 : List Lit := [(1105, true)]
theorem step6420 (p : Nat → Bool) (h : Constraints p) : clause p c6420 = true :=
  Snake9.LocalRup.prove_clause [c6418, c6369, c1436] c6420 (by decide) p (sat_cons (step6418 p h) (sat_cons (step6369 p h) (sat_cons (step1436 p h) (sat_nil p))))
def c6421 : List Lit := [(960, false)]
theorem step6421 (p : Nat → Bool) (h : Constraints p) : clause p c6421 = true :=
  Snake9.LocalRup.prove_clause [c6420, c2032] c6421 (by decide) p (sat_cons (step6420 p h) (sat_cons (step2032 p h) (sat_nil p)))
def c6422 : List Lit := [(883, false)]
theorem step6422 (p : Nat → Bool) (h : Constraints p) : clause p c6422 = true :=
  Snake9.LocalRup.prove_clause [c6421, c5859, c1125] c6422 (by decide) p (sat_cons (step6421 p h) (sat_cons (step5859 p h) (sat_cons (step1125 p h) (sat_nil p))))
def c6423 : List Lit := [(940, false)]
theorem step6423 (p : Nat → Bool) (h : Constraints p) : clause p c6423 = true :=
  Snake9.LocalRup.prove_clause [c6421, c6412, c1115] c6423 (by decide) p (sat_cons (step6421 p h) (sat_cons (step6412 p h) (sat_cons (step1115 p h) (sat_nil p))))
def c6424 : List Lit := [(907, false)]
theorem step6424 (p : Nat → Bool) (h : Constraints p) : clause p c6424 = true :=
  Snake9.LocalRup.prove_clause [c6423, c5858, c1087] c6424 (by decide) p (sat_cons (step6423 p h) (sat_cons (step5858 p h) (sat_cons (step1087 p h) (sat_nil p))))
def c6425 : List Lit := [(903, false)]
theorem step6425 (p : Nat → Bool) (h : Constraints p) : clause p c6425 = true :=
  Snake9.LocalRup.prove_clause [c6424, c1015] c6425 (by decide) p (sat_cons (step6424 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c6426 : List Lit := [(895, false)]
theorem step6426 (p : Nat → Bool) (h : Constraints p) : clause p c6426 = true :=
  Snake9.LocalRup.prove_clause [c6424, c2001] c6426 (by decide) p (sat_cons (step6424 p h) (sat_cons (step2001 p h) (sat_nil p)))
def c6427 : List Lit := [(36, true)]
theorem step6427 (p : Nat → Bool) (h : Constraints p) : clause p c6427 = true :=
  Snake9.LocalRup.prove_clause [c6424, c6069] c6427 (by decide) p (sat_cons (step6424 p h) (sat_cons (step6069 p h) (sat_nil p)))
def c6428 : List Lit := [(87, false), (21, false), (6, false), (28, false), (17, true), (29, false), (33, false), (870, true)]
theorem step6428 (p : Nat → Bool) (h : Constraints p) : clause p c6428 = true :=
  Snake9.LocalRup.prove_clause [c6424, c6425, c6234, c5323, c993, c1017, c995] c6428 (by decide) p (sat_cons (step6424 p h) (sat_cons (step6425 p h) (sat_cons (step6234 p h) (sat_cons (step5323 p h) (sat_cons (step993 p h) (sat_cons (step1017 p h) (sat_cons (step995 p h) (sat_nil p))))))))
def c6429 : List Lit := [(17, true), (70, true), (979, false)]
theorem step6429 (p : Nat → Bool) (h : Constraints p) : clause p c6429 = true :=
  Snake9.LocalRup.prove_clause [c6280, c6423, c5989, c6424, c5858, c6421, c6414, c6408, c6409, c6417, c6427, c6419, c5990, c1141, c1150, c1159, c1246, c1198, c2730, c4471, c2687, c1081, c1121, c1998, c985, c1639, c1717, c6242, c935, c945, c954, c955, c926, c6428, c1184, c1193, c1194, c2322, c1186, c1172, c3075, c5290] c6429 (by decide) p (sat_cons (step6280 p h) (sat_cons (step6423 p h) (sat_cons (step5989 p h) (sat_cons (step6424 p h) (sat_cons (step5858 p h) (sat_cons (step6421 p h) (sat_cons (step6414 p h) (sat_cons (step6408 p h) (sat_cons (step6409 p h) (sat_cons (step6417 p h) (sat_cons (step6427 p h) (sat_cons (step6419 p h) (sat_cons (step5990 p h) (sat_cons (step1141 p h) (sat_cons (step1150 p h) (sat_cons (step1159 p h) (sat_cons (step1246 p h) (sat_cons (step1198 p h) (sat_cons (step2730 p h) (sat_cons (step4471 p h) (sat_cons (step2687 p h) (sat_cons (step1081 p h) (sat_cons (step1121 p h) (sat_cons (step1998 p h) (sat_cons (step985 p h) (sat_cons (step1639 p h) (sat_cons (step1717 p h) (sat_cons (step6242 p h) (sat_cons (step935 p h) (sat_cons (step945 p h) (sat_cons (step954 p h) (sat_cons (step955 p h) (sat_cons (step926 p h) (sat_cons (step6428 p h) (sat_cons (step1184 p h) (sat_cons (step1193 p h) (sat_cons (step1194 p h) (sat_cons (step2322 p h) (sat_cons (step1186 p h) (sat_cons (step1172 p h) (sat_cons (step3075 p h) (sat_cons (step5290 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c6430 : List Lit := [(853, true), (17, false)]
theorem step6430 (p : Nat → Bool) (h : Constraints p) : clause p c6430 = true :=
  Snake9.LocalRup.prove_clause [c942, c943, c1837] c6430 (by decide) p (sat_cons (step942 p h) (sat_cons (step943 p h) (sat_cons (step1837 p h) (sat_nil p))))
def c6431 : List Lit := [(892, false), (857, false)]
theorem step6431 (p : Nat → Bool) (h : Constraints p) : clause p c6431 = true :=
  Snake9.LocalRup.prove_clause [c6426, c6408, c5858, c6421, c995, c998, c2000, c6061, c1081, c1121] c6431 (by decide) p (sat_cons (step6426 p h) (sat_cons (step6408 p h) (sat_cons (step5858 p h) (sat_cons (step6421 p h) (sat_cons (step995 p h) (sat_cons (step998 p h) (sat_cons (step2000 p h) (sat_cons (step6061 p h) (sat_cons (step1081 p h) (sat_cons (step1121 p h) (sat_nil p)))))))))))
def c6432 : List Lit := [(34, false), (17, false)]
theorem step6432 (p : Nat → Bool) (h : Constraints p) : clause p c6432 = true :=
  Snake9.LocalRup.prove_clause [c5858, c6421, c6408, c6422, c6284, c2358, c4196, c1121, c997, c1081, c2000] c6432 (by decide) p (sat_cons (step5858 p h) (sat_cons (step6421 p h) (sat_cons (step6408 p h) (sat_cons (step6422 p h) (sat_cons (step6284 p h) (sat_cons (step2358 p h) (sat_cons (step4196 p h) (sat_cons (step1121 p h) (sat_cons (step997 p h) (sat_cons (step1081 p h) (sat_cons (step2000 p h) (sat_nil p))))))))))))
def c6433 : List Lit := [(17, false)]
theorem step6433 (p : Nat → Bool) (h : Constraints p) : clause p c6433 = true :=
  Snake9.LocalRup.prove_clause [c6430, c947, c6431, c993, c6432] c6433 (by decide) p (sat_cons (step6430 p h) (sat_cons (step947 p h) (sat_cons (step6431 p h) (sat_cons (step993 p h) (sat_cons (step6432 p h) (sat_nil p))))))
def c6434 : List Lit := [(906, true)]
theorem step6434 (p : Nat → Bool) (h : Constraints p) : clause p c6434 = true :=
  Snake9.LocalRup.prove_clause [c6433, c5989, c2730] c6434 (by decide) p (sat_cons (step6433 p h) (sat_cons (step5989 p h) (sat_cons (step2730 p h) (sat_nil p))))
def c6435 : List Lit := [(123, true)]
theorem step6435 (p : Nat → Bool) (h : Constraints p) : clause p c6435 = true :=
  Snake9.LocalRup.prove_clause [c6433, c5989, c5858, c6423, c4471] c6435 (by decide) p (sat_cons (step6433 p h) (sat_cons (step5989 p h) (sat_cons (step5858 p h) (sat_cons (step6423 p h) (sat_cons (step4471 p h) (sat_nil p))))))
def c6436 : List Lit := [(33, true)]
theorem step6436 (p : Nat → Bool) (h : Constraints p) : clause p c6436 = true :=
  Snake9.LocalRup.prove_clause [c6433, c6424, c5989, c2687] c6436 (by decide) p (sat_cons (step6433 p h) (sat_cons (step6424 p h) (sat_cons (step5989 p h) (sat_cons (step2687 p h) (sat_nil p)))))
def c6437 : List Lit := [(939, true)]
theorem step6437 (p : Nat → Bool) (h : Constraints p) : clause p c6437 = true :=
  Snake9.LocalRup.prove_clause [c6434, c5858, c1081] c6437 (by decide) p (sat_cons (step6434 p h) (sat_cons (step5858 p h) (sat_cons (step1081 p h) (sat_nil p))))
def c6438 : List Lit := [(37, false)]
theorem step6438 (p : Nat → Bool) (h : Constraints p) : clause p c6438 = true :=
  Snake9.LocalRup.prove_clause [c6436, c6427, c6279, c115] c6438 (by decide) p (sat_cons (step6436 p h) (sat_cons (step6427 p h) (sat_cons (step6279 p h) (sat_cons (step115 p h) (sat_nil p)))))
def c6439 : List Lit := [(882, false)]
theorem step6439 (p : Nat → Bool) (h : Constraints p) : clause p c6439 = true :=
  Snake9.LocalRup.prove_clause [c6437, c6421, c1121] c6439 (by decide) p (sat_cons (step6437 p h) (sat_cons (step6421 p h) (sat_cons (step1121 p h) (sat_nil p))))
def c6440 : List Lit := [(112, true)]
theorem step6440 (p : Nat → Bool) (h : Constraints p) : clause p c6440 = true :=
  Snake9.LocalRup.prove_clause [c6438, c6427, c1865] c6440 (by decide) p (sat_cons (step6438 p h) (sat_cons (step6427 p h) (sat_cons (step1865 p h) (sat_nil p))))
def c6441 : List Lit := [(850, false)]
theorem step6441 (p : Nat → Bool) (h : Constraints p) : clause p c6441 = true :=
  Snake9.LocalRup.prove_clause [c6439, c1998] c6441 (by decide) p (sat_cons (step6439 p h) (sat_cons (step1998 p h) (sat_nil p)))
def c6442 : List Lit := [(870, false)]
theorem step6442 (p : Nat → Bool) (h : Constraints p) : clause p c6442 = true :=
  Snake9.LocalRup.prove_clause [c6439, c6414, c985] c6442 (by decide) p (sat_cons (step6439 p h) (sat_cons (step6414 p h) (sat_cons (step985 p h) (sat_nil p))))
def c6443 : List Lit := [(843, false)]
theorem step6443 (p : Nat → Bool) (h : Constraints p) : clause p c6443 = true :=
  Snake9.LocalRup.prove_clause [c6441, c1639] c6443 (by decide) p (sat_cons (step6441 p h) (sat_cons (step1639 p h) (sat_nil p)))
def c6444 : List Lit := [(855, false)]
theorem step6444 (p : Nat → Bool) (h : Constraints p) : clause p c6444 = true :=
  Snake9.LocalRup.prove_clause [c6442, c1717] c6444 (by decide) p (sat_cons (step6442 p h) (sat_cons (step1717 p h) (sat_nil p)))
def c6445 : List Lit := [(863, false)]
theorem step6445 (p : Nat → Bool) (h : Constraints p) : clause p c6445 = true :=
  Snake9.LocalRup.prove_clause [c6442, c6433, c6242] c6445 (by decide) p (sat_cons (step6442 p h) (sat_cons (step6433 p h) (sat_cons (step6242 p h) (sat_nil p))))
def c6446 : List Lit := [(839, false)]
theorem step6446 (p : Nat → Bool) (h : Constraints p) : clause p c6446 = true :=
  Snake9.LocalRup.prove_clause [c6443, c935] c6446 (by decide) p (sat_cons (step6443 p h) (sat_cons (step935 p h) (sat_nil p)))
def c6447 : List Lit := [(21, true)]
theorem step6447 (p : Nat → Bool) (h : Constraints p) : clause p c6447 = true :=
  Snake9.LocalRup.prove_clause [c6444, c945] c6447 (by decide) p (sat_cons (step6444 p h) (sat_cons (step945 p h) (sat_nil p)))
def c6448 : List Lit := [(29, true)]
theorem step6448 (p : Nat → Bool) (h : Constraints p) : clause p c6448 = true :=
  Snake9.LocalRup.prove_clause [c6445, c954] c6448 (by decide) p (sat_cons (step6445 p h) (sat_cons (step954 p h) (sat_nil p)))
def c6449 : List Lit := [(28, true)]
theorem step6449 (p : Nat → Bool) (h : Constraints p) : clause p c6449 = true :=
  Snake9.LocalRup.prove_clause [c6445, c955] c6449 (by decide) p (sat_cons (step6445 p h) (sat_cons (step955 p h) (sat_nil p)))
def c6450 : List Lit := [(6, true)]
theorem step6450 (p : Nat → Bool) (h : Constraints p) : clause p c6450 = true :=
  Snake9.LocalRup.prove_clause [c6446, c6408, c926] c6450 (by decide) p (sat_cons (step6446 p h) (sat_cons (step6408 p h) (sat_cons (step926 p h) (sat_nil p))))
def c6451 : List Lit := [(87, false)]
theorem step6451 (p : Nat → Bool) (h : Constraints p) : clause p c6451 = true :=
  Snake9.LocalRup.prove_clause [c6449, c6450, c6447, c6433, c6448, c6436, c6442, c6428] c6451 (by decide) p (sat_cons (step6449 p h) (sat_cons (step6450 p h) (sat_cons (step6447 p h) (sat_cons (step6433 p h) (sat_cons (step6448 p h) (sat_cons (step6436 p h) (sat_cons (step6442 p h) (sat_cons (step6428 p h) (sat_nil p)))))))))
def c6452 : List Lit := [(1001, true)]
theorem step6452 (p : Nat → Bool) (h : Constraints p) : clause p c6452 = true :=
  Snake9.LocalRup.prove_clause [c6451, c6409, c1184] c6452 (by decide) p (sat_cons (step6451 p h) (sat_cons (step6409 p h) (sat_cons (step1184 p h) (sat_nil p))))
def c6453 : List Lit := [(70, false)]
theorem step6453 (p : Nat → Bool) (h : Constraints p) : clause p c6453 = true :=
  Snake9.LocalRup.prove_clause [c6277, c6407, c4477, c2345, c1058, c1047, c1050, c1062, c4475, c1041, c194, c200, c1025, c1028, c1034] c6453 (by decide) p (sat_cons (step6277 p h) (sat_cons (step6407 p h) (sat_cons (step4477 p h) (sat_cons (step2345 p h) (sat_cons (step1058 p h) (sat_cons (step1047 p h) (sat_cons (step1050 p h) (sat_cons (step1062 p h) (sat_cons (step4475 p h) (sat_cons (step1041 p h) (sat_cons (step194 p h) (sat_cons (step200 p h) (sat_cons (step1025 p h) (sat_cons (step1028 p h) (sat_cons (step1034 p h) (sat_nil p))))))))))))))))
def c6454 : List Lit := [(977, true)]
theorem step6454 (p : Nat → Bool) (h : Constraints p) : clause p c6454 = true :=
  Snake9.LocalRup.prove_clause [c6453, c1141] c6454 (by decide) p (sat_cons (step6453 p h) (sat_cons (step1141 p h) (sat_nil p)))
def c6455 : List Lit := [(979, false)]
theorem step6455 (p : Nat → Bool) (h : Constraints p) : clause p c6455 = true :=
  Snake9.LocalRup.prove_clause [c6453, c6433, c6429] c6455 (by decide) p (sat_cons (step6453 p h) (sat_cons (step6433 p h) (sat_cons (step6429 p h) (sat_nil p))))
def c6456 : List Lit := [(981, true)]
theorem step6456 (p : Nat → Bool) (h : Constraints p) : clause p c6456 = true :=
  Snake9.LocalRup.prove_clause [c6454, c1149] c6456 (by decide) p (sat_cons (step6454 p h) (sat_cons (step1149 p h) (sat_nil p)))
def c6457 : List Lit := [(72, true)]
theorem step6457 (p : Nat → Bool) (h : Constraints p) : clause p c6457 = true :=
  Snake9.LocalRup.prove_clause [c6455, c1145] c6457 (by decide) p (sat_cons (step6455 p h) (sat_cons (step1145 p h) (sat_nil p)))
def c6458 : List Lit := [(986, true)]
theorem step6458 (p : Nat → Bool) (h : Constraints p) : clause p c6458 = true :=
  Snake9.LocalRup.prove_clause [c6456, c6280, c1158] c6458 (by decide) p (sat_cons (step6456 p h) (sat_cons (step6280 p h) (sat_cons (step1158 p h) (sat_nil p))))
end B112E097
