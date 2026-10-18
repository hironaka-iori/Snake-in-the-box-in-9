import B112E081Part0002
namespace B112E081
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1386 : List Lit := [(2, true), (944, false), (867, false), (989, false), (21, false), (16, true), (929, false), (8, true), (9, false), (1, false), (7, false)]
theorem step1386 (p : Nat → Bool) (h : Constraints p) : clause p c1386 = true :=
  Snake9.LocalRup.prove_clause [c533, c530, c1351, c1156, c1282, c1058, c1080, c1099, c1036, c1119, c1151, c913, c893, c1035, c34, c12, c9, c19, c846, c848, c1227, c890, c910, c1148, c1383, c1384, c1385, c166, c344, c1347, c1061, c1062, c943, c1070, c972, c1084, c1041, c1103, c1126] c1386 (by decide) p (sat_cons (step533 p h) (sat_cons (step530 p h) (sat_cons (step1351 p h) (sat_cons (step1156 p h) (sat_cons (step1282 p h) (sat_cons (step1058 p h) (sat_cons (step1080 p h) (sat_cons (step1099 p h) (sat_cons (step1036 p h) (sat_cons (step1119 p h) (sat_cons (step1151 p h) (sat_cons (step913 p h) (sat_cons (step893 p h) (sat_cons (step1035 p h) (sat_cons (step34 p h) (sat_cons (step12 p h) (sat_cons (step9 p h) (sat_cons (step19 p h) (sat_cons (step846 p h) (sat_cons (step848 p h) (sat_cons (step1227 p h) (sat_cons (step890 p h) (sat_cons (step910 p h) (sat_cons (step1148 p h) (sat_cons (step1383 p h) (sat_cons (step1384 p h) (sat_cons (step1385 p h) (sat_cons (step166 p h) (sat_cons (step344 p h) (sat_cons (step1347 p h) (sat_cons (step1061 p h) (sat_cons (step1062 p h) (sat_cons (step943 p h) (sat_cons (step1070 p h) (sat_cons (step972 p h) (sat_cons (step1084 p h) (sat_cons (step1041 p h) (sat_cons (step1103 p h) (sat_cons (step1126 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1387 : List Lit := [(46, false), (1054, true), (877, false), (59, true), (944, false), (867, false), (989, false), (931, false), (1, false)]
theorem step1387 (p : Nat → Bool) (h : Constraints p) : clause p c1387 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1058, c1080, c1099, c1371, c1041, c1372, c968] c1387 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1058 p h) (sat_cons (step1080 p h) (sat_cons (step1099 p h) (sat_cons (step1371 p h) (sat_cons (step1041 p h) (sat_cons (step1372 p h) (sat_cons (step968 p h) (sat_nil p)))))))))
def c1388 : List Lit := [(17, true), (19, false), (16, true), (3, true), (840, true)]
theorem step1388 (p : Nat → Bool) (h : Constraints p) : clause p c1388 = true :=
  Snake9.TreeRup.prove_clause [c534, c1350, c1241, c542, c1351, c1156, c530, c569, c1282, c792, c1378, c770, c783, c796, c726, c728, c747, c741, c733, c734, c749, c731, c30, c36, c37, c940, c942, c739, c737, c729, c727, c1377, c759, c780, c773, c771, c765, c766, c760, c128, c755, c122, c123, c87, c89, c88, c1245, c764, c102, c103, c1215, c1056, c820, c1058, c829, c1080, c1099, c1382, c1036, c1119, c1151, c913, c893, c1386, c13, c31, c1380, c837, c1370, c1224, c891, c864, c911, c1149, c1387, c8, c19, c101, c846, c469, c854, c1061, c1083, c1101, c1125, c1041, c1037, c972, c1008, c1251, c945, c1317, c1285] c1388 (by decide) p (sat_cons (step534 p h) (sat_cons (step1350 p h) (sat_cons (step1241 p h) (sat_cons (step542 p h) (sat_cons (step1351 p h) (sat_cons (step1156 p h) (sat_cons (step530 p h) (sat_cons (step569 p h) (sat_cons (step1282 p h) (sat_cons (step792 p h) (sat_cons (step1378 p h) (sat_cons (step770 p h) (sat_cons (step783 p h) (sat_cons (step796 p h) (sat_cons (step726 p h) (sat_cons (step728 p h) (sat_cons (step747 p h) (sat_cons (step741 p h) (sat_cons (step733 p h) (sat_cons (step734 p h) (sat_cons (step749 p h) (sat_cons (step731 p h) (sat_cons (step30 p h) (sat_cons (step36 p h) (sat_cons (step37 p h) (sat_cons (step940 p h) (sat_cons (step942 p h) (sat_cons (step739 p h) (sat_cons (step737 p h) (sat_cons (step729 p h) (sat_cons (step727 p h) (sat_cons (step1377 p h) (sat_cons (step759 p h) (sat_cons (step780 p h) (sat_cons (step773 p h) (sat_cons (step771 p h) (sat_cons (step765 p h) (sat_cons (step766 p h) (sat_cons (step760 p h) (sat_cons (step128 p h) (sat_cons (step755 p h) (sat_cons (step122 p h) (sat_cons (step123 p h) (sat_cons (step87 p h) (sat_cons (step89 p h) (sat_cons (step88 p h) (sat_cons (step1245 p h) (sat_cons (step764 p h) (sat_cons (step102 p h) (sat_cons (step103 p h) (sat_cons (step1215 p h) (sat_cons (step1056 p h) (sat_cons (step820 p h) (sat_cons (step1058 p h) (sat_cons (step829 p h) (sat_cons (step1080 p h) (sat_cons (step1099 p h) (sat_cons (step1382 p h) (sat_cons (step1036 p h) (sat_cons (step1119 p h) (sat_cons (step1151 p h) (sat_cons (step913 p h) (sat_cons (step893 p h) (sat_cons (step1386 p h) (sat_cons (step13 p h) (sat_cons (step31 p h) (sat_cons (step1380 p h) (sat_cons (step837 p h) (sat_cons (step1370 p h) (sat_cons (step1224 p h) (sat_cons (step891 p h) (sat_cons (step864 p h) (sat_cons (step911 p h) (sat_cons (step1149 p h) (sat_cons (step1387 p h) (sat_cons (step8 p h) (sat_cons (step19 p h) (sat_cons (step101 p h) (sat_cons (step846 p h) (sat_cons (step469 p h) (sat_cons (step854 p h) (sat_cons (step1061 p h) (sat_cons (step1083 p h) (sat_cons (step1101 p h) (sat_cons (step1125 p h) (sat_cons (step1041 p h) (sat_cons (step1037 p h) (sat_cons (step972 p h) (sat_cons (step1008 p h) (sat_cons (step1251 p h) (sat_cons (step945 p h) (sat_cons (step1317 p h) (sat_cons (step1285 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1389 : List Lit := [(19, false), (16, true), (3, true), (840, true)]
theorem step1389 (p : Nat → Bool) (h : Constraints p) : clause p c1389 = true :=
  Snake9.TreeRup.prove_clause [c1241, c534, c1350, c537, c541, c542, c530, c1273, c1156, c796, c726, c728, c747, c741, c733, c734, c749, c731, c30, c36, c37, c940, c942, c739, c737, c729, c727, c1377, c792, c1378, c1388, c82, c81, c77, c83, c58, c755, c757, c780, c773, c771, c764, c765, c766, c108, c128, c119, c123, c121, c99, c102, c103, c808, c8, c12, c1215, c1056, c813, c1158, c31, c820, c1221, c833, c837, c1370, c1382, c895, c1224, c905, c1387, c1149] c1389 (by decide) p (sat_cons (step1241 p h) (sat_cons (step534 p h) (sat_cons (step1350 p h) (sat_cons (step537 p h) (sat_cons (step541 p h) (sat_cons (step542 p h) (sat_cons (step530 p h) (sat_cons (step1273 p h) (sat_cons (step1156 p h) (sat_cons (step796 p h) (sat_cons (step726 p h) (sat_cons (step728 p h) (sat_cons (step747 p h) (sat_cons (step741 p h) (sat_cons (step733 p h) (sat_cons (step734 p h) (sat_cons (step749 p h) (sat_cons (step731 p h) (sat_cons (step30 p h) (sat_cons (step36 p h) (sat_cons (step37 p h) (sat_cons (step940 p h) (sat_cons (step942 p h) (sat_cons (step739 p h) (sat_cons (step737 p h) (sat_cons (step729 p h) (sat_cons (step727 p h) (sat_cons (step1377 p h) (sat_cons (step792 p h) (sat_cons (step1378 p h) (sat_cons (step1388 p h) (sat_cons (step82 p h) (sat_cons (step81 p h) (sat_cons (step77 p h) (sat_cons (step83 p h) (sat_cons (step58 p h) (sat_cons (step755 p h) (sat_cons (step757 p h) (sat_cons (step780 p h) (sat_cons (step773 p h) (sat_cons (step771 p h) (sat_cons (step764 p h) (sat_cons (step765 p h) (sat_cons (step766 p h) (sat_cons (step108 p h) (sat_cons (step128 p h) (sat_cons (step119 p h) (sat_cons (step123 p h) (sat_cons (step121 p h) (sat_cons (step99 p h) (sat_cons (step102 p h) (sat_cons (step103 p h) (sat_cons (step808 p h) (sat_cons (step8 p h) (sat_cons (step12 p h) (sat_cons (step1215 p h) (sat_cons (step1056 p h) (sat_cons (step813 p h) (sat_cons (step1158 p h) (sat_cons (step31 p h) (sat_cons (step820 p h) (sat_cons (step1221 p h) (sat_cons (step833 p h) (sat_cons (step837 p h) (sat_cons (step1370 p h) (sat_cons (step1382 p h) (sat_cons (step895 p h) (sat_cons (step1224 p h) (sat_cons (step905 p h) (sat_cons (step1387 p h) (sat_cons (step1149 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1390 : List Lit := [(938, true), (59, true)]
theorem step1390 (p : Nat → Bool) (h : Constraints p) : clause p c1390 = true :=
  Snake9.LocalRup.prove_clause [c557, c953, c955, c951, c948, c1359, c396] c1390 (by decide) p (sat_cons (step557 p h) (sat_cons (step953 p h) (sat_cons (step955 p h) (sat_cons (step951 p h) (sat_cons (step948 p h) (sat_cons (step1359 p h) (sat_cons (step396 p h) (sat_nil p))))))))
def c1391 : List Lit := [(944, true), (934, false), (55, false), (69, true)]
theorem step1391 (p : Nat → Bool) (h : Constraints p) : clause p c1391 = true :=
  Snake9.LocalRup.prove_clause [c559, c950, c956, c963, c967, c957, c942, c944, c952, c939, c940, c330, c417, c390] c1391 (by decide) p (sat_cons (step559 p h) (sat_cons (step950 p h) (sat_cons (step956 p h) (sat_cons (step963 p h) (sat_cons (step967 p h) (sat_cons (step957 p h) (sat_cons (step942 p h) (sat_cons (step944 p h) (sat_cons (step952 p h) (sat_cons (step939 p h) (sat_cons (step940 p h) (sat_cons (step330 p h) (sat_cons (step417 p h) (sat_cons (step390 p h) (sat_nil p)))))))))))))))
def c1392 : List Lit := [(3, false), (866, true), (19, false), (20, false), (921, true), (891, false)]
theorem step1392 (p : Nat → Bool) (h : Constraints p) : clause p c1392 = true :=
  Snake9.LocalRup.prove_clause [c1241, c545, c63, c72, c71, c67, c806, c762, c755, c809, c760, c1219, c826, c879, c820, c927, c1215, c793, c145, c784, c773, c771, c764, c765, c102] c1392 (by decide) p (sat_cons (step1241 p h) (sat_cons (step545 p h) (sat_cons (step63 p h) (sat_cons (step72 p h) (sat_cons (step71 p h) (sat_cons (step67 p h) (sat_cons (step806 p h) (sat_cons (step762 p h) (sat_cons (step755 p h) (sat_cons (step809 p h) (sat_cons (step760 p h) (sat_cons (step1219 p h) (sat_cons (step826 p h) (sat_cons (step879 p h) (sat_cons (step820 p h) (sat_cons (step927 p h) (sat_cons (step1215 p h) (sat_cons (step793 p h) (sat_cons (step145 p h) (sat_cons (step784 p h) (sat_cons (step773 p h) (sat_cons (step771 p h) (sat_cons (step764 p h) (sat_cons (step765 p h) (sat_cons (step102 p h) (sat_nil p))))))))))))))))))))))))))
def c1393 : List Lit := [(29, false), (865, true)]
theorem step1393 (p : Nat → Bool) (h : Constraints p) : clause p c1393 = true :=
  Snake9.LocalRup.prove_clause [c542, c1219, c809, c807, c824, c1217, c816, c1246, c138, c122] c1393 (by decide) p (sat_cons (step542 p h) (sat_cons (step1219 p h) (sat_cons (step809 p h) (sat_cons (step807 p h) (sat_cons (step824 p h) (sat_cons (step1217 p h) (sat_cons (step816 p h) (sat_cons (step1246 p h) (sat_cons (step138 p h) (sat_cons (step122 p h) (sat_nil p)))))))))))
def c1394 : List Lit := [(833, true), (17, true), (865, true), (19, true)]
theorem step1394 (p : Nat → Bool) (h : Constraints p) : clause p c1394 = true :=
  Snake9.LocalRup.prove_clause [c539, c759, c1393, c1269, c1219, c1262, c771, c809, c807, c781, c784, c772, c760, c754, c767, c98, c121] c1394 (by decide) p (sat_cons (step539 p h) (sat_cons (step759 p h) (sat_cons (step1393 p h) (sat_cons (step1269 p h) (sat_cons (step1219 p h) (sat_cons (step1262 p h) (sat_cons (step771 p h) (sat_cons (step809 p h) (sat_cons (step807 p h) (sat_cons (step781 p h) (sat_cons (step784 p h) (sat_cons (step772 p h) (sat_cons (step760 p h) (sat_cons (step754 p h) (sat_cons (step767 p h) (sat_cons (step98 p h) (sat_cons (step121 p h) (sat_nil p))))))))))))))))))
def c1395 : List Lit := [(977, true), (880, true), (929, false), (944, false), (939, false)]
theorem step1395 (p : Nat → Bool) (h : Constraints p) : clause p c1395 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1041, c1037, c972, c1008, c1251, c945, c1317, c1285] c1395 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1041 p h) (sat_cons (step1037 p h) (sat_cons (step972 p h) (sat_cons (step1008 p h) (sat_cons (step1251 p h) (sat_cons (step945 p h) (sat_cons (step1317 p h) (sat_cons (step1285 p h) (sat_nil p))))))))))
def c1396 : List Lit := [(945, true), (929, false), (7, false), (934, false), (55, false), (69, true), (939, false)]
theorem step1396 (p : Nat → Bool) (h : Constraints p) : clause p c1396 = true :=
  Snake9.LocalRup.prove_clause [c559, c942, c950, c972, c968, c945, c959, c957, c310, c952, c416, c408, c409, c949] c1396 (by decide) p (sat_cons (step559 p h) (sat_cons (step942 p h) (sat_cons (step950 p h) (sat_cons (step972 p h) (sat_cons (step968 p h) (sat_cons (step945 p h) (sat_cons (step959 p h) (sat_cons (step957 p h) (sat_cons (step310 p h) (sat_cons (step952 p h) (sat_cons (step416 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step949 p h) (sat_nil p)))))))))))))))
def c1397 : List Lit := [(940, true), (58, true), (934, false), (55, false), (69, true)]
theorem step1397 (p : Nat → Bool) (h : Constraints p) : clause p c1397 = true :=
  Snake9.LocalRup.prove_clause [c559, c950, c959, c957, c952, c416, c408, c409, c949] c1397 (by decide) p (sat_cons (step559 p h) (sat_cons (step950 p h) (sat_cons (step959 p h) (sat_cons (step957 p h) (sat_cons (step952 p h) (sat_cons (step416 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step949 p h) (sat_nil p))))))))))
def c1398 : List Lit := [(1002, true), (32, true), (89, true)]
theorem step1398 (p : Nat → Bool) (h : Constraints p) : clause p c1398 = true :=
  Snake9.LocalRup.prove_clause [c575, c1055, c1057, c1080, c1078, c1058, c1068, c1070, c1056, c1065, c1063, c493, c519] c1398 (by decide) p (sat_cons (step575 p h) (sat_cons (step1055 p h) (sat_cons (step1057 p h) (sat_cons (step1080 p h) (sat_cons (step1078 p h) (sat_cons (step1058 p h) (sat_cons (step1068 p h) (sat_cons (step1070 p h) (sat_cons (step1056 p h) (sat_cons (step1065 p h) (sat_cons (step1063 p h) (sat_cons (step493 p h) (sat_cons (step519 p h) (sat_nil p))))))))))))))
def c1399 : List Lit := [(21, true), (1, false), (20, true), (853, true), (833, true)]
theorem step1399 (p : Nat → Bool) (h : Constraints p) : clause p c1399 = true :=
  Snake9.LocalRup.prove_clause [c537, c1262, c754, c757, c781, c774, c811, c763, c764, c771, c784, c758, c760, c756, c49, c58, c109] c1399 (by decide) p (sat_cons (step537 p h) (sat_cons (step1262 p h) (sat_cons (step754 p h) (sat_cons (step757 p h) (sat_cons (step781 p h) (sat_cons (step774 p h) (sat_cons (step811 p h) (sat_cons (step763 p h) (sat_cons (step764 p h) (sat_cons (step771 p h) (sat_cons (step784 p h) (sat_cons (step758 p h) (sat_cons (step760 p h) (sat_cons (step756 p h) (sat_cons (step49 p h) (sat_cons (step58 p h) (sat_cons (step109 p h) (sat_nil p))))))))))))))))))
def c1400 : List Lit := [(1, false), (53, false), (20, true), (9, false), (10, false), (992, true), (35, false), (853, true), (833, true), (89, true)]
theorem step1400 (p : Nat → Bool) (h : Constraints p) : clause p c1400 = true :=
  Snake9.LocalRup.prove_clause [c545, c530, c145, c30, c1399, c104, c19, c1056, c1061, c175, c54, c8] c1400 (by decide) p (sat_cons (step545 p h) (sat_cons (step530 p h) (sat_cons (step145 p h) (sat_cons (step30 p h) (sat_cons (step1399 p h) (sat_cons (step104 p h) (sat_cons (step19 p h) (sat_cons (step1056 p h) (sat_cons (step1061 p h) (sat_cons (step175 p h) (sat_cons (step54 p h) (sat_cons (step8 p h) (sat_nil p)))))))))))))
def c1401 : List Lit := [(865, true), (841, true), (878, false), (89, true), (797, false), (880, false), (977, false)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true :=
  Snake9.LocalRup.prove_clause [c1241, c543, c1156, c537, c793, c853, c868, c1234, c728, c824, c1219, c1393, c1217, c820, c809, c1363, c816, c1215, c806, c807, c1368, c917, c1149, c1125, c1101, c1083, c797, c749, c747, c739, c741, c737, c733, c734, c731, c132, c142, c1398, c1099, c1124, c1150, c918, c1235, c869, c854, c846, c1400, c121, c767, c769, c784, c1271, c772, c781, c757, c759, c755, c82, c49, c59] c1401 (by decide) p (sat_cons (step1241 p h) (sat_cons (step543 p h) (sat_cons (step1156 p h) (sat_cons (step537 p h) (sat_cons (step793 p h) (sat_cons (step853 p h) (sat_cons (step868 p h) (sat_cons (step1234 p h) (sat_cons (step728 p h) (sat_cons (step824 p h) (sat_cons (step1219 p h) (sat_cons (step1393 p h) (sat_cons (step1217 p h) (sat_cons (step820 p h) (sat_cons (step809 p h) (sat_cons (step1363 p h) (sat_cons (step816 p h) (sat_cons (step1215 p h) (sat_cons (step806 p h) (sat_cons (step807 p h) (sat_cons (step1368 p h) (sat_cons (step917 p h) (sat_cons (step1149 p h) (sat_cons (step1125 p h) (sat_cons (step1101 p h) (sat_cons (step1083 p h) (sat_cons (step797 p h) (sat_cons (step749 p h) (sat_cons (step747 p h) (sat_cons (step739 p h) (sat_cons (step741 p h) (sat_cons (step737 p h) (sat_cons (step733 p h) (sat_cons (step734 p h) (sat_cons (step731 p h) (sat_cons (step132 p h) (sat_cons (step142 p h) (sat_cons (step1398 p h) (sat_cons (step1099 p h) (sat_cons (step1124 p h) (sat_cons (step1150 p h) (sat_cons (step918 p h) (sat_cons (step1235 p h) (sat_cons (step869 p h) (sat_cons (step854 p h) (sat_cons (step846 p h) (sat_cons (step1400 p h) (sat_cons (step121 p h) (sat_cons (step767 p h) (sat_cons (step769 p h) (sat_cons (step784 p h) (sat_cons (step1271 p h) (sat_cons (step772 p h) (sat_cons (step781 p h) (sat_cons (step757 p h) (sat_cons (step759 p h) (sat_cons (step755 p h) (sat_cons (step82 p h) (sat_cons (step49 p h) (sat_cons (step59 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1402 : List Lit := [(825, false), (828, true), (833, true)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c769, c772, c784, c1271] c1402 (by decide) p (sat_cons (step769 p h) (sat_cons (step772 p h) (sat_cons (step784 p h) (sat_cons (step1271 p h) (sat_nil p)))))
def c1403 : List Lit := [(832, true), (819, false), (824, false)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c768, c780, c783, c771, c1271] c1403 (by decide) p (sat_cons (step768 p h) (sat_cons (step780 p h) (sat_cons (step783 p h) (sat_cons (step771 p h) (sat_cons (step1271 p h) (sat_nil p))))))
def c1404 : List Lit := [(811, true), (14, true), (804, false)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c536, c739, c745, c747, c740, c742, c728, c738, c733, c726, c48, c39] c1404 (by decide) p (sat_cons (step536 p h) (sat_cons (step739 p h) (sat_cons (step745 p h) (sat_cons (step747 p h) (sat_cons (step740 p h) (sat_cons (step742 p h) (sat_cons (step728 p h) (sat_cons (step738 p h) (sat_cons (step733 p h) (sat_cons (step726 p h) (sat_cons (step48 p h) (sat_cons (step39 p h) (sat_nil p)))))))))))))
def c1405 : List Lit := [(46, true), (4, true), (1, false), (16, true), (8, true)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c530, c8] c1405 (by decide) p (sat_cons (step530 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1406 : List Lit := [(46, true), (2, true), (1, false), (8, true), (16, true)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c530, c9] c1406 (by decide) p (sat_cons (step530 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1407 : List Lit := [(46, true), (4, true), (1, false), (16, true), (2, true)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c530, c10] c1407 (by decide) p (sat_cons (step530 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1408 : List Lit := [(46, true), (2, true), (1, false), (4, true), (8, true)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c530, c11] c1408 (by decide) p (sat_cons (step530 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1409 : List Lit := [(51, true), (3, false), (19, true)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c531, c16] c1409 (by decide) p (sat_cons (step531 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1410 : List Lit := [(12, true), (51, true), (3, false)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c531, c17] c1410 (by decide) p (sat_cons (step531 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1411 : List Lit := [(12, true), (3, false), (19, true)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c531, c18] c1411 (by decide) p (sat_cons (step531 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1412 : List Lit := [(6, true), (58, true), (7, false)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c532, c27] c1412 (by decide) p (sat_cons (step532 p h) (sat_cons (step27 p h) (sat_nil p)))
def c1413 : List Lit := [(5, true), (58, true), (7, false)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c532, c28] c1413 (by decide) p (sat_cons (step532 p h) (sat_cons (step28 p h) (sat_nil p)))
def c1414 : List Lit := [(6, true), (5, true), (7, false)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c532, c29] c1414 (by decide) p (sat_cons (step532 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1415 : List Lit := [(11, true), (8, true), (59, true), (9, false)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c533, c32] c1415 (by decide) p (sat_cons (step533 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1416 : List Lit := [(11, true), (2, true), (9, false), (59, true)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c533, c33] c1416 (by decide) p (sat_cons (step533 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1417 : List Lit := [(2, true), (59, true), (8, true), (9, false)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c533, c34] c1417 (by decide) p (sat_cons (step533 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1418 : List Lit := [(8, true), (10, false), (12, true)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c534, c35] c1418 (by decide) p (sat_cons (step534 p h) (sat_cons (step35 p h) (sat_nil p)))
def c1419 : List Lit := [(11, true), (8, true), (10, false)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c534, c36] c1419 (by decide) p (sat_cons (step534 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1420 : List Lit := [(13, true), (32, true), (14, false)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c535, c45] c1420 (by decide) p (sat_cons (step535 p h) (sat_cons (step45 p h) (sat_nil p)))
def c1421 : List Lit := [(13, true), (6, true), (14, false)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c535, c46] c1421 (by decide) p (sat_cons (step535 p h) (sat_cons (step46 p h) (sat_nil p)))
def c1422 : List Lit := [(15, false), (13, true)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c536, c47] c1422 (by decide) p (sat_cons (step536 p h) (sat_cons (step47 p h) (sat_nil p)))
def c1423 : List Lit := [(12, true), (15, false)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c536, c48] c1423 (by decide) p (sat_cons (step536 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1424 : List Lit := [(17, false), (16, true), (19, true)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c537, c59] c1424 (by decide) p (sat_cons (step537 p h) (sat_cons (step59 p h) (sat_nil p)))
def c1425 : List Lit := [(24, true), (18, false), (19, true), (16, true)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c538, c61] c1425 (by decide) p (sat_cons (step538 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1426 : List Lit := [(90, true), (20, false), (19, true)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c539, c97] c1426 (by decide) p (sat_cons (step539 p h) (sat_cons (step97 p h) (sat_nil p)))
def c1427 : List Lit := [(23, true), (24, true), (25, false)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c540, c115] c1427 (by decide) p (sat_cons (step540 p h) (sat_cons (step115 p h) (sat_nil p)))
def c1428 : List Lit := [(24, true), (25, false), (19, true)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c540, c116] c1428 (by decide) p (sat_cons (step540 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1429 : List Lit := [(23, true), (25, false), (19, true)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c540, c117] c1429 (by decide) p (sat_cons (step540 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1430 : List Lit := [(26, true), (27, false), (32, true)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c541, c120] c1430 (by decide) p (sat_cons (step541 p h) (sat_cons (step120 p h) (sat_nil p)))
def c1431 : List Lit := [(31, true), (32, true), (29, false)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c542, c122] c1431 (by decide) p (sat_cons (step542 p h) (sat_cons (step122 p h) (sat_nil p)))
def c1432 : List Lit := [(22, true), (32, true), (29, false)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c542, c123] c1432 (by decide) p (sat_cons (step542 p h) (sat_cons (step123 p h) (sat_nil p)))
def c1433 : List Lit := [(31, true), (32, true), (33, false)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c543, c141] c1433 (by decide) p (sat_cons (step543 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1434 : List Lit := [(28, true), (32, true), (33, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c543, c142] c1434 (by decide) p (sat_cons (step543 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1435 : List Lit := [(38, true), (34, false), (19, true)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c544, c143] c1435 (by decide) p (sat_cons (step544 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1436 : List Lit := [(35, false), (36, true)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c545, c144] c1436 (by decide) p (sat_cons (step545 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1437 : List Lit := [(35, false), (22, true)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c545, c145] c1437 (by decide) p (sat_cons (step545 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1438 : List Lit := [(41, true), (36, false), (153, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c1196, c146] c1438 (by decide) p (sat_cons (step1196 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1439 : List Lit := [(40, true), (41, false), (32, true)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c547, c154] c1439 (by decide) p (sat_cons (step547 p h) (sat_cons (step154 p h) (sat_nil p)))
def c1440 : List Lit := [(39, true), (40, true), (42, false)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c548, c156] c1440 (by decide) p (sat_cons (step548 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1441 : List Lit := [(39, true), (38, true), (42, false)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c548, c158] c1441 (by decide) p (sat_cons (step548 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1442 : List Lit := [(161, true), (44, false), (34, true)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c1197, c1198, c160] c1442 (by decide) p (sat_cons (step1197 p h) (sat_cons (step1198 p h) (sat_cons (step160 p h) (sat_nil p))))
def c1443 : List Lit := [(46, true), (2, true), (47, false), (50, true), (59, true), (88, true)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c551, c204] c1443 (by decide) p (sat_cons (step551 p h) (sat_cons (step204 p h) (sat_nil p)))
def c1444 : List Lit := [(51, true), (48, false), (54, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c552, c206] c1444 (by decide) p (sat_cons (step552 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1445 : List Lit := [(48, false), (46, true), (54, true)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c552, c207] c1445 (by decide) p (sat_cons (step552 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1446 : List Lit := [(48, false), (51, true), (46, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c552, c208] c1446 (by decide) p (sat_cons (step552 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1447 : List Lit := [(51, true), (46, true), (50, true), (61, true), (49, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c553, c211] c1447 (by decide) p (sat_cons (step553 p h) (sat_cons (step211 p h) (sat_nil p)))
def c1448 : List Lit := [(56, true), (51, true), (50, true), (46, true), (49, false)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c553, c212] c1448 (by decide) p (sat_cons (step553 p h) (sat_cons (step212 p h) (sat_nil p)))
def c1449 : List Lit := [(72, true), (51, true), (90, true), (52, false), (58, true), (50, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c554, c259] c1449 (by decide) p (sat_cons (step554 p h) (sat_cons (step259 p h) (sat_nil p)))
end B112E081
