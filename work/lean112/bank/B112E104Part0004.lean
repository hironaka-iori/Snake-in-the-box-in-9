import B112E104Part0003
namespace B112E104
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1412 : List Lit := [(1678, true), (1648, false), (1589, false), (34, true), (70, true), (81, false), (1612, false), (1588, false), (106, true), (108, false)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c558, c539, c960, c427, c428, c1149, c1103, c1381, c1084, c909, c1002, c1403, c206, c828, c297, c826, c983, c344, c993, c984] c1412 (by decide) p (sat_cons (step558 p h) (sat_cons (step539 p h) (sat_cons (step960 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step1149 p h) (sat_cons (step1103 p h) (sat_cons (step1381 p h) (sat_cons (step1084 p h) (sat_cons (step909 p h) (sat_cons (step1002 p h) (sat_cons (step1403 p h) (sat_cons (step206 p h) (sat_cons (step828 p h) (sat_cons (step297 p h) (sat_cons (step826 p h) (sat_cons (step983 p h) (sat_cons (step344 p h) (sat_cons (step993 p h) (sat_cons (step984 p h) (sat_nil p)))))))))))))))))))))
def c1413 : List Lit := [(1648, false), (1589, false), (70, true), (37, true), (81, false), (1612, false), (1588, false), (106, true), (117, false), (107, false), (108, false)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c558, c521, c1127, c1220, c1203, c1205, c523, c164, c1370, c875, c885, c1122, c960, c1104, c1398, c134, c825, c827, c427, c428, c1149, c982, c1089, c1003, c1412, c1123, c886, c878, c876, c847, c845, c1240, c828, c1402, c851, c852, c826, c1157, c141, c475, c476, c345, c344, c130, c1027, c1009, c984, c983, c990, c994, c986, c1016, c1360, c307] c1413 (by decide) p (sat_cons (step558 p h) (sat_cons (step521 p h) (sat_cons (step1127 p h) (sat_cons (step1220 p h) (sat_cons (step1203 p h) (sat_cons (step1205 p h) (sat_cons (step523 p h) (sat_cons (step164 p h) (sat_cons (step1370 p h) (sat_cons (step875 p h) (sat_cons (step885 p h) (sat_cons (step1122 p h) (sat_cons (step960 p h) (sat_cons (step1104 p h) (sat_cons (step1398 p h) (sat_cons (step134 p h) (sat_cons (step825 p h) (sat_cons (step827 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step1149 p h) (sat_cons (step982 p h) (sat_cons (step1089 p h) (sat_cons (step1003 p h) (sat_cons (step1412 p h) (sat_cons (step1123 p h) (sat_cons (step886 p h) (sat_cons (step878 p h) (sat_cons (step876 p h) (sat_cons (step847 p h) (sat_cons (step845 p h) (sat_cons (step1240 p h) (sat_cons (step828 p h) (sat_cons (step1402 p h) (sat_cons (step851 p h) (sat_cons (step852 p h) (sat_cons (step826 p h) (sat_cons (step1157 p h) (sat_cons (step141 p h) (sat_cons (step475 p h) (sat_cons (step476 p h) (sat_cons (step345 p h) (sat_cons (step344 p h) (sat_cons (step130 p h) (sat_cons (step1027 p h) (sat_cons (step1009 p h) (sat_cons (step984 p h) (sat_cons (step983 p h) (sat_cons (step990 p h) (sat_cons (step994 p h) (sat_cons (step986 p h) (sat_cons (step1016 p h) (sat_cons (step1360 p h) (sat_cons (step307 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1414 : List Lit := [(1612, false), (106, true), (117, false), (1571, false), (107, false), (108, false)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c558, c547, c521, c1205, c1220, c1127, c427, c428, c1149, c982, c932, c1214, c952, c1407, c1036, c1405, c1398, c1410, c939, c240, c241, c414, c419, c243, c134, c1411, c937, c946, c953, c1413, c1037, c1041, c1034, c1016, c1406, c1009, c1344, c364, c355, c345, c852, c984, c905, c826, c1240, c990, c913, c828, c1001, c918, c847, c1077, c964, c879, c1108, c887, c1124] c1414 (by decide) p (sat_cons (step558 p h) (sat_cons (step547 p h) (sat_cons (step521 p h) (sat_cons (step1205 p h) (sat_cons (step1220 p h) (sat_cons (step1127 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step1149 p h) (sat_cons (step982 p h) (sat_cons (step932 p h) (sat_cons (step1214 p h) (sat_cons (step952 p h) (sat_cons (step1407 p h) (sat_cons (step1036 p h) (sat_cons (step1405 p h) (sat_cons (step1398 p h) (sat_cons (step1410 p h) (sat_cons (step939 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step414 p h) (sat_cons (step419 p h) (sat_cons (step243 p h) (sat_cons (step134 p h) (sat_cons (step1411 p h) (sat_cons (step937 p h) (sat_cons (step946 p h) (sat_cons (step953 p h) (sat_cons (step1413 p h) (sat_cons (step1037 p h) (sat_cons (step1041 p h) (sat_cons (step1034 p h) (sat_cons (step1016 p h) (sat_cons (step1406 p h) (sat_cons (step1009 p h) (sat_cons (step1344 p h) (sat_cons (step364 p h) (sat_cons (step355 p h) (sat_cons (step345 p h) (sat_cons (step852 p h) (sat_cons (step984 p h) (sat_cons (step905 p h) (sat_cons (step826 p h) (sat_cons (step1240 p h) (sat_cons (step990 p h) (sat_cons (step913 p h) (sat_cons (step828 p h) (sat_cons (step1001 p h) (sat_cons (step918 p h) (sat_cons (step847 p h) (sat_cons (step1077 p h) (sat_cons (step964 p h) (sat_cons (step879 p h) (sat_cons (step1108 p h) (sat_cons (step887 p h) (sat_cons (step1124 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1415 : List Lit := [(1621, true), (102, true), (1617, false), (106, true), (108, false)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c558, c427, c428, c1149, c982, c991, c993, c986, c1367] c1415 (by decide) p (sat_cons (step558 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step1149 p h) (sat_cons (step982 p h) (sat_cons (step991 p h) (sat_cons (step993 p h) (sat_cons (step986 p h) (sat_cons (step1367 p h) (sat_nil p))))))))))
def c1416 : List Lit := [(1625, false), (1678, true), (1589, false), (1644, false), (104, false), (108, false)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c960, c1103, c1037, c1078, c1079, c1109, c1042, c964, c1016, c918, c1009, c913, c355, c905] c1416 (by decide) p (sat_cons (step960 p h) (sat_cons (step1103 p h) (sat_cons (step1037 p h) (sat_cons (step1078 p h) (sat_cons (step1079 p h) (sat_cons (step1109 p h) (sat_cons (step1042 p h) (sat_cons (step964 p h) (sat_cons (step1016 p h) (sat_cons (step918 p h) (sat_cons (step1009 p h) (sat_cons (step913 p h) (sat_cons (step355 p h) (sat_cons (step905 p h) (sat_nil p)))))))))))))))
def c1417 : List Lit := [(1617, false), (1621, true), (1597, false), (1641, false), (106, true), (117, false), (107, false), (108, false)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c558, c427, c428, c1149, c982, c1370, c990, c993, c1415, c983, c364, c306, c1009, c1360, c1016] c1417 (by decide) p (sat_cons (step558 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step1149 p h) (sat_cons (step982 p h) (sat_cons (step1370 p h) (sat_cons (step990 p h) (sat_cons (step993 p h) (sat_cons (step1415 p h) (sat_cons (step983 p h) (sat_cons (step364 p h) (sat_cons (step306 p h) (sat_cons (step1009 p h) (sat_cons (step1360 p h) (sat_cons (step1016 p h) (sat_nil p))))))))))))))))
def c1418 : List Lit := [(106, true), (117, false), (1571, false), (107, false), (108, false)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c558, c547, c1220, c1127, c1370, c1214, c427, c428, c1414, c977, c975, c488, c490, c470, c489, c1143, c1023, c1027, c852, c240, c1032, c1240, c939, c1400, c876, c960, c886, c1123, c1416, c997, c1417, c984, c985, c364, c1367, c307, c1009, c992, c1360, c1016] c1418 (by decide) p (sat_cons (step558 p h) (sat_cons (step547 p h) (sat_cons (step1220 p h) (sat_cons (step1127 p h) (sat_cons (step1370 p h) (sat_cons (step1214 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step1414 p h) (sat_cons (step977 p h) (sat_cons (step975 p h) (sat_cons (step488 p h) (sat_cons (step490 p h) (sat_cons (step470 p h) (sat_cons (step489 p h) (sat_cons (step1143 p h) (sat_cons (step1023 p h) (sat_cons (step1027 p h) (sat_cons (step852 p h) (sat_cons (step240 p h) (sat_cons (step1032 p h) (sat_cons (step1240 p h) (sat_cons (step939 p h) (sat_cons (step1400 p h) (sat_cons (step876 p h) (sat_cons (step960 p h) (sat_cons (step886 p h) (sat_cons (step1123 p h) (sat_cons (step1416 p h) (sat_cons (step997 p h) (sat_cons (step1417 p h) (sat_cons (step984 p h) (sat_cons (step985 p h) (sat_cons (step364 p h) (sat_cons (step1367 p h) (sat_cons (step307 p h) (sat_cons (step1009 p h) (sat_cons (step992 p h) (sat_cons (step1360 p h) (sat_cons (step1016 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c1419 : List Lit := [(1625, true), (1649, true), (102, true), (99, true), (117, false), (107, false), (108, false)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c558, c981, c984, c990, c997, c1001, c991, c993, c977, c986, c983, c975, c301, c488, c490, c489, c429, c1023, c1027, c363, c1032, c1009, c1042, c1016] c1419 (by decide) p (sat_cons (step558 p h) (sat_cons (step981 p h) (sat_cons (step984 p h) (sat_cons (step990 p h) (sat_cons (step997 p h) (sat_cons (step1001 p h) (sat_cons (step991 p h) (sat_cons (step993 p h) (sat_cons (step977 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step975 p h) (sat_cons (step301 p h) (sat_cons (step488 p h) (sat_cons (step490 p h) (sat_cons (step489 p h) (sat_cons (step429 p h) (sat_cons (step1023 p h) (sat_cons (step1027 p h) (sat_cons (step363 p h) (sat_cons (step1032 p h) (sat_cons (step1009 p h) (sat_cons (step1042 p h) (sat_cons (step1016 p h) (sat_nil p)))))))))))))))))))))))))
def c1420 : List Lit := [(117, false), (1571, false), (107, false), (108, false)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c521, c1203, c1220, c1127, c536, c1398, c1407, c1036, c1418, c391, c416, c407, c401, c410, c411, c1402, c134, c939, c909, c981, c984, c825, c941, c911, c990, c827, c1400, c918, c996, c845, c964, c878, c886, c1123, c1109, c1073, c1419, c1077, c1078, c1115, c1041, c969, c1014, c1016, c919, c922, c1011, c1009, c912, c914, c904, c910, c905, c906, c903, c205, c185, c287, c187] c1420 (by decide) p (sat_cons (step521 p h) (sat_cons (step1203 p h) (sat_cons (step1220 p h) (sat_cons (step1127 p h) (sat_cons (step536 p h) (sat_cons (step1398 p h) (sat_cons (step1407 p h) (sat_cons (step1036 p h) (sat_cons (step1418 p h) (sat_cons (step391 p h) (sat_cons (step416 p h) (sat_cons (step407 p h) (sat_cons (step401 p h) (sat_cons (step410 p h) (sat_cons (step411 p h) (sat_cons (step1402 p h) (sat_cons (step134 p h) (sat_cons (step939 p h) (sat_cons (step909 p h) (sat_cons (step981 p h) (sat_cons (step984 p h) (sat_cons (step825 p h) (sat_cons (step941 p h) (sat_cons (step911 p h) (sat_cons (step990 p h) (sat_cons (step827 p h) (sat_cons (step1400 p h) (sat_cons (step918 p h) (sat_cons (step996 p h) (sat_cons (step845 p h) (sat_cons (step964 p h) (sat_cons (step878 p h) (sat_cons (step886 p h) (sat_cons (step1123 p h) (sat_cons (step1109 p h) (sat_cons (step1073 p h) (sat_cons (step1419 p h) (sat_cons (step1077 p h) (sat_cons (step1078 p h) (sat_cons (step1115 p h) (sat_cons (step1041 p h) (sat_cons (step969 p h) (sat_cons (step1014 p h) (sat_cons (step1016 p h) (sat_cons (step919 p h) (sat_cons (step922 p h) (sat_cons (step1011 p h) (sat_cons (step1009 p h) (sat_cons (step912 p h) (sat_cons (step914 p h) (sat_cons (step904 p h) (sat_cons (step910 p h) (sat_cons (step905 p h) (sat_cons (step906 p h) (sat_cons (step903 p h) (sat_cons (step205 p h) (sat_cons (step185 p h) (sat_cons (step287 p h) (sat_cons (step187 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1421 : List Lit := [(116, false), (1634, true), (1641, true)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c1016, c1009, c1014, c1011, c460, c459, c1027] c1421 (by decide) p (sat_cons (step1016 p h) (sat_cons (step1009 p h) (sat_cons (step1014 p h) (sat_cons (step1011 p h) (sat_cons (step460 p h) (sat_cons (step459 p h) (sat_cons (step1027 p h) (sat_nil p))))))))
def c1422 : List Lit := [(1634, true), (1644, true), (117, true), (103, true)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c559, c562, c1335, c1032, c1014, c1011, c1421, c430, c457, c1026, c1027, c1034, c448, c449, c1024] c1422 (by decide) p (sat_cons (step559 p h) (sat_cons (step562 p h) (sat_cons (step1335 p h) (sat_cons (step1032 p h) (sat_cons (step1014 p h) (sat_cons (step1011 p h) (sat_cons (step1421 p h) (sat_cons (step430 p h) (sat_cons (step457 p h) (sat_cons (step1026 p h) (sat_cons (step1027 p h) (sat_cons (step1034 p h) (sat_cons (step448 p h) (sat_cons (step449 p h) (sat_cons (step1024 p h) (sat_nil p))))))))))))))))
def c1423 : List Lit := [(1648, true), (117, true), (103, true)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c562, c1335, c1030, c1037, c1045, c1422, c1041, c1031, c1025, c1026, c457, c461, c462, c1009, c1011, c1017] c1423 (by decide) p (sat_cons (step562 p h) (sat_cons (step1335 p h) (sat_cons (step1030 p h) (sat_cons (step1037 p h) (sat_cons (step1045 p h) (sat_cons (step1422 p h) (sat_cons (step1041 p h) (sat_cons (step1031 p h) (sat_cons (step1025 p h) (sat_cons (step1026 p h) (sat_cons (step457 p h) (sat_cons (step461 p h) (sat_cons (step462 p h) (sat_cons (step1009 p h) (sat_cons (step1011 p h) (sat_cons (step1017 p h) (sat_nil p)))))))))))))))))
def c1424 : List Lit := [(106, false), (1571, false), (107, false), (108, false)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c1220, c1127, c550, c558, c1398, c1420, c1423, c1370, c1337, c886, c1123, c932, c407, c401, c410, c411, c939, c1215, c909, c981, c984, c941, c911, c990, c1400, c918, c996, c964, c1109, c1373, c1072, c1078, c977, c1115, c997, c975, c969, c965, c991, c993, c255, c919, c954, c986, c983, c244, c914, c947, c301, c937, c905, c429, c349] c1424 (by decide) p (sat_cons (step1220 p h) (sat_cons (step1127 p h) (sat_cons (step550 p h) (sat_cons (step558 p h) (sat_cons (step1398 p h) (sat_cons (step1420 p h) (sat_cons (step1423 p h) (sat_cons (step1370 p h) (sat_cons (step1337 p h) (sat_cons (step886 p h) (sat_cons (step1123 p h) (sat_cons (step932 p h) (sat_cons (step407 p h) (sat_cons (step401 p h) (sat_cons (step410 p h) (sat_cons (step411 p h) (sat_cons (step939 p h) (sat_cons (step1215 p h) (sat_cons (step909 p h) (sat_cons (step981 p h) (sat_cons (step984 p h) (sat_cons (step941 p h) (sat_cons (step911 p h) (sat_cons (step990 p h) (sat_cons (step1400 p h) (sat_cons (step918 p h) (sat_cons (step996 p h) (sat_cons (step964 p h) (sat_cons (step1109 p h) (sat_cons (step1373 p h) (sat_cons (step1072 p h) (sat_cons (step1078 p h) (sat_cons (step977 p h) (sat_cons (step1115 p h) (sat_cons (step997 p h) (sat_cons (step975 p h) (sat_cons (step969 p h) (sat_cons (step965 p h) (sat_cons (step991 p h) (sat_cons (step993 p h) (sat_cons (step255 p h) (sat_cons (step919 p h) (sat_cons (step954 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step244 p h) (sat_cons (step914 p h) (sat_cons (step947 p h) (sat_cons (step301 p h) (sat_cons (step937 p h) (sat_cons (step905 p h) (sat_cons (step429 p h) (sat_cons (step349 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1425 : List Lit := [(1617, false), (1625, true), (1571, false), (107, false), (108, false)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c1220, c1127, c558, c550, c997, c1424, c427, c428, c1149, c982, c1398, c1420, c1423, c1370, c1337, c886, c1123, c932, c990, c1415, c996, c1001, c1235, c360, c1072, c977, c905, c1115, c975, c913, c255, c918, c245, c244, c965, c939, c937, c954, c947] c1425 (by decide) p (sat_cons (step1220 p h) (sat_cons (step1127 p h) (sat_cons (step558 p h) (sat_cons (step550 p h) (sat_cons (step997 p h) (sat_cons (step1424 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step1149 p h) (sat_cons (step982 p h) (sat_cons (step1398 p h) (sat_cons (step1420 p h) (sat_cons (step1423 p h) (sat_cons (step1370 p h) (sat_cons (step1337 p h) (sat_cons (step886 p h) (sat_cons (step1123 p h) (sat_cons (step932 p h) (sat_cons (step990 p h) (sat_cons (step1415 p h) (sat_cons (step996 p h) (sat_cons (step1001 p h) (sat_cons (step1235 p h) (sat_cons (step360 p h) (sat_cons (step1072 p h) (sat_cons (step977 p h) (sat_cons (step905 p h) (sat_cons (step1115 p h) (sat_cons (step975 p h) (sat_cons (step913 p h) (sat_cons (step255 p h) (sat_cons (step918 p h) (sat_cons (step245 p h) (sat_cons (step244 p h) (sat_cons (step965 p h) (sat_cons (step939 p h) (sat_cons (step937 p h) (sat_cons (step954 p h) (sat_cons (step947 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1426 : List Lit := [(1625, true), (1571, false), (107, false), (108, false)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c1220, c1127, c558, c550, c932, c1424, c1214, c952, c428, c427, c1370, c1420, c1337, c886, c1123, c1425, c984, c985, c1235, c364, c1367, c307, c905, c1009, c992, c913, c1016, c996, c1001, c918, c977, c963, c974, c975, c1103, c254, c258, c1368, c1074, c1025, c1042, c1365, c1034, c1024] c1426 (by decide) p (sat_cons (step1220 p h) (sat_cons (step1127 p h) (sat_cons (step558 p h) (sat_cons (step550 p h) (sat_cons (step932 p h) (sat_cons (step1424 p h) (sat_cons (step1214 p h) (sat_cons (step952 p h) (sat_cons (step428 p h) (sat_cons (step427 p h) (sat_cons (step1370 p h) (sat_cons (step1420 p h) (sat_cons (step1337 p h) (sat_cons (step886 p h) (sat_cons (step1123 p h) (sat_cons (step1425 p h) (sat_cons (step984 p h) (sat_cons (step985 p h) (sat_cons (step1235 p h) (sat_cons (step364 p h) (sat_cons (step1367 p h) (sat_cons (step307 p h) (sat_cons (step905 p h) (sat_cons (step1009 p h) (sat_cons (step992 p h) (sat_cons (step913 p h) (sat_cons (step1016 p h) (sat_cons (step996 p h) (sat_cons (step1001 p h) (sat_cons (step918 p h) (sat_cons (step977 p h) (sat_cons (step963 p h) (sat_cons (step974 p h) (sat_cons (step975 p h) (sat_cons (step1103 p h) (sat_cons (step254 p h) (sat_cons (step258 p h) (sat_cons (step1368 p h) (sat_cons (step1074 p h) (sat_cons (step1025 p h) (sat_cons (step1042 p h) (sat_cons (step1365 p h) (sat_cons (step1034 p h) (sat_cons (step1024 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1427 : List Lit := [(102, false), (1571, false), (107, false), (108, false)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c558, c1220, c1127, c932, c1424, c1214, c952, c1370, c1420, c1337, c886, c1123, c1398, c1423, c1426, c1078, c1109, c968, c919, c427, c1235, c360, c905, c913, c914, c918, c909, c964, c1351, c953] c1427 (by decide) p (sat_cons (step558 p h) (sat_cons (step1220 p h) (sat_cons (step1127 p h) (sat_cons (step932 p h) (sat_cons (step1424 p h) (sat_cons (step1214 p h) (sat_cons (step952 p h) (sat_cons (step1370 p h) (sat_cons (step1420 p h) (sat_cons (step1337 p h) (sat_cons (step886 p h) (sat_cons (step1123 p h) (sat_cons (step1398 p h) (sat_cons (step1423 p h) (sat_cons (step1426 p h) (sat_cons (step1078 p h) (sat_cons (step1109 p h) (sat_cons (step968 p h) (sat_cons (step919 p h) (sat_cons (step427 p h) (sat_cons (step1235 p h) (sat_cons (step360 p h) (sat_cons (step905 p h) (sat_cons (step913 p h) (sat_cons (step914 p h) (sat_cons (step918 p h) (sat_cons (step909 p h) (sat_cons (step964 p h) (sat_cons (step1351 p h) (sat_cons (step953 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1428 : List Lit := [(67, true), (102, true), (1598, true), (97, true), (106, true), (1648, false), (1678, true), (1571, false), (107, false)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c536, c932, c1214, c952, c968, c919, c916, c905, c907, c913, c914, c918, c922, c908, c909, c963, c964, c904, c210, c1103, c956, c903, c1230, c1084, c933, c185, c983, c998, c927, c994, c986, c198, c279, c188] c1428 (by decide) p (sat_cons (step536 p h) (sat_cons (step932 p h) (sat_cons (step1214 p h) (sat_cons (step952 p h) (sat_cons (step968 p h) (sat_cons (step919 p h) (sat_cons (step916 p h) (sat_cons (step905 p h) (sat_cons (step907 p h) (sat_cons (step913 p h) (sat_cons (step914 p h) (sat_cons (step918 p h) (sat_cons (step922 p h) (sat_cons (step908 p h) (sat_cons (step909 p h) (sat_cons (step963 p h) (sat_cons (step964 p h) (sat_cons (step904 p h) (sat_cons (step210 p h) (sat_cons (step1103 p h) (sat_cons (step956 p h) (sat_cons (step903 p h) (sat_cons (step1230 p h) (sat_cons (step1084 p h) (sat_cons (step933 p h) (sat_cons (step185 p h) (sat_cons (step983 p h) (sat_cons (step998 p h) (sat_cons (step927 p h) (sat_cons (step994 p h) (sat_cons (step986 p h) (sat_cons (step198 p h) (sat_cons (step279 p h) (sat_cons (step188 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1429 : List Lit := [(1589, true), (84, true), (1583, false), (1571, false)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c935, c932, c956, c953, c933, c946, c944, c927, c937, c938, c1212] c1429 (by decide) p (sat_cons (step935 p h) (sat_cons (step932 p h) (sat_cons (step956 p h) (sat_cons (step953 p h) (sat_cons (step933 p h) (sat_cons (step946 p h) (sat_cons (step944 p h) (sat_cons (step927 p h) (sat_cons (step937 p h) (sat_cons (step938 p h) (sat_cons (step1212 p h) (sat_nil p))))))))))))
def c1430 : List Lit := [(1571, false), (107, false), (108, false)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c1220, c1127, c558, c557, c1398, c1370, c932, c1420, c1337, c886, c1123, c1423, c1424, c1214, c427, c428, c1149, c1426, c1078, c1109, c961, c954, c1427, c984, c1415, c1428, c349, c1429, c960, c964, c1103, c918, c1084, c911, c913, c1002, c909, c906, c977, c210, c975, c425, c245, c244, c939, c937, c947] c1430 (by decide) p (sat_cons (step1220 p h) (sat_cons (step1127 p h) (sat_cons (step558 p h) (sat_cons (step557 p h) (sat_cons (step1398 p h) (sat_cons (step1370 p h) (sat_cons (step932 p h) (sat_cons (step1420 p h) (sat_cons (step1337 p h) (sat_cons (step886 p h) (sat_cons (step1123 p h) (sat_cons (step1423 p h) (sat_cons (step1424 p h) (sat_cons (step1214 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step1149 p h) (sat_cons (step1426 p h) (sat_cons (step1078 p h) (sat_cons (step1109 p h) (sat_cons (step961 p h) (sat_cons (step954 p h) (sat_cons (step1427 p h) (sat_cons (step984 p h) (sat_cons (step1415 p h) (sat_cons (step1428 p h) (sat_cons (step349 p h) (sat_cons (step1429 p h) (sat_cons (step960 p h) (sat_cons (step964 p h) (sat_cons (step1103 p h) (sat_cons (step918 p h) (sat_cons (step1084 p h) (sat_cons (step911 p h) (sat_cons (step913 p h) (sat_cons (step1002 p h) (sat_cons (step909 p h) (sat_cons (step906 p h) (sat_cons (step977 p h) (sat_cons (step210 p h) (sat_cons (step975 p h) (sat_cons (step425 p h) (sat_cons (step245 p h) (sat_cons (step244 p h) (sat_cons (step939 p h) (sat_cons (step937 p h) (sat_cons (step947 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c1431 : List Lit := [(1, false), (6, true), (119, true)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c1163, c1] c1431 (by decide) p (sat_cons (step1163 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1432 : List Lit := [(3, false), (8, true), (5, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c1164, c3] c1432 (by decide) p (sat_cons (step1164 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1433 : List Lit := [(8, true), (3, false), (121, true)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c1164, c5] c1433 (by decide) p (sat_cons (step1164 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1434 : List Lit := [(3, false), (5, true), (121, true)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c1164, c6] c1434 (by decide) p (sat_cons (step1164 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1435 : List Lit := [(5, false), (15, true)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c507, c8] c1435 (by decide) p (sat_cons (step507 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1436 : List Lit := [(5, false), (3, true)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c507, c9] c1436 (by decide) p (sat_cons (step507 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1437 : List Lit := [(11, true), (6, false), (18, true)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c508, c11] c1437 (by decide) p (sat_cons (step508 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1438 : List Lit := [(1, true), (6, false), (18, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c508, c12] c1438 (by decide) p (sat_cons (step508 p h) (sat_cons (step12 p h) (sat_nil p)))
def c1439 : List Lit := [(22, true), (7, true), (8, false)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c509, c17] c1439 (by decide) p (sat_cons (step509 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1440 : List Lit := [(22, true), (3, true), (8, false)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c509, c18] c1440 (by decide) p (sat_cons (step509 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1441 : List Lit := [(11, true), (9, false), (10, true)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c510, c20] c1441 (by decide) p (sat_cons (step510 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1442 : List Lit := [(7, true), (11, true), (9, false)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c510, c21] c1442 (by decide) p (sat_cons (step510 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1443 : List Lit := [(16, true), (13, false), (18, true)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c511, c32] c1443 (by decide) p (sat_cons (step511 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1444 : List Lit := [(12, true), (13, false), (18, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c511, c33] c1444 (by decide) p (sat_cons (step511 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1445 : List Lit := [(16, true), (12, true), (13, false)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c511, c34] c1445 (by decide) p (sat_cons (step511 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1446 : List Lit := [(16, true), (12, true), (14, false), (20, true), (32, true), (64, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c512, c44] c1446 (by decide) p (sat_cons (step512 p h) (sat_cons (step44 p h) (sat_nil p)))
def c1447 : List Lit := [(12, true), (20, true), (18, true), (17, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c513, c56] c1447 (by decide) p (sat_cons (step513 p h) (sat_cons (step56 p h) (sat_nil p)))
def c1448 : List Lit := [(19, false), (68, true), (18, true)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c514, c88] c1448 (by decide) p (sat_cons (step514 p h) (sat_cons (step88 p h) (sat_nil p)))
def c1449 : List Lit := [(29, true), (19, false), (18, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c514, c89] c1449 (by decide) p (sat_cons (step514 p h) (sat_cons (step89 p h) (sat_nil p)))
def c1450 : List Lit := [(20, true), (21, false), (18, true)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c515, c99] c1450 (by decide) p (sat_cons (step515 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1451 : List Lit := [(16, true), (20, true), (21, false)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c515, c100] c1451 (by decide) p (sat_cons (step515 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1452 : List Lit := [(16, true), (21, false), (18, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c515, c101] c1452 (by decide) p (sat_cons (step515 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1453 : List Lit := [(23, false), (29, true), (22, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c516, c111] c1453 (by decide) p (sat_cons (step516 p h) (sat_cons (step111 p h) (sat_nil p)))
def c1454 : List Lit := [(23, false), (26, true), (22, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c516, c112] c1454 (by decide) p (sat_cons (step516 p h) (sat_cons (step112 p h) (sat_nil p)))
def c1455 : List Lit := [(26, true), (22, true), (24, false)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c517, c113] c1455 (by decide) p (sat_cons (step517 p h) (sat_cons (step113 p h) (sat_nil p)))
def c1456 : List Lit := [(16, true), (25, false), (10, true), (74, true)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c518, c115] c1456 (by decide) p (sat_cons (step518 p h) (sat_cons (step115 p h) (sat_nil p)))
def c1457 : List Lit := [(29, true), (22, true), (28, false)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c519, c118] c1457 (by decide) p (sat_cons (step519 p h) (sat_cons (step118 p h) (sat_nil p)))
def c1458 : List Lit := [(22, true), (28, false), (27, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c519, c119] c1458 (by decide) p (sat_cons (step519 p h) (sat_cons (step119 p h) (sat_nil p)))
def c1459 : List Lit := [(33, true), (98, true), (31, false)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c520, c126] c1459 (by decide) p (sat_cons (step520 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1460 : List Lit := [(30, true), (98, true), (31, false)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c520, c127] c1460 (by decide) p (sat_cons (step520 p h) (sat_cons (step127 p h) (sat_nil p)))
def c1461 : List Lit := [(30, true), (33, true), (31, false)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c520, c128] c1461 (by decide) p (sat_cons (step520 p h) (sat_cons (step128 p h) (sat_nil p)))
def c1462 : List Lit := [(32, false), (14, false), (36, false)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c164, c129] c1462 (by decide) p (sat_cons (step164 p h) (sat_cons (step129 p h) (sat_nil p)))
def c1463 : List Lit := [(32, false), (36, false), (99, false)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c164, c130] c1463 (by decide) p (sat_cons (step164 p h) (sat_cons (step130 p h) (sat_nil p)))
def c1464 : List Lit := [(150, false), (36, false)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c164, c131] c1464 (by decide) p (sat_cons (step164 p h) (sat_cons (step131 p h) (sat_nil p)))
def c1465 : List Lit := [(37, true), (34, false), (103, true)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c521, c134] c1465 (by decide) p (sat_cons (step521 p h) (sat_cons (step134 p h) (sat_nil p)))
def c1466 : List Lit := [(30, true), (34, false), (103, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c521, c135] c1466 (by decide) p (sat_cons (step521 p h) (sat_cons (step135 p h) (sat_nil p)))
def c1467 : List Lit := [(30, true), (37, true), (34, false)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c521, c136] c1467 (by decide) p (sat_cons (step521 p h) (sat_cons (step136 p h) (sat_nil p)))
def c1468 : List Lit := [(42, true), (35, false), (104, true)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c522, c138] c1468 (by decide) p (sat_cons (step522 p h) (sat_cons (step138 p h) (sat_nil p)))
def c1469 : List Lit := [(18, true), (35, false), (104, true)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c522, c139] c1469 (by decide) p (sat_cons (step522 p h) (sat_cons (step139 p h) (sat_nil p)))
def c1470 : List Lit := [(42, true), (18, true), (35, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c522, c140] c1470 (by decide) p (sat_cons (step522 p h) (sat_cons (step140 p h) (sat_nil p)))
def c1471 : List Lit := [(32, true), (43, true), (36, false), (106, true), (37, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c523, c141] c1471 (by decide) p (sat_cons (step523 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1472 : List Lit := [(20, true), (43, true), (36, false), (106, true), (37, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c523, c142] c1472 (by decide) p (sat_cons (step523 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1473 : List Lit := [(20, true), (32, true), (36, false), (43, true), (106, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c523, c143] c1473 (by decide) p (sat_cons (step523 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1474 : List Lit := [(20, true), (32, true), (37, true), (106, true), (36, false)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c523, c144] c1474 (by decide) p (sat_cons (step523 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1475 : List Lit := [(38, false), (40, false), (39, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c164, c151] c1475 (by decide) p (sat_cons (step164 p h) (sat_cons (step151 p h) (sat_nil p)))
end B112E104
