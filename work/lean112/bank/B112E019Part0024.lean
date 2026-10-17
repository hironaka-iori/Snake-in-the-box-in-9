import B112E019Part0023
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3342 : List Lit := [(91, true), (26, false), (85, false), (1680, true), (103, false), (216, true), (116, false)]
theorem step3342 (p : Nat → Bool) (h : Constraints p) : clause p c3342 = true :=
  Snake9.LocalRup.prove_clause [c1585, c491, c1559, c3337, c1581, c510, c1570, c1919, c1563] c3342 (by decide) p (sat_cons (step1585 p h) (sat_cons (step491 p h) (sat_cons (step1559 p h) (sat_cons (step3337 p h) (sat_cons (step1581 p h) (sat_cons (step510 p h) (sat_cons (step1570 p h) (sat_cons (step1919 p h) (sat_cons (step1563 p h) (sat_nil p))))))))))
def c3343 : List Lit := [(83, true), (107, true), (1673, true), (224, true), (100, true)]
theorem step3343 (p : Nat → Bool) (h : Constraints p) : clause p c3343 = true :=
  Snake9.LocalRup.prove_clause [c1566, c1565, c628, c627, c632, c2082] c3343 (by decide) p (sat_cons (step1566 p h) (sat_cons (step1565 p h) (sat_cons (step628 p h) (sat_cons (step627 p h) (sat_cons (step632 p h) (sat_cons (step2082 p h) (sat_nil p)))))))
def c3344 : List Lit := [(26, false), (83, false), (85, false), (1680, true), (103, false), (216, true), (116, false)]
theorem step3344 (p : Nat → Bool) (h : Constraints p) : clause p c3344 = true :=
  Snake9.LocalRup.prove_clause [c3342, c426] c3344 (by decide) p (sat_cons (step3342 p h) (sat_cons (step426 p h) (sat_nil p)))
def c3345 : List Lit := [(83, true), (26, false), (147, true), (25, true)]
theorem step3345 (p : Nat → Bool) (h : Constraints p) : clause p c3345 = true :=
  Snake9.LocalRup.prove_clause [c109, c108, c2000, c1759] c3345 (by decide) p (sat_cons (step109 p h) (sat_cons (step108 p h) (sat_cons (step2000 p h) (sat_cons (step1759 p h) (sat_nil p)))))
def c3346 : List Lit := [(26, false), (82, false), (103, false), (147, true), (25, true)]
theorem step3346 (p : Nat → Bool) (h : Constraints p) : clause p c3346 = true :=
  Snake9.LocalRup.prove_clause [c425, c3345] c3346 (by decide) p (sat_cons (step425 p h) (sat_cons (step3345 p h) (sat_nil p)))
def c3347 : List Lit := [(1699, true), (241, true), (116, false), (109, true), (76, false), (118, true)]
theorem step3347 (p : Nat → Bool) (h : Constraints p) : clause p c3347 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1916, c1613, c2347] c3347 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1916 p h) (sat_cons (step1613 p h) (sat_cons (step2347 p h) (sat_nil p)))))
def c3348 : List Lit := [(1692, true), (107, true), (87, false), (1673, true), (112, true), (1688, false), (223, true), (100, true), (99, false)]
theorem step3348 (p : Nat → Bool) (h : Constraints p) : clause p c3348 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1566, c1565, c1606, c1604, c1596, c1599, c632, c672, c607, c620] c3348 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1566 p h) (sat_cons (step1565 p h) (sat_cons (step1606 p h) (sat_cons (step1604 p h) (sat_cons (step1596 p h) (sat_cons (step1599 p h) (sat_cons (step632 p h) (sat_cons (step672 p h) (sat_cons (step607 p h) (sat_cons (step620 p h) (sat_nil p))))))))))))
def c3349 : List Lit := [(1679, true), (87, false)]
theorem step3349 (p : Nat → Bool) (h : Constraints p) : clause p c3349 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1580, c1570, c1888, c1563] c3349 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1580 p h) (sat_cons (step1570 p h) (sat_cons (step1888 p h) (sat_cons (step1563 p h) (sat_nil p))))))
def c3350 : List Lit := [(1688, true), (112, false), (102, false), (100, true), (99, false)]
theorem step3350 (p : Nat → Bool) (h : Constraints p) : clause p c3350 = true :=
  Snake9.LocalRup.prove_clause [c1597, c2457, c733] c3350 (by decide) p (sat_cons (step1597 p h) (sat_cons (step2457 p h) (sat_cons (step733 p h) (sat_nil p))))
def c3351 : List Lit := [(112, false), (102, false), (233, true), (1686, false), (1706, true), (116, true), (100, true), (1696, false), (99, false)]
theorem step3351 (p : Nat → Bool) (h : Constraints p) : clause p c3351 = true :=
  Snake9.LocalRup.prove_clause [c3350, c750, c1603, c734, c1634, c1610, c1620] c3351 (by decide) p (sat_cons (step3350 p h) (sat_cons (step750 p h) (sat_cons (step1603 p h) (sat_cons (step734 p h) (sat_cons (step1634 p h) (sat_cons (step1610 p h) (sat_cons (step1620 p h) (sat_nil p))))))))
def c3352 : List Lit := [(112, false), (233, true), (1686, false), (1706, true), (116, true), (100, true), (118, true), (99, false)]
theorem step3352 (p : Nat → Bool) (h : Constraints p) : clause p c3352 = true :=
  Snake9.LocalRup.prove_clause [c1612, c750, c749, c3351, c733, c2092] c3352 (by decide) p (sat_cons (step1612 p h) (sat_cons (step750 p h) (sat_cons (step749 p h) (sat_cons (step3351 p h) (sat_cons (step733 p h) (sat_cons (step2092 p h) (sat_nil p)))))))
def c3353 : List Lit := [(1669, true), (92, true), (103, false), (212, true), (26, false)]
theorem step3353 (p : Nat → Bool) (h : Constraints p) : clause p c3353 = true :=
  Snake9.LocalRup.prove_clause [c1555, c3337, c1560, c426, c497, c498, c526, c2057] c3353 (by decide) p (sat_cons (step1555 p h) (sat_cons (step3337 p h) (sat_cons (step1560 p h) (sat_cons (step426 p h) (sat_cons (step497 p h) (sat_cons (step498 p h) (sat_cons (step526 p h) (sat_cons (step2057 p h) (sat_nil p)))))))))
def c3354 : List Lit := [(92, true), (212, true), (82, false), (103, false), (1680, true)]
theorem step3354 (p : Nat → Bool) (h : Constraints p) : clause p c3354 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1558, c1555, c1556, c1557, c1560, c1581, c430, c1570, c497, c1563, c526] c3354 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1558 p h) (sat_cons (step1555 p h) (sat_cons (step1556 p h) (sat_cons (step1557 p h) (sat_cons (step1560 p h) (sat_cons (step1581 p h) (sat_cons (step430 p h) (sat_cons (step1570 p h) (sat_cons (step497 p h) (sat_cons (step1563 p h) (sat_cons (step526 p h) (sat_nil p)))))))))))))
def c3355 : List Lit := [(475, true), (1673, true), (1706, true), (112, false), (107, false), (116, true), (100, true), (1696, false), (99, false)]
theorem step3355 (p : Nat → Bool) (h : Constraints p) : clause p c3355 = true :=
  Snake9.LocalRup.prove_clause [c1566, c1162, c1164, c1159, c1129, c1141, c1125, c1138, c1124, c1137, c1123, c3351, c2274, c1594] c3355 (by decide) p (sat_cons (step1566 p h) (sat_cons (step1162 p h) (sat_cons (step1164 p h) (sat_cons (step1159 p h) (sat_cons (step1129 p h) (sat_cons (step1141 p h) (sat_cons (step1125 p h) (sat_cons (step1138 p h) (sat_cons (step1124 p h) (sat_cons (step1137 p h) (sat_cons (step1123 p h) (sat_cons (step3351 p h) (sat_cons (step2274 p h) (sat_cons (step1594 p h) (sat_nil p)))))))))))))))
def c3356 : List Lit := [(1644, true), (107, false), (413, true), (109, true), (99, false)]
theorem step3356 (p : Nat → Bool) (h : Constraints p) : clause p c3356 = true :=
  Snake9.LocalRup.prove_clause [c1093, c1091, c1088, c2661, c1491, c1495, c2363, c1487, c1468, c652, c1465, c1476, c3090, c1485] c3356 (by decide) p (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1088 p h) (sat_cons (step2661 p h) (sat_cons (step1491 p h) (sat_cons (step1495 p h) (sat_cons (step2363 p h) (sat_cons (step1487 p h) (sat_cons (step1468 p h) (sat_cons (step652 p h) (sat_cons (step1465 p h) (sat_cons (step1476 p h) (sat_cons (step3090 p h) (sat_cons (step1485 p h) (sat_nil p)))))))))))))))
def c3357 : List Lit := [(83, true), (110, false), (103, false), (224, true), (100, true)]
theorem step3357 (p : Nat → Bool) (h : Constraints p) : clause p c3357 = true :=
  Snake9.LocalRup.prove_clause [c628, c627, c1797] c3357 (by decide) p (sat_cons (step628 p h) (sat_cons (step627 p h) (sat_cons (step1797 p h) (sat_nil p))))
def c3358 : List Lit := [(107, false), (81, false), (415, true), (1640, true), (1645, true), (109, true), (100, true), (99, false)]
theorem step3358 (p : Nat → Bool) (h : Constraints p) : clause p c3358 = true :=
  Snake9.LocalRup.prove_clause [c1098, c1093, c1091, c1088, c1487, c3090, c1485, c1476, c1477, c652, c470, c2369, c484, c461] c3358 (by decide) p (sat_cons (step1098 p h) (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1088 p h) (sat_cons (step1487 p h) (sat_cons (step3090 p h) (sat_cons (step1485 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step652 p h) (sat_cons (step470 p h) (sat_cons (step2369 p h) (sat_cons (step484 p h) (sat_cons (step461 p h) (sat_nil p)))))))))))))))
def c3359 : List Lit := [(87, true), (25, true), (79, true), (81, false), (203, true), (1640, true), (1638, true)]
theorem step3359 (p : Nat → Bool) (h : Constraints p) : clause p c3359 = true :=
  Snake9.LocalRup.prove_clause [c1480, c1481, c1485, c1476, c1477, c469, c431, c418] c3359 (by decide) p (sat_cons (step1480 p h) (sat_cons (step1481 p h) (sat_cons (step1485 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step469 p h) (sat_cons (step431 p h) (sat_cons (step418 p h) (sat_nil p)))))))))
def c3360 : List Lit := [(110, false), (87, false), (101, true), (102, false), (103, false), (223, true), (100, true)]
theorem step3360 (p : Nat → Bool) (h : Constraints p) : clause p c3360 = true :=
  Snake9.LocalRup.prove_clause [c632, c672, c620] c3360 (by decide) p (sat_cons (step632 p h) (sat_cons (step672 p h) (sat_cons (step620 p h) (sat_nil p))))
def c3361 : List Lit := [(1680, true), (81, false), (1673, false)]
theorem step3361 (p : Nat → Bool) (h : Constraints p) : clause p c3361 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1577, c2361, c1581, c1571, c491, c1089, c1557, c1563, c1090, c1555, c1093, c504, c1098, c1103, c2145, c1164, c1131, c1116, c1108, c502, c501, c1783] c3361 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1577 p h) (sat_cons (step2361 p h) (sat_cons (step1581 p h) (sat_cons (step1571 p h) (sat_cons (step491 p h) (sat_cons (step1089 p h) (sat_cons (step1557 p h) (sat_cons (step1563 p h) (sat_cons (step1090 p h) (sat_cons (step1555 p h) (sat_cons (step1093 p h) (sat_cons (step504 p h) (sat_cons (step1098 p h) (sat_cons (step1103 p h) (sat_cons (step2145 p h) (sat_cons (step1164 p h) (sat_cons (step1131 p h) (sat_cons (step1116 p h) (sat_cons (step1108 p h) (sat_cons (step502 p h) (sat_cons (step501 p h) (sat_cons (step1783 p h) (sat_nil p))))))))))))))))))))))))
def c3362 : List Lit := [(1639, true), (66, false), (109, true), (99, false)]
theorem step3362 (p : Nat → Bool) (h : Constraints p) : clause p c3362 = true :=
  Snake9.LocalRup.prove_clause [c1484, c2993, c1476, c646] c3362 (by decide) p (sat_cons (step1484 p h) (sat_cons (step2993 p h) (sat_cons (step1476 p h) (sat_cons (step646 p h) (sat_nil p)))))
def c3363 : List Lit := [(1679, true), (83, false), (213, true), (90, true)]
theorem step3363 (p : Nat → Bool) (h : Constraints p) : clause p c3363 = true :=
  Snake9.LocalRup.prove_clause [c1580, c2370, c1557, c494, c1555, c501] c3363 (by decide) p (sat_cons (step1580 p h) (sat_cons (step2370 p h) (sat_cons (step1557 p h) (sat_cons (step494 p h) (sat_cons (step1555 p h) (sat_cons (step501 p h) (sat_nil p)))))))
def c3364 : List Lit := [(1680, true), (90, true), (213, true), (1673, false)]
theorem step3364 (p : Nat → Bool) (h : Constraints p) : clause p c3364 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1577, c2361, c1581, c1571, c491, c1557, c1563, c1555, c504, c501] c3364 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1577 p h) (sat_cons (step2361 p h) (sat_cons (step1581 p h) (sat_cons (step1571 p h) (sat_cons (step491 p h) (sat_cons (step1557 p h) (sat_cons (step1563 p h) (sat_cons (step1555 p h) (sat_cons (step504 p h) (sat_cons (step501 p h) (sat_nil p))))))))))))
def c3365 : List Lit := [(46, true), (357, true), (1577, true), (109, true), (100, true), (1561, false)]
theorem step3365 (p : Nat → Bool) (h : Constraints p) : clause p c3365 = true :=
  Snake9.LocalRup.prove_clause [c1027, c2378, c1365, c1347, c1327, c1025, c1022, c1002, c992, c991, c1317, c1324, c1343, c1325, c1370, c1318, c1319, c2375, c3327] c3365 (by decide) p (sat_cons (step1027 p h) (sat_cons (step2378 p h) (sat_cons (step1365 p h) (sat_cons (step1347 p h) (sat_cons (step1327 p h) (sat_cons (step1025 p h) (sat_cons (step1022 p h) (sat_cons (step1002 p h) (sat_cons (step992 p h) (sat_cons (step991 p h) (sat_cons (step1317 p h) (sat_cons (step1324 p h) (sat_cons (step1343 p h) (sat_cons (step1325 p h) (sat_cons (step1370 p h) (sat_cons (step1318 p h) (sat_cons (step1319 p h) (sat_cons (step2375 p h) (sat_cons (step3327 p h) (sat_nil p))))))))))))))))))))
def c3366 : List Lit := [(1610, true), (100, true), (1607, false), (99, false)]
theorem step3366 (p : Nat → Bool) (h : Constraints p) : clause p c3366 = true :=
  Snake9.LocalRup.prove_clause [c1428, c1904, c291] c3366 (by decide) p (sat_cons (step1428 p h) (sat_cons (step1904 p h) (sat_cons (step291 p h) (sat_nil p))))
def c3367 : List Lit := [(387, true), (188, true), (202, true), (203, true), (206, true), (208, true), (210, true), (212, true), (475, true), (359, true), (228, true), (201, true), (149, true), (139, true), (185, true), (239, true), (179, true)]
theorem step3367 (p : Nat → Bool) (h : Constraints p) : clause p c3367 = true :=
  Snake9.TreeRup.prove_clause [c1164, c1131, c1114, c1112, c1109, c1111, c1110, c1129, c1126, c1121, c1118, c1120, c1119, c1125, c1124, c1123, c1162, c1159, c1141, c1139, c1135, c1138, c1137, c1136, c1157, c1154, c1147, c1144, c1146, c1145, c1153, c1151, c1150, c1116, c1108, c1032, c960, c930, c920, c912, c911, c918, c916, c913, c915, c914, c929, c928, c924, c921, c923, c922, c927, c926, c925, c958, c956, c941, c939, c936, c938, c937, c954, c952, c948, c945, c947, c946, c1030, c1027, c988, c971, c964, c963, c970, c969, c966, c968, c967, c986, c983, c976, c973, c975, c974, c982, c981, c978, c980, c979, c1025, c1022, c1002, c992, c991, c1000, c998, c996, c995, c1020, c1017, c1008, c1005, c1007, c1006, c1015, c1012, c1011, c943, c935, c965, c993, c1068, c1070, c1063, c1065, c1045, c1047, c1061, c1054, c1056, c1043, c1038, c1058, c1059, c1051, c1052, c1050, c1040, c1036, c1862] c3367 (by decide) p (sat_cons (step1164 p h) (sat_cons (step1131 p h) (sat_cons (step1114 p h) (sat_cons (step1112 p h) (sat_cons (step1109 p h) (sat_cons (step1111 p h) (sat_cons (step1110 p h) (sat_cons (step1129 p h) (sat_cons (step1126 p h) (sat_cons (step1121 p h) (sat_cons (step1118 p h) (sat_cons (step1120 p h) (sat_cons (step1119 p h) (sat_cons (step1125 p h) (sat_cons (step1124 p h) (sat_cons (step1123 p h) (sat_cons (step1162 p h) (sat_cons (step1159 p h) (sat_cons (step1141 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step1138 p h) (sat_cons (step1137 p h) (sat_cons (step1136 p h) (sat_cons (step1157 p h) (sat_cons (step1154 p h) (sat_cons (step1147 p h) (sat_cons (step1144 p h) (sat_cons (step1146 p h) (sat_cons (step1145 p h) (sat_cons (step1153 p h) (sat_cons (step1151 p h) (sat_cons (step1150 p h) (sat_cons (step1116 p h) (sat_cons (step1108 p h) (sat_cons (step1032 p h) (sat_cons (step960 p h) (sat_cons (step930 p h) (sat_cons (step920 p h) (sat_cons (step912 p h) (sat_cons (step911 p h) (sat_cons (step918 p h) (sat_cons (step916 p h) (sat_cons (step913 p h) (sat_cons (step915 p h) (sat_cons (step914 p h) (sat_cons (step929 p h) (sat_cons (step928 p h) (sat_cons (step924 p h) (sat_cons (step921 p h) (sat_cons (step923 p h) (sat_cons (step922 p h) (sat_cons (step927 p h) (sat_cons (step926 p h) (sat_cons (step925 p h) (sat_cons (step958 p h) (sat_cons (step956 p h) (sat_cons (step941 p h) (sat_cons (step939 p h) (sat_cons (step936 p h) (sat_cons (step938 p h) (sat_cons (step937 p h) (sat_cons (step954 p h) (sat_cons (step952 p h) (sat_cons (step948 p h) (sat_cons (step945 p h) (sat_cons (step947 p h) (sat_cons (step946 p h) (sat_cons (step1030 p h) (sat_cons (step1027 p h) (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step970 p h) (sat_cons (step969 p h) (sat_cons (step966 p h) (sat_cons (step968 p h) (sat_cons (step967 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step976 p h) (sat_cons (step973 p h) (sat_cons (step975 p h) (sat_cons (step974 p h) (sat_cons (step982 p h) (sat_cons (step981 p h) (sat_cons (step978 p h) (sat_cons (step980 p h) (sat_cons (step979 p h) (sat_cons (step1025 p h) (sat_cons (step1022 p h) (sat_cons (step1002 p h) (sat_cons (step992 p h) (sat_cons (step991 p h) (sat_cons (step1000 p h) (sat_cons (step998 p h) (sat_cons (step996 p h) (sat_cons (step995 p h) (sat_cons (step1020 p h) (sat_cons (step1017 p h) (sat_cons (step1008 p h) (sat_cons (step1005 p h) (sat_cons (step1007 p h) (sat_cons (step1006 p h) (sat_cons (step1015 p h) (sat_cons (step1012 p h) (sat_cons (step1011 p h) (sat_cons (step943 p h) (sat_cons (step935 p h) (sat_cons (step965 p h) (sat_cons (step993 p h) (sat_cons (step1068 p h) (sat_cons (step1070 p h) (sat_cons (step1063 p h) (sat_cons (step1065 p h) (sat_cons (step1045 p h) (sat_cons (step1047 p h) (sat_cons (step1061 p h) (sat_cons (step1054 p h) (sat_cons (step1056 p h) (sat_cons (step1043 p h) (sat_cons (step1038 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step1051 p h) (sat_cons (step1052 p h) (sat_cons (step1050 p h) (sat_cons (step1040 p h) (sat_cons (step1036 p h) (sat_cons (step1862 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c3368 : List Lit := [(66, false), (68, true), (187, true), (74, true), (99, false)]
theorem step3368 (p : Nat → Bool) (h : Constraints p) : clause p c3368 = true :=
  Snake9.LocalRup.prove_clause [c304, c307, c1774] c3368 (by decide) p (sat_cons (step304 p h) (sat_cons (step307 p h) (sat_cons (step1774 p h) (sat_nil p))))
def c3369 : List Lit := [(1644, true), (210, true), (80, true)]
theorem step3369 (p : Nat → Bool) (h : Constraints p) : clause p c3369 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1468, c1495, c1482, c1479, c1480, c2373] c3369 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1468 p h) (sat_cons (step1495 p h) (sat_cons (step1482 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step2373 p h) (sat_nil p))))))))
def c3370 : List Lit := [(72, false), (193, true), (113, false), (65, true), (76, false)]
theorem step3370 (p : Nat → Bool) (h : Constraints p) : clause p c3370 = true :=
  Snake9.LocalRup.prove_clause [c344, c331] c3370 (by decide) p (sat_cons (step344 p h) (sat_cons (step331 p h) (sat_nil p)))
def c3371 : List Lit := [(1688, true), (233, true), (100, true), (99, false)]
theorem step3371 (p : Nat → Bool) (h : Constraints p) : clause p c3371 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1598, c733, c750] c3371 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1598 p h) (sat_cons (step733 p h) (sat_cons (step750 p h) (sat_nil p)))))
def c3372 : List Lit := [(1705, true), (1688, false), (74, true), (105, true), (116, false), (109, false), (76, false), (100, true), (118, true), (99, false)]
theorem step3372 (p : Nat → Bool) (h : Constraints p) : clause p c3372 = true :=
  Snake9.LocalRup.prove_clause [c3255, c2936, c1144, c3329, c1147, c1137, c1154, c1138, c2143, c1141] c3372 (by decide) p (sat_cons (step3255 p h) (sat_cons (step2936 p h) (sat_cons (step1144 p h) (sat_cons (step3329 p h) (sat_cons (step1147 p h) (sat_cons (step1137 p h) (sat_cons (step1154 p h) (sat_cons (step1138 p h) (sat_cons (step2143 p h) (sat_cons (step1141 p h) (sat_nil p)))))))))))
def c3373 : List Lit := [(89, false), (1688, false), (1706, true), (1694, false), (109, false), (118, true)]
theorem step3373 (p : Nat → Bool) (h : Constraints p) : clause p c3373 = true :=
  Snake9.LocalRup.prove_clause [c2301, c1886] c3373 (by decide) p (sat_cons (step2301 p h) (sat_cons (step1886 p h) (sat_nil p)))
def c3374 : List Lit := [(299, true), (74, false), (7, false), (9, false), (10, true), (18, true), (12, true)]
theorem step3374 (p : Nat → Bool) (h : Constraints p) : clause p c3374 = true :=
  Snake9.LocalRup.prove_clause [c958, c960, c2481, c956, c929, c1987, c81, c941, c927, c928, c938, c926, c924, c937, c925, c921, c91, c31, c1993, c1985, c66] c3374 (by decide) p (sat_cons (step958 p h) (sat_cons (step960 p h) (sat_cons (step2481 p h) (sat_cons (step956 p h) (sat_cons (step929 p h) (sat_cons (step1987 p h) (sat_cons (step81 p h) (sat_cons (step941 p h) (sat_cons (step927 p h) (sat_cons (step928 p h) (sat_cons (step938 p h) (sat_cons (step926 p h) (sat_cons (step924 p h) (sat_cons (step937 p h) (sat_cons (step925 p h) (sat_cons (step921 p h) (sat_cons (step91 p h) (sat_cons (step31 p h) (sat_cons (step1993 p h) (sat_cons (step1985 p h) (sat_cons (step66 p h) (sat_nil p))))))))))))))))))))))
def c3375 : List Lit := [(72, true), (1615, true), (192, true)]
theorem step3375 (p : Nat → Bool) (h : Constraints p) : clause p c3375 = true :=
  Snake9.LocalRup.prove_clause [c2043, c1435, c338] c3375 (by decide) p (sat_cons (step2043 p h) (sat_cons (step1435 p h) (sat_cons (step338 p h) (sat_nil p))))
def c3376 : List Lit := [(212, true), (1714, true), (105, true), (116, false), (74, true), (109, false), (76, false), (100, true), (118, true), (99, false)]
theorem step3376 (p : Nat → Bool) (h : Constraints p) : clause p c3376 = true :=
  Snake9.LocalRup.prove_clause [c2657, c2370, c1650, c3372, c1597, c1598, c3350, c737, c805, c1566, c2855, c2361, c1656] c3376 (by decide) p (sat_cons (step2657 p h) (sat_cons (step2370 p h) (sat_cons (step1650 p h) (sat_cons (step3372 p h) (sat_cons (step1597 p h) (sat_cons (step1598 p h) (sat_cons (step3350 p h) (sat_cons (step737 p h) (sat_cons (step805 p h) (sat_cons (step1566 p h) (sat_cons (step2855 p h) (sat_cons (step2361 p h) (sat_cons (step1656 p h) (sat_nil p))))))))))))))
def c3377 : List Lit := [(48, true), (1567, true), (116, false), (1577, true), (76, false), (1559, false)]
theorem step3377 (p : Nat → Bool) (h : Constraints p) : clause p c3377 = true :=
  Snake9.LocalRup.prove_clause [c2486, c2586] c3377 (by decide) p (sat_cons (step2486 p h) (sat_cons (step2586 p h) (sat_nil p)))
def c3378 : List Lit := [(1576, true), (116, false), (76, false), (1559, false), (99, false)]
theorem step3378 (p : Nat → Bool) (h : Constraints p) : clause p c3378 = true :=
  Snake9.LocalRup.prove_clause [c2530, c2488, c3331] c3378 (by decide) p (sat_cons (step2530 p h) (sat_cons (step2488 p h) (sat_cons (step3331 p h) (sat_nil p))))
def c3379 : List Lit := [(1627, false), (1645, true), (80, true), (116, false), (109, false), (99, false)]
theorem step3379 (p : Nat → Bool) (h : Constraints p) : clause p c3379 = true :=
  Snake9.LocalRup.prove_clause [c1466, c2933, c1471, c653, c1500, c1476, c1484] c3379 (by decide) p (sat_cons (step1466 p h) (sat_cons (step2933 p h) (sat_cons (step1471 p h) (sat_cons (step653 p h) (sat_cons (step1500 p h) (sat_cons (step1476 p h) (sat_cons (step1484 p h) (sat_nil p))))))))
def c3380 : List Lit := [(26, false), (83, false), (103, false), (1680, true), (216, true), (147, true), (25, true), (1636, true), (116, false)]
theorem step3380 (p : Nat → Bool) (h : Constraints p) : clause p c3380 = true :=
  Snake9.LocalRup.prove_clause [c3346, c3344, c1478] c3380 (by decide) p (sat_cons (step3346 p h) (sat_cons (step3344 p h) (sat_cons (step1478 p h) (sat_nil p))))
def c3381 : List Lit := [(48, true), (54, false), (1550, true), (162, true), (1577, true), (100, true), (10, true), (12, true), (1559, false)]
theorem step3381 (p : Nat → Bool) (h : Constraints p) : clause p c3381 = true :=
  Snake9.LocalRup.prove_clause [c3186, c1318, c169, c194] c3381 (by decide) p (sat_cons (step3186 p h) (sat_cons (step1318 p h) (sat_cons (step169 p h) (sat_cons (step194 p h) (sat_nil p)))))
def c3382 : List Lit := [(48, true), (162, true), (1554, true), (172, true), (1577, true), (100, true), (10, true), (12, true), (1559, false)]
theorem step3382 (p : Nat → Bool) (h : Constraints p) : clause p c3382 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1316, c3381, c1325, c2029, c2626] c3382 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1316 p h) (sat_cons (step3381 p h) (sat_cons (step1325 p h) (sat_cons (step2029 p h) (sat_cons (step2626 p h) (sat_nil p)))))))
def c3383 : List Lit := [(48, true), (1567, true), (117, true), (176, true), (1559, false)]
theorem step3383 (p : Nat → Bool) (h : Constraints p) : clause p c3383 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1347, c1327, c1316, c1318, c1324, c1876, c1344, c1336] c3383 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1347 p h) (sat_cons (step1327 p h) (sat_cons (step1316 p h) (sat_cons (step1318 p h) (sat_cons (step1324 p h) (sat_cons (step1876 p h) (sat_cons (step1344 p h) (sat_cons (step1336 p h) (sat_nil p))))))))))
def c3384 : List Lit := [(48, true), (327, true), (1577, true), (100, true), (10, true), (12, true), (1559, false)]
theorem step3384 (p : Nat → Bool) (h : Constraints p) : clause p c3384 = true :=
  Snake9.LocalRup.prove_clause [c1334, c2378, c1365, c1347, c1327, c986, c983, c975, c974, c1316, c3381, c1324, c1331, c1344, c1336] c3384 (by decide) p (sat_cons (step1334 p h) (sat_cons (step2378 p h) (sat_cons (step1365 p h) (sat_cons (step1347 p h) (sat_cons (step1327 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step975 p h) (sat_cons (step974 p h) (sat_cons (step1316 p h) (sat_cons (step3381 p h) (sat_cons (step1324 p h) (sat_cons (step1331 p h) (sat_cons (step1344 p h) (sat_cons (step1336 p h) (sat_nil p))))))))))))))))
def c3385 : List Lit := [(1567, true), (54, false), (48, true), (355, true), (1577, true), (100, true), (10, true), (12, true), (1559, false)]
theorem step3385 (p : Nat → Bool) (h : Constraints p) : clause p c3385 = true :=
  Snake9.LocalRup.prove_clause [c1316, c1324, c3186, c1022, c1000, c998, c996, c1020, c1017, c1008, c1005, c1334, c1347, c3217, c1344, c1327, c3382, c1336, c1318, c167, c2203, c255] c3385 (by decide) p (sat_cons (step1316 p h) (sat_cons (step1324 p h) (sat_cons (step3186 p h) (sat_cons (step1022 p h) (sat_cons (step1000 p h) (sat_cons (step998 p h) (sat_cons (step996 p h) (sat_cons (step1020 p h) (sat_cons (step1017 p h) (sat_cons (step1008 p h) (sat_cons (step1005 p h) (sat_cons (step1334 p h) (sat_cons (step1347 p h) (sat_cons (step3217 p h) (sat_cons (step1344 p h) (sat_cons (step1327 p h) (sat_cons (step3382 p h) (sat_cons (step1336 p h) (sat_cons (step1318 p h) (sat_cons (step167 p h) (sat_cons (step2203 p h) (sat_cons (step255 p h) (sat_nil p)))))))))))))))))))))))
def c3386 : List Lit := [(44, false), (41, false), (172, true), (1577, true), (100, true), (1559, false), (99, false)]
theorem step3386 (p : Nat → Bool) (h : Constraints p) : clause p c3386 = true :=
  Snake9.LocalRup.prove_clause [c160, c2612, c165] c3386 (by decide) p (sat_cons (step160 p h) (sat_cons (step2612 p h) (sat_cons (step165 p h) (sat_nil p))))
def c3387 : List Lit := [(1551, false), (175, true), (1567, true), (1577, true), (1559, false)]
theorem step3387 (p : Nat → Bool) (h : Constraints p) : clause p c3387 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1347, c1322, c1325, c2607, c1343, c1344, c1317, c1291, c1370, c1336, c2203, c2309, c1331, c255, c194] c3387 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1347 p h) (sat_cons (step1322 p h) (sat_cons (step1325 p h) (sat_cons (step2607 p h) (sat_cons (step1343 p h) (sat_cons (step1344 p h) (sat_cons (step1317 p h) (sat_cons (step1291 p h) (sat_cons (step1370 p h) (sat_cons (step1336 p h) (sat_cons (step2203 p h) (sat_cons (step2309 p h) (sat_cons (step1331 p h) (sat_cons (step255 p h) (sat_cons (step194 p h) (sat_nil p)))))))))))))))))
def c3388 : List Lit := [(327, true), (42, false), (175, true), (1544, true), (48, false), (1577, true), (100, true), (1559, false)]
theorem step3388 (p : Nat → Bool) (h : Constraints p) : clause p c3388 = true :=
  Snake9.LocalRup.prove_clause [c2378, c2375, c1365, c172, c3387, c1319] c3388 (by decide) p (sat_cons (step2378 p h) (sat_cons (step2375 p h) (sat_cons (step1365 p h) (sat_cons (step172 p h) (sat_cons (step3387 p h) (sat_cons (step1319 p h) (sat_nil p)))))))
def c3389 : List Lit := [(1645, true), (415, true), (89, true), (107, false), (100, true), (99, false)]
theorem step3389 (p : Nat → Bool) (h : Constraints p) : clause p c3389 = true :=
  Snake9.LocalRup.prove_clause [c1100, c1081, c1078, c1074, c1935, c1468, c1479, c2369, c1496, c652, c1485, c1476] c3389 (by decide) p (sat_cons (step1100 p h) (sat_cons (step1081 p h) (sat_cons (step1078 p h) (sat_cons (step1074 p h) (sat_cons (step1935 p h) (sat_cons (step1468 p h) (sat_cons (step1479 p h) (sat_cons (step2369 p h) (sat_cons (step1496 p h) (sat_cons (step652 p h) (sat_cons (step1485 p h) (sat_cons (step1476 p h) (sat_nil p)))))))))))))
def c3390 : List Lit := [(1543, true), (172, true), (1577, true), (100, true), (1559, false), (99, false)]
theorem step3390 (p : Nat → Bool) (h : Constraints p) : clause p c3390 = true :=
  Snake9.LocalRup.prove_clause [c2290, c2542, c3386, c1291] c3390 (by decide) p (sat_cons (step2290 p h) (sat_cons (step2542 p h) (sat_cons (step3386 p h) (sat_cons (step1291 p h) (sat_nil p)))))
def c3391 : List Lit := [(1706, true), (1686, false), (116, true), (107, false), (233, true), (236, true), (100, true), (118, true), (99, false)]
theorem step3391 (p : Nat → Bool) (h : Constraints p) : clause p c3391 = true :=
  Snake9.LocalRup.prove_clause [c3371, c1603, c1612, c1608, c1617, c1634, c1638, c3352, c1620, c1618, c1604, c1610, c1613, c1599, c829, c736, c775] c3391 (by decide) p (sat_cons (step3371 p h) (sat_cons (step1603 p h) (sat_cons (step1612 p h) (sat_cons (step1608 p h) (sat_cons (step1617 p h) (sat_cons (step1634 p h) (sat_cons (step1638 p h) (sat_cons (step3352 p h) (sat_cons (step1620 p h) (sat_cons (step1618 p h) (sat_cons (step1604 p h) (sat_cons (step1610 p h) (sat_cons (step1613 p h) (sat_cons (step1599 p h) (sat_cons (step829 p h) (sat_cons (step736 p h) (sat_cons (step775 p h) (sat_nil p))))))))))))))))))
def c3392 : List Lit := [(1622, true), (107, false), (109, true), (74, true), (63, true), (187, true), (1610, false), (99, false)]
theorem step3392 (p : Nat → Bool) (h : Constraints p) : clause p c3392 = true :=
  Snake9.LocalRup.prove_clause [c2806, c1881, c649] c3392 (by decide) p (sat_cons (step2806 p h) (sat_cons (step1881 p h) (sat_cons (step649 p h) (sat_nil p))))
def c3393 : List Lit := [(1645, true), (201, true), (210, true), (1627, false), (100, true), (99, false)]
theorem step3393 (p : Nat → Bool) (h : Constraints p) : clause p c3393 = true :=
  Snake9.LocalRup.prove_clause [c3332, c2923] c3393 (by decide) p (sat_cons (step3332 p h) (sat_cons (step2923 p h) (sat_nil p)))
def c3394 : List Lit := [(115, false), (116, false), (1551, true), (236, true), (99, false)]
theorem step3394 (p : Nat → Bool) (h : Constraints p) : clause p c3394 = true :=
  Snake9.LocalRup.prove_clause [c738, c1928, c777] c3394 (by decide) p (sat_cons (step738 p h) (sat_cons (step1928 p h) (sat_cons (step777 p h) (sat_nil p))))
def c3395 : List Lit := [(1576, true), (52, false), (48, false), (351, false), (100, true), (1559, false)]
theorem step3395 (p : Nat → Bool) (h : Constraints p) : clause p c3395 = true :=
  Snake9.LocalRup.prove_clause [c1015, c2118, c1002, c992, c991, c1020, c2119, c2378, c1334, c1339, c1369, c1364, c2375, c2608, c2561] c3395 (by decide) p (sat_cons (step1015 p h) (sat_cons (step2118 p h) (sat_cons (step1002 p h) (sat_cons (step992 p h) (sat_cons (step991 p h) (sat_cons (step1020 p h) (sat_cons (step2119 p h) (sat_cons (step2378 p h) (sat_cons (step1334 p h) (sat_cons (step1339 p h) (sat_cons (step1369 p h) (sat_cons (step1364 p h) (sat_cons (step2375 p h) (sat_cons (step2608 p h) (sat_cons (step2561 p h) (sat_nil p))))))))))))))))
def c3396 : List Lit := [(43, true), (1577, true), (351, false), (100, true), (1559, false)]
theorem step3396 (p : Nat → Bool) (h : Constraints p) : clause p c3396 = true :=
  Snake9.LocalRup.prove_clause [c2117, c1008, c1005, c1015, c1020, c2119, c2378, c1365, c3387, c1334, c1339, c1374, c2118, c1000, c998, c996, c2375, c1370, c2443, c2608, c2445] c3396 (by decide) p (sat_cons (step2117 p h) (sat_cons (step1008 p h) (sat_cons (step1005 p h) (sat_cons (step1015 p h) (sat_cons (step1020 p h) (sat_cons (step2119 p h) (sat_cons (step2378 p h) (sat_cons (step1365 p h) (sat_cons (step3387 p h) (sat_cons (step1334 p h) (sat_cons (step1339 p h) (sat_cons (step1374 p h) (sat_cons (step2118 p h) (sat_cons (step1000 p h) (sat_cons (step998 p h) (sat_cons (step996 p h) (sat_cons (step2375 p h) (sat_cons (step1370 p h) (sat_cons (step2443 p h) (sat_cons (step2608 p h) (sat_cons (step2445 p h) (sat_nil p))))))))))))))))))))))
def c3397 : List Lit := [(1500, true), (81, false), (1640, true), (25, false), (2, false), (149, true), (28, false)]
theorem step3397 (p : Nat → Bool) (h : Constraints p) : clause p c3397 = true :=
  Snake9.LocalRup.prove_clause [c1487, c1222, c1223, c103, c94, c1477, c1478, c1485, c448, c1480, c117, c121] c3397 (by decide) p (sat_cons (step1487 p h) (sat_cons (step1222 p h) (sat_cons (step1223 p h) (sat_cons (step103 p h) (sat_cons (step94 p h) (sat_cons (step1477 p h) (sat_cons (step1478 p h) (sat_cons (step1485 p h) (sat_cons (step448 p h) (sat_cons (step1480 p h) (sat_cons (step117 p h) (sat_cons (step121 p h) (sat_nil p)))))))))))))
def c3398 : List Lit := [(1568, true), (1544, true), (1551, false), (48, true), (116, false), (76, false), (1559, false)]
theorem step3398 (p : Nat → Bool) (h : Constraints p) : clause p c3398 = true :=
  Snake9.LocalRup.prove_clause [c1316, c1325, c1334, c1350, c1348, c1328, c1336, c1318, c1331, c2391, c195, c194, c1291, c2309] c3398 (by decide) p (sat_cons (step1316 p h) (sat_cons (step1325 p h) (sat_cons (step1334 p h) (sat_cons (step1350 p h) (sat_cons (step1348 p h) (sat_cons (step1328 p h) (sat_cons (step1336 p h) (sat_cons (step1318 p h) (sat_cons (step1331 p h) (sat_cons (step2391 p h) (sat_cons (step195 p h) (sat_cons (step194 p h) (sat_cons (step1291 p h) (sat_cons (step2309 p h) (sat_nil p)))))))))))))))
def c3399 : List Lit := [(1500, true), (1640, true), (80, true), (1645, true), (25, false), (2, false), (149, true), (28, false)]
theorem step3399 (p : Nat → Bool) (h : Constraints p) : clause p c3399 = true :=
  Snake9.LocalRup.prove_clause [c1222, c3397, c103, c1467, c1477, c1469, c1484, c1500] c3399 (by decide) p (sat_cons (step1222 p h) (sat_cons (step3397 p h) (sat_cons (step103 p h) (sat_cons (step1467 p h) (sat_cons (step1477 p h) (sat_cons (step1469 p h) (sat_cons (step1484 p h) (sat_cons (step1500 p h) (sat_nil p)))))))))
def c3400 : List Lit := [(1578, true), (1551, false), (1567, false), (1543, false), (48, true), (116, false), (76, false), (1559, false)]
theorem step3400 (p : Nat → Bool) (h : Constraints p) : clause p c3400 = true :=
  Snake9.LocalRup.prove_clause [c1366, c1371, c3398] c3400 (by decide) p (sat_cons (step1366 p h) (sat_cons (step1371 p h) (sat_cons (step3398 p h) (sat_nil p))))
def c3401 : List Lit := [(1673, false), (213, true), (1715, true), (107, true), (1694, false), (1688, false), (109, true), (76, false), (118, true)]
theorem step3401 (p : Nat → Bool) (h : Constraints p) : clause p c3401 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1617, c1595, c1603, c1633, c1657, c3361, c3364, c3138, c2056] c3401 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1617 p h) (sat_cons (step1595 p h) (sat_cons (step1603 p h) (sat_cons (step1633 p h) (sat_cons (step1657 p h) (sat_cons (step3361 p h) (sat_cons (step3364 p h) (sat_cons (step3138 p h) (sat_cons (step2056 p h) (sat_nil p)))))))))))
def c3402 : List Lit := [(1687, false), (1706, true), (236, true), (116, false), (1688, false), (118, true)]
theorem step3402 (p : Nat → Bool) (h : Constraints p) : clause p c3402 = true :=
  Snake9.LocalRup.prove_clause [c1606, c2377] c3402 (by decide) p (sat_cons (step1606 p h) (sat_cons (step2377 p h) (sat_nil p)))
def c3403 : List Lit := [(1680, false), (1645, false), (1694, false), (1688, false), (109, false), (1610, false), (1736, true), (118, true)]
theorem step3403 (p : Nat → Bool) (h : Constraints p) : clause p c3403 = true :=
  Snake9.LocalRup.prove_clause [c1453, c1527, c1714, c3064, c1657, c1658, c1721, c3074, c1535, c1430, c1454, c1438] c3403 (by decide) p (sat_cons (step1453 p h) (sat_cons (step1527 p h) (sat_cons (step1714 p h) (sat_cons (step3064 p h) (sat_cons (step1657 p h) (sat_cons (step1658 p h) (sat_cons (step1721 p h) (sat_cons (step3074 p h) (sat_cons (step1535 p h) (sat_cons (step1430 p h) (sat_cons (step1454 p h) (sat_cons (step1438 p h) (sat_nil p)))))))))))))
def c3404 : List Lit := [(1504, true), (83, false), (152, true), (25, false), (28, false)]
theorem step3404 (p : Nat → Bool) (h : Constraints p) : clause p c3404 = true :=
  Snake9.LocalRup.prove_clause [c1228, c1230, c1225, c1222, c1223, c111, c106, c119, c136] c3404 (by decide) p (sat_cons (step1228 p h) (sat_cons (step1230 p h) (sat_cons (step1225 p h) (sat_cons (step1222 p h) (sat_cons (step1223 p h) (sat_cons (step111 p h) (sat_cons (step106 p h) (sat_cons (step119 p h) (sat_cons (step136 p h) (sat_nil p))))))))))
def c3405 : List Lit := [(1704, true), (1690, false), (236, true), (111, true), (109, false), (118, true)]
theorem step3405 (p : Nat → Bool) (h : Constraints p) : clause p c3405 = true :=
  Snake9.LocalRup.prove_clause [c3028, c3058, c1628, c1609, c1916, c775] c3405 (by decide) p (sat_cons (step3028 p h) (sat_cons (step3058 p h) (sat_cons (step1628 p h) (sat_cons (step1609 p h) (sat_cons (step1916 p h) (sat_cons (step775 p h) (sat_nil p)))))))
end B112E019
