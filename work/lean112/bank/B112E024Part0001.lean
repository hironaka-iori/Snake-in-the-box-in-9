import B112E024Part0000
namespace B112E024
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1426 : List Lit := [(82, false), (1694, true), (105, false)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c627, c1423, c624, c626, c1220, c1216, c1209, c1214, c1212, c1208, c556, c558, c1222, c1206, c524, c525, c535, c1195, c1197, c1204, c1198, c1199, c548, c552] c1426 (by decide) p (sat_cons (step627 p h) (sat_cons (step1423 p h) (sat_cons (step624 p h) (sat_cons (step626 p h) (sat_cons (step1220 p h) (sat_cons (step1216 p h) (sat_cons (step1209 p h) (sat_cons (step1214 p h) (sat_cons (step1212 p h) (sat_cons (step1208 p h) (sat_cons (step556 p h) (sat_cons (step558 p h) (sat_cons (step1222 p h) (sat_cons (step1206 p h) (sat_cons (step524 p h) (sat_cons (step525 p h) (sat_cons (step535 p h) (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_cons (step1204 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step548 p h) (sat_cons (step552 p h) (sat_nil p)))))))))))))))))))))))))
def c1427 : List Lit := [(1653, true), (84, true), (86, false)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c617, c1144, c1145, c454, c450] c1427 (by decide) p (sat_cons (step617 p h) (sat_cons (step1144 p h) (sat_cons (step1145 p h) (sat_cons (step454 p h) (sat_cons (step450 p h) (sat_nil p))))))
def c1428 : List Lit := [(86, false), (1672, true), (94, true), (81, false), (85, false), (99, true)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c618, c1158, c1166, c1186, c1148, c340, c1427, c1154, c1153, c1149, c1182, c486, c1169, c489, c1160] c1428 (by decide) p (sat_cons (step618 p h) (sat_cons (step1158 p h) (sat_cons (step1166 p h) (sat_cons (step1186 p h) (sat_cons (step1148 p h) (sat_cons (step340 p h) (sat_cons (step1427 p h) (sat_cons (step1154 p h) (sat_cons (step1153 p h) (sat_cons (step1149 p h) (sat_cons (step1182 p h) (sat_cons (step486 p h) (sat_cons (step1169 p h) (sat_cons (step489 p h) (sat_cons (step1160 p h) (sat_nil p))))))))))))))))
def c1429 : List Lit := [(96, false), (94, false), (84, true), (85, false)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c618, c486, c487] c1429 (by decide) p (sat_cons (step618 p h) (sat_cons (step486 p h) (sat_cons (step487 p h) (sat_nil p))))
def c1430 : List Lit := [(98, false), (94, false), (86, false), (85, false), (102, false)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c619, c385, c480, c488, c496] c1430 (by decide) p (sat_cons (step619 p h) (sat_cons (step385 p h) (sat_cons (step480 p h) (sat_cons (step488 p h) (sat_cons (step496 p h) (sat_nil p))))))
def c1431 : List Lit := [(55, false), (194, true), (1603, true), (71, false), (110, false)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c610, c293, c295, c1054, c301, c1063, c298, c1058] c1431 (by decide) p (sat_cons (step610 p h) (sat_cons (step293 p h) (sat_cons (step295 p h) (sat_cons (step1054 p h) (sat_cons (step301 p h) (sat_cons (step1063 p h) (sat_cons (step298 p h) (sat_cons (step1058 p h) (sat_nil p)))))))))
def c1432 : List Lit := [(1515, false), (1539, false), (1554, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c595, c953, c984, c911, c914, c979, c891, c958, c883, c930, c932, c928, c925, c211, c227] c1432 (by decide) p (sat_cons (step595 p h) (sat_cons (step953 p h) (sat_cons (step984 p h) (sat_cons (step911 p h) (sat_cons (step914 p h) (sat_cons (step979 p h) (sat_cons (step891 p h) (sat_cons (step958 p h) (sat_cons (step883 p h) (sat_cons (step930 p h) (sat_cons (step932 p h) (sat_cons (step928 p h) (sat_cons (step925 p h) (sat_cons (step211 p h) (sat_cons (step227 p h) (sat_nil p))))))))))))))))
def c1433 : List Lit := [(111, false), (108, true), (120, true), (230, true), (105, true)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c626, c547, c546, c543, c1360] c1433 (by decide) p (sat_cons (step626 p h) (sat_cons (step547 p h) (sat_cons (step546 p h) (sat_cons (step543 p h) (sat_cons (step1360 p h) (sat_nil p))))))
def c1434 : List Lit := [(1514, true), (41, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c593, c903, c905, c901, c898, c198, c183] c1434 (by decide) p (sat_cons (step593 p h) (sat_cons (step903 p h) (sat_cons (step905 p h) (sat_cons (step901 p h) (sat_cons (step898 p h) (sat_cons (step198 p h) (sat_cons (step183 p h) (sat_nil p))))))))
def c1435 : List Lit := [(1553, true), (1514, false), (1539, false)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c595, c910, c953, c978, c913, c973, c891, c958, c883, c930, c932, c928, c925, c211, c227] c1435 (by decide) p (sat_cons (step595 p h) (sat_cons (step910 p h) (sat_cons (step953 p h) (sat_cons (step978 p h) (sat_cons (step913 p h) (sat_cons (step973 p h) (sat_cons (step891 p h) (sat_cons (step958 p h) (sat_cons (step883 p h) (sat_cons (step930 p h) (sat_cons (step932 p h) (sat_cons (step928 p h) (sat_cons (step925 p h) (sat_cons (step211 p h) (sat_cons (step227 p h) (sat_nil p))))))))))))))))
def c1436 : List Lit := [(1707, true), (1658, false), (1682, false), (119, true), (105, true)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c627, c1161, c1164, c1181, c1211, c1214, c1223, c1243, c1248, c1224, c1182, c1215, c1217, c1165, c1167, c1213, c1208, c1209, c1163, c1159, c556, c483, c559] c1436 (by decide) p (sat_cons (step627 p h) (sat_cons (step1161 p h) (sat_cons (step1164 p h) (sat_cons (step1181 p h) (sat_cons (step1211 p h) (sat_cons (step1214 p h) (sat_cons (step1223 p h) (sat_cons (step1243 p h) (sat_cons (step1248 p h) (sat_cons (step1224 p h) (sat_cons (step1182 p h) (sat_cons (step1215 p h) (sat_cons (step1217 p h) (sat_cons (step1165 p h) (sat_cons (step1167 p h) (sat_cons (step1213 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step1163 p h) (sat_cons (step1159 p h) (sat_cons (step556 p h) (sat_cons (step483 p h) (sat_cons (step559 p h) (sat_nil p))))))))))))))))))))))))
def c1437 : List Lit := [(1530, true), (31, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c595, c930, c932, c928, c925, c211, c227] c1437 (by decide) p (sat_cons (step595 p h) (sat_cons (step930 p h) (sat_cons (step932 p h) (sat_cons (step928 p h) (sat_cons (step925 p h) (sat_cons (step211 p h) (sat_cons (step227 p h) (sat_nil p))))))))
def c1438 : List Lit := [(34, false), (1519, true), (41, false)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c1434, c913, c889, c886, c911, c181, c182, c898, c901, c906] c1438 (by decide) p (sat_cons (step1434 p h) (sat_cons (step913 p h) (sat_cons (step889 p h) (sat_cons (step886 p h) (sat_cons (step911 p h) (sat_cons (step181 p h) (sat_cons (step182 p h) (sat_cons (step898 p h) (sat_cons (step901 p h) (sat_cons (step906 p h) (sat_nil p)))))))))))
def c1439 : List Lit := [(1534, true), (1654, true), (87, false), (1661, true)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c600, c1159, c1158, c938, c939, c250, c411, c381, c1146] c1439 (by decide) p (sat_cons (step600 p h) (sat_cons (step1159 p h) (sat_cons (step1158 p h) (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step250 p h) (sat_cons (step411 p h) (sat_cons (step381 p h) (sat_cons (step1146 p h) (sat_nil p))))))))))
def c1440 : List Lit := [(43, false), (31, false), (47, false)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c595, c211, c227] c1440 (by decide) p (sat_cons (step595 p h) (sat_cons (step211 p h) (sat_cons (step227 p h) (sat_nil p))))
def c1441 : List Lit := [(1471, true), (16, false), (17, true), (1481, true), (85, false), (1465, false)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c829, c830, c1404, c88] c1441 (by decide) p (sat_cons (step829 p h) (sat_cons (step830 p h) (sat_cons (step1404 p h) (sat_cons (step88 p h) (sat_nil p)))))
def c1442 : List Lit := [(1471, false), (17, true), (1481, true), (1465, false)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c588, c821, c849, c837, c838, c853, c832, c833, c824, c144, c815, c132] c1442 (by decide) p (sat_cons (step588 p h) (sat_cons (step821 p h) (sat_cons (step849 p h) (sat_cons (step837 p h) (sat_cons (step838 p h) (sat_cons (step853 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step824 p h) (sat_cons (step144 p h) (sat_cons (step815 p h) (sat_cons (step132 p h) (sat_nil p)))))))))))))
def c1443 : List Lit := [(1593, true), (52, true)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c605, c1048, c1049, c1046, c1042, c1043, c275, c269] c1443 (by decide) p (sat_cons (step605 p h) (sat_cons (step1048 p h) (sat_cons (step1049 p h) (sat_cons (step1046 p h) (sat_cons (step1042 p h) (sat_cons (step1043 p h) (sat_cons (step275 p h) (sat_cons (step269 p h) (sat_nil p)))))))))
def c1444 : List Lit := [(1589, true), (60, false), (62, false)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c1042, c1043, c269] c1444 (by decide) p (sat_cons (step1042 p h) (sat_cons (step1043 p h) (sat_cons (step269 p h) (sat_nil p))))
def c1445 : List Lit := [(63, true), (186, true), (1592, true), (52, true)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c605, c1047, c279, c274] c1445 (by decide) p (sat_cons (step605 p h) (sat_cons (step1047 p h) (sat_cons (step279 p h) (sat_cons (step274 p h) (sat_nil p)))))
def c1446 : List Lit := [(379, false), (74, true), (75, false), (79, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c1379, c1368, c612, c720, c721, c722, c718, c724, c305, c745, c306, c740, c311, c734, c730, c733] c1446 (by decide) p (sat_cons (step1379 p h) (sat_cons (step1368 p h) (sat_cons (step612 p h) (sat_cons (step720 p h) (sat_cons (step721 p h) (sat_cons (step722 p h) (sat_cons (step718 p h) (sat_cons (step724 p h) (sat_cons (step305 p h) (sat_cons (step745 p h) (sat_cons (step306 p h) (sat_cons (step740 p h) (sat_cons (step311 p h) (sat_cons (step734 p h) (sat_cons (step730 p h) (sat_cons (step733 p h) (sat_nil p)))))))))))))))))
def c1447 : List Lit := [(1695, true), (87, true), (86, false), (108, true), (1687, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c1423, c623, c1214, c1221, c1223, c1217, c1206, c1208, c1197, c531, c534] c1447 (by decide) p (sat_cons (step1423 p h) (sat_cons (step623 p h) (sat_cons (step1214 p h) (sat_cons (step1221 p h) (sat_cons (step1223 p h) (sat_cons (step1217 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step1197 p h) (sat_cons (step531 p h) (sat_cons (step534 p h) (sat_nil p))))))))))))
def c1448 : List Lit := [(1539, true), (57, false), (55, false), (54, true)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c938, c949, c947, c940, c941, c258] c1448 (by decide) p (sat_cons (step938 p h) (sat_cons (step949 p h) (sat_cons (step947 p h) (sat_cons (step940 p h) (sat_cons (step941 p h) (sat_cons (step258 p h) (sat_nil p)))))))
def c1449 : List Lit := [(1593, true), (53, false), (86, false)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c1048, c1443, c1046, c244] c1449 (by decide) p (sat_cons (step1048 p h) (sat_cons (step1443 p h) (sat_cons (step1046 p h) (sat_cons (step244 p h) (sat_nil p)))))
def c1450 : List Lit := [(1593, true), (81, true), (54, true), (170, true)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c604, c603, c1048, c1049, c1046, c1042, c1043, c1444, c272, c264, c265, c233] c1450 (by decide) p (sat_cons (step604 p h) (sat_cons (step603 p h) (sat_cons (step1048 p h) (sat_cons (step1049 p h) (sat_cons (step1046 p h) (sat_cons (step1042 p h) (sat_cons (step1043 p h) (sat_cons (step1444 p h) (sat_cons (step272 p h) (sat_cons (step264 p h) (sat_cons (step265 p h) (sat_cons (step233 p h) (sat_nil p)))))))))))))
def c1451 : List Lit := [(417, true), (75, false), (74, true), (67, false), (70, false)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c1364, c612, c614, c742, c744, c740, c724, c734, c735, c722, c733, c729, c719, c730, c728, c718, c309, c305, c306, c311, c297, c310] c1451 (by decide) p (sat_cons (step1364 p h) (sat_cons (step612 p h) (sat_cons (step614 p h) (sat_cons (step742 p h) (sat_cons (step744 p h) (sat_cons (step740 p h) (sat_cons (step724 p h) (sat_cons (step734 p h) (sat_cons (step735 p h) (sat_cons (step722 p h) (sat_cons (step733 p h) (sat_cons (step729 p h) (sat_cons (step719 p h) (sat_cons (step730 p h) (sat_cons (step728 p h) (sat_cons (step718 p h) (sat_cons (step309 p h) (sat_cons (step305 p h) (sat_cons (step306 p h) (sat_cons (step311 p h) (sat_cons (step297 p h) (sat_cons (step310 p h) (sat_nil p)))))))))))))))))))))))
def c1452 : List Lit := [(58, false), (61, false), (170, true), (60, true), (81, true), (54, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c604, c603, c272, c264, c265, c233] c1452 (by decide) p (sat_cons (step604 p h) (sat_cons (step603 p h) (sat_cons (step272 p h) (sat_cons (step264 p h) (sat_cons (step265 p h) (sat_cons (step233 p h) (sat_nil p)))))))
def c1453 : List Lit := [(1475, true), (17, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c835, c837, c1406, c829] c1453 (by decide) p (sat_cons (step835 p h) (sat_cons (step837 p h) (sat_cons (step1406 p h) (sat_cons (step829 p h) (sat_nil p)))))
def c1454 : List Lit := [(55, false), (1601, true), (90, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c601, c253, c1420] c1454 (by decide) p (sat_cons (step601 p h) (sat_cons (step253 p h) (sat_cons (step1420 p h) (sat_nil p))))
def c1455 : List Lit := [(14, true), (17, true), (151, true), (85, false), (88, true), (1481, true)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c583, c585, c588, c1453, c853, c826, c815, c817, c823, c824, c849, c818, c819, c840, c98, c97, c1323, c829, c831, c838, c88, c832, c108, c109, c143, c155, c110, c165] c1455 (by decide) p (sat_cons (step583 p h) (sat_cons (step585 p h) (sat_cons (step588 p h) (sat_cons (step1453 p h) (sat_cons (step853 p h) (sat_cons (step826 p h) (sat_cons (step815 p h) (sat_cons (step817 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step849 p h) (sat_cons (step818 p h) (sat_cons (step819 p h) (sat_cons (step840 p h) (sat_cons (step98 p h) (sat_cons (step97 p h) (sat_cons (step1323 p h) (sat_cons (step829 p h) (sat_cons (step831 p h) (sat_cons (step838 p h) (sat_cons (step88 p h) (sat_cons (step832 p h) (sat_cons (step108 p h) (sat_cons (step109 p h) (sat_cons (step143 p h) (sat_cons (step155 p h) (sat_cons (step110 p h) (sat_cons (step165 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1456 : List Lit := [(1473, true), (14, false), (17, true)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c588, c832, c833, c144, c132] c1456 (by decide) p (sat_cons (step588 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step144 p h) (sat_cons (step132 p h) (sat_nil p))))))
def c1457 : List Lit := [(18, false), (22, false), (14, false), (88, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c583, c98, c38] c1457 (by decide) p (sat_cons (step583 p h) (sat_cons (step98 p h) (sat_cons (step38 p h) (sat_nil p))))
def c1458 : List Lit := [(1476, true), (14, false), (17, true), (85, false), (88, true), (1481, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c588, c581, c1456, c1453, c853, c822, c836, c838, c829, c1421, c144, c834, c1457, c819, c820, c1404, c1441, c79, c33, c124, c54] c1458 (by decide) p (sat_cons (step588 p h) (sat_cons (step581 p h) (sat_cons (step1456 p h) (sat_cons (step1453 p h) (sat_cons (step853 p h) (sat_cons (step822 p h) (sat_cons (step836 p h) (sat_cons (step838 p h) (sat_cons (step829 p h) (sat_cons (step1421 p h) (sat_cons (step144 p h) (sat_cons (step834 p h) (sat_cons (step1457 p h) (sat_cons (step819 p h) (sat_cons (step820 p h) (sat_cons (step1404 p h) (sat_cons (step1441 p h) (sat_cons (step79 p h) (sat_cons (step33 p h) (sat_cons (step124 p h) (sat_cons (step54 p h) (sat_nil p))))))))))))))))))))))
def c1459 : List Lit := [(14, false), (17, true), (1481, true), (85, false), (88, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c583, c1458, c849, c821, c823, c819, c816, c98, c32] c1459 (by decide) p (sat_cons (step583 p h) (sat_cons (step1458 p h) (sat_cons (step849 p h) (sat_cons (step821 p h) (sat_cons (step823 p h) (sat_cons (step819 p h) (sat_cons (step816 p h) (sat_cons (step98 p h) (sat_cons (step32 p h) (sat_nil p))))))))))
def c1460 : List Lit := [(17, true), (151, true), (1481, true), (85, false), (88, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c1455, c1459] c1460 (by decide) p (sat_cons (step1455 p h) (sat_cons (step1459 p h) (sat_nil p)))
def c1461 : List Lit := [(17, true), (85, false), (88, true), (1481, true)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c1380, c583, c585, c1453, c1460, c1459, c853, c656, c815, c826, c659, c823, c824, c817, c655, c849, c819, c840, c98, c97, c1323, c829, c831, c838, c88, c832, c108, c163, c164, c160] c1461 (by decide) p (sat_cons (step1380 p h) (sat_cons (step583 p h) (sat_cons (step585 p h) (sat_cons (step1453 p h) (sat_cons (step1460 p h) (sat_cons (step1459 p h) (sat_cons (step853 p h) (sat_cons (step656 p h) (sat_cons (step815 p h) (sat_cons (step826 p h) (sat_cons (step659 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step817 p h) (sat_cons (step655 p h) (sat_cons (step849 p h) (sat_cons (step819 p h) (sat_cons (step840 p h) (sat_cons (step98 p h) (sat_cons (step97 p h) (sat_cons (step1323 p h) (sat_cons (step829 p h) (sat_cons (step831 p h) (sat_cons (step838 p h) (sat_cons (step88 p h) (sat_cons (step832 p h) (sat_cons (step108 p h) (sat_cons (step163 p h) (sat_cons (step164 p h) (sat_cons (step160 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1462 : List Lit := [(18, false), (12, false), (22, false), (88, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c583, c97, c1323] c1462 (by decide) p (sat_cons (step583 p h) (sat_cons (step97 p h) (sat_cons (step1323 p h) (sat_nil p))))
def c1463 : List Lit := [(18, true), (26, true), (14, false), (1481, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c587, c832, c835, c853, c822, c819, c820, c821, c824, c849, c816, c836, c838, c73, c834, c829, c130, c124, c140] c1463 (by decide) p (sat_cons (step587 p h) (sat_cons (step832 p h) (sat_cons (step835 p h) (sat_cons (step853 p h) (sat_cons (step822 p h) (sat_cons (step819 p h) (sat_cons (step820 p h) (sat_cons (step821 p h) (sat_cons (step824 p h) (sat_cons (step849 p h) (sat_cons (step816 p h) (sat_cons (step836 p h) (sat_cons (step838 p h) (sat_cons (step73 p h) (sat_cons (step834 p h) (sat_cons (step829 p h) (sat_cons (step130 p h) (sat_cons (step124 p h) (sat_cons (step140 p h) (sat_nil p))))))))))))))))))))
def c1464 : List Lit := [(30, false), (31, true), (29, false), (27, false), (151, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c155, c165] c1464 (by decide) p (sat_cons (step155 p h) (sat_cons (step165 p h) (sat_nil p)))
def c1465 : List Lit := [(82, false), (1674, true), (99, true), (15, true), (13, false), (25, false), (12, false), (1654, false), (85, false)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c587, c1158, c327, c328, c47, c1148, c1161, c139, c1156, c1188, c1168, c1170, c1163, c1160, c472] c1465 (by decide) p (sat_cons (step587 p h) (sat_cons (step1158 p h) (sat_cons (step327 p h) (sat_cons (step328 p h) (sat_cons (step47 p h) (sat_cons (step1148 p h) (sat_cons (step1161 p h) (sat_cons (step139 p h) (sat_cons (step1156 p h) (sat_cons (step1188 p h) (sat_cons (step1168 p h) (sat_cons (step1170 p h) (sat_cons (step1163 p h) (sat_cons (step1160 p h) (sat_cons (step472 p h) (sat_nil p))))))))))))))))
def c1466 : List Lit := [(1481, true), (24, true), (1465, false), (25, false), (12, true), (14, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c586, c815, c824, c857, c853, c827, c837, c817, c829, c124, c123] c1466 (by decide) p (sat_cons (step586 p h) (sat_cons (step815 p h) (sat_cons (step824 p h) (sat_cons (step857 p h) (sat_cons (step853 p h) (sat_cons (step827 p h) (sat_cons (step837 p h) (sat_cons (step817 p h) (sat_cons (step829 p h) (sat_cons (step124 p h) (sat_cons (step123 p h) (sat_nil p))))))))))))
def c1467 : List Lit := [(1502, false), (1539, false), (1554, true)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c595, c953, c984, c1432, c1414, c1434, c916, c891, c892, c913, c886, c979, c958, c932, c925, c212, c210] c1467 (by decide) p (sat_cons (step595 p h) (sat_cons (step953 p h) (sat_cons (step984 p h) (sat_cons (step1432 p h) (sat_cons (step1414 p h) (sat_cons (step1434 p h) (sat_cons (step916 p h) (sat_cons (step891 p h) (sat_cons (step892 p h) (sat_cons (step913 p h) (sat_cons (step886 p h) (sat_cons (step979 p h) (sat_cons (step958 p h) (sat_cons (step932 p h) (sat_cons (step925 p h) (sat_cons (step212 p h) (sat_cons (step210 p h) (sat_nil p))))))))))))))))))
def c1468 : List Lit := [(1539, false), (1554, true)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c592, c594, c593, c1432, c1414, c1434, c910, c974, c963, c935, c1467, c883, c1437, c958, c979, c913, c1438, c889, c198, c209, c886, c887, c901, c210, c906, c925, c926, c897, c898, c933, c172, c928, c196, c218, c189] c1468 (by decide) p (sat_cons (step592 p h) (sat_cons (step594 p h) (sat_cons (step593 p h) (sat_cons (step1432 p h) (sat_cons (step1414 p h) (sat_cons (step1434 p h) (sat_cons (step910 p h) (sat_cons (step974 p h) (sat_cons (step963 p h) (sat_cons (step935 p h) (sat_cons (step1467 p h) (sat_cons (step883 p h) (sat_cons (step1437 p h) (sat_cons (step958 p h) (sat_cons (step979 p h) (sat_cons (step913 p h) (sat_cons (step1438 p h) (sat_cons (step889 p h) (sat_cons (step198 p h) (sat_cons (step209 p h) (sat_cons (step886 p h) (sat_cons (step887 p h) (sat_cons (step901 p h) (sat_cons (step210 p h) (sat_cons (step906 p h) (sat_cons (step925 p h) (sat_cons (step926 p h) (sat_cons (step897 p h) (sat_cons (step898 p h) (sat_cons (step933 p h) (sat_cons (step172 p h) (sat_cons (step928 p h) (sat_cons (step196 p h) (sat_cons (step218 p h) (sat_cons (step189 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1469 : List Lit := [(1452, true), (53, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c580, c794, c796, c791, c788, c31, c16] c1469 (by decide) p (sat_cons (step580 p h) (sat_cons (step794 p h) (sat_cons (step796 p h) (sat_cons (step791 p h) (sat_cons (step788 p h) (sat_cons (step31 p h) (sat_cons (step16 p h) (sat_nil p))))))))
def c1470 : List Lit := [(11, false), (1446, true), (53, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c580, c31, c14, c15, c787, c784] c1470 (by decide) p (sat_cons (step580 p h) (sat_cons (step31 p h) (sat_cons (step14 p h) (sat_cons (step15 p h) (sat_cons (step787 p h) (sat_cons (step784 p h) (sat_nil p)))))))
def c1471 : List Lit := [(35, false), (41, false), (16, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c591, c186, c185, c1339] c1471 (by decide) p (sat_cons (step591 p h) (sat_cons (step186 p h) (sat_cons (step185 p h) (sat_cons (step1339 p h) (sat_nil p)))))
def c1472 : List Lit := [(1536, true), (51, true), (53, false)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c602, c941, c942, c257, c258] c1472 (by decide) p (sat_cons (step602 p h) (sat_cons (step941 p h) (sat_cons (step942 p h) (sat_cons (step257 p h) (sat_cons (step258 p h) (sat_nil p))))))
def c1473 : List Lit := [(1510, true), (44, false), (47, false), (33, false)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c592, c897, c898, c172, c196, c189, c218] c1473 (by decide) p (sat_cons (step592 p h) (sat_cons (step897 p h) (sat_cons (step898 p h) (sat_cons (step172 p h) (sat_cons (step196 p h) (sat_cons (step189 p h) (sat_cons (step218 p h) (sat_nil p))))))))
def c1474 : List Lit := [(1601, true), (417, true), (51, true)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c610, c608, c1059, c1061, c1056, c1057, c1053, c1054, c299, c288, c285, c1451] c1474 (by decide) p (sat_cons (step610 p h) (sat_cons (step608 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step299 p h) (sat_cons (step288 p h) (sat_cons (step285 p h) (sat_cons (step1451 p h) (sat_nil p)))))))))))))
def c1475 : List Lit := [(1480, true), (1465, false), (86, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c821, c852, c848, c824, c835, c1453, c815, c832, c92] c1475 (by decide) p (sat_cons (step821 p h) (sat_cons (step852 p h) (sat_cons (step848 p h) (sat_cons (step824 p h) (sat_cons (step835 p h) (sat_cons (step1453 p h) (sat_cons (step815 p h) (sat_cons (step832 p h) (sat_cons (step92 p h) (sat_nil p))))))))))
def c1476 : List Lit := [(1459, true), (53, false), (3, false)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c19, c1362, c579, c4, c789, c1398, c5, c805, c813, c1470, c793, c798, c801, c809, c790, c786, c23, c13] c1476 (by decide) p (sat_cons (step19 p h) (sat_cons (step1362 p h) (sat_cons (step579 p h) (sat_cons (step4 p h) (sat_cons (step789 p h) (sat_cons (step1398 p h) (sat_cons (step5 p h) (sat_cons (step805 p h) (sat_cons (step813 p h) (sat_cons (step1470 p h) (sat_cons (step793 p h) (sat_cons (step798 p h) (sat_cons (step801 p h) (sat_cons (step809 p h) (sat_cons (step790 p h) (sat_cons (step786 p h) (sat_cons (step23 p h) (sat_cons (step13 p h) (sat_nil p)))))))))))))))))))
def c1477 : List Lit := [(1553, true), (1504, false), (1519, false), (1514, false), (1538, false)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c952, c983, c978, c916, c957, c892, c1437, c883] c1477 (by decide) p (sat_cons (step952 p h) (sat_cons (step983 p h) (sat_cons (step978 p h) (sat_cons (step916 p h) (sat_cons (step957 p h) (sat_cons (step892 p h) (sat_cons (step1437 p h) (sat_cons (step883 p h) (sat_nil p)))))))))
def c1478 : List Lit := [(1682, true), (108, true), (1625, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c623, c1195, c1095, c1087, c1093, c1091, c1206, c1204, c1197, c1198, c1199, c386, c533, c552] c1478 (by decide) p (sat_cons (step623 p h) (sat_cons (step1195 p h) (sat_cons (step1095 p h) (sat_cons (step1087 p h) (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1206 p h) (sat_cons (step1204 p h) (sat_cons (step1197 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step386 p h) (sat_cons (step533 p h) (sat_cons (step552 p h) (sat_nil p)))))))))))))))
def c1479 : List Lit := [(107, false), (87, true), (111, false), (110, false)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c623, c533, c552] c1479 (by decide) p (sat_cons (step623 p h) (sat_cons (step533 p h) (sat_cons (step552 p h) (sat_nil p))))
def c1480 : List Lit := [(54, false), (81, false)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c600, c250, c251, c1343] c1480 (by decide) p (sat_cons (step600 p h) (sat_cons (step250 p h) (sat_cons (step251 p h) (sat_cons (step1343 p h) (sat_nil p)))))
def c1481 : List Lit := [(1480, true), (1625, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c583, c1095, c1088, c1093, c1091, c1090, c852, c1475, c826, c819, c398, c98, c36, c817, c39] c1481 (by decide) p (sat_cons (step583 p h) (sat_cons (step1095 p h) (sat_cons (step1088 p h) (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1090 p h) (sat_cons (step852 p h) (sat_cons (step1475 p h) (sat_cons (step826 p h) (sat_cons (step819 p h) (sat_cons (step398 p h) (sat_cons (step98 p h) (sat_cons (step36 p h) (sat_cons (step817 p h) (sat_cons (step39 p h) (sat_nil p))))))))))))))))
def c1482 : List Lit := [(1539, true), (1621, true)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c1088, c1480, c938, c1087, c949, c947, c940, c941, c1472, c243] c1482 (by decide) p (sat_cons (step1088 p h) (sat_cons (step1480 p h) (sat_cons (step938 p h) (sat_cons (step1087 p h) (sat_cons (step949 p h) (sat_cons (step947 p h) (sat_cons (step940 p h) (sat_cons (step941 p h) (sat_cons (step1472 p h) (sat_cons (step243 p h) (sat_nil p)))))))))))
def c1483 : List Lit := [(1655, true), (1625, true)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c1093, c1091, c1095, c1087, c1088, c340, c1147, c1148, c1429] c1483 (by decide) p (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1095 p h) (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step340 p h) (sat_cons (step1147 p h) (sat_cons (step1148 p h) (sat_cons (step1429 p h) (sat_nil p))))))))))
def c1484 : List Lit := [(1706, true), (1625, true), (1665, false), (1689, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c1423, c617, c624, c616, c1483, c1093, c1091, c1095, c1087, c1088, c340, c1427, c1153, c1181, c1090, c338, c1220, c1247, c1242, c1186, c1182, c1223, c1156, c1165, c1478, c416, c451, c537, c1146, c522, c453, c1163, c430, c445] c1484 (by decide) p (sat_cons (step1423 p h) (sat_cons (step617 p h) (sat_cons (step624 p h) (sat_cons (step616 p h) (sat_cons (step1483 p h) (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1095 p h) (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step340 p h) (sat_cons (step1427 p h) (sat_cons (step1153 p h) (sat_cons (step1181 p h) (sat_cons (step1090 p h) (sat_cons (step338 p h) (sat_cons (step1220 p h) (sat_cons (step1247 p h) (sat_cons (step1242 p h) (sat_cons (step1186 p h) (sat_cons (step1182 p h) (sat_cons (step1223 p h) (sat_cons (step1156 p h) (sat_cons (step1165 p h) (sat_cons (step1478 p h) (sat_cons (step416 p h) (sat_cons (step451 p h) (sat_cons (step537 p h) (sat_cons (step1146 p h) (sat_cons (step522 p h) (sat_cons (step453 p h) (sat_cons (step1163 p h) (sat_cons (step430 p h) (sat_cons (step445 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1485 : List Lit := [(19, true), (14, true), (88, true), (1469, true), (81, false)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c583, c815, c825, c818, c820, c827, c98, c817, c36] c1485 (by decide) p (sat_cons (step583 p h) (sat_cons (step815 p h) (sat_cons (step825 p h) (sat_cons (step818 p h) (sat_cons (step820 p h) (sat_cons (step827 p h) (sat_cons (step98 p h) (sat_cons (step817 p h) (sat_cons (step36 p h) (sat_nil p))))))))))
def c1486 : List Lit := [(86, false), (1690, true), (102, false), (98, false), (93, false), (83, true), (89, false)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c616, c619, c445, c521, c453, c390, c427, c495, c509, c483, c1212, c1209, c1217] c1486 (by decide) p (sat_cons (step616 p h) (sat_cons (step619 p h) (sat_cons (step445 p h) (sat_cons (step521 p h) (sat_cons (step453 p h) (sat_cons (step390 p h) (sat_cons (step427 p h) (sat_cons (step495 p h) (sat_cons (step509 p h) (sat_cons (step483 p h) (sat_cons (step1212 p h) (sat_cons (step1209 p h) (sat_cons (step1217 p h) (sat_nil p))))))))))))))
def c1487 : List Lit := [(85, false), (103, true), (98, false), (93, false), (1656, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c619, c387, c495, c494, c1355, c489, c1149] c1487 (by decide) p (sat_cons (step619 p h) (sat_cons (step387 p h) (sat_cons (step495 p h) (sat_cons (step494 p h) (sat_cons (step1355 p h) (sat_cons (step489 p h) (sat_cons (step1149 p h) (sat_nil p))))))))
def c1488 : List Lit := [(85, false), (1655, true), (81, false)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c1148, c1147, c342, c1429] c1488 (by decide) p (sat_cons (step1148 p h) (sat_cons (step1147 p h) (sat_cons (step342 p h) (sat_cons (step1429 p h) (sat_nil p)))))
def c1489 : List Lit := [(1539, true), (102, false), (89, false), (54, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c601, c938, c949, c947, c940, c941, c942, c1472, c1344, c440, c254] c1489 (by decide) p (sat_cons (step601 p h) (sat_cons (step938 p h) (sat_cons (step949 p h) (sat_cons (step947 p h) (sat_cons (step940 p h) (sat_cons (step941 p h) (sat_cons (step942 p h) (sat_cons (step1472 p h) (sat_cons (step1344 p h) (sat_cons (step440 p h) (sat_cons (step254 p h) (sat_nil p))))))))))))
end B112E024
