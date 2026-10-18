import B112E174Part0006
namespace B112E174
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1469 : List Lit := [(56, false), (7, false), (1235, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c1415, c1466, c1390, c1400, c1402, c1416, c1103, c930, c931, c937, c943, c1222, c766, c1055, c1062, c815, c887, c1385, c1468, c1186, c1465, c1376, c998, c995, c944, c1386, c939, c891, c933, c816, c1346, c809, c1249, c1059, c788] c1469 (by decide) p (sat_cons (step1415 p h) (sat_cons (step1466 p h) (sat_cons (step1390 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1416 p h) (sat_cons (step1103 p h) (sat_cons (step930 p h) (sat_cons (step931 p h) (sat_cons (step937 p h) (sat_cons (step943 p h) (sat_cons (step1222 p h) (sat_cons (step766 p h) (sat_cons (step1055 p h) (sat_cons (step1062 p h) (sat_cons (step815 p h) (sat_cons (step887 p h) (sat_cons (step1385 p h) (sat_cons (step1468 p h) (sat_cons (step1186 p h) (sat_cons (step1465 p h) (sat_cons (step1376 p h) (sat_cons (step998 p h) (sat_cons (step995 p h) (sat_cons (step944 p h) (sat_cons (step1386 p h) (sat_cons (step939 p h) (sat_cons (step891 p h) (sat_cons (step933 p h) (sat_cons (step816 p h) (sat_cons (step1346 p h) (sat_cons (step809 p h) (sat_cons (step1249 p h) (sat_cons (step1059 p h) (sat_cons (step788 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1470 : List Lit := [(1226, true), (7, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c787, c788, c1071] c1470 (by decide) p (sat_cons (step787 p h) (sat_cons (step788 p h) (sat_cons (step1071 p h) (sat_nil p))))
def c1471 : List Lit := [(7, false), (1235, false)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c1415, c1466, c1390, c1416, c1222, c1103, c930, c931, c937, c1462, c943, c1379, c1387, c895, c1469, c1470, c1059, c809, c820, c1056, c767, c769, c765, c1316, c1319, c21] c1471 (by decide) p (sat_cons (step1415 p h) (sat_cons (step1466 p h) (sat_cons (step1390 p h) (sat_cons (step1416 p h) (sat_cons (step1222 p h) (sat_cons (step1103 p h) (sat_cons (step930 p h) (sat_cons (step931 p h) (sat_cons (step937 p h) (sat_cons (step1462 p h) (sat_cons (step943 p h) (sat_cons (step1379 p h) (sat_cons (step1387 p h) (sat_cons (step895 p h) (sat_cons (step1469 p h) (sat_cons (step1470 p h) (sat_cons (step1059 p h) (sat_cons (step809 p h) (sat_cons (step820 p h) (sat_cons (step1056 p h) (sat_cons (step767 p h) (sat_cons (step769 p h) (sat_cons (step765 p h) (sat_cons (step1316 p h) (sat_cons (step1319 p h) (sat_cons (step21 p h) (sat_nil p)))))))))))))))))))))))))))
def c1472 : List Lit := [(1357, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c1466, c942] c1472 (by decide) p (sat_cons (step1466 p h) (sat_cons (step942 p h) (sat_nil p)))
def c1473 : List Lit := [(1350, false), (1427, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1381, c943, c946, c995, c1186, c1376, c1465] c1473 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1381 p h) (sat_cons (step943 p h) (sat_cons (step946 p h) (sat_cons (step995 p h) (sat_cons (step1186 p h) (sat_cons (step1376 p h) (sat_cons (step1465 p h) (sat_nil p)))))))))
def c1474 : List Lit := [(1298, true), (1264, false), (26, false)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c838, c1369, c1373, c879, c1370, c1077, c841, c861, c1336, c95] c1474 (by decide) p (sat_cons (step838 p h) (sat_cons (step1369 p h) (sat_cons (step1373 p h) (sat_cons (step879 p h) (sat_cons (step1370 p h) (sat_cons (step1077 p h) (sat_cons (step841 p h) (sat_cons (step861 p h) (sat_cons (step1336 p h) (sat_cons (step95 p h) (sat_nil p)))))))))))
def c1475 : List Lit := [(1426, true)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c1472, c1379, c992, c945, c1376, c1186, c1465] c1475 (by decide) p (sat_cons (step1472 p h) (sat_cons (step1379 p h) (sat_cons (step992 p h) (sat_cons (step945 p h) (sat_cons (step1376 p h) (sat_cons (step1186 p h) (sat_cons (step1465 p h) (sat_nil p))))))))
def c1476 : List Lit := [(1316, false)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1387] c1476 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1387 p h) (sat_nil p)))
def c1477 : List Lit := [(26, false), (28, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1463, c1062, c1471, c1053, c1461, c778, c836, c1474, c892, c816, c819, c809, c779, c781, c1059, c776, c768, c787, c1051, c1322, c29] c1477 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1463 p h) (sat_cons (step1062 p h) (sat_cons (step1471 p h) (sat_cons (step1053 p h) (sat_cons (step1461 p h) (sat_cons (step778 p h) (sat_cons (step836 p h) (sat_cons (step1474 p h) (sat_cons (step892 p h) (sat_cons (step816 p h) (sat_cons (step819 p h) (sat_cons (step809 p h) (sat_cons (step779 p h) (sat_cons (step781 p h) (sat_cons (step1059 p h) (sat_cons (step776 p h) (sat_cons (step768 p h) (sat_cons (step787 p h) (sat_cons (step1051 p h) (sat_cons (step1322 p h) (sat_cons (step29 p h) (sat_nil p)))))))))))))))))))))))
def c1478 : List Lit := [(1251, false)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1390, c895] c1478 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1390 p h) (sat_cons (step895 p h) (sat_nil p))))
def c1479 : List Lit := [(1222, true), (1226, true)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c787, c788, c1326, c1324, c311, c312, c315, c317, c1353, c339, c328, c322, c321, c41, c1327, c1470, c1053, c779, c781, c776, c768, c1051, c29] c1479 (by decide) p (sat_cons (step787 p h) (sat_cons (step788 p h) (sat_cons (step1326 p h) (sat_cons (step1324 p h) (sat_cons (step311 p h) (sat_cons (step312 p h) (sat_cons (step315 p h) (sat_cons (step317 p h) (sat_cons (step1353 p h) (sat_cons (step339 p h) (sat_cons (step328 p h) (sat_cons (step322 p h) (sat_cons (step321 p h) (sat_cons (step41 p h) (sat_cons (step1327 p h) (sat_cons (step1470 p h) (sat_cons (step1053 p h) (sat_cons (step779 p h) (sat_cons (step781 p h) (sat_cons (step776 p h) (sat_cons (step768 p h) (sat_cons (step1051 p h) (sat_cons (step29 p h) (sat_nil p))))))))))))))))))))))))
def c1480 : List Lit := [(1222, false), (1266, false), (28, true)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1332, c827, c1477, c833, c847, c1373, c892, c1067, c819, c889, c1062, c1374, c799, c800, c850, c798, c794, c795, c834, c65, c829, c1331] c1480 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1332 p h) (sat_cons (step827 p h) (sat_cons (step1477 p h) (sat_cons (step833 p h) (sat_cons (step847 p h) (sat_cons (step1373 p h) (sat_cons (step892 p h) (sat_cons (step1067 p h) (sat_cons (step819 p h) (sat_cons (step889 p h) (sat_cons (step1062 p h) (sat_cons (step1374 p h) (sat_cons (step799 p h) (sat_cons (step800 p h) (sat_cons (step850 p h) (sat_cons (step798 p h) (sat_cons (step794 p h) (sat_cons (step795 p h) (sat_cons (step834 p h) (sat_cons (step65 p h) (sat_cons (step829 p h) (sat_cons (step1331 p h) (sat_nil p))))))))))))))))))))))))
def c1481 : List Lit := [(1221, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c778, c1055, c1053, c766, c1222] c1481 (by decide) p (sat_cons (step778 p h) (sat_cons (step1055 p h) (sat_cons (step1053 p h) (sat_cons (step766 p h) (sat_cons (step1222 p h) (sat_nil p))))))
def c1482 : List Lit := [(1266, false), (28, true)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1476, c1332, c827, c1477, c833, c847, c1373, c892, c1480, c1479, c1059, c808, c816, c815, c809, c889, c799, c800, c1374, c798, c794, c795, c850, c65, c834, c1331, c829] c1482 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1476 p h) (sat_cons (step1332 p h) (sat_cons (step827 p h) (sat_cons (step1477 p h) (sat_cons (step833 p h) (sat_cons (step847 p h) (sat_cons (step1373 p h) (sat_cons (step892 p h) (sat_cons (step1480 p h) (sat_cons (step1479 p h) (sat_cons (step1059 p h) (sat_cons (step808 p h) (sat_cons (step816 p h) (sat_cons (step815 p h) (sat_cons (step809 p h) (sat_cons (step889 p h) (sat_cons (step799 p h) (sat_cons (step800 p h) (sat_cons (step1374 p h) (sat_cons (step798 p h) (sat_cons (step794 p h) (sat_cons (step795 p h) (sat_cons (step850 p h) (sat_cons (step65 p h) (sat_cons (step834 p h) (sat_cons (step1331 p h) (sat_cons (step829 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1483 : List Lit := [(1242, false)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1478, c817] c1483 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1478 p h) (sat_cons (step817 p h) (sat_nil p))))
def c1484 : List Lit := [(1237, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c1483, c1064] c1484 (by decide) p (sat_cons (step1483 p h) (sat_cons (step1064 p h) (sat_nil p)))
def c1485 : List Lit := [(1229, false), (1241, true), (28, true)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1476, c1482, c838, c836, c835, c1332, c827, c1477, c833, c808, c809, c815, c799, c800, c889, c797, c798, c794, c1464, c69] c1485 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1476 p h) (sat_cons (step1482 p h) (sat_cons (step838 p h) (sat_cons (step836 p h) (sat_cons (step835 p h) (sat_cons (step1332 p h) (sat_cons (step827 p h) (sat_cons (step1477 p h) (sat_cons (step833 p h) (sat_cons (step808 p h) (sat_cons (step809 p h) (sat_cons (step815 p h) (sat_cons (step799 p h) (sat_cons (step800 p h) (sat_cons (step889 p h) (sat_cons (step797 p h) (sat_cons (step798 p h) (sat_cons (step794 p h) (sat_cons (step1464 p h) (sat_cons (step69 p h) (sat_nil p))))))))))))))))))))))
def c1486 : List Lit := [(1250, true), (28, true)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1476, c1482, c838, c836, c835, c1332, c827, c1477, c833, c816, c1485, c1059, c1479, c1067, c819, c889, c1062, c799, c800, c797, c798, c794, c1464, c69] c1486 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1476 p h) (sat_cons (step1482 p h) (sat_cons (step838 p h) (sat_cons (step836 p h) (sat_cons (step835 p h) (sat_cons (step1332 p h) (sat_cons (step827 p h) (sat_cons (step1477 p h) (sat_cons (step833 p h) (sat_cons (step816 p h) (sat_cons (step1485 p h) (sat_cons (step1059 p h) (sat_cons (step1479 p h) (sat_cons (step1067 p h) (sat_cons (step819 p h) (sat_cons (step889 p h) (sat_cons (step1062 p h) (sat_cons (step799 p h) (sat_cons (step800 p h) (sat_cons (step797 p h) (sat_cons (step798 p h) (sat_cons (step794 p h) (sat_cons (step1464 p h) (sat_cons (step69 p h) (sat_nil p))))))))))))))))))))))))))
def c1487 : List Lit := [(29, false), (37, false), (21, false)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c1484, c71, c70, c68, c798, c796, c803] c1487 (by decide) p (sat_cons (step1484 p h) (sat_cons (step71 p h) (sat_cons (step70 p h) (sat_cons (step68 p h) (sat_cons (step798 p h) (sat_cons (step796 p h) (sat_cons (step803 p h) (sat_nil p))))))))
def c1488 : List Lit := [(28, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1332, c1477, c1482, c838, c835, c1486, c892, c1373, c849, c834, c829, c1331, c1487] c1488 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1332 p h) (sat_cons (step1477 p h) (sat_cons (step1482 p h) (sat_cons (step838 p h) (sat_cons (step835 p h) (sat_cons (step1486 p h) (sat_cons (step892 p h) (sat_cons (step1373 p h) (sat_cons (step849 p h) (sat_cons (step834 p h) (sat_cons (step829 p h) (sat_cons (step1331 p h) (sat_cons (step1487 p h) (sat_nil p)))))))))))))))
def c1489 : List Lit := [(1236, false)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c1483, c1478, c1063, c810, c820, c1059, c1479] c1489 (by decide) p (sat_cons (step1483 p h) (sat_cons (step1478 p h) (sat_cons (step1063 p h) (sat_cons (step810 p h) (sat_cons (step820 p h) (sat_cons (step1059 p h) (sat_cons (step1479 p h) (sat_nil p))))))))
def c1490 : List Lit := [(1232, false)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c1489, c802] c1490 (by decide) p (sat_cons (step1489 p h) (sat_cons (step802 p h) (sat_nil p)))
def c1491 : List Lit := [(1298, true), (1264, false), (1259, false)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c838, c1373, c1474, c847, c833] c1491 (by decide) p (sat_cons (step838 p h) (sat_cons (step1373 p h) (sat_cons (step1474 p h) (sat_cons (step847 p h) (sat_cons (step833 p h) (sat_nil p))))))
def c1492 : List Lit := [(1233, false), (21, false)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c1489, c1488, c1476, c1481, c799, c801, c1062, c794, c795, c1015, c66, c828, c835, c1491, c892, c816, c819, c809, c1479, c1059] c1492 (by decide) p (sat_cons (step1489 p h) (sat_cons (step1488 p h) (sat_cons (step1476 p h) (sat_cons (step1481 p h) (sat_cons (step799 p h) (sat_cons (step801 p h) (sat_cons (step1062 p h) (sat_cons (step794 p h) (sat_cons (step795 p h) (sat_cons (step1015 p h) (sat_cons (step66 p h) (sat_cons (step828 p h) (sat_cons (step835 p h) (sat_cons (step1491 p h) (sat_cons (step892 p h) (sat_cons (step816 p h) (sat_cons (step819 p h) (sat_cons (step809 p h) (sat_cons (step1479 p h) (sat_cons (step1059 p h) (sat_nil p)))))))))))))))))))))
def c1493 : List Lit := [(1235, false), (1250, true)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c1481, c816, c1062, c809, c819, c1059, c1479] c1493 (by decide) p (sat_cons (step1481 p h) (sat_cons (step816 p h) (sat_cons (step1062 p h) (sat_cons (step809 p h) (sat_cons (step819 p h) (sat_cons (step1059 p h) (sat_cons (step1479 p h) (sat_nil p))))))))
def c1494 : List Lit := [(1231, true), (21, false)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c1492, c798, c794, c795, c65] c1494 (by decide) p (sat_cons (step1492 p h) (sat_cons (step798 p h) (sat_cons (step794 p h) (sat_cons (step795 p h) (sat_cons (step65 p h) (sat_nil p))))))
def c1495 : List Lit := [(37, true), (1298, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c1373, c1370, c835, c1491, c827, c1075] c1495 (by decide) p (sat_cons (step1373 p h) (sat_cons (step1370 p h) (sat_cons (step835 p h) (sat_cons (step1491 p h) (sat_cons (step827 p h) (sat_cons (step1075 p h) (sat_nil p)))))))
def c1496 : List Lit := [(37, false), (23, false), (21, false)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c1490, c69, c67, c796] c1496 (by decide) p (sat_cons (step1490 p h) (sat_cons (step69 p h) (sat_cons (step67 p h) (sat_cons (step796 p h) (sat_nil p)))))
def c1497 : List Lit := [(21, false)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1492, c798, c1494, c800, c1493, c892, c1495, c1496] c1497 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1492 p h) (sat_cons (step798 p h) (sat_cons (step1494 p h) (sat_cons (step800 p h) (sat_cons (step1493 p h) (sat_cons (step892 p h) (sat_cons (step1495 p h) (sat_cons (step1496 p h) (sat_nil p))))))))))
def c1498 : List Lit := [(720, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c1497, c533] c1498 (by decide) p (sat_cons (step1497 p h) (sat_cons (step533 p h) (sat_nil p)))
def c1499 : List Lit := [(723, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c1498, c535] c1499 (by decide) p (sat_cons (step1498 p h) (sat_cons (step535 p h) (sat_nil p)))
def c1500 : List Lit := [(729, true)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c1499, c542] c1500 (by decide) p (sat_cons (step1499 p h) (sat_cons (step542 p h) (sat_nil p)))
def c1501 : List Lit := [(20, true), (37, false)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.TreeRup.prove_clause [c1483, c1390, c1476, c1472, c1400, c1416, c1415, c1401, c1478, c1447, c1499, c1500, c1498, c794, c800, c1471, c812, c1493, c1060, c891, c892, c1209, c1386, c395, c1359, c1381, c993, c1473, c1363, c388, c390, c948, c1377, c937, c493, c384, c366, c931, c932, c448, c450, c381, c1406, c929, c930, c1346, c1344, c444, c419, c378, c379, c1348, c52, c1192, c200, c442, c443, c416, c376, c375, c1051, c1315, c648, c1432, c440, c437, c407, c1109, c776, c650, c518, c439, c435, c1217, c610, c779, c666, c513, c219, c1338, c820, c674, c150, c809, c1467, c1059, c227, c787, c788, c675, c1325, c680, c1436, c42, c683, c1353, c509, c695, c339, c512, c749, c327, c517, c1366, c325, c545, c624, c633, c323, c628, c546, c1165, c538, c836, c527, c1474, c526, c56] c1501 (by decide) p (sat_cons (step1483 p h) (sat_cons (step1390 p h) (sat_cons (step1476 p h) (sat_cons (step1472 p h) (sat_cons (step1400 p h) (sat_cons (step1416 p h) (sat_cons (step1415 p h) (sat_cons (step1401 p h) (sat_cons (step1478 p h) (sat_cons (step1447 p h) (sat_cons (step1499 p h) (sat_cons (step1500 p h) (sat_cons (step1498 p h) (sat_cons (step794 p h) (sat_cons (step800 p h) (sat_cons (step1471 p h) (sat_cons (step812 p h) (sat_cons (step1493 p h) (sat_cons (step1060 p h) (sat_cons (step891 p h) (sat_cons (step892 p h) (sat_cons (step1209 p h) (sat_cons (step1386 p h) (sat_cons (step395 p h) (sat_cons (step1359 p h) (sat_cons (step1381 p h) (sat_cons (step993 p h) (sat_cons (step1473 p h) (sat_cons (step1363 p h) (sat_cons (step388 p h) (sat_cons (step390 p h) (sat_cons (step948 p h) (sat_cons (step1377 p h) (sat_cons (step937 p h) (sat_cons (step493 p h) (sat_cons (step384 p h) (sat_cons (step366 p h) (sat_cons (step931 p h) (sat_cons (step932 p h) (sat_cons (step448 p h) (sat_cons (step450 p h) (sat_cons (step381 p h) (sat_cons (step1406 p h) (sat_cons (step929 p h) (sat_cons (step930 p h) (sat_cons (step1346 p h) (sat_cons (step1344 p h) (sat_cons (step444 p h) (sat_cons (step419 p h) (sat_cons (step378 p h) (sat_cons (step379 p h) (sat_cons (step1348 p h) (sat_cons (step52 p h) (sat_cons (step1192 p h) (sat_cons (step200 p h) (sat_cons (step442 p h) (sat_cons (step443 p h) (sat_cons (step416 p h) (sat_cons (step376 p h) (sat_cons (step375 p h) (sat_cons (step1051 p h) (sat_cons (step1315 p h) (sat_cons (step648 p h) (sat_cons (step1432 p h) (sat_cons (step440 p h) (sat_cons (step437 p h) (sat_cons (step407 p h) (sat_cons (step1109 p h) (sat_cons (step776 p h) (sat_cons (step650 p h) (sat_cons (step518 p h) (sat_cons (step439 p h) (sat_cons (step435 p h) (sat_cons (step1217 p h) (sat_cons (step610 p h) (sat_cons (step779 p h) (sat_cons (step666 p h) (sat_cons (step513 p h) (sat_cons (step219 p h) (sat_cons (step1338 p h) (sat_cons (step820 p h) (sat_cons (step674 p h) (sat_cons (step150 p h) (sat_cons (step809 p h) (sat_cons (step1467 p h) (sat_cons (step1059 p h) (sat_cons (step227 p h) (sat_cons (step787 p h) (sat_cons (step788 p h) (sat_cons (step675 p h) (sat_cons (step1325 p h) (sat_cons (step680 p h) (sat_cons (step1436 p h) (sat_cons (step42 p h) (sat_cons (step683 p h) (sat_cons (step1353 p h) (sat_cons (step509 p h) (sat_cons (step695 p h) (sat_cons (step339 p h) (sat_cons (step512 p h) (sat_cons (step749 p h) (sat_cons (step327 p h) (sat_cons (step517 p h) (sat_cons (step1366 p h) (sat_cons (step325 p h) (sat_cons (step545 p h) (sat_cons (step624 p h) (sat_cons (step633 p h) (sat_cons (step323 p h) (sat_cons (step628 p h) (sat_cons (step546 p h) (sat_cons (step1165 p h) (sat_cons (step538 p h) (sat_cons (step836 p h) (sat_cons (step527 p h) (sat_cons (step1474 p h) (sat_cons (step526 p h) (sat_cons (step56 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1502 : List Lit := [(1259, true), (20, false)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c1488, c827, c828, c87] c1502 (by decide) p (sat_cons (step1488 p h) (sat_cons (step827 p h) (sat_cons (step828 p h) (sat_cons (step87 p h) (sat_nil p)))))
def c1503 : List Lit := [(1249, true)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1067, c815, c1479, c808, c1059] c1503 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1067 p h) (sat_cons (step815 p h) (sat_cons (step1479 p h) (sat_cons (step808 p h) (sat_cons (step1059 p h) (sat_nil p)))))))
def c1504 : List Lit := [(1299, false)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c1503, c1476, c889] c1504 (by decide) p (sat_cons (step1503 p h) (sat_cons (step1476 p h) (sat_cons (step889 p h) (sat_nil p))))
def c1505 : List Lit := [(1278, false), (1262, false)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c1504, c846, c880, c871, c872, c882, c862, c863, c847, c860, c857, c838, c1335, c836, c145] c1505 (by decide) p (sat_cons (step1504 p h) (sat_cons (step846 p h) (sat_cons (step880 p h) (sat_cons (step871 p h) (sat_cons (step872 p h) (sat_cons (step882 p h) (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step847 p h) (sat_cons (step860 p h) (sat_cons (step857 p h) (sat_cons (step838 p h) (sat_cons (step1335 p h) (sat_cons (step836 p h) (sat_cons (step145 p h) (sat_nil p))))))))))))))))
def c1506 : List Lit := [(40, true), (1262, false)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c1504, c1505, c854, c846, c880, c851, c853, c870, c865, c856, c852, c1334, c118, c858, c859, c863, c864, c1335, c869, c860, c145, c882, c836, c847, c838] c1506 (by decide) p (sat_cons (step1504 p h) (sat_cons (step1505 p h) (sat_cons (step854 p h) (sat_cons (step846 p h) (sat_cons (step880 p h) (sat_cons (step851 p h) (sat_cons (step853 p h) (sat_cons (step870 p h) (sat_cons (step865 p h) (sat_cons (step856 p h) (sat_cons (step852 p h) (sat_cons (step1334 p h) (sat_cons (step118 p h) (sat_cons (step858 p h) (sat_cons (step859 p h) (sat_cons (step863 p h) (sat_cons (step864 p h) (sat_cons (step1335 p h) (sat_cons (step869 p h) (sat_cons (step860 p h) (sat_cons (step145 p h) (sat_cons (step882 p h) (sat_cons (step836 p h) (sat_cons (step847 p h) (sat_cons (step838 p h) (sat_nil p))))))))))))))))))))))))))
def c1507 : List Lit := [(1262, false), (37, false)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1501, c846, c1506, c110, c1333, c123, c125, c798, c860, c799, c1077, c1493, c879, c892] c1507 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1501 p h) (sat_cons (step846 p h) (sat_cons (step1506 p h) (sat_cons (step110 p h) (sat_cons (step1333 p h) (sat_cons (step123 p h) (sat_cons (step125 p h) (sat_cons (step798 p h) (sat_cons (step860 p h) (sat_cons (step799 p h) (sat_cons (step1077 p h) (sat_cons (step1493 p h) (sat_cons (step879 p h) (sat_cons (step892 p h) (sat_nil p))))))))))))))))
def c1508 : List Lit := [(37, false)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c1488, c1501, c1502, c1507, c831, c833, c85, c86, c829] c1508 (by decide) p (sat_cons (step1488 p h) (sat_cons (step1501 p h) (sat_cons (step1502 p h) (sat_cons (step1507 p h) (sat_cons (step831 p h) (sat_cons (step833 p h) (sat_cons (step85 p h) (sat_cons (step86 p h) (sat_cons (step829 p h) (sat_nil p))))))))))
def c1509 : List Lit := [(1298, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c1508, c1495] c1509 (by decide) p (sat_cons (step1508 p h) (sat_cons (step1495 p h) (sat_nil p)))
def c1510 : List Lit := [(1250, false)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c1509, c1476, c892] c1510 (by decide) p (sat_cons (step1509 p h) (sat_cons (step1476 p h) (sat_cons (step892 p h) (sat_nil p))))
def c1511 : List Lit := [(1315, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c1509, c1503, c888] c1511 (by decide) p (sat_cons (step1509 p h) (sat_cons (step1503 p h) (sat_cons (step888 p h) (sat_nil p))))
def c1512 : List Lit := [(1241, false)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c1510, c1481, c816] c1512 (by decide) p (sat_cons (step1510 p h) (sat_cons (step1481 p h) (sat_cons (step816 p h) (sat_nil p))))
def c1513 : List Lit := [(1427, false)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c1511, c1386] c1513 (by decide) p (sat_cons (step1511 p h) (sat_cons (step1386 p h) (sat_nil p)))
def c1514 : List Lit := [(1230, false)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c1512, c811] c1514 (by decide) p (sat_cons (step1512 p h) (sat_cons (step811 p h) (sat_nil p)))
def c1515 : List Lit := [(1350, false)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1473] c1515 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1473 p h) (sat_nil p)))
def c1516 : List Lit := [(1227, false)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c1514, c1060] c1516 (by decide) p (sat_cons (step1514 p h) (sat_cons (step1060 p h) (sat_nil p)))
def c1517 : List Lit := [(1339, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c1515, c937] c1517 (by decide) p (sat_cons (step1515 p h) (sat_cons (step937 p h) (sat_nil p)))
def c1518 : List Lit := [(1337, false)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c1517, c931] c1518 (by decide) p (sat_cons (step1517 p h) (sat_cons (step931 p h) (sat_nil p)))
def c1519 : List Lit := [(63, true)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c1517, c932] c1519 (by decide) p (sat_cons (step1517 p h) (sat_cons (step932 p h) (sat_nil p)))
def c1520 : List Lit := [(68, true)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c1518, c929] c1520 (by decide) p (sat_cons (step1518 p h) (sat_cons (step929 p h) (sat_nil p)))
def c1521 : List Lit := [(65, true)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c1518, c930] c1521 (by decide) p (sat_cons (step1518 p h) (sat_cons (step930 p h) (sat_nil p)))
def c1522 : List Lit := [(4, true)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1400, c1346] c1522 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1400 p h) (sat_cons (step1346 p h) (sat_nil p))))
def c1523 : List Lit := [(64, true)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1400, c1344] c1523 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1400 p h) (sat_cons (step1344 p h) (sat_nil p))))
def c1524 : List Lit := [(17, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c1520, c1348] c1524 (by decide) p (sat_cons (step1520 p h) (sat_cons (step1348 p h) (sat_nil p)))
def c1525 : List Lit := [(7, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1415, c1416, c205] c1525 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1415 p h) (sat_cons (step1416 p h) (sat_cons (step205 p h) (sat_nil p)))))
def c1526 : List Lit := [(1, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1522, c1478, c1525, c1192] c1526 (by decide) p (sat_cons (step1522 p h) (sat_cons (step1478 p h) (sat_cons (step1525 p h) (sat_cons (step1192 p h) (sat_nil p)))))
def c1527 : List Lit := [(56, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c1523, c1416, c1521, c200] c1527 (by decide) p (sat_cons (step1523 p h) (sat_cons (step1416 p h) (sat_cons (step1521 p h) (sat_cons (step200 p h) (sat_nil p)))))
def c1528 : List Lit := [(255, true)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1516, c1209] c1528 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1516 p h) (sat_cons (step1209 p h) (sat_nil p))))
def c1529 : List Lit := [(10, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1526, c1527, c1315] c1529 (by decide) p (sat_cons (step1526 p h) (sat_cons (step1527 p h) (sat_cons (step1315 p h) (sat_nil p))))
def c1530 : List Lit := [(307, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c1528, c395] c1530 (by decide) p (sat_cons (step1528 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1531 : List Lit := [(409, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c1530, c1363] c1531 (by decide) p (sat_cons (step1530 p h) (sat_cons (step1363 p h) (sat_nil p)))
def c1532 : List Lit := [(357, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c1531, c493] c1532 (by decide) p (sat_cons (step1531 p h) (sat_cons (step493 p h) (sat_nil p)))
end B112E174
