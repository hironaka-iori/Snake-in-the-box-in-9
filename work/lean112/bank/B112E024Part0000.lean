import B112E024Inputs
namespace B112E024
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1362 : List Lit := [(2, true)]
theorem step1362 (p : Nat → Bool) (h : Constraints p) : clause p c1362 = true :=
  Snake9.LocalRup.prove_clause [c19, c18] c1362 (by decide) p (sat_cons (step19 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1363 : List Lit := [(10, false), (34, false), (68, false)]
theorem step1363 (p : Nat → Bool) (h : Constraints p) : clause p c1363 = true :=
  Snake9.LocalRup.prove_clause [c1362, c29] c1363 (by decide) p (sat_cons (step1362 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1364 : List Lit := [(77, false)]
theorem step1364 (p : Nat → Bool) (h : Constraints p) : clause p c1364 = true :=
  Snake9.LocalRup.prove_clause [c613, c308] c1364 (by decide) p (sat_cons (step613 p h) (sat_cons (step308 p h) (sat_nil p)))
def c1365 : List Lit := [(478, false)]
theorem step1365 (p : Nat → Bool) (h : Constraints p) : clause p c1365 = true :=
  Snake9.LocalRup.prove_clause [c783, c780] c1365 (by decide) p (sat_cons (step783 p h) (sat_cons (step780 p h) (sat_nil p)))
def c1366 : List Lit := [(360, false)]
theorem step1366 (p : Nat → Bool) (h : Constraints p) : clause p c1366 = true :=
  Snake9.LocalRup.prove_clause [c783, c782] c1366 (by decide) p (sat_cons (step783 p h) (sat_cons (step782 p h) (sat_nil p)))
def c1367 : List Lit := [(476, false)]
theorem step1367 (p : Nat → Bool) (h : Constraints p) : clause p c1367 = true :=
  Snake9.LocalRup.prove_clause [c1365, c776] c1367 (by decide) p (sat_cons (step1365 p h) (sat_cons (step776 p h) (sat_nil p)))
def c1368 : List Lit := [(418, false)]
theorem step1368 (p : Nat → Bool) (h : Constraints p) : clause p c1368 = true :=
  Snake9.LocalRup.prove_clause [c1365, c779] c1368 (by decide) p (sat_cons (step1365 p h) (sat_cons (step779 p h) (sat_nil p)))
def c1369 : List Lit := [(358, false)]
theorem step1369 (p : Nat → Bool) (h : Constraints p) : clause p c1369 = true :=
  Snake9.LocalRup.prove_clause [c1366, c704] c1369 (by decide) p (sat_cons (step1366 p h) (sat_cons (step704 p h) (sat_nil p)))
def c1370 : List Lit := [(300, false)]
theorem step1370 (p : Nat → Bool) (h : Constraints p) : clause p c1370 = true :=
  Snake9.LocalRup.prove_clause [c1366, c707] c1370 (by decide) p (sat_cons (step1366 p h) (sat_cons (step707 p h) (sat_nil p)))
def c1371 : List Lit := [(446, false)]
theorem step1371 (p : Nat → Bool) (h : Constraints p) : clause p c1371 = true :=
  Snake9.LocalRup.prove_clause [c1367, c774] c1371 (by decide) p (sat_cons (step1367 p h) (sat_cons (step774 p h) (sat_nil p)))
def c1372 : List Lit := [(416, false)]
theorem step1372 (p : Nat → Bool) (h : Constraints p) : clause p c1372 = true :=
  Snake9.LocalRup.prove_clause [c1368, c743] c1372 (by decide) p (sat_cons (step1368 p h) (sat_cons (step743 p h) (sat_nil p)))
def c1373 : List Lit := [(388, false)]
theorem step1373 (p : Nat → Bool) (h : Constraints p) : clause p c1373 = true :=
  Snake9.LocalRup.prove_clause [c1368, c746] c1373 (by decide) p (sat_cons (step1368 p h) (sat_cons (step746 p h) (sat_nil p)))
def c1374 : List Lit := [(356, false)]
theorem step1374 (p : Nat → Bool) (h : Constraints p) : clause p c1374 = true :=
  Snake9.LocalRup.prove_clause [c1369, c700] c1374 (by decide) p (sat_cons (step1369 p h) (sat_cons (step700 p h) (sat_nil p)))
def c1375 : List Lit := [(298, false)]
theorem step1375 (p : Nat → Bool) (h : Constraints p) : clause p c1375 = true :=
  Snake9.LocalRup.prove_clause [c1370, c668] c1375 (by decide) p (sat_cons (step1370 p h) (sat_cons (step668 p h) (sat_nil p)))
def c1376 : List Lit := [(386, false)]
theorem step1376 (p : Nat → Bool) (h : Constraints p) : clause p c1376 = true :=
  Snake9.LocalRup.prove_clause [c1373, c725] c1376 (by decide) p (sat_cons (step1373 p h) (sat_cons (step725 p h) (sat_nil p)))
def c1377 : List Lit := [(340, false)]
theorem step1377 (p : Nat → Bool) (h : Constraints p) : clause p c1377 = true :=
  Snake9.LocalRup.prove_clause [c1374, c698] c1377 (by decide) p (sat_cons (step1374 p h) (sat_cons (step698 p h) (sat_nil p)))
def c1378 : List Lit := [(296, false)]
theorem step1378 (p : Nat → Bool) (h : Constraints p) : clause p c1378 = true :=
  Snake9.LocalRup.prove_clause [c1375, c664] c1378 (by decide) p (sat_cons (step1375 p h) (sat_cons (step664 p h) (sat_nil p)))
def c1379 : List Lit := [(384, false)]
theorem step1379 (p : Nat → Bool) (h : Constraints p) : clause p c1379 = true :=
  Snake9.LocalRup.prove_clause [c1376, c723] c1379 (by decide) p (sat_cons (step1376 p h) (sat_cons (step723 p h) (sat_nil p)))
def c1380 : List Lit := [(294, false)]
theorem step1380 (p : Nat → Bool) (h : Constraints p) : clause p c1380 = true :=
  Snake9.LocalRup.prove_clause [c1378, c661] c1380 (by decide) p (sat_cons (step1378 p h) (sat_cons (step661 p h) (sat_nil p)))
def c1381 : List Lit := [(1615, true)]
theorem step1381 (p : Nat → Bool) (h : Constraints p) : clause p c1381 = true :=
  Snake9.LocalRup.prove_clause [c1364, c1079] c1381 (by decide) p (sat_cons (step1364 p h) (sat_cons (step1079 p h) (sat_nil p)))
def c1382 : List Lit := [(79, true), (1616, true)]
theorem step1382 (p : Nat → Bool) (h : Constraints p) : clause p c1382 = true :=
  Snake9.LocalRup.prove_clause [c1364, c1080] c1382 (by decide) p (sat_cons (step1364 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c1383 : List Lit := [(1617, true)]
theorem step1383 (p : Nat → Bool) (h : Constraints p) : clause p c1383 = true :=
  Snake9.LocalRup.prove_clause [c1381, c1081] c1383 (by decide) p (sat_cons (step1381 p h) (sat_cons (step1081 p h) (sat_nil p)))
def c1384 : List Lit := [(1613, false), (1618, true)]
theorem step1384 (p : Nat → Bool) (h : Constraints p) : clause p c1384 = true :=
  Snake9.LocalRup.prove_clause [c1381, c1083] c1384 (by decide) p (sat_cons (step1381 p h) (sat_cons (step1083 p h) (sat_nil p)))
def c1385 : List Lit := [(1614, false), (1619, true)]
theorem step1385 (p : Nat → Bool) (h : Constraints p) : clause p c1385 = true :=
  Snake9.LocalRup.prove_clause [c1381, c1085] c1385 (by decide) p (sat_cons (step1381 p h) (sat_cons (step1085 p h) (sat_nil p)))
def c1386 : List Lit := [(1629, true)]
theorem step1386 (p : Nat → Bool) (h : Constraints p) : clause p c1386 = true :=
  Snake9.LocalRup.prove_clause [c1383, c1101] c1386 (by decide) p (sat_cons (step1383 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c1387 : List Lit := [(1625, false), (1630, true)]
theorem step1387 (p : Nat → Bool) (h : Constraints p) : clause p c1387 = true :=
  Snake9.LocalRup.prove_clause [c1383, c1102] c1387 (by decide) p (sat_cons (step1383 p h) (sat_cons (step1102 p h) (sat_nil p)))
def c1388 : List Lit := [(1626, false), (1631, true)]
theorem step1388 (p : Nat → Bool) (h : Constraints p) : clause p c1388 = true :=
  Snake9.LocalRup.prove_clause [c1383, c1103] c1388 (by decide) p (sat_cons (step1383 p h) (sat_cons (step1103 p h) (sat_nil p)))
def c1389 : List Lit := [(1627, false), (1632, true)]
theorem step1389 (p : Nat → Bool) (h : Constraints p) : clause p c1389 = true :=
  Snake9.LocalRup.prove_clause [c1383, c1104] c1389 (by decide) p (sat_cons (step1383 p h) (sat_cons (step1104 p h) (sat_nil p)))
def c1390 : List Lit := [(1628, false), (1633, true)]
theorem step1390 (p : Nat → Bool) (h : Constraints p) : clause p c1390 = true :=
  Snake9.LocalRup.prove_clause [c1383, c1105] c1390 (by decide) p (sat_cons (step1383 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c1391 : List Lit := [(1637, true)]
theorem step1391 (p : Nat → Bool) (h : Constraints p) : clause p c1391 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1116] c1391 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1116 p h) (sat_nil p)))
def c1392 : List Lit := [(1605, false), (1638, true)]
theorem step1392 (p : Nat → Bool) (h : Constraints p) : clause p c1392 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1122] c1392 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1122 p h) (sat_nil p)))
def c1393 : List Lit := [(1606, false), (1639, true)]
theorem step1393 (p : Nat → Bool) (h : Constraints p) : clause p c1393 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1128] c1393 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1128 p h) (sat_nil p)))
def c1394 : List Lit := [(1607, false), (1640, true)]
theorem step1394 (p : Nat → Bool) (h : Constraints p) : clause p c1394 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1134] c1394 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c1395 : List Lit := [(1708, false), (1725, true)]
theorem step1395 (p : Nat → Bool) (h : Constraints p) : clause p c1395 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1261] c1395 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c1396 : List Lit := [(1456, true)]
theorem step1396 (p : Nat → Bool) (h : Constraints p) : clause p c1396 = true :=
  Snake9.LocalRup.prove_clause [c580, c802, c806, c794, c785, c786, c791, c784, c31, c12] c1396 (by decide) p (sat_cons (step580 p h) (sat_cons (step802 p h) (sat_cons (step806 p h) (sat_cons (step794 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step791 p h) (sat_cons (step784 p h) (sat_cons (step31 p h) (sat_cons (step12 p h) (sat_nil p)))))))))))
def c1397 : List Lit := [(1479, true)]
theorem step1397 (p : Nat → Bool) (h : Constraints p) : clause p c1397 = true :=
  Snake9.LocalRup.prove_clause [c587, c843, c847, c835, c837, c821, c823, c832, c833, c829, c818, c815, c816, c132, c124, c79, c140] c1397 (by decide) p (sat_cons (step587 p h) (sat_cons (step843 p h) (sat_cons (step847 p h) (sat_cons (step835 p h) (sat_cons (step837 p h) (sat_cons (step821 p h) (sat_cons (step823 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step829 p h) (sat_cons (step818 p h) (sat_cons (step815 p h) (sat_cons (step816 p h) (sat_cons (step132 p h) (sat_cons (step124 p h) (sat_cons (step79 p h) (sat_cons (step140 p h) (sat_nil p))))))))))))))))))
def c1398 : List Lit := [(3, false), (1453, true)]
theorem step1398 (p : Nat → Bool) (h : Constraints p) : clause p c1398 = true :=
  Snake9.LocalRup.prove_clause [c1362, c19, c4, c5, c789, c792, c797] c1398 (by decide) p (sat_cons (step1362 p h) (sat_cons (step19 p h) (sat_cons (step4 p h) (sat_cons (step5 p h) (sat_cons (step789 p h) (sat_cons (step792 p h) (sat_cons (step797 p h) (sat_nil p))))))))
def c1399 : List Lit := [(1457, true)]
theorem step1399 (p : Nat → Bool) (h : Constraints p) : clause p c1399 = true :=
  Snake9.LocalRup.prove_clause [c580, c803, c811, c1398, c784, c785, c787, c807, c794, c791, c30, c31, c1318] c1399 (by decide) p (sat_cons (step580 p h) (sat_cons (step803 p h) (sat_cons (step811 p h) (sat_cons (step1398 p h) (sat_cons (step784 p h) (sat_cons (step785 p h) (sat_cons (step787 p h) (sat_cons (step807 p h) (sat_cons (step794 p h) (sat_cons (step791 p h) (sat_cons (step30 p h) (sat_cons (step31 p h) (sat_cons (step1318 p h) (sat_nil p))))))))))))))
def c1400 : List Lit := [(1489, true)]
theorem step1400 (p : Nat → Bool) (h : Constraints p) : clause p c1400 = true :=
  Snake9.LocalRup.prove_clause [c1399, c1397, c864] c1400 (by decide) p (sat_cons (step1399 p h) (sat_cons (step1397 p h) (sat_cons (step864 p h) (sat_nil p))))
def c1401 : List Lit := [(1510, true), (1530, true)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true :=
  Snake9.LocalRup.prove_clause [c595, c596, c592, c932, c925, c211, c924, c930, c928, c897, c898, c218, c213, c222, c188, c189, c1338] c1401 (by decide) p (sat_cons (step595 p h) (sat_cons (step596 p h) (sat_cons (step592 p h) (sat_cons (step932 p h) (sat_cons (step925 p h) (sat_cons (step211 p h) (sat_cons (step924 p h) (sat_cons (step930 p h) (sat_cons (step928 p h) (sat_cons (step897 p h) (sat_cons (step898 p h) (sat_cons (step218 p h) (sat_cons (step213 p h) (sat_cons (step222 p h) (sat_cons (step188 p h) (sat_cons (step189 p h) (sat_cons (step1338 p h) (sat_nil p))))))))))))))))))
def c1402 : List Lit := [(40, false), (38, true), (46, true), (39, true), (161, true)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c592, c204, c205, c1338, c189] c1402 (by decide) p (sat_cons (step592 p h) (sat_cons (step204 p h) (sat_cons (step205 p h) (sat_cons (step1338 p h) (sat_cons (step189 p h) (sat_nil p))))))
def c1403 : List Lit := [(1481, true), (1465, false), (1471, false), (17, false), (36, false)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c821, c837, c853, c849, c824, c838, c815, c832, c91] c1403 (by decide) p (sat_cons (step821 p h) (sat_cons (step837 p h) (sat_cons (step853 p h) (sat_cons (step849 p h) (sat_cons (step824 p h) (sat_cons (step838 p h) (sat_cons (step815 p h) (sat_cons (step832 p h) (sat_cons (step91 p h) (sat_nil p))))))))))
def c1404 : List Lit := [(13, true), (1481, true), (1465, false), (22, false), (17, true)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c588, c857, c827, c816, c817, c824, c853, c835, c832, c131, c144] c1404 (by decide) p (sat_cons (step588 p h) (sat_cons (step857 p h) (sat_cons (step827 p h) (sat_cons (step816 p h) (sat_cons (step817 p h) (sat_cons (step824 p h) (sat_cons (step853 p h) (sat_cons (step835 p h) (sat_cons (step832 p h) (sat_cons (step131 p h) (sat_cons (step144 p h) (sat_nil p))))))))))))
def c1405 : List Lit := [(35, false), (34, true), (13, false), (20, false)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c591, c186, c87] c1405 (by decide) p (sat_cons (step591 p h) (sat_cons (step186 p h) (sat_cons (step87 p h) (sat_nil p))))
def c1406 : List Lit := [(1473, true), (22, false), (17, true)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c588, c832, c833, c144, c133] c1406 (by decide) p (sat_cons (step588 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step144 p h) (sat_cons (step133 p h) (sat_nil p))))))
def c1407 : List Lit := [(1689, true), (46, true)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c629, c1214, c1216, c1211, c1212, c1208, c1209, c576, c556, c572] c1407 (by decide) p (sat_cons (step629 p h) (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1211 p h) (sat_cons (step1212 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step576 p h) (sat_cons (step556 p h) (sat_cons (step572 p h) (sat_nil p)))))))))))
def c1408 : List Lit := [(19, false), (1689, false), (1657, false), (1704, true), (90, false), (55, false)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c433, c434, c1162, c1199, c1164, c1201, c1176, c1220, c1236] c1408 (by decide) p (sat_cons (step433 p h) (sat_cons (step434 p h) (sat_cons (step1162 p h) (sat_cons (step1199 p h) (sat_cons (step1164 p h) (sat_cons (step1201 p h) (sat_cons (step1176 p h) (sat_cons (step1220 p h) (sat_cons (step1236 p h) (sat_nil p))))))))))
def c1409 : List Lit := [(1689, true), (1704, true), (90, false), (55, false)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c627, c630, c629, c1245, c1214, c1216, c1211, c1212, c1208, c1209, c576, c556, c558, c559, c575, c571, c1356, c566, c513, c1149, c1162, c1151, c1164, c1186, c1181, c1154, c1240, c1144, c1219, c443, c1201, c1199] c1409 (by decide) p (sat_cons (step627 p h) (sat_cons (step630 p h) (sat_cons (step629 p h) (sat_cons (step1245 p h) (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1211 p h) (sat_cons (step1212 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step576 p h) (sat_cons (step556 p h) (sat_cons (step558 p h) (sat_cons (step559 p h) (sat_cons (step575 p h) (sat_cons (step571 p h) (sat_cons (step1356 p h) (sat_cons (step566 p h) (sat_cons (step513 p h) (sat_cons (step1149 p h) (sat_cons (step1162 p h) (sat_cons (step1151 p h) (sat_cons (step1164 p h) (sat_cons (step1186 p h) (sat_cons (step1181 p h) (sat_cons (step1154 p h) (sat_cons (step1240 p h) (sat_cons (step1144 p h) (sat_cons (step1219 p h) (sat_cons (step443 p h) (sat_cons (step1201 p h) (sat_cons (step1199 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1410 : List Lit := [(117, false), (1687, true), (96, false)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c630, c1212, c1211, c576, c566, c575] c1410 (by decide) p (sat_cons (step630 p h) (sat_cons (step1212 p h) (sat_cons (step1211 p h) (sat_cons (step576 p h) (sat_cons (step566 p h) (sat_cons (step575 p h) (sat_nil p)))))))
def c1411 : List Lit := [(114, true), (115, false), (94, false)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c627, c558, c559, c1356] c1411 (by decide) p (sat_cons (step627 p h) (sat_cons (step558 p h) (sat_cons (step559 p h) (sat_cons (step1356 p h) (sat_nil p)))))
def c1412 : List Lit := [(98, false), (95, true), (1657, true), (90, false)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c619, c1152, c1144, c1150, c1148, c1147, c490, c496, c493, c460] c1412 (by decide) p (sat_cons (step619 p h) (sat_cons (step1152 p h) (sat_cons (step1144 p h) (sat_cons (step1150 p h) (sat_cons (step1148 p h) (sat_cons (step1147 p h) (sat_cons (step490 p h) (sat_cons (step496 p h) (sat_cons (step493 p h) (sat_cons (step460 p h) (sat_nil p)))))))))))
def c1413 : List Lit := [(1683, true), (87, true), (108, true), (110, true), (93, false)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c623, c1195, c1199, c1207, c1205, c1197, c1200, c550, c533] c1413 (by decide) p (sat_cons (step623 p h) (sat_cons (step1195 p h) (sat_cons (step1199 p h) (sat_cons (step1207 p h) (sat_cons (step1205 p h) (sat_cons (step1197 p h) (sat_cons (step1200 p h) (sat_cons (step550 p h) (sat_cons (step533 p h) (sat_nil p))))))))))
def c1414 : List Lit := [(1515, true), (41, true)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c593, c900, c904, c906, c902, c897, c898, c197, c201] c1414 (by decide) p (sat_cons (step593 p h) (sat_cons (step900 p h) (sat_cons (step904 p h) (sat_cons (step906 p h) (sat_cons (step902 p h) (sat_cons (step897 p h) (sat_cons (step898 p h) (sat_cons (step197 p h) (sat_cons (step201 p h) (sat_nil p))))))))))
def c1415 : List Lit := [(1544, true), (1526, false), (54, true), (57, true)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c602, c932, c938, c946, c962, c958, c933, c949, c947, c927, c940, c941, c237, c257] c1415 (by decide) p (sat_cons (step602 p h) (sat_cons (step932 p h) (sat_cons (step938 p h) (sat_cons (step946 p h) (sat_cons (step962 p h) (sat_cons (step958 p h) (sat_cons (step933 p h) (sat_cons (step949 p h) (sat_cons (step947 p h) (sat_cons (step927 p h) (sat_cons (step940 p h) (sat_cons (step941 p h) (sat_cons (step237 p h) (sat_cons (step257 p h) (sat_nil p)))))))))))))))
def c1416 : List Lit := [(86, false), (1657, true)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c617, c1152, c1145, c1144, c1150, c1147, c349, c454, c450] c1416 (by decide) p (sat_cons (step617 p h) (sat_cons (step1152 p h) (sat_cons (step1145 p h) (sat_cons (step1144 p h) (sat_cons (step1150 p h) (sat_cons (step1147 p h) (sat_cons (step349 p h) (sat_cons (step454 p h) (sat_cons (step450 p h) (sat_nil p))))))))))
def c1417 : List Lit := [(85, false), (1657, true)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c618, c1152, c1145, c1150, c1148, c1147, c348, c487, c486] c1417 (by decide) p (sat_cons (step618 p h) (sat_cons (step1152 p h) (sat_cons (step1145 p h) (sat_cons (step1150 p h) (sat_cons (step1148 p h) (sat_cons (step1147 p h) (sat_cons (step348 p h) (sat_cons (step487 p h) (sat_cons (step486 p h) (sat_nil p))))))))))
def c1418 : List Lit := [(1593, true), (94, false)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c603, c1048, c1049, c1046, c1042, c1043, c269, c267, c263] c1418 (by decide) p (sat_cons (step603 p h) (sat_cons (step1048 p h) (sat_cons (step1049 p h) (sat_cons (step1046 p h) (sat_cons (step1042 p h) (sat_cons (step1043 p h) (sat_cons (step269 p h) (sat_cons (step267 p h) (sat_cons (step263 p h) (sat_nil p))))))))))
def c1419 : List Lit := [(1618, true), (1598, true), (71, false), (55, false)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c612, c1082, c1384, c1382, c1076, c1077, c292, c307, c1055, c304] c1419 (by decide) p (sat_cons (step612 p h) (sat_cons (step1082 p h) (sat_cons (step1384 p h) (sat_cons (step1382 p h) (sat_cons (step1076 p h) (sat_cons (step1077 p h) (sat_cons (step292 p h) (sat_cons (step307 p h) (sat_cons (step1055 p h) (sat_cons (step304 p h) (sat_nil p)))))))))))
def c1420 : List Lit := [(1601, true), (71, false), (55, false)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c1059, c1061, c1057, c1054, c291] c1420 (by decide) p (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1057 p h) (sat_cons (step1054 p h) (sat_cons (step291 p h) (sat_nil p))))))
def c1421 : List Lit := [(24, false), (1474, true), (14, false), (22, false)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c130, c131, c834] c1421 (by decide) p (sat_cons (step130 p h) (sat_cons (step131 p h) (sat_cons (step834 p h) (sat_nil p))))
def c1422 : List Lit := [(1543, true), (1526, false)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c602, c932, c961, c957, c933, c944, c946, c927, c941, c942, c939, c258, c237, c257] c1422 (by decide) p (sat_cons (step602 p h) (sat_cons (step932 p h) (sat_cons (step961 p h) (sat_cons (step957 p h) (sat_cons (step933 p h) (sat_cons (step944 p h) (sat_cons (step946 p h) (sat_cons (step927 p h) (sat_cons (step941 p h) (sat_cons (step942 p h) (sat_cons (step939 p h) (sat_cons (step258 p h) (sat_cons (step237 p h) (sat_cons (step257 p h) (sat_nil p)))))))))))))))
def c1423 : List Lit := [(1681, true)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c626, c1201, c1203, c1198, c1199, c1195, c1196, c541, c552, c548] c1423 (by decide) p (sat_cons (step626 p h) (sat_cons (step1201 p h) (sat_cons (step1203 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step1195 p h) (sat_cons (step1196 p h) (sat_cons (step541 p h) (sat_cons (step552 p h) (sat_cons (step548 p h) (sat_nil p)))))))))))
def c1424 : List Lit := [(1693, true)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c1423, c1219] c1424 (by decide) p (sat_cons (step1423 p h) (sat_cons (step1219 p h) (sat_nil p)))
def c1425 : List Lit := [(1701, true)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1228] c1425 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1228 p h) (sat_nil p)))
end B112E024
