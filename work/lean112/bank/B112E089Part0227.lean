import B112E089Part0226
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c16540 : List Lit := [(27, false), (103, true), (1784, true), (1661, false), (61, false)]
theorem step16540 (p : Nat → Bool) (h : Constraints p) : clause p c16540 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13745, c13803, c4118, c1610, c9483, c1640] c16540 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13745 p h) (sat_cons (step13803 p h) (sat_cons (step4118 p h) (sat_cons (step1610 p h) (sat_cons (step9483 p h) (sat_cons (step1640 p h) (sat_nil p))))))))
def c16541 : List Lit := [(489, true), (1568, false), (1605, false), (1784, true), (49, false), (73, false), (1598, true)]
theorem step16541 (p : Nat → Bool) (h : Constraints p) : clause p c16541 = true :=
  Snake9.LocalRup.prove_clause [c15726, c15724, c16286, c1534, c1447, c1434, c1478, c13848, c1609, c16504, c16520, c16233, c1635, c6481, c1726, c1722, c1899, c16424, c16526, c14692, c1294, c16531, c2382, c1576, c1526, c1446, c1433, c14633, c1430, c13762] c16541 (by decide) p (sat_cons (step15726 p h) (sat_cons (step15724 p h) (sat_cons (step16286 p h) (sat_cons (step1534 p h) (sat_cons (step1447 p h) (sat_cons (step1434 p h) (sat_cons (step1478 p h) (sat_cons (step13848 p h) (sat_cons (step1609 p h) (sat_cons (step16504 p h) (sat_cons (step16520 p h) (sat_cons (step16233 p h) (sat_cons (step1635 p h) (sat_cons (step6481 p h) (sat_cons (step1726 p h) (sat_cons (step1722 p h) (sat_cons (step1899 p h) (sat_cons (step16424 p h) (sat_cons (step16526 p h) (sat_cons (step14692 p h) (sat_cons (step1294 p h) (sat_cons (step16531 p h) (sat_cons (step2382 p h) (sat_cons (step1576 p h) (sat_cons (step1526 p h) (sat_cons (step1446 p h) (sat_cons (step1433 p h) (sat_cons (step14633 p h) (sat_cons (step1430 p h) (sat_cons (step13762 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c16542 : List Lit := [(1568, false), (51, true), (1784, true), (49, false), (73, false), (1598, true)]
theorem step16542 (p : Nat → Bool) (h : Constraints p) : clause p c16542 = true :=
  Snake9.LocalRup.prove_clause [c1478, c16504, c16520, c16233, c16539, c16540, c1357, c5198, c1498, c16526, c16424, c16286, c1445, c1520, c1508, c16541, c2361, c1160, c1162, c1157, c1090, c16535, c16325, c1121, c1123, c333, c335, c5279, c1116, c1099, c1100, c1461, c1466, c1503, c1112, c1098, c1094, c1474, c1527, c1109, c1097, c1093, c1463, c1450, c2074, c3387, c189, c1430, c16528, c13762] c16542 (by decide) p (sat_cons (step1478 p h) (sat_cons (step16504 p h) (sat_cons (step16520 p h) (sat_cons (step16233 p h) (sat_cons (step16539 p h) (sat_cons (step16540 p h) (sat_cons (step1357 p h) (sat_cons (step5198 p h) (sat_cons (step1498 p h) (sat_cons (step16526 p h) (sat_cons (step16424 p h) (sat_cons (step16286 p h) (sat_cons (step1445 p h) (sat_cons (step1520 p h) (sat_cons (step1508 p h) (sat_cons (step16541 p h) (sat_cons (step2361 p h) (sat_cons (step1160 p h) (sat_cons (step1162 p h) (sat_cons (step1157 p h) (sat_cons (step1090 p h) (sat_cons (step16535 p h) (sat_cons (step16325 p h) (sat_cons (step1121 p h) (sat_cons (step1123 p h) (sat_cons (step333 p h) (sat_cons (step335 p h) (sat_cons (step5279 p h) (sat_cons (step1116 p h) (sat_cons (step1099 p h) (sat_cons (step1100 p h) (sat_cons (step1461 p h) (sat_cons (step1466 p h) (sat_cons (step1503 p h) (sat_cons (step1112 p h) (sat_cons (step1098 p h) (sat_cons (step1094 p h) (sat_cons (step1474 p h) (sat_cons (step1527 p h) (sat_cons (step1109 p h) (sat_cons (step1097 p h) (sat_cons (step1093 p h) (sat_cons (step1463 p h) (sat_cons (step1450 p h) (sat_cons (step2074 p h) (sat_cons (step3387 p h) (sat_cons (step189 p h) (sat_cons (step1430 p h) (sat_cons (step16528 p h) (sat_cons (step13762 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c16543 : List Lit := [(115, false), (1594, false), (103, true), (1784, true), (1661, false), (1598, true)]
theorem step16543 (p : Nat → Bool) (h : Constraints p) : clause p c16543 = true :=
  Snake9.LocalRup.prove_clause [c15724, c15726, c16286, c1503, c1527, c1442, c16424, c1478, c13755, c13762, c1610, c1430, c1640, c1433, c1436, c9483, c1441, c1428, c2152, c3025, c1520, c1797, c1504, c1483, c1475, c16170, c514, c1613, c7243, c1645, c15884, c1738, c2556, c1913] c16543 (by decide) p (sat_cons (step15724 p h) (sat_cons (step15726 p h) (sat_cons (step16286 p h) (sat_cons (step1503 p h) (sat_cons (step1527 p h) (sat_cons (step1442 p h) (sat_cons (step16424 p h) (sat_cons (step1478 p h) (sat_cons (step13755 p h) (sat_cons (step13762 p h) (sat_cons (step1610 p h) (sat_cons (step1430 p h) (sat_cons (step1640 p h) (sat_cons (step1433 p h) (sat_cons (step1436 p h) (sat_cons (step9483 p h) (sat_cons (step1441 p h) (sat_cons (step1428 p h) (sat_cons (step2152 p h) (sat_cons (step3025 p h) (sat_cons (step1520 p h) (sat_cons (step1797 p h) (sat_cons (step1504 p h) (sat_cons (step1483 p h) (sat_cons (step1475 p h) (sat_cons (step16170 p h) (sat_cons (step514 p h) (sat_cons (step1613 p h) (sat_cons (step7243 p h) (sat_cons (step1645 p h) (sat_cons (step15884 p h) (sat_cons (step1738 p h) (sat_cons (step2556 p h) (sat_cons (step1913 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c16544 : List Lit := [(51, true), (1784, true), (49, false), (73, false), (1598, true)]
theorem step16544 (p : Nat → Bool) (h : Constraints p) : clause p c16544 = true :=
  Snake9.LocalRup.prove_clause [c15724, c1478, c13848, c1609, c16504, c16520, c16233, c1635, c16424, c16539, c14197, c16542, c1419, c1416, c5279, c16543, c4118, c9483, c1640, c1610, c1612, c13079] c16544 (by decide) p (sat_cons (step15724 p h) (sat_cons (step1478 p h) (sat_cons (step13848 p h) (sat_cons (step1609 p h) (sat_cons (step16504 p h) (sat_cons (step16520 p h) (sat_cons (step16233 p h) (sat_cons (step1635 p h) (sat_cons (step16424 p h) (sat_cons (step16539 p h) (sat_cons (step14197 p h) (sat_cons (step16542 p h) (sat_cons (step1419 p h) (sat_cons (step1416 p h) (sat_cons (step5279 p h) (sat_cons (step16543 p h) (sat_cons (step4118 p h) (sat_cons (step9483 p h) (sat_cons (step1640 p h) (sat_cons (step1610 p h) (sat_cons (step1612 p h) (sat_cons (step13079 p h) (sat_nil p)))))))))))))))))))))))
def c16545 : List Lit := [(103, true), (115, true), (1784, true), (1661, false), (1598, true)]
theorem step16545 (p : Nat → Bool) (h : Constraints p) : clause p c16545 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4118, c1478, c13848, c1609, c1635, c16424, c14197, c9483, c1640, c1610, c1612, c13079] c16545 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4118 p h) (sat_cons (step1478 p h) (sat_cons (step13848 p h) (sat_cons (step1609 p h) (sat_cons (step1635 p h) (sat_cons (step16424 p h) (sat_cons (step14197 p h) (sat_cons (step9483 p h) (sat_cons (step1640 p h) (sat_cons (step1610 p h) (sat_cons (step1612 p h) (sat_cons (step13079 p h) (sat_nil p))))))))))))))
def c16546 : List Lit := [(103, false), (1605, false), (1784, true), (49, false), (73, false), (1598, true)]
theorem step16546 (p : Nat → Bool) (h : Constraints p) : clause p c16546 = true :=
  Snake9.LocalRup.prove_clause [c16286, c1478, c13403, c337, c1430, c1416, c13767, c1419, c16535, c16541, c1162, c2361] c16546 (by decide) p (sat_cons (step16286 p h) (sat_cons (step1478 p h) (sat_cons (step13403 p h) (sat_cons (step337 p h) (sat_cons (step1430 p h) (sat_cons (step1416 p h) (sat_cons (step13767 p h) (sat_cons (step1419 p h) (sat_cons (step16535 p h) (sat_cons (step16541 p h) (sat_cons (step1162 p h) (sat_cons (step2361 p h) (sat_nil p)))))))))))))
def c16547 : List Lit := [(39, true), (1605, false), (1784, true), (49, false), (73, false), (1598, true)]
theorem step16547 (p : Nat → Bool) (h : Constraints p) : clause p c16547 = true :=
  Snake9.LocalRup.prove_clause [c1478, c16504, c16520, c16233, c16546, c16540, c1416, c16535, c1419, c1162, c16541, c2361] c16547 (by decide) p (sat_cons (step1478 p h) (sat_cons (step16504 p h) (sat_cons (step16520 p h) (sat_cons (step16233 p h) (sat_cons (step16546 p h) (sat_cons (step16540 p h) (sat_cons (step1416 p h) (sat_cons (step16535 p h) (sat_cons (step1419 p h) (sat_cons (step1162 p h) (sat_cons (step16541 p h) (sat_cons (step2361 p h) (sat_nil p)))))))))))))
def c16548 : List Lit := [(175, true), (1784, true), (49, false), (73, false), (1598, true)]
theorem step16548 (p : Nat → Bool) (h : Constraints p) : clause p c16548 = true :=
  Snake9.LocalRup.prove_clause [c16544, c16526, c16504, c16520, c16233, c3571, c16424, c16286, c1478, c16538, c1476, c11516, c1483, c1494, c16546, c16545, c13762, c16543, c1430, c16547, c5479, c333, c335, c1499, c1465, c1527, c1473, c1442, c1463, c1436, c359, c1428] c16548 (by decide) p (sat_cons (step16544 p h) (sat_cons (step16526 p h) (sat_cons (step16504 p h) (sat_cons (step16520 p h) (sat_cons (step16233 p h) (sat_cons (step3571 p h) (sat_cons (step16424 p h) (sat_cons (step16286 p h) (sat_cons (step1478 p h) (sat_cons (step16538 p h) (sat_cons (step1476 p h) (sat_cons (step11516 p h) (sat_cons (step1483 p h) (sat_cons (step1494 p h) (sat_cons (step16546 p h) (sat_cons (step16545 p h) (sat_cons (step13762 p h) (sat_cons (step16543 p h) (sat_cons (step1430 p h) (sat_cons (step16547 p h) (sat_cons (step5479 p h) (sat_cons (step333 p h) (sat_cons (step335 p h) (sat_cons (step1499 p h) (sat_cons (step1465 p h) (sat_cons (step1527 p h) (sat_cons (step1473 p h) (sat_cons (step1442 p h) (sat_cons (step1463 p h) (sat_cons (step1436 p h) (sat_cons (step359 p h) (sat_cons (step1428 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c16549 : List Lit := [(103, true), (487, true), (1784, true), (1661, false), (1598, true)]
theorem step16549 (p : Nat → Bool) (h : Constraints p) : clause p c16549 = true :=
  Snake9.LocalRup.prove_clause [c15726, c15724, c1289, c1284, c1281, c16424, c1478, c16545, c2725, c13755, c1913, c1610, c1738, c1640, c1645, c9483, c1613, c2671] c16549 (by decide) p (sat_cons (step15726 p h) (sat_cons (step15724 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step16424 p h) (sat_cons (step1478 p h) (sat_cons (step16545 p h) (sat_cons (step2725 p h) (sat_cons (step13755 p h) (sat_cons (step1913 p h) (sat_cons (step1610 p h) (sat_cons (step1738 p h) (sat_cons (step1640 p h) (sat_cons (step1645 p h) (sat_cons (step9483 p h) (sat_cons (step1613 p h) (sat_cons (step2671 p h) (sat_nil p)))))))))))))))))))
def c16550 : List Lit := [(1784, true), (49, false), (73, false), (1598, true)]
theorem step16550 (p : Nat → Bool) (h : Constraints p) : clause p c16550 = true :=
  Snake9.LocalRup.prove_clause [c16504, c16520, c16233, c16548, c1129, c1132, c1134, c1152, c1155, c1160, c2361, c1294, c16549, c4701, c16546, c1498] c16550 (by decide) p (sat_cons (step16504 p h) (sat_cons (step16520 p h) (sat_cons (step16233 p h) (sat_cons (step16548 p h) (sat_cons (step1129 p h) (sat_cons (step1132 p h) (sat_cons (step1134 p h) (sat_cons (step1152 p h) (sat_cons (step1155 p h) (sat_cons (step1160 p h) (sat_cons (step2361 p h) (sat_cons (step1294 p h) (sat_cons (step16549 p h) (sat_cons (step4701 p h) (sat_cons (step16546 p h) (sat_cons (step1498 p h) (sat_nil p)))))))))))))))))
def c16551 : List Lit := [(103, false), (49, false), (73, false), (1598, true)]
theorem step16551 (p : Nat → Bool) (h : Constraints p) : clause p c16551 = true :=
  Snake9.LocalRup.prove_clause [c15726, c15724, c16550, c2383, c16424, c16286, c16526, c14692, c16504, c16520, c16233, c1478, c13403, c337, c341, c340, c4701, c1430, c1416, c1461, c1498, c13833, c13762, c13767, c1419, c16452, c1610, c3384, c2361, c1640, c2382, c1294, c1730, c16453, c1907, c1289, c1291, c6580, c1284, c1664, c15941, c2511, c1914, c1731] c16551 (by decide) p (sat_cons (step15726 p h) (sat_cons (step15724 p h) (sat_cons (step16550 p h) (sat_cons (step2383 p h) (sat_cons (step16424 p h) (sat_cons (step16286 p h) (sat_cons (step16526 p h) (sat_cons (step14692 p h) (sat_cons (step16504 p h) (sat_cons (step16520 p h) (sat_cons (step16233 p h) (sat_cons (step1478 p h) (sat_cons (step13403 p h) (sat_cons (step337 p h) (sat_cons (step341 p h) (sat_cons (step340 p h) (sat_cons (step4701 p h) (sat_cons (step1430 p h) (sat_cons (step1416 p h) (sat_cons (step1461 p h) (sat_cons (step1498 p h) (sat_cons (step13833 p h) (sat_cons (step13762 p h) (sat_cons (step13767 p h) (sat_cons (step1419 p h) (sat_cons (step16452 p h) (sat_cons (step1610 p h) (sat_cons (step3384 p h) (sat_cons (step2361 p h) (sat_cons (step1640 p h) (sat_cons (step2382 p h) (sat_cons (step1294 p h) (sat_cons (step1730 p h) (sat_cons (step16453 p h) (sat_cons (step1907 p h) (sat_cons (step1289 p h) (sat_cons (step1291 p h) (sat_cons (step6580 p h) (sat_cons (step1284 p h) (sat_cons (step1664 p h) (sat_cons (step15941 p h) (sat_cons (step2511 p h) (sat_cons (step1914 p h) (sat_cons (step1731 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c16552 : List Lit := [(107, false), (62, false), (1752, true), (114, true), (115, true), (485, true), (1598, true)]
theorem step16552 (p : Nat → Bool) (h : Constraints p) : clause p c16552 = true :=
  Snake9.LocalRup.prove_clause [c1286, c1264, c1256, c1255, c1284, c1281, c1270, c1267, c16424, c3394, c13202, c2437, c1798] c16552 (by decide) p (sat_cons (step1286 p h) (sat_cons (step1264 p h) (sat_cons (step1256 p h) (sat_cons (step1255 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1270 p h) (sat_cons (step1267 p h) (sat_cons (step16424 p h) (sat_cons (step3394 p h) (sat_cons (step13202 p h) (sat_cons (step2437 p h) (sat_cons (step1798 p h) (sat_nil p))))))))))))))
def c16553 : List Lit := [(107, true), (1667, false), (1750, false), (455, true), (103, true), (1786, true), (1614, false)]
theorem step16553 (p : Nat → Bool) (h : Constraints p) : clause p c16553 = true :=
  Snake9.LocalRup.prove_clause [c15724, c1250, c1248, c1242, c1240, c1252, c3512, c14876, c1864, c1915] c16553 (by decide) p (sat_cons (step15724 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1240 p h) (sat_cons (step1252 p h) (sat_cons (step3512 p h) (sat_cons (step14876 p h) (sat_cons (step1864 p h) (sat_cons (step1915 p h) (sat_nil p)))))))))))
def c16554 : List Lit := [(1667, false), (114, true), (115, true), (487, true), (103, true), (1786, true), (1614, false), (1598, true)]
theorem step16554 (p : Nat → Bool) (h : Constraints p) : clause p c16554 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4118, c1291, c1250, c1248, c1242, c1240, c1289, c1286, c1264, c1256, c1255, c1284, c1281, c1272, c1266, c1270, c1267, c2781, c1252, c16424, c12823, c9487, c16553, c13202, c16552, c1798, c16507, c14944] c16554 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4118 p h) (sat_cons (step1291 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1240 p h) (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step1264 p h) (sat_cons (step1256 p h) (sat_cons (step1255 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1270 p h) (sat_cons (step1267 p h) (sat_cons (step2781 p h) (sat_cons (step1252 p h) (sat_cons (step16424 p h) (sat_cons (step12823 p h) (sat_cons (step9487 p h) (sat_cons (step16553 p h) (sat_cons (step13202 p h) (sat_cons (step16552 p h) (sat_cons (step1798 p h) (sat_cons (step16507 p h) (sat_cons (step14944 p h) (sat_nil p))))))))))))))))))))))))))))))
def c16555 : List Lit := [(115, true), (1568, false), (1605, false), (487, true), (49, false), (73, false), (1598, true)]
theorem step16555 (p : Nat → Bool) (h : Constraints p) : clause p c16555 = true :=
  Snake9.LocalRup.prove_clause [c15726, c1289, c1284, c1281, c1272, c1266, c16551, c16526, c16424, c16456, c14810, c2381, c16286, c14692, c1478, c13848, c1609, c16504, c16520, c16233, c1635, c1722, c2303, c16554, c1640, c1610, c1612, c13833, c12655, c1430, c13513, c1433, c1900, c1446, c2382, c1526, c1576] c16555 (by decide) p (sat_cons (step15726 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step16551 p h) (sat_cons (step16526 p h) (sat_cons (step16424 p h) (sat_cons (step16456 p h) (sat_cons (step14810 p h) (sat_cons (step2381 p h) (sat_cons (step16286 p h) (sat_cons (step14692 p h) (sat_cons (step1478 p h) (sat_cons (step13848 p h) (sat_cons (step1609 p h) (sat_cons (step16504 p h) (sat_cons (step16520 p h) (sat_cons (step16233 p h) (sat_cons (step1635 p h) (sat_cons (step1722 p h) (sat_cons (step2303 p h) (sat_cons (step16554 p h) (sat_cons (step1640 p h) (sat_cons (step1610 p h) (sat_cons (step1612 p h) (sat_cons (step13833 p h) (sat_cons (step12655 p h) (sat_cons (step1430 p h) (sat_cons (step13513 p h) (sat_cons (step1433 p h) (sat_cons (step1900 p h) (sat_cons (step1446 p h) (sat_cons (step2382 p h) (sat_cons (step1526 p h) (sat_cons (step1576 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c16556 : List Lit := [(1568, false), (1593, false), (1605, false), (487, true), (49, false), (73, false), (1598, true)]
theorem step16556 (p : Nat → Bool) (h : Constraints p) : clause p c16556 = true :=
  Snake9.LocalRup.prove_clause [c15724, c16286, c1534, c1291, c1252, c16551, c2725, c16550, c2383, c16424, c16526, c14692, c16504, c16520, c16233, c1478, c1447, c1434, c16555, c13755, c13762, c13745, c1430, c1432, c1433, c1436, c1451, c1446, c1428, c1527, c1526, c1503, c1499, c1576, c1585, c1483, c2382, c13684, c1475, c1476, c1118, c4566, c1105, c3506, c1104, c4006, c511, c514, c1613, c1797, c1645, c2152, c9415] c16556 (by decide) p (sat_cons (step15724 p h) (sat_cons (step16286 p h) (sat_cons (step1534 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step16551 p h) (sat_cons (step2725 p h) (sat_cons (step16550 p h) (sat_cons (step2383 p h) (sat_cons (step16424 p h) (sat_cons (step16526 p h) (sat_cons (step14692 p h) (sat_cons (step16504 p h) (sat_cons (step16520 p h) (sat_cons (step16233 p h) (sat_cons (step1478 p h) (sat_cons (step1447 p h) (sat_cons (step1434 p h) (sat_cons (step16555 p h) (sat_cons (step13755 p h) (sat_cons (step13762 p h) (sat_cons (step13745 p h) (sat_cons (step1430 p h) (sat_cons (step1432 p h) (sat_cons (step1433 p h) (sat_cons (step1436 p h) (sat_cons (step1451 p h) (sat_cons (step1446 p h) (sat_cons (step1428 p h) (sat_cons (step1527 p h) (sat_cons (step1526 p h) (sat_cons (step1503 p h) (sat_cons (step1499 p h) (sat_cons (step1576 p h) (sat_cons (step1585 p h) (sat_cons (step1483 p h) (sat_cons (step2382 p h) (sat_cons (step13684 p h) (sat_cons (step1475 p h) (sat_cons (step1476 p h) (sat_cons (step1118 p h) (sat_cons (step4566 p h) (sat_cons (step1105 p h) (sat_cons (step3506 p h) (sat_cons (step1104 p h) (sat_cons (step4006 p h) (sat_cons (step511 p h) (sat_cons (step514 p h) (sat_cons (step1613 p h) (sat_cons (step1797 p h) (sat_cons (step1645 p h) (sat_cons (step2152 p h) (sat_cons (step9415 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c16557 : List Lit := [(1696, true), (1663, false)]
theorem step16557 (p : Nat → Bool) (h : Constraints p) : clause p c16557 = true :=
  Snake9.LocalRup.prove_clause [c15726, c1701] c16557 (by decide) p (sat_cons (step15726 p h) (sat_cons (step1701 p h) (sat_nil p)))
def c16558 : List Lit := [(1684, false), (1689, true)]
theorem step16558 (p : Nat → Bool) (h : Constraints p) : clause p c16558 = true :=
  Snake9.LocalRup.prove_clause [c15725, c1682] c16558 (by decide) p (sat_cons (step15725 p h) (sat_cons (step1682 p h) (sat_nil p)))
def c16559 : List Lit := [(1669, false), (1702, true)]
theorem step16559 (p : Nat → Bool) (h : Constraints p) : clause p c16559 = true :=
  Snake9.LocalRup.prove_clause [c15726, c1745] c16559 (by decide) p (sat_cons (step15726 p h) (sat_cons (step1745 p h) (sat_nil p)))
def c16560 : List Lit := [(1701, true), (1668, false)]
theorem step16560 (p : Nat → Bool) (h : Constraints p) : clause p c16560 = true :=
  Snake9.LocalRup.prove_clause [c15726, c1738] c16560 (by decide) p (sat_cons (step15726 p h) (sat_cons (step1738 p h) (sat_nil p)))
def c16561 : List Lit := [(1673, false), (1676, true)]
theorem step16561 (p : Nat → Bool) (h : Constraints p) : clause p c16561 = true :=
  Snake9.LocalRup.prove_clause [c15724, c1657] c16561 (by decide) p (sat_cons (step15724 p h) (sat_cons (step1657 p h) (sat_nil p)))
def c16562 : List Lit := [(1667, false), (1700, true)]
theorem step16562 (p : Nat → Bool) (h : Constraints p) : clause p c16562 = true :=
  Snake9.LocalRup.prove_clause [c15726, c1730] c16562 (by decide) p (sat_cons (step15726 p h) (sat_cons (step1730 p h) (sat_nil p)))
def c16563 : List Lit := [(1688, true), (1680, false)]
theorem step16563 (p : Nat → Bool) (h : Constraints p) : clause p c16563 = true :=
  Snake9.LocalRup.prove_clause [c15724, c2511] c16563 (by decide) p (sat_cons (step15724 p h) (sat_cons (step2511 p h) (sat_nil p)))
def c16564 : List Lit := [(1675, true), (1672, false)]
theorem step16564 (p : Nat → Bool) (h : Constraints p) : clause p c16564 = true :=
  Snake9.LocalRup.prove_clause [c15724, c1656] c16564 (by decide) p (sat_cons (step15724 p h) (sat_cons (step1656 p h) (sat_nil p)))
def c16565 : List Lit := [(1699, true), (1666, false)]
theorem step16565 (p : Nat → Bool) (h : Constraints p) : clause p c16565 = true :=
  Snake9.LocalRup.prove_clause [c15726, c1722] c16565 (by decide) p (sat_cons (step15726 p h) (sat_cons (step1722 p h) (sat_nil p)))
def c16566 : List Lit := [(1685, false), (1690, true)]
theorem step16566 (p : Nat → Bool) (h : Constraints p) : clause p c16566 = true :=
  Snake9.LocalRup.prove_clause [c15725, c1683] c16566 (by decide) p (sat_cons (step15725 p h) (sat_cons (step1683 p h) (sat_nil p)))
def c16567 : List Lit := [(1697, true), (1664, false)]
theorem step16567 (p : Nat → Bool) (h : Constraints p) : clause p c16567 = true :=
  Snake9.LocalRup.prove_clause [c15726, c1708] c16567 (by decide) p (sat_cons (step15726 p h) (sat_cons (step1708 p h) (sat_nil p)))
def c16568 : List Lit := [(1698, true), (1665, false)]
theorem step16568 (p : Nat → Bool) (h : Constraints p) : clause p c16568 = true :=
  Snake9.LocalRup.prove_clause [c15726, c1715] c16568 (by decide) p (sat_cons (step15726 p h) (sat_cons (step1715 p h) (sat_nil p)))
def c16569 : List Lit := [(81, true), (79, true), (1692, true), (91, true), (415, true)]
theorem step16569 (p : Nat → Bool) (h : Constraints p) : clause p c16569 = true :=
  Snake9.LocalRup.prove_clause [c15724, c2694] c16569 (by decide) p (sat_cons (step15724 p h) (sat_cons (step2694 p h) (sat_nil p)))
def c16570 : List Lit := [(81, true), (79, true), (211, true), (209, true), (1691, true), (213, true)]
theorem step16570 (p : Nat → Bool) (h : Constraints p) : clause p c16570 = true :=
  Snake9.LocalRup.prove_clause [c15724, c2712] c16570 (by decide) p (sat_cons (step15724 p h) (sat_cons (step2712 p h) (sat_nil p)))
def c16571 : List Lit := [(1781, true), (487, true), (1666, false)]
theorem step16571 (p : Nat → Bool) (h : Constraints p) : clause p c16571 = true :=
  Snake9.LocalRup.prove_clause [c15724, c2733] c16571 (by decide) p (sat_cons (step15724 p h) (sat_cons (step2733 p h) (sat_nil p)))
def c16572 : List Lit := [(1782, true), (1750, false), (1666, false), (487, true), (74, true)]
theorem step16572 (p : Nat → Bool) (h : Constraints p) : clause p c16572 = true :=
  Snake9.LocalRup.prove_clause [c15724, c2804] c16572 (by decide) p (sat_cons (step15724 p h) (sat_cons (step2804 p h) (sat_nil p)))
def c16573 : List Lit := [(1780, true), (439, true), (1665, false)]
theorem step16573 (p : Nat → Bool) (h : Constraints p) : clause p c16573 = true :=
  Snake9.LocalRup.prove_clause [c15724, c2770] c16573 (by decide) p (sat_cons (step15724 p h) (sat_cons (step2770 p h) (sat_nil p)))
def c16574 : List Lit := [(1783, true), (107, true), (1701, true), (1667, false), (439, true)]
theorem step16574 (p : Nat → Bool) (h : Constraints p) : clause p c16574 = true :=
  Snake9.LocalRup.prove_clause [c15724, c3284] c16574 (by decide) p (sat_cons (step15724 p h) (sat_cons (step3284 p h) (sat_nil p)))
def c16575 : List Lit := [(81, true), (1688, true)]
theorem step16575 (p : Nat → Bool) (h : Constraints p) : clause p c16575 = true :=
  Snake9.LocalRup.prove_clause [c15724, c3204] c16575 (by decide) p (sat_cons (step15724 p h) (sat_cons (step3204 p h) (sat_nil p)))
def c16576 : List Lit := [(1781, true), (1760, false), (49, true), (1750, false), (1664, false), (455, true)]
theorem step16576 (p : Nat → Bool) (h : Constraints p) : clause p c16576 = true :=
  Snake9.LocalRup.prove_clause [c15724, c3491] c16576 (by decide) p (sat_cons (step15724 p h) (sat_cons (step3491 p h) (sat_nil p)))
def c16577 : List Lit := [(1619, false), (1751, false), (427, false), (1553, false), (1760, false), (1664, false)]
theorem step16577 (p : Nat → Bool) (h : Constraints p) : clause p c16577 = true :=
  Snake9.LocalRup.prove_clause [c15724, c3528] c16577 (by decide) p (sat_cons (step15724 p h) (sat_cons (step3528 p h) (sat_nil p)))
def c16578 : List Lit := [(1782, true), (107, true), (1751, false), (439, true), (1664, false)]
theorem step16578 (p : Nat → Bool) (h : Constraints p) : clause p c16578 = true :=
  Snake9.LocalRup.prove_clause [c15724, c10490] c16578 (by decide) p (sat_cons (step15724 p h) (sat_cons (step10490 p h) (sat_nil p)))
def c16579 : List Lit := [(1746, false), (1667, false), (487, true), (1725, false), (1785, true), (115, true), (49, true)]
theorem step16579 (p : Nat → Bool) (h : Constraints p) : clause p c16579 = true :=
  Snake9.LocalRup.prove_clause [c15724, c3760] c16579 (by decide) p (sat_cons (step15724 p h) (sat_cons (step3760 p h) (sat_nil p)))
def c16580 : List Lit := [(1619, false), (1761, false), (305, true), (1664, false)]
theorem step16580 (p : Nat → Bool) (h : Constraints p) : clause p c16580 = true :=
  Snake9.LocalRup.prove_clause [c15724, c3504] c16580 (by decide) p (sat_cons (step15724 p h) (sat_cons (step3504 p h) (sat_nil p)))
def c16581 : List Lit := [(89, true), (1701, true), (415, true), (1750, false), (1729, true), (1666, false), (439, true), (1784, true)]
theorem step16581 (p : Nat → Bool) (h : Constraints p) : clause p c16581 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4056] c16581 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4056 p h) (sat_nil p)))
def c16582 : List Lit := [(72, false), (1750, false), (1784, true), (1762, true), (103, true), (487, true), (483, true)]
theorem step16582 (p : Nat → Bool) (h : Constraints p) : clause p c16582 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4545] c16582 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4545 p h) (sat_nil p)))
def c16583 : List Lit := [(1782, true), (1750, false), (439, true), (1665, false), (1760, false)]
theorem step16583 (p : Nat → Bool) (h : Constraints p) : clause p c16583 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4496] c16583 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4496 p h) (sat_nil p)))
def c16584 : List Lit := [(1781, true), (439, true), (1750, false), (1665, false)]
theorem step16584 (p : Nat → Bool) (h : Constraints p) : clause p c16584 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4107] c16584 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4107 p h) (sat_nil p)))
def c16585 : List Lit := [(63, false), (1533, true), (1660, false), (1701, true), (113, false)]
theorem step16585 (p : Nat → Bool) (h : Constraints p) : clause p c16585 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4551] c16585 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4551 p h) (sat_nil p)))
def c16586 : List Lit := [(1709, true), (1688, true)]
theorem step16586 (p : Nat → Bool) (h : Constraints p) : clause p c16586 = true :=
  Snake9.LocalRup.prove_clause [c15724, c3958] c16586 (by decide) p (sat_cons (step15724 p h) (sat_cons (step3958 p h) (sat_nil p)))
def c16587 : List Lit := [(1727, true), (1688, true), (439, true)]
theorem step16587 (p : Nat → Bool) (h : Constraints p) : clause p c16587 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4164] c16587 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4164 p h) (sat_nil p)))
def c16588 : List Lit := [(1752, false), (1782, true), (1664, false), (439, true)]
theorem step16588 (p : Nat → Bool) (h : Constraints p) : clause p c16588 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4509] c16588 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4509 p h) (sat_nil p)))
def c16589 : List Lit := [(95, false), (81, true), (91, true), (1727, true), (489, true), (1692, true), (43, true)]
theorem step16589 (p : Nat → Bool) (h : Constraints p) : clause p c16589 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4478] c16589 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4478 p h) (sat_nil p)))
def c16590 : List Lit := [(1760, true), (1688, true), (1750, false)]
theorem step16590 (p : Nat → Bool) (h : Constraints p) : clause p c16590 = true :=
  Snake9.LocalRup.prove_clause [c15724, c5129] c16590 (by decide) p (sat_cons (step15724 p h) (sat_cons (step5129 p h) (sat_nil p)))
def c16591 : List Lit := [(98, true), (1576, true), (222, true), (218, true), (209, true), (213, true), (220, true), (1691, true), (1728, true), (107, true), (211, true)]
theorem step16591 (p : Nat → Bool) (h : Constraints p) : clause p c16591 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4751] c16591 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4751 p h) (sat_nil p)))
def c16592 : List Lit := [(53, true), (1688, true), (43, true), (40, true), (39, false), (42, false), (166, true)]
theorem step16592 (p : Nat → Bool) (h : Constraints p) : clause p c16592 = true :=
  Snake9.LocalRup.prove_clause [c15724, c4755] c16592 (by decide) p (sat_cons (step15724 p h) (sat_cons (step4755 p h) (sat_nil p)))
def c16593 : List Lit := [(1678, false), (89, true), (1760, false), (439, true), (1666, false), (1784, true), (1688, false), (1750, false)]
theorem step16593 (p : Nat → Bool) (h : Constraints p) : clause p c16593 = true :=
  Snake9.LocalRup.prove_clause [c15725, c5105] c16593 (by decide) p (sat_cons (step15725 p h) (sat_cons (step5105 p h) (sat_nil p)))
def c16594 : List Lit := [(1782, true), (1750, false), (1759, false), (1666, false), (1699, false)]
theorem step16594 (p : Nat → Bool) (h : Constraints p) : clause p c16594 = true :=
  Snake9.LocalRup.prove_clause [c15724, c6852] c16594 (by decide) p (sat_cons (step15724 p h) (sat_cons (step6852 p h) (sat_nil p)))
def c16595 : List Lit := [(1617, false), (91, true), (1785, true), (1759, false), (1750, false), (1688, false), (1667, false)]
theorem step16595 (p : Nat → Bool) (h : Constraints p) : clause p c16595 = true :=
  Snake9.LocalRup.prove_clause [c15725, c7530] c16595 (by decide) p (sat_cons (step15725 p h) (sat_cons (step7530 p h) (sat_nil p)))
def c16596 : List Lit := [(1618, false), (91, true), (1760, false), (415, true), (1665, false), (1639, true), (1685, true)]
theorem step16596 (p : Nat → Bool) (h : Constraints p) : clause p c16596 = true :=
  Snake9.LocalRup.prove_clause [c15725, c7389] c16596 (by decide) p (sat_cons (step15725 p h) (sat_cons (step7389 p h) (sat_nil p)))
def c16597 : List Lit := [(91, true), (1667, false), (1750, false), (1616, false), (1760, false), (1688, false)]
theorem step16597 (p : Nat → Bool) (h : Constraints p) : clause p c16597 = true :=
  Snake9.LocalRup.prove_clause [c15725, c7429] c16597 (by decide) p (sat_cons (step15725 p h) (sat_cons (step7429 p h) (sat_nil p)))
def c16598 : List Lit := [(1783, true), (1667, false), (1750, false), (1701, true)]
theorem step16598 (p : Nat → Bool) (h : Constraints p) : clause p c16598 = true :=
  Snake9.LocalRup.prove_clause [c15724, c7614] c16598 (by decide) p (sat_cons (step15724 p h) (sat_cons (step7614 p h) (sat_nil p)))
def c16599 : List Lit := [(91, true), (1700, false), (1616, false), (1666, false), (1761, false)]
theorem step16599 (p : Nat → Bool) (h : Constraints p) : clause p c16599 = true :=
  Snake9.LocalRup.prove_clause [c15724, c7517] c16599 (by decide) p (sat_cons (step15724 p h) (sat_cons (step7517 p h) (sat_nil p)))
def c16600 : List Lit := [(1667, false), (1761, false), (1616, false)]
theorem step16600 (p : Nat → Bool) (h : Constraints p) : clause p c16600 = true :=
  Snake9.LocalRup.prove_clause [c15724, c7586] c16600 (by decide) p (sat_cons (step15724 p h) (sat_cons (step7586 p h) (sat_nil p)))
def c16601 : List Lit := [(1668, false), (1750, false), (1785, true), (439, true), (1760, false)]
theorem step16601 (p : Nat → Bool) (h : Constraints p) : clause p c16601 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9415] c16601 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9415 p h) (sat_nil p)))
def c16602 : List Lit := [(1617, false), (1761, false), (1666, false)]
theorem step16602 (p : Nat → Bool) (h : Constraints p) : clause p c16602 = true :=
  Snake9.LocalRup.prove_clause [c15724, c8680] c16602 (by decide) p (sat_cons (step15724 p h) (sat_cons (step8680 p h) (sat_nil p)))
def c16603 : List Lit := [(1601, false), (1582, false), (1759, false), (51, true), (1553, false), (1666, false), (1783, true), (1750, false)]
theorem step16603 (p : Nat → Bool) (h : Constraints p) : clause p c16603 = true :=
  Snake9.LocalRup.prove_clause [c15724, c10359] c16603 (by decide) p (sat_cons (step15724 p h) (sat_cons (step10359 p h) (sat_nil p)))
end B112E089
