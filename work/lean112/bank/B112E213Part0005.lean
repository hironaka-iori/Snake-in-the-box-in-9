import B112E213Part0004
namespace B112E213
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1524 : List Lit := [(77, true), (87, false), (86, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c547, c473] c1524 (by decide) p (sat_cons (step547 p h) (sat_cons (step473 p h) (sat_nil p)))
def c1525 : List Lit := [(89, true), (34, true), (80, true), (90, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c548, c478] c1525 (by decide) p (sat_cons (step548 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1526 : List Lit := [(91, false), (88, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c549, c479] c1526 (by decide) p (sat_cons (step549 p h) (sat_cons (step479 p h) (sat_nil p)))
def c1527 : List Lit := [(93, false), (98, true)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c550, c482] c1527 (by decide) p (sat_cons (step550 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1528 : List Lit := [(93, false), (43, true)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c550, c483] c1528 (by decide) p (sat_cons (step550 p h) (sat_cons (step483 p h) (sat_nil p)))
def c1529 : List Lit := [(96, true), (48, true), (94, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c551, c485] c1529 (by decide) p (sat_cons (step551 p h) (sat_cons (step485 p h) (sat_nil p)))
def c1530 : List Lit := [(95, true), (96, true), (97, false)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c552, c489] c1530 (by decide) p (sat_cons (step552 p h) (sat_cons (step489 p h) (sat_nil p)))
def c1531 : List Lit := [(92, true), (96, true), (97, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c552, c490] c1531 (by decide) p (sat_cons (step552 p h) (sat_cons (step490 p h) (sat_nil p)))
def c1532 : List Lit := [(92, true), (95, true), (97, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c552, c491] c1532 (by decide) p (sat_cons (step552 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1533 : List Lit := [(215, true), (100, true), (98, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1206, c492] c1533 (by decide) p (sat_cons (step1206 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1534 : List Lit := [(93, true), (215, true), (98, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1206, c493] c1534 (by decide) p (sat_cons (step1206 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1535 : List Lit := [(98, true), (100, false), (53, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c554, c496] c1535 (by decide) p (sat_cons (step554 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1536 : List Lit := [(121, false), (122, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1229, c565] c1536 (by decide) p (sat_cons (step1229 p h) (sat_cons (step565 p h) (sat_nil p)))
def c1537 : List Lit := [(239, false), (241, false)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1227, c569] c1537 (by decide) p (sat_cons (step1227 p h) (sat_cons (step569 p h) (sat_nil p)))
def c1538 : List Lit := [(237, false), (243, false)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1225, c574] c1538 (by decide) p (sat_cons (step1225 p h) (sat_cons (step574 p h) (sat_nil p)))
def c1539 : List Lit := [(249, false), (255, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1224, c582] c1539 (by decide) p (sat_cons (step1224 p h) (sat_cons (step582 p h) (sat_nil p)))
def c1540 : List Lit := [(245, false), (257, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1219, c586] c1540 (by decide) p (sat_cons (step1219 p h) (sat_cons (step586 p h) (sat_nil p)))
def c1541 : List Lit := [(135, false), (136, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1228, c590] c1541 (by decide) p (sat_cons (step1228 p h) (sat_cons (step590 p h) (sat_nil p)))
def c1542 : List Lit := [(259, false), (287, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1214, c606] c1542 (by decide) p (sat_cons (step1214 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1543 : List Lit := [(289, false), (345, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1210, c642] c1543 (by decide) p (sat_cons (step1210 p h) (sat_cons (step642 p h) (sat_nil p)))
def c1544 : List Lit := [(377, false), (383, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1221, c655] c1544 (by decide) p (sat_cons (step1221 p h) (sat_cons (step655 p h) (sat_nil p)))
def c1545 : List Lit := [(429, false), (457, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1211, c703] c1545 (by decide) p (sat_cons (step1211 p h) (sat_cons (step703 p h) (sat_nil p)))
def c1546 : List Lit := [(403, false), (459, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1209, c708] c1546 (by decide) p (sat_cons (step1209 p h) (sat_cons (step708 p h) (sat_nil p)))
def c1547 : List Lit := [(347, false), (461, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c713, c711] c1547 (by decide) p (sat_cons (step713 p h) (sat_cons (step711 p h) (sat_nil p)))
def c1548 : List Lit := [(832, true), (820, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1421, c780] c1548 (by decide) p (sat_cons (step1421 p h) (sat_cons (step780 p h) (sat_nil p)))
def c1549 : List Lit := [(821, false), (833, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1421, c784] c1549 (by decide) p (sat_cons (step1421 p h) (sat_cons (step784 p h) (sat_nil p)))
def c1550 : List Lit := [(840, true), (832, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1398, c792] c1550 (by decide) p (sat_cons (step1398 p h) (sat_cons (step792 p h) (sat_nil p)))
def c1551 : List Lit := [(841, true), (833, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1398, c793] c1551 (by decide) p (sat_cons (step1398 p h) (sat_cons (step793 p h) (sat_nil p)))
def c1552 : List Lit := [(834, false), (842, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1398, c794] c1552 (by decide) p (sat_cons (step1398 p h) (sat_cons (step794 p h) (sat_nil p)))
def c1553 : List Lit := [(835, false), (843, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1398, c795] c1553 (by decide) p (sat_cons (step1398 p h) (sat_cons (step795 p h) (sat_nil p)))
def c1554 : List Lit := [(836, false), (844, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1398, c796] c1554 (by decide) p (sat_cons (step1398 p h) (sat_cons (step796 p h) (sat_nil p)))
def c1555 : List Lit := [(840, true), (811, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1335, c797] c1555 (by decide) p (sat_cons (step1335 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1556 : List Lit := [(841, true), (812, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1335, c802] c1556 (by decide) p (sat_cons (step1335 p h) (sat_cons (step802 p h) (sat_nil p)))
def c1557 : List Lit := [(813, false), (842, true)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1335, c807] c1557 (by decide) p (sat_cons (step1335 p h) (sat_cons (step807 p h) (sat_nil p)))
def c1558 : List Lit := [(917, true), (899, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1399, c943] c1558 (by decide) p (sat_cons (step1399 p h) (sat_cons (step943 p h) (sat_nil p)))
def c1559 : List Lit := [(900, false), (918, true)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1399, c944] c1559 (by decide) p (sat_cons (step1399 p h) (sat_cons (step944 p h) (sat_nil p)))
def c1560 : List Lit := [(901, false), (919, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1399, c945] c1560 (by decide) p (sat_cons (step1399 p h) (sat_cons (step945 p h) (sat_nil p)))
def c1561 : List Lit := [(917, false), (1057, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1160] c1561 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1160 p h) (sat_nil p)))
def c1562 : List Lit := [(918, false), (1056, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1161] c1562 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1161 p h) (sat_nil p)))
def c1563 : List Lit := [(919, false), (1055, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1162] c1563 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1162 p h) (sat_nil p)))
def c1564 : List Lit := [(920, false), (1054, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1163] c1564 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1163 p h) (sat_nil p)))
def c1565 : List Lit := [(921, false), (1053, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1164] c1565 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1164 p h) (sat_nil p)))
def c1566 : List Lit := [(922, false), (1052, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1165] c1566 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1165 p h) (sat_nil p)))
def c1567 : List Lit := [(923, false), (1051, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1166] c1567 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c1568 : List Lit := [(924, false), (1050, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1167] c1568 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1167 p h) (sat_nil p)))
def c1569 : List Lit := [(83, true), (962, true), (91, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1040, c1031, c1032, c1039, c1377, c1034] c1569 (by decide) p (sat_cons (step1040 p h) (sat_cons (step1031 p h) (sat_cons (step1032 p h) (sat_cons (step1039 p h) (sat_cons (step1377 p h) (sat_cons (step1034 p h) (sat_nil p)))))))
def c1570 : List Lit := [(841, true), (806, false), (16, true), (18, false), (17, false), (827, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c754, c776, c1551, c798, c781, c777, c740, c755, c717, c749, c714, c715, c87, c1437, c757, c17, c767, c760, c762, c769, c1316, c759] c1570 (by decide) p (sat_cons (step754 p h) (sat_cons (step776 p h) (sat_cons (step1551 p h) (sat_cons (step798 p h) (sat_cons (step781 p h) (sat_cons (step777 p h) (sat_cons (step740 p h) (sat_cons (step755 p h) (sat_cons (step717 p h) (sat_cons (step749 p h) (sat_cons (step714 p h) (sat_cons (step715 p h) (sat_cons (step87 p h) (sat_cons (step1437 p h) (sat_cons (step757 p h) (sat_cons (step17 p h) (sat_cons (step767 p h) (sat_cons (step760 p h) (sat_cons (step762 p h) (sat_cons (step769 p h) (sat_cons (step1316 p h) (sat_cons (step759 p h) (sat_nil p)))))))))))))))))))))))
def c1571 : List Lit := [(887, true), (94, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c880, c883, c872, c874, c858, c870, c1359, c1274] c1571 (by decide) p (sat_cons (step880 p h) (sat_cons (step883 p h) (sat_cons (step872 p h) (sat_cons (step874 p h) (sat_cons (step858 p h) (sat_cons (step870 p h) (sat_cons (step1359 p h) (sat_cons (step1274 p h) (sat_nil p)))))))))
def c1572 : List Lit := [(888, true), (859, true), (94, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1379, c870, c1368, c852, c853, c1356, c1473, c353, c866, c874, c884, c858, c855, c856, c1274, c1478, c1479, c298, c279, c825] c1572 (by decide) p (sat_cons (step1379 p h) (sat_cons (step870 p h) (sat_cons (step1368 p h) (sat_cons (step852 p h) (sat_cons (step853 p h) (sat_cons (step1356 p h) (sat_cons (step1473 p h) (sat_cons (step353 p h) (sat_cons (step866 p h) (sat_cons (step874 p h) (sat_cons (step884 p h) (sat_cons (step858 p h) (sat_cons (step855 p h) (sat_cons (step856 p h) (sat_cons (step1274 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step298 p h) (sat_cons (step279 p h) (sat_cons (step825 p h) (sat_nil p)))))))))))))))))))))
def c1573 : List Lit := [(854, false), (899, true), (94, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1571, c923, c843, c845, c910, c827, c1572, c917, c844, c826, c823, c824, c1365, c1266, c869, c322, c1274, c867, c858, c875, c885] c1573 (by decide) p (sat_cons (step1571 p h) (sat_cons (step923 p h) (sat_cons (step843 p h) (sat_cons (step845 p h) (sat_cons (step910 p h) (sat_cons (step827 p h) (sat_cons (step1572 p h) (sat_cons (step917 p h) (sat_cons (step844 p h) (sat_cons (step826 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step1365 p h) (sat_cons (step1266 p h) (sat_cons (step869 p h) (sat_cons (step322 p h) (sat_cons (step1274 p h) (sat_cons (step867 p h) (sat_cons (step858 p h) (sat_cons (step875 p h) (sat_cons (step885 p h) (sat_nil p))))))))))))))))))))))
def c1574 : List Lit := [(864, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c834, c838, c828, c815, c820, c812, c813, c239, c1323, c1467] c1574 (by decide) p (sat_cons (step834 p h) (sat_cons (step838 p h) (sat_cons (step828 p h) (sat_cons (step815 p h) (sat_cons (step820 p h) (sat_cons (step812 p h) (sat_cons (step813 p h) (sat_cons (step239 p h) (sat_cons (step1323 p h) (sat_cons (step1467 p h) (sat_nil p)))))))))))
def c1575 : List Lit := [(40, false), (48, false), (874, true), (94, false)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c318, c321, c857] c1575 (by decide) p (sat_cons (step318 p h) (sat_cons (step321 p h) (sat_cons (step857 p h) (sat_nil p))))
def c1576 : List Lit := [(48, false), (884, false), (899, true), (94, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1574, c904, c890, c859, c1274, c858, c885, c910, c835, c1575, c823, c826, c829, c839, c820, c815, c812, c813, c239, c1323, c1467] c1576 (by decide) p (sat_cons (step1574 p h) (sat_cons (step904 p h) (sat_cons (step890 p h) (sat_cons (step859 p h) (sat_cons (step1274 p h) (sat_cons (step858 p h) (sat_cons (step885 p h) (sat_cons (step910 p h) (sat_cons (step835 p h) (sat_cons (step1575 p h) (sat_cons (step823 p h) (sat_cons (step826 p h) (sat_cons (step829 p h) (sat_cons (step839 p h) (sat_cons (step820 p h) (sat_cons (step815 p h) (sat_cons (step812 p h) (sat_cons (step813 p h) (sat_cons (step239 p h) (sat_cons (step1323 p h) (sat_cons (step1467 p h) (sat_nil p))))))))))))))))))))))
def c1577 : List Lit := [(865, true), (858, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c826, c835, c839, c829, c815, c820, c812, c813, c239, c1323, c1467] c1577 (by decide) p (sat_cons (step826 p h) (sat_cons (step835 p h) (sat_cons (step839 p h) (sat_cons (step829 p h) (sat_cons (step815 p h) (sat_cons (step820 p h) (sat_cons (step812 p h) (sat_cons (step813 p h) (sat_cons (step239 p h) (sat_cons (step1323 p h) (sat_cons (step1467 p h) (sat_nil p))))))))))))
def c1578 : List Lit := [(40, true), (48, true), (884, false), (859, true), (899, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c823, c825, c1577, c910, c885, c858, c860, c855, c853, c1479, c278] c1578 (by decide) p (sat_cons (step823 p h) (sat_cons (step825 p h) (sat_cons (step1577 p h) (sat_cons (step910 p h) (sat_cons (step885 p h) (sat_cons (step858 p h) (sat_cons (step860 p h) (sat_cons (step855 p h) (sat_cons (step853 p h) (sat_cons (step1479 p h) (sat_cons (step278 p h) (sat_nil p))))))))))))
def c1579 : List Lit := [(48, true), (884, false), (899, true), (859, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1470, c1266, c824, c1577, c910, c885, c858, c860, c855, c853, c279] c1579 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1470 p h) (sat_cons (step1266 p h) (sat_cons (step824 p h) (sat_cons (step1577 p h) (sat_cons (step910 p h) (sat_cons (step885 p h) (sat_cons (step858 p h) (sat_cons (step860 p h) (sat_cons (step855 p h) (sat_cons (step853 p h) (sat_cons (step279 p h) (sat_nil p)))))))))))))
def c1580 : List Lit := [(884, false), (859, true), (899, true), (94, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1579] c1580 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1579 p h) (sat_nil p)))
def c1581 : List Lit := [(40, false), (56, false), (48, true), (883, false), (899, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1470, c1266, c1471, c824, c267, c1577, c856, c910, c889, c859, c861, c857, c853, c279] c1581 (by decide) p (sat_cons (step1470 p h) (sat_cons (step1266 p h) (sat_cons (step1471 p h) (sat_cons (step824 p h) (sat_cons (step267 p h) (sat_cons (step1577 p h) (sat_cons (step856 p h) (sat_cons (step910 p h) (sat_cons (step889 p h) (sat_cons (step859 p h) (sat_cons (step861 p h) (sat_cons (step857 p h) (sat_cons (step853 p h) (sat_cons (step279 p h) (sat_nil p)))))))))))))))
def c1582 : List Lit := [(49, false), (42, false), (39, false), (48, true)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c1479, c278] c1582 (by decide) p (sat_cons (step1479 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1583 : List Lit := [(33, false), (30, false), (856, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c820, c239, c1323, c1467] c1583 (by decide) p (sat_cons (step820 p h) (sat_cons (step239 p h) (sat_cons (step1323 p h) (sat_cons (step1467 p h) (sat_nil p)))))
def c1584 : List Lit := [(17, false), (27, false), (30, false), (56, false)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c62, c180, c1449] c1584 (by decide) p (sat_cons (step62 p h) (sat_cons (step180 p h) (sat_cons (step1449 p h) (sat_nil p))))
def c1585 : List Lit := [(827, true), (34, true), (856, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c820, c1467, c1469, c1187, c760, c821, c764, c766, c1271, c757] c1585 (by decide) p (sat_cons (step820 p h) (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step1187 p h) (sat_cons (step760 p h) (sat_cons (step821 p h) (sat_cons (step764 p h) (sat_cons (step766 p h) (sat_cons (step1271 p h) (sat_cons (step757 p h) (sat_nil p)))))))))))
def c1586 : List Lit := [(834, true), (16, true), (18, false), (827, false), (25, true), (26, false), (17, true), (30, false), (37, false)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c750, c755, c782, c785, c756, c751, c90, c151, c757, c762, c767] c1586 (by decide) p (sat_cons (step750 p h) (sat_cons (step755 p h) (sat_cons (step782 p h) (sat_cons (step785 p h) (sat_cons (step756 p h) (sat_cons (step751 p h) (sat_cons (step90 p h) (sat_cons (step151 p h) (sat_cons (step757 p h) (sat_cons (step762 p h) (sat_cons (step767 p h) (sat_nil p))))))))))))
def c1587 : List Lit := [(1054, true), (975, false), (943, false), (988, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1077, c1240, c1251, c1143, c1147, c1252, c1063, c1241, c1391, c1080] c1587 (by decide) p (sat_cons (step1077 p h) (sat_cons (step1240 p h) (sat_cons (step1251 p h) (sat_cons (step1143 p h) (sat_cons (step1147 p h) (sat_cons (step1252 p h) (sat_cons (step1063 p h) (sat_cons (step1241 p h) (sat_cons (step1391 p h) (sat_cons (step1080 p h) (sat_nil p)))))))))))
end B112E213
