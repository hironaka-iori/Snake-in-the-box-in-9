import B112E168Part0003
namespace B112E168
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1394 : List Lit := [(1414, true)]
theorem step1394 (p : Nat → Bool) (h : Constraints p) : clause p c1394 = true :=
  Snake9.LocalRup.prove_clause [c1393, c1166] c1394 (by decide) p (sat_cons (step1393 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c1395 : List Lit := [(1470, true), (48, false), (10, false), (27, true), (26, false), (24, false)]
theorem step1395 (p : Nat → Bool) (h : Constraints p) : clause p c1395 = true :=
  Snake9.LocalRup.prove_clause [c459, c1190, c1191, c92, c83, c786, c90, c1118, c858, c868, c851, c809, c823, c1219, c177, c210, c818] c1395 (by decide) p (sat_cons (step459 p h) (sat_cons (step1190 p h) (sat_cons (step1191 p h) (sat_cons (step92 p h) (sat_cons (step83 p h) (sat_cons (step786 p h) (sat_cons (step90 p h) (sat_cons (step1118 p h) (sat_cons (step858 p h) (sat_cons (step868 p h) (sat_cons (step851 p h) (sat_cons (step809 p h) (sat_cons (step823 p h) (sat_cons (step1219 p h) (sat_cons (step177 p h) (sat_cons (step210 p h) (sat_cons (step818 p h) (sat_nil p))))))))))))))))))
def c1396 : List Lit := [(1566, true), (91, true), (87, true)]
theorem step1396 (p : Nat → Bool) (h : Constraints p) : clause p c1396 = true :=
  Snake9.LocalRup.prove_clause [c493, c1008, c1012, c1036, c1034, c1013, c1022, c1009, c1014, c1015, c405, c410] c1396 (by decide) p (sat_cons (step493 p h) (sat_cons (step1008 p h) (sat_cons (step1012 p h) (sat_cons (step1036 p h) (sat_cons (step1034 p h) (sat_cons (step1013 p h) (sat_cons (step1022 p h) (sat_cons (step1009 p h) (sat_cons (step1014 p h) (sat_cons (step1015 p h) (sat_cons (step405 p h) (sat_cons (step410 p h) (sat_nil p)))))))))))))
def c1397 : List Lit := [(98, false), (1472, true), (27, true), (26, false), (24, false)]
theorem step1397 (p : Nat → Bool) (h : Constraints p) : clause p c1397 = true :=
  Snake9.LocalRup.prove_clause [c459, c92, c83, c786, c90, c1118, c179, c184, c185, c1219, c817, c828, c809, c822, c830, c870, c848] c1397 (by decide) p (sat_cons (step459 p h) (sat_cons (step92 p h) (sat_cons (step83 p h) (sat_cons (step786 p h) (sat_cons (step90 p h) (sat_cons (step1118 p h) (sat_cons (step179 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step1219 p h) (sat_cons (step817 p h) (sat_cons (step828 p h) (sat_cons (step809 p h) (sat_cons (step822 p h) (sat_cons (step830 p h) (sat_cons (step870 p h) (sat_cons (step848 p h) (sat_nil p))))))))))))))))))
def c1398 : List Lit := [(1456, true), (1501, true)]
theorem step1398 (p : Nat → Bool) (h : Constraints p) : clause p c1398 = true :=
  Snake9.LocalRup.prove_clause [c830, c832, c1292] c1398 (by decide) p (sat_cons (step830 p h) (sat_cons (step832 p h) (sat_cons (step1292 p h) (sat_nil p))))
def c1399 : List Lit := [(1462, true), (1500, true), (18, false), (57, true), (1456, false), (44, true)]
theorem step1399 (p : Nat → Bool) (h : Constraints p) : clause p c1399 = true :=
  Snake9.LocalRup.prove_clause [c478, c933, c828, c821, c844, c848, c1310, c833, c822, c930, c931, c825, c816, c935, c297, c254, c326, c322] c1399 (by decide) p (sat_cons (step478 p h) (sat_cons (step933 p h) (sat_cons (step828 p h) (sat_cons (step821 p h) (sat_cons (step844 p h) (sat_cons (step848 p h) (sat_cons (step1310 p h) (sat_cons (step833 p h) (sat_cons (step822 p h) (sat_cons (step930 p h) (sat_cons (step931 p h) (sat_cons (step825 p h) (sat_cons (step816 p h) (sat_cons (step935 p h) (sat_cons (step297 p h) (sat_cons (step254 p h) (sat_cons (step326 p h) (sat_cons (step322 p h) (sat_nil p)))))))))))))))))))
def c1400 : List Lit := [(1416, true), (8, true)]
theorem step1400 (p : Nat → Bool) (h : Constraints p) : clause p c1400 = true :=
  Snake9.LocalRup.prove_clause [c1393, c1392, c456, c449, c1141, c1147, c687, c694, c1161, c756, c761, c740, c1362, c706, c717, c1158, c715, c680, c49, c6, c81, c3, c534, c503, c540, c514, c541, c523, c545] c1400 (by decide) p (sat_cons (step1393 p h) (sat_cons (step1392 p h) (sat_cons (step456 p h) (sat_cons (step449 p h) (sat_cons (step1141 p h) (sat_cons (step1147 p h) (sat_cons (step687 p h) (sat_cons (step694 p h) (sat_cons (step1161 p h) (sat_cons (step756 p h) (sat_cons (step761 p h) (sat_cons (step740 p h) (sat_cons (step1362 p h) (sat_cons (step706 p h) (sat_cons (step717 p h) (sat_cons (step1158 p h) (sat_cons (step715 p h) (sat_cons (step680 p h) (sat_cons (step49 p h) (sat_cons (step6 p h) (sat_cons (step81 p h) (sat_cons (step3 p h) (sat_cons (step534 p h) (sat_cons (step503 p h) (sat_cons (step540 p h) (sat_cons (step514 p h) (sat_cons (step541 p h) (sat_cons (step523 p h) (sat_cons (step545 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1401 : List Lit := [(47, false), (1490, true), (1456, false), (27, true), (26, false), (24, false), (1530, false)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true :=
  Snake9.LocalRup.prove_clause [c459, c1225, c1393, c1110, c90, c92, c1118, c821, c843, c83, c786, c177, c167, c184, c183, c1219, c687, c1018, c809, c694, c1282, c869, c1067, c906, c767, c711, c1159, c1388, c1400, c900, c899, c870, c1105, c1399, c1087, c1179, c994] c1401 (by decide) p (sat_cons (step459 p h) (sat_cons (step1225 p h) (sat_cons (step1393 p h) (sat_cons (step1110 p h) (sat_cons (step90 p h) (sat_cons (step92 p h) (sat_cons (step1118 p h) (sat_cons (step821 p h) (sat_cons (step843 p h) (sat_cons (step83 p h) (sat_cons (step786 p h) (sat_cons (step177 p h) (sat_cons (step167 p h) (sat_cons (step184 p h) (sat_cons (step183 p h) (sat_cons (step1219 p h) (sat_cons (step687 p h) (sat_cons (step1018 p h) (sat_cons (step809 p h) (sat_cons (step694 p h) (sat_cons (step1282 p h) (sat_cons (step869 p h) (sat_cons (step1067 p h) (sat_cons (step906 p h) (sat_cons (step767 p h) (sat_cons (step711 p h) (sat_cons (step1159 p h) (sat_cons (step1388 p h) (sat_cons (step1400 p h) (sat_cons (step900 p h) (sat_cons (step899 p h) (sat_cons (step870 p h) (sat_cons (step1105 p h) (sat_cons (step1399 p h) (sat_cons (step1087 p h) (sat_cons (step1179 p h) (sat_cons (step994 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c1402 : List Lit := [(1540, false), (1416, false), (1558, false), (1462, false), (1429, false)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c1190, c1110, c1225, c858, c898, c1104, c1282, c1067, c1087, c1088, c1105, c1069, c899, c1224, c864, c793, c808, c795] c1402 (by decide) p (sat_cons (step1190 p h) (sat_cons (step1110 p h) (sat_cons (step1225 p h) (sat_cons (step858 p h) (sat_cons (step898 p h) (sat_cons (step1104 p h) (sat_cons (step1282 p h) (sat_cons (step1067 p h) (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step1105 p h) (sat_cons (step1069 p h) (sat_cons (step899 p h) (sat_cons (step1224 p h) (sat_cons (step864 p h) (sat_cons (step793 p h) (sat_cons (step808 p h) (sat_cons (step795 p h) (sat_nil p)))))))))))))))))))
def c1403 : List Lit := [(1436, true), (27, true)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c795, c797, c793, c1370] c1403 (by decide) p (sat_cons (step795 p h) (sat_cons (step797 p h) (sat_cons (step793 p h) (sat_cons (step1370 p h) (sat_nil p)))))
def c1404 : List Lit := [(1472, true), (1462, false), (1450, false), (27, true), (26, false), (24, false)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c459, c460, c92, c83, c786, c1403, c808, c90, c870, c809, c1219, c178, c828, c812, c865, c787, c849, c781, c782, c833, c93, c825, c96, c127] c1404 (by decide) p (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step92 p h) (sat_cons (step83 p h) (sat_cons (step786 p h) (sat_cons (step1403 p h) (sat_cons (step808 p h) (sat_cons (step90 p h) (sat_cons (step870 p h) (sat_cons (step809 p h) (sat_cons (step1219 p h) (sat_cons (step178 p h) (sat_cons (step828 p h) (sat_cons (step812 p h) (sat_cons (step865 p h) (sat_cons (step787 p h) (sat_cons (step849 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step833 p h) (sat_cons (step93 p h) (sat_cons (step825 p h) (sat_cons (step96 p h) (sat_cons (step127 p h) (sat_nil p)))))))))))))))))))))))))
def c1405 : List Lit := [(1427, true), (52, false), (27, true), (26, false)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c460, c781, c782, c93, c127, c96] c1405 (by decide) p (sat_cons (step460 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step93 p h) (sat_cons (step127 p h) (sat_cons (step96 p h) (sat_nil p)))))))
def c1406 : List Lit := [(52, false), (1437, false), (47, true), (1490, true), (1456, false), (30, true), (44, true), (27, true), (26, false)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c1394, c1393, c817, c822, c848, c886, c1405, c787, c813, c876, c877, c893, c852, c755, c823, c1161, c818, c692, c1238] c1406 (by decide) p (sat_cons (step1394 p h) (sat_cons (step1393 p h) (sat_cons (step817 p h) (sat_cons (step822 p h) (sat_cons (step848 p h) (sat_cons (step886 p h) (sat_cons (step1405 p h) (sat_cons (step787 p h) (sat_cons (step813 p h) (sat_cons (step876 p h) (sat_cons (step877 p h) (sat_cons (step893 p h) (sat_cons (step852 p h) (sat_cons (step755 p h) (sat_cons (step823 p h) (sat_cons (step1161 p h) (sat_cons (step818 p h) (sat_cons (step692 p h) (sat_cons (step1238 p h) (sat_nil p))))))))))))))))))))
def c1407 : List Lit := [(1490, true), (1456, false), (27, true), (26, false), (24, false), (1530, false)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.TreeRup.prove_clause [c459, c1225, c1394, c1110, c1393, c452, c92, c83, c786, c90, c1118, c886, c1401, c817, c822, c848, c1404, c900, c761, c1400, c710, c168, c166, c169, c1159, c828, c1219, c1018, c1388, c809, c1282, c872, c1067, c1311, c1406, c825, c833, c849, c853, c871, c823, c885, c893, c818, c1105, c1167, c755, c1087, c736, c1161, c994, c694, c948, c686, c1227, c25, c24, c59, c208, c722, c724, c730] c1407 (by decide) p (sat_cons (step459 p h) (sat_cons (step1225 p h) (sat_cons (step1394 p h) (sat_cons (step1110 p h) (sat_cons (step1393 p h) (sat_cons (step452 p h) (sat_cons (step92 p h) (sat_cons (step83 p h) (sat_cons (step786 p h) (sat_cons (step90 p h) (sat_cons (step1118 p h) (sat_cons (step886 p h) (sat_cons (step1401 p h) (sat_cons (step817 p h) (sat_cons (step822 p h) (sat_cons (step848 p h) (sat_cons (step1404 p h) (sat_cons (step900 p h) (sat_cons (step761 p h) (sat_cons (step1400 p h) (sat_cons (step710 p h) (sat_cons (step168 p h) (sat_cons (step166 p h) (sat_cons (step169 p h) (sat_cons (step1159 p h) (sat_cons (step828 p h) (sat_cons (step1219 p h) (sat_cons (step1018 p h) (sat_cons (step1388 p h) (sat_cons (step809 p h) (sat_cons (step1282 p h) (sat_cons (step872 p h) (sat_cons (step1067 p h) (sat_cons (step1311 p h) (sat_cons (step1406 p h) (sat_cons (step825 p h) (sat_cons (step833 p h) (sat_cons (step849 p h) (sat_cons (step853 p h) (sat_cons (step871 p h) (sat_cons (step823 p h) (sat_cons (step885 p h) (sat_cons (step893 p h) (sat_cons (step818 p h) (sat_cons (step1105 p h) (sat_cons (step1167 p h) (sat_cons (step755 p h) (sat_cons (step1087 p h) (sat_cons (step736 p h) (sat_cons (step1161 p h) (sat_cons (step994 p h) (sat_cons (step694 p h) (sat_cons (step948 p h) (sat_cons (step686 p h) (sat_cons (step1227 p h) (sat_cons (step25 p h) (sat_cons (step24 p h) (sat_cons (step59 p h) (sat_cons (step208 p h) (sat_cons (step722 p h) (sat_cons (step724 p h) (sat_cons (step730 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1408 : List Lit := [(1378, true), (1610, true), (45, false), (24, false), (1530, false)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c1225, c452, c686, c687, c169, c1018, c1282, c1067, c1083, c990, c945, c1178, c1227, c934, c25, c24, c1113] c1408 (by decide) p (sat_cons (step1225 p h) (sat_cons (step452 p h) (sat_cons (step686 p h) (sat_cons (step687 p h) (sat_cons (step169 p h) (sat_cons (step1018 p h) (sat_cons (step1282 p h) (sat_cons (step1067 p h) (sat_cons (step1083 p h) (sat_cons (step990 p h) (sat_cons (step945 p h) (sat_cons (step1178 p h) (sat_cons (step1227 p h) (sat_cons (step934 p h) (sat_cons (step25 p h) (sat_cons (step24 p h) (sat_cons (step1113 p h) (sat_nil p))))))))))))))))))
def c1409 : List Lit := [(1, false), (3, true)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c1141, c2] c1409 (by decide) p (sat_cons (step1141 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1410 : List Lit := [(1, false), (115, true)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c1141, c3] c1410 (by decide) p (sat_cons (step1141 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1411 : List Lit := [(3, false), (6, true)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c449, c5] c1411 (by decide) p (sat_cons (step449 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1412 : List Lit := [(3, false), (1, true)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c449, c6] c1412 (by decide) p (sat_cons (step449 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1413 : List Lit := [(5, false), (6, true)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c450, c9] c1413 (by decide) p (sat_cons (step450 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1414 : List Lit := [(5, false), (4, true)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c450, c10] c1414 (by decide) p (sat_cons (step450 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1415 : List Lit := [(8, false), (45, true)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c451, c19] c1415 (by decide) p (sat_cons (step451 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1416 : List Lit := [(8, false), (7, true)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c451, c20] c1416 (by decide) p (sat_cons (step451 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1417 : List Lit := [(48, true), (71, true), (10, false)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c452, c24] c1417 (by decide) p (sat_cons (step452 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1418 : List Lit := [(19, true), (71, true), (10, false)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c452, c25] c1418 (by decide) p (sat_cons (step452 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1419 : List Lit := [(19, true), (48, true), (10, false)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c452, c26] c1419 (by decide) p (sat_cons (step452 p h) (sat_cons (step26 p h) (sat_nil p)))
def c1420 : List Lit := [(49, true), (13, true), (11, false), (20, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c453, c29] c1420 (by decide) p (sat_cons (step453 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1421 : List Lit := [(49, true), (20, true), (7, true), (11, false)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c453, c30] c1421 (by decide) p (sat_cons (step453 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1422 : List Lit := [(13, true), (20, true), (7, true), (11, false)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c453, c31] c1422 (by decide) p (sat_cons (step453 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1423 : List Lit := [(13, true), (50, true), (12, false)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c454, c33] c1423 (by decide) p (sat_cons (step454 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1424 : List Lit := [(9, true), (50, true), (12, false)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c454, c34] c1424 (by decide) p (sat_cons (step454 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1425 : List Lit := [(13, true), (9, true), (12, false)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c454, c35] c1425 (by decide) p (sat_cons (step454 p h) (sat_cons (step35 p h) (sat_nil p)))
def c1426 : List Lit := [(14, true), (16, true), (15, false)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c455, c43] c1426 (by decide) p (sat_cons (step455 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1427 : List Lit := [(9, true), (16, true), (15, false)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c455, c44] c1427 (by decide) p (sat_cons (step455 p h) (sat_cons (step44 p h) (sat_nil p)))
def c1428 : List Lit := [(9, true), (14, true), (15, false)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c455, c45] c1428 (by decide) p (sat_cons (step455 p h) (sat_cons (step45 p h) (sat_nil p)))
def c1429 : List Lit := [(17, false), (22, true)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c456, c49] c1429 (by decide) p (sat_cons (step456 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1430 : List Lit := [(17, false), (16, true)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c456, c50] c1430 (by decide) p (sat_cons (step456 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1431 : List Lit := [(19, true), (59, true), (14, true), (20, true), (18, false)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c457, c57] c1431 (by decide) p (sat_cons (step457 p h) (sat_cons (step57 p h) (sat_nil p)))
def c1432 : List Lit := [(19, true), (4, true), (18, false), (59, true), (20, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c457, c58] c1432 (by decide) p (sat_cons (step457 p h) (sat_cons (step58 p h) (sat_nil p)))
def c1433 : List Lit := [(22, true), (21, false), (20, true)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c458, c78] c1433 (by decide) p (sat_cons (step458 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1434 : List Lit := [(19, true), (21, false), (20, true)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c458, c79] c1434 (by decide) p (sat_cons (step458 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1435 : List Lit := [(27, true), (45, true), (24, false)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c459, c90] c1435 (by decide) p (sat_cons (step459 p h) (sat_cons (step90 p h) (sat_nil p)))
def c1436 : List Lit := [(23, true), (45, true), (24, false)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c459, c91] c1436 (by decide) p (sat_cons (step459 p h) (sat_cons (step91 p h) (sat_nil p)))
def c1437 : List Lit := [(27, true), (23, true), (24, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c459, c92] c1437 (by decide) p (sat_cons (step459 p h) (sat_cons (step92 p h) (sat_nil p)))
def c1438 : List Lit := [(25, true), (32, true), (26, false), (27, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c460, c96] c1438 (by decide) p (sat_cons (step460 p h) (sat_cons (step96 p h) (sat_nil p)))
def c1439 : List Lit := [(25, true), (32, true), (23, true), (26, false)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c460, c97] c1439 (by decide) p (sat_cons (step460 p h) (sat_cons (step97 p h) (sat_nil p)))
def c1440 : List Lit := [(28, true), (86, true), (29, false), (48, true)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c461, c114] c1440 (by decide) p (sat_cons (step461 p h) (sat_cons (step114 p h) (sat_nil p)))
def c1441 : List Lit := [(28, true), (86, true), (29, false), (37, true)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c461, c115] c1441 (by decide) p (sat_cons (step461 p h) (sat_cons (step115 p h) (sat_nil p)))
def c1442 : List Lit := [(28, true), (48, true), (29, false), (37, true)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c461, c116] c1442 (by decide) p (sat_cons (step461 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1443 : List Lit := [(38, true), (28, true), (30, false), (23, true), (49, true)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c462, c119] c1443 (by decide) p (sat_cons (step462 p h) (sat_cons (step119 p h) (sat_nil p)))
def c1444 : List Lit := [(32, true), (23, true), (38, true), (28, true), (30, false)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c462, c120] c1444 (by decide) p (sat_cons (step462 p h) (sat_cons (step120 p h) (sat_nil p)))
def c1445 : List Lit := [(32, true), (28, true), (31, false), (50, true)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c463, c122] c1445 (by decide) p (sat_cons (step463 p h) (sat_cons (step122 p h) (sat_nil p)))
def c1446 : List Lit := [(32, true), (25, true), (31, false), (50, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c463, c123] c1446 (by decide) p (sat_cons (step463 p h) (sat_cons (step123 p h) (sat_nil p)))
def c1447 : List Lit := [(28, true), (50, true), (31, false), (25, true)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c463, c124] c1447 (by decide) p (sat_cons (step463 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1448 : List Lit := [(25, true), (28, true), (32, true), (31, false)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c463, c125] c1448 (by decide) p (sat_cons (step463 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1449 : List Lit := [(35, true), (33, true), (34, false)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c464, c132] c1449 (by decide) p (sat_cons (step464 p h) (sat_cons (step132 p h) (sat_nil p)))
def c1450 : List Lit := [(25, true), (35, true), (34, false)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c464, c133] c1450 (by decide) p (sat_cons (step464 p h) (sat_cons (step133 p h) (sat_nil p)))
def c1451 : List Lit := [(35, true), (41, true), (36, false)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c465, c137] c1451 (by decide) p (sat_cons (step465 p h) (sat_cons (step137 p h) (sat_nil p)))
def c1452 : List Lit := [(41, true), (36, false), (27, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c465, c138] c1452 (by decide) p (sat_cons (step465 p h) (sat_cons (step138 p h) (sat_nil p)))
def c1453 : List Lit := [(41, true), (38, true), (39, false)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c466, c147] c1453 (by decide) p (sat_cons (step466 p h) (sat_cons (step147 p h) (sat_nil p)))
def c1454 : List Lit := [(37, true), (41, true), (39, false)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c466, c148] c1454 (by decide) p (sat_cons (step466 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1455 : List Lit := [(37, true), (38, true), (39, false)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c466, c149] c1455 (by decide) p (sat_cons (step466 p h) (sat_cons (step149 p h) (sat_nil p)))
def c1456 : List Lit := [(55, true), (42, true), (43, false), (48, true), (45, true)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c468, c157] c1456 (by decide) p (sat_cons (step468 p h) (sat_cons (step157 p h) (sat_nil p)))
def c1457 : List Lit := [(46, true), (42, true), (43, false), (45, true), (48, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c468, c158] c1457 (by decide) p (sat_cons (step468 p h) (sat_cons (step158 p h) (sat_nil p)))
end B112E168
