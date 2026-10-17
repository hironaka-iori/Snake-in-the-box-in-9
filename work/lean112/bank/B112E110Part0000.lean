import B112E110Inputs
namespace B112E110
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1301 : List Lit := [(53, true)]
theorem step1301 (p : Nat → Bool) (h : Constraints p) : clause p c1301 = true :=
  Snake9.LocalRup.prove_clause [c197, c196] c1301 (by decide) p (sat_cons (step197 p h) (sat_cons (step196 p h) (sat_nil p)))
def c1302 : List Lit := [(2, false)]
theorem step1302 (p : Nat → Bool) (h : Constraints p) : clause p c1302 = true :=
  Snake9.LocalRup.prove_clause [c568, c8] c1302 (by decide) p (sat_cons (step568 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1303 : List Lit := [(5, false)]
theorem step1303 (p : Nat → Bool) (h : Constraints p) : clause p c1303 = true :=
  Snake9.LocalRup.prove_clause [c570, c13] c1303 (by decide) p (sat_cons (step570 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1304 : List Lit := [(466, false)]
theorem step1304 (p : Nat → Bool) (h : Constraints p) : clause p c1304 = true :=
  Snake9.LocalRup.prove_clause [c776, c773] c1304 (by decide) p (sat_cons (step776 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1305 : List Lit := [(350, false)]
theorem step1305 (p : Nat → Bool) (h : Constraints p) : clause p c1305 = true :=
  Snake9.LocalRup.prove_clause [c776, c775] c1305 (by decide) p (sat_cons (step776 p h) (sat_cons (step775 p h) (sat_nil p)))
def c1306 : List Lit := [(464, false)]
theorem step1306 (p : Nat → Bool) (h : Constraints p) : clause p c1306 = true :=
  Snake9.LocalRup.prove_clause [c1304, c770] c1306 (by decide) p (sat_cons (step1304 p h) (sat_cons (step770 p h) (sat_nil p)))
def c1307 : List Lit := [(348, false)]
theorem step1307 (p : Nat → Bool) (h : Constraints p) : clause p c1307 = true :=
  Snake9.LocalRup.prove_clause [c1305, c704] c1307 (by decide) p (sat_cons (step1305 p h) (sat_cons (step704 p h) (sat_nil p)))
def c1308 : List Lit := [(292, false)]
theorem step1308 (p : Nat → Bool) (h : Constraints p) : clause p c1308 = true :=
  Snake9.LocalRup.prove_clause [c1305, c707] c1308 (by decide) p (sat_cons (step1305 p h) (sat_cons (step707 p h) (sat_nil p)))
def c1309 : List Lit := [(434, false)]
theorem step1309 (p : Nat → Bool) (h : Constraints p) : clause p c1309 = true :=
  Snake9.LocalRup.prove_clause [c1306, c768] c1309 (by decide) p (sat_cons (step1306 p h) (sat_cons (step768 p h) (sat_nil p)))
def c1310 : List Lit := [(290, false)]
theorem step1310 (p : Nat → Bool) (h : Constraints p) : clause p c1310 = true :=
  Snake9.LocalRup.prove_clause [c1308, c663] c1310 (by decide) p (sat_cons (step1308 p h) (sat_cons (step663 p h) (sat_nil p)))
def c1311 : List Lit := [(262, false)]
theorem step1311 (p : Nat → Bool) (h : Constraints p) : clause p c1311 = true :=
  Snake9.LocalRup.prove_clause [c1308, c666] c1311 (by decide) p (sat_cons (step1308 p h) (sat_cons (step666 p h) (sat_nil p)))
def c1312 : List Lit := [(274, false)]
theorem step1312 (p : Nat → Bool) (h : Constraints p) : clause p c1312 = true :=
  Snake9.LocalRup.prove_clause [c1310, c661] c1312 (by decide) p (sat_cons (step1310 p h) (sat_cons (step661 p h) (sat_nil p)))
def c1313 : List Lit := [(260, false)]
theorem step1313 (p : Nat → Bool) (h : Constraints p) : clause p c1313 = true :=
  Snake9.LocalRup.prove_clause [c1311, c636] c1313 (by decide) p (sat_cons (step1311 p h) (sat_cons (step636 p h) (sat_nil p)))
def c1314 : List Lit := [(248, false)]
theorem step1314 (p : Nat → Bool) (h : Constraints p) : clause p c1314 = true :=
  Snake9.LocalRup.prove_clause [c1311, c639] c1314 (by decide) p (sat_cons (step1311 p h) (sat_cons (step639 p h) (sat_nil p)))
def c1315 : List Lit := [(240, false)]
theorem step1315 (p : Nat → Bool) (h : Constraints p) : clause p c1315 = true :=
  Snake9.LocalRup.prove_clause [c1314, c626] c1315 (by decide) p (sat_cons (step1314 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1316 : List Lit := [(1413, true)]
theorem step1316 (p : Nat → Bool) (h : Constraints p) : clause p c1316 = true :=
  Snake9.LocalRup.prove_clause [c1303, c777] c1316 (by decide) p (sat_cons (step1303 p h) (sat_cons (step777 p h) (sat_nil p)))
def c1317 : List Lit := [(4, true), (1414, true)]
theorem step1317 (p : Nat → Bool) (h : Constraints p) : clause p c1317 = true :=
  Snake9.LocalRup.prove_clause [c1303, c778] c1317 (by decide) p (sat_cons (step1303 p h) (sat_cons (step778 p h) (sat_nil p)))
def c1318 : List Lit := [(1415, true)]
theorem step1318 (p : Nat → Bool) (h : Constraints p) : clause p c1318 = true :=
  Snake9.LocalRup.prove_clause [c1316, c779] c1318 (by decide) p (sat_cons (step1316 p h) (sat_cons (step779 p h) (sat_nil p)))
def c1319 : List Lit := [(1416, true)]
theorem step1319 (p : Nat → Bool) (h : Constraints p) : clause p c1319 = true :=
  Snake9.LocalRup.prove_clause [c1302, c1316, c780] c1319 (by decide) p (sat_cons (step1302 p h) (sat_cons (step1316 p h) (sat_cons (step780 p h) (sat_nil p))))
def c1320 : List Lit := [(1414, false), (1417, true)]
theorem step1320 (p : Nat → Bool) (h : Constraints p) : clause p c1320 = true :=
  Snake9.LocalRup.prove_clause [c1302, c781] c1320 (by decide) p (sat_cons (step1302 p h) (sat_cons (step781 p h) (sat_nil p)))
def c1321 : List Lit := [(1423, false), (1428, true)]
theorem step1321 (p : Nat → Bool) (h : Constraints p) : clause p c1321 = true :=
  Snake9.LocalRup.prove_clause [c1318, c794] c1321 (by decide) p (sat_cons (step1318 p h) (sat_cons (step794 p h) (sat_nil p)))
def c1322 : List Lit := [(1427, true)]
theorem step1322 (p : Nat → Bool) (h : Constraints p) : clause p c1322 = true :=
  Snake9.LocalRup.prove_clause [c1319, c795] c1322 (by decide) p (sat_cons (step1319 p h) (sat_cons (step795 p h) (sat_nil p)))
def c1323 : List Lit := [(1422, false), (1428, true)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true :=
  Snake9.LocalRup.prove_clause [c1319, c796] c1323 (by decide) p (sat_cons (step1319 p h) (sat_cons (step796 p h) (sat_nil p)))
def c1324 : List Lit := [(1423, false), (1429, true)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true :=
  Snake9.LocalRup.prove_clause [c1319, c797] c1324 (by decide) p (sat_cons (step1319 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1325 : List Lit := [(1424, false), (1430, true)]
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true :=
  Snake9.LocalRup.prove_clause [c1319, c798] c1325 (by decide) p (sat_cons (step1319 p h) (sat_cons (step798 p h) (sat_nil p)))
def c1326 : List Lit := [(1458, true)]
theorem step1326 (p : Nat → Bool) (h : Constraints p) : clause p c1326 = true :=
  Snake9.LocalRup.prove_clause [c1322, c847] c1326 (by decide) p (sat_cons (step1322 p h) (sat_cons (step847 p h) (sat_nil p)))
def c1327 : List Lit := [(1449, false), (1459, true)]
theorem step1327 (p : Nat → Bool) (h : Constraints p) : clause p c1327 = true :=
  Snake9.LocalRup.prove_clause [c1322, c848] c1327 (by decide) p (sat_cons (step1322 p h) (sat_cons (step848 p h) (sat_nil p)))
def c1328 : List Lit := [(1450, false), (1460, true)]
theorem step1328 (p : Nat → Bool) (h : Constraints p) : clause p c1328 = true :=
  Snake9.LocalRup.prove_clause [c1322, c849] c1328 (by decide) p (sat_cons (step1322 p h) (sat_cons (step849 p h) (sat_nil p)))
def c1329 : List Lit := [(1451, false), (1461, true)]
theorem step1329 (p : Nat → Bool) (h : Constraints p) : clause p c1329 = true :=
  Snake9.LocalRup.prove_clause [c1322, c850] c1329 (by decide) p (sat_cons (step1322 p h) (sat_cons (step850 p h) (sat_nil p)))
def c1330 : List Lit := [(1452, false), (1462, true)]
theorem step1330 (p : Nat → Bool) (h : Constraints p) : clause p c1330 = true :=
  Snake9.LocalRup.prove_clause [c1322, c851] c1330 (by decide) p (sat_cons (step1322 p h) (sat_cons (step851 p h) (sat_nil p)))
def c1331 : List Lit := [(1453, false), (1463, true)]
theorem step1331 (p : Nat → Bool) (h : Constraints p) : clause p c1331 = true :=
  Snake9.LocalRup.prove_clause [c1322, c852] c1331 (by decide) p (sat_cons (step1322 p h) (sat_cons (step852 p h) (sat_nil p)))
def c1332 : List Lit := [(1454, false), (1464, true)]
theorem step1332 (p : Nat → Bool) (h : Constraints p) : clause p c1332 = true :=
  Snake9.LocalRup.prove_clause [c1322, c853] c1332 (by decide) p (sat_cons (step1322 p h) (sat_cons (step853 p h) (sat_nil p)))
def c1333 : List Lit := [(1519, false), (1536, true)]
theorem step1333 (p : Nat → Bool) (h : Constraints p) : clause p c1333 = true :=
  Snake9.LocalRup.prove_clause [c1326, c958] c1333 (by decide) p (sat_cons (step1326 p h) (sat_cons (step958 p h) (sat_nil p)))
def c1334 : List Lit := [(1553, true)]
theorem step1334 (p : Nat → Bool) (h : Constraints p) : clause p c1334 = true :=
  Snake9.LocalRup.prove_clause [c597, c995, c997, c992, c993, c208, c203] c1334 (by decide) p (sat_cons (step597 p h) (sat_cons (step995 p h) (sat_cons (step997 p h) (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step208 p h) (sat_cons (step203 p h) (sat_nil p))))))))
def c1335 : List Lit := [(1564, true)]
theorem step1335 (p : Nat → Bool) (h : Constraints p) : clause p c1335 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1013] c1335 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1013 p h) (sat_nil p)))
def c1336 : List Lit := [(1587, true)]
theorem step1336 (p : Nat → Bool) (h : Constraints p) : clause p c1336 = true :=
  Snake9.LocalRup.prove_clause [c610, c1050, c1054, c1042, c1044, c1028, c1039, c1040, c1036, c1037, c1025, c321, c326, c296, c333] c1336 (by decide) p (sat_cons (step610 p h) (sat_cons (step1050 p h) (sat_cons (step1054 p h) (sat_cons (step1042 p h) (sat_cons (step1044 p h) (sat_cons (step1028 p h) (sat_cons (step1039 p h) (sat_cons (step1040 p h) (sat_cons (step1036 p h) (sat_cons (step1037 p h) (sat_cons (step1025 p h) (sat_cons (step321 p h) (sat_cons (step326 p h) (sat_cons (step296 p h) (sat_cons (step333 p h) (sat_nil p))))))))))))))))
def c1337 : List Lit := [(1596, true)]
theorem step1337 (p : Nat → Bool) (h : Constraints p) : clause p c1337 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1335, c1071] c1337 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1335 p h) (sat_cons (step1071 p h) (sat_nil p))))
def c1338 : List Lit := [(1583, true), (88, false), (1574, true)]
theorem step1338 (p : Nat → Bool) (h : Constraints p) : clause p c1338 = true :=
  Snake9.LocalRup.prove_clause [c610, c605, c1042, c1044, c1039, c1040, c1036, c1037, c321, c326, c333, c296, c1027, c261, c292, c274] c1338 (by decide) p (sat_cons (step610 p h) (sat_cons (step605 p h) (sat_cons (step1042 p h) (sat_cons (step1044 p h) (sat_cons (step1039 p h) (sat_cons (step1040 p h) (sat_cons (step1036 p h) (sat_cons (step1037 p h) (sat_cons (step321 p h) (sat_cons (step326 p h) (sat_cons (step333 p h) (sat_cons (step296 p h) (sat_cons (step1027 p h) (sat_cons (step261 p h) (sat_cons (step292 p h) (sat_cons (step274 p h) (sat_nil p)))))))))))))))))
def c1339 : List Lit := [(40, false), (84, false), (64, false), (1419, true)]
theorem step1339 (p : Nat → Bool) (h : Constraints p) : clause p c1339 = true :=
  Snake9.LocalRup.prove_clause [c600, c451, c219, c25, c26, c784] c1339 (by decide) p (sat_cons (step600 p h) (sat_cons (step451 p h) (sat_cons (step219 p h) (sat_cons (step25 p h) (sat_cons (step26 p h) (sat_cons (step784 p h) (sat_nil p)))))))
def c1340 : List Lit := [(1494, true), (1481, true)]
theorem step1340 (p : Nat → Bool) (h : Constraints p) : clause p c1340 = true :=
  Snake9.LocalRup.prove_clause [c592, c889, c881, c887, c885, c913, c914, c185, c142, c181] c1340 (by decide) p (sat_cons (step592 p h) (sat_cons (step889 p h) (sat_cons (step881 p h) (sat_cons (step887 p h) (sat_cons (step885 p h) (sat_cons (step913 p h) (sat_cons (step914 p h) (sat_cons (step185 p h) (sat_cons (step142 p h) (sat_cons (step181 p h) (sat_nil p)))))))))))
def c1341 : List Lit := [(48, false), (50, true), (1481, true)]
theorem step1341 (p : Nat → Bool) (h : Constraints p) : clause p c1341 = true :=
  Snake9.LocalRup.prove_clause [c592, c889, c881, c887, c885, c142, c181] c1341 (by decide) p (sat_cons (step592 p h) (sat_cons (step889 p h) (sat_cons (step881 p h) (sat_cons (step887 p h) (sat_cons (step885 p h) (sat_cons (step142 p h) (sat_cons (step181 p h) (sat_nil p))))))))
def c1342 : List Lit := [(7, false), (1419, true), (64, false), (40, false)]
theorem step1342 (p : Nat → Bool) (h : Constraints p) : clause p c1342 = true :=
  Snake9.LocalRup.prove_clause [c25, c26, c784] c1342 (by decide) p (sat_cons (step25 p h) (sat_cons (step26 p h) (sat_cons (step784 p h) (sat_nil p))))
def c1343 : List Lit := [(1571, true), (74, false), (64, false)]
theorem step1343 (p : Nat → Bool) (h : Constraints p) : clause p c1343 = true :=
  Snake9.LocalRup.prove_clause [c1022, c1023, c249] c1343 (by decide) p (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step249 p h) (sat_nil p))))
def c1344 : List Lit := [(1418, false), (1461, true), (1445, false), (16, false)]
theorem step1344 (p : Nat → Bool) (h : Constraints p) : clause p c1344 = true :=
  Snake9.LocalRup.prove_clause [c576, c830, c861, c1324, c49, c789, c790, c1323, c785, c856, c45, c834, c804, c811] c1344 (by decide) p (sat_cons (step576 p h) (sat_cons (step830 p h) (sat_cons (step861 p h) (sat_cons (step1324 p h) (sat_cons (step49 p h) (sat_cons (step789 p h) (sat_cons (step790 p h) (sat_cons (step1323 p h) (sat_cons (step785 p h) (sat_cons (step856 p h) (sat_cons (step45 p h) (sat_cons (step834 p h) (sat_cons (step804 p h) (sat_cons (step811 p h) (sat_nil p)))))))))))))))
def c1345 : List Lit := [(20, true), (22, true), (1452, true), (1443, false), (23, false), (40, false)]
theorem step1345 (p : Nat → Bool) (h : Constraints p) : clause p c1345 = true :=
  Snake9.LocalRup.prove_clause [c817, c825, c840, c810, c806, c808, c809, c80, c836, c818, c828] c1345 (by decide) p (sat_cons (step817 p h) (sat_cons (step825 p h) (sat_cons (step840 p h) (sat_cons (step810 p h) (sat_cons (step806 p h) (sat_cons (step808 p h) (sat_cons (step809 p h) (sat_cons (step80 p h) (sat_cons (step836 p h) (sat_cons (step818 p h) (sat_cons (step828 p h) (sat_nil p))))))))))))
def c1346 : List Lit := [(1632, false), (1649, true), (115, true), (107, true), (1481, true)]
theorem step1346 (p : Nat → Bool) (h : Constraints p) : clause p c1346 = true :=
  Snake9.LocalRup.prove_clause [c589, c1150, c1152, c1175, c1132, c889, c881, c887, c884, c1141, c1144, c1171, c1134, c1153, c149, c1151, c153, c484] c1346 (by decide) p (sat_cons (step589 p h) (sat_cons (step1150 p h) (sat_cons (step1152 p h) (sat_cons (step1175 p h) (sat_cons (step1132 p h) (sat_cons (step889 p h) (sat_cons (step881 p h) (sat_cons (step887 p h) (sat_cons (step884 p h) (sat_cons (step1141 p h) (sat_cons (step1144 p h) (sat_cons (step1171 p h) (sat_cons (step1134 p h) (sat_cons (step1153 p h) (sat_cons (step149 p h) (sat_cons (step1151 p h) (sat_cons (step153 p h) (sat_cons (step484 p h) (sat_nil p)))))))))))))))))))
def c1347 : List Lit := [(1492, true), (44, false), (13, false)]
theorem step1347 (p : Nat → Bool) (h : Constraints p) : clause p c1347 = true :=
  Snake9.LocalRup.prove_clause [c910, c911, c161] c1347 (by decide) p (sat_cons (step910 p h) (sat_cons (step911 p h) (sat_cons (step161 p h) (sat_nil p))))
def c1348 : List Lit := [(7, false), (1419, true), (4, false), (40, false)]
theorem step1348 (p : Nat → Bool) (h : Constraints p) : clause p c1348 = true :=
  Snake9.LocalRup.prove_clause [c18, c20, c784] c1348 (by decide) p (sat_cons (step18 p h) (sat_cons (step20 p h) (sat_cons (step784 p h) (sat_nil p))))
def c1349 : List Lit := [(20, true), (1436, true), (1452, true), (1443, false), (23, false), (40, false)]
theorem step1349 (p : Nat → Bool) (h : Constraints p) : clause p c1349 = true :=
  Snake9.LocalRup.prove_clause [c808, c1345, c78] c1349 (by decide) p (sat_cons (step808 p h) (sat_cons (step1345 p h) (sat_cons (step78 p h) (sat_nil p))))
def c1350 : List Lit := [(20, true), (1452, true), (40, false), (1443, false), (23, false)]
theorem step1350 (p : Nat → Bool) (h : Constraints p) : clause p c1350 = true :=
  Snake9.LocalRup.prove_clause [c1345, c1349, c83, c810, c816, c840, c825] c1350 (by decide) p (sat_cons (step1345 p h) (sat_cons (step1349 p h) (sat_cons (step83 p h) (sat_cons (step810 p h) (sat_cons (step816 p h) (sat_cons (step840 p h) (sat_cons (step825 p h) (sat_nil p))))))))
def c1351 : List Lit := [(115, true), (1643, true), (1632, false), (1649, true), (95, false), (1481, true)]
theorem step1351 (p : Nat → Bool) (h : Constraints p) : clause p c1351 = true :=
  Snake9.LocalRup.prove_clause [c620, c1153, c887, c884, c1150, c1346, c1151, c1155, c564, c485, c1146, c561, c562, c1300] c1351 (by decide) p (sat_cons (step620 p h) (sat_cons (step1153 p h) (sat_cons (step887 p h) (sat_cons (step884 p h) (sat_cons (step1150 p h) (sat_cons (step1346 p h) (sat_cons (step1151 p h) (sat_cons (step1155 p h) (sat_cons (step564 p h) (sat_cons (step485 p h) (sat_cons (step1146 p h) (sat_cons (step561 p h) (sat_cons (step562 p h) (sat_cons (step1300 p h) (sat_nil p)))))))))))))))
def c1352 : List Lit := [(1617, true), (96, false), (97, false)]
theorem step1352 (p : Nat → Bool) (h : Constraints p) : clause p c1352 = true :=
  Snake9.LocalRup.prove_clause [c1104, c1105, c407] c1352 (by decide) p (sat_cons (step1104 p h) (sat_cons (step1105 p h) (sat_cons (step407 p h) (sat_nil p))))
def c1353 : List Lit := [(115, true), (1632, false), (1649, true), (95, false), (1481, true)]
theorem step1353 (p : Nat → Bool) (h : Constraints p) : clause p c1353 = true :=
  Snake9.LocalRup.prove_clause [c589, c889, c881, c887, c884, c1346, c1351, c1171, c1141, c1133, c483, c149, c153] c1353 (by decide) p (sat_cons (step589 p h) (sat_cons (step889 p h) (sat_cons (step881 p h) (sat_cons (step887 p h) (sat_cons (step884 p h) (sat_cons (step1346 p h) (sat_cons (step1351 p h) (sat_cons (step1171 p h) (sat_cons (step1141 p h) (sat_cons (step1133 p h) (sat_cons (step483 p h) (sat_cons (step149 p h) (sat_cons (step153 p h) (sat_nil p))))))))))))))
def c1354 : List Lit := [(88, false), (80, true), (95, false)]
theorem step1354 (p : Nat → Bool) (h : Constraints p) : clause p c1354 = true :=
  Snake9.LocalRup.prove_clause [c611, c338, c339, c1288] c1354 (by decide) p (sat_cons (step611 p h) (sat_cons (step338 p h) (sat_cons (step339 p h) (sat_cons (step1288 p h) (sat_nil p)))))
def c1355 : List Lit := [(1557, false), (1567, true), (193, true), (113, false), (102, true), (59, true), (60, true)]
theorem step1355 (p : Nat → Bool) (h : Constraints p) : clause p c1355 = true :=
  Snake9.LocalRup.prove_clause [c1334, c602, c599, c1016, c1011, c1012, c1019, c1004, c998, c229, c992, c256, c217, c238] c1355 (by decide) p (sat_cons (step1334 p h) (sat_cons (step602 p h) (sat_cons (step599 p h) (sat_cons (step1016 p h) (sat_cons (step1011 p h) (sat_cons (step1012 p h) (sat_cons (step1019 p h) (sat_cons (step1004 p h) (sat_cons (step998 p h) (sat_cons (step229 p h) (sat_cons (step992 p h) (sat_cons (step256 p h) (sat_cons (step217 p h) (sat_cons (step238 p h) (sat_nil p)))))))))))))))
def c1356 : List Lit := [(1579, true), (86, false), (84, false), (102, true), (76, true)]
theorem step1356 (p : Nat → Bool) (h : Constraints p) : clause p c1356 = true :=
  Snake9.LocalRup.prove_clause [c608, c1036, c1037, c321, c326, c302] c1356 (by decide) p (sat_cons (step608 p h) (sat_cons (step1036 p h) (sat_cons (step1037 p h) (sat_cons (step321 p h) (sat_cons (step326 p h) (sat_cons (step302 p h) (sat_nil p)))))))
def c1357 : List Lit := [(63, true), (1566, true), (59, true), (60, true)]
theorem step1357 (p : Nat → Bool) (h : Constraints p) : clause p c1357 = true :=
  Snake9.LocalRup.prove_clause [c598, c1020, c999, c992, c994, c998, c211, c212, c1018, c1274, c1008, c1000] c1357 (by decide) p (sat_cons (step598 p h) (sat_cons (step1020 p h) (sat_cons (step999 p h) (sat_cons (step992 p h) (sat_cons (step994 p h) (sat_cons (step998 p h) (sat_cons (step211 p h) (sat_cons (step212 p h) (sat_cons (step1018 p h) (sat_cons (step1274 p h) (sat_cons (step1008 p h) (sat_cons (step1000 p h) (sat_nil p)))))))))))))
def c1358 : List Lit := [(74, false), (1572, true), (75, false), (71, false)]
theorem step1358 (p : Nat → Bool) (h : Constraints p) : clause p c1358 = true :=
  Snake9.LocalRup.prove_clause [c596, c776, c1301, c595, c240, c1024, c256, c246, c720, c202, c721, c723, c731, c732, c771, c774, c703, c700, c698, c696, c697, c695, c689, c691, c688, c201, c195, c198] c1358 (by decide) p (sat_cons (step596 p h) (sat_cons (step776 p h) (sat_cons (step1301 p h) (sat_cons (step595 p h) (sat_cons (step240 p h) (sat_cons (step1024 p h) (sat_cons (step256 p h) (sat_cons (step246 p h) (sat_cons (step720 p h) (sat_cons (step202 p h) (sat_cons (step721 p h) (sat_cons (step723 p h) (sat_cons (step731 p h) (sat_cons (step732 p h) (sat_cons (step771 p h) (sat_cons (step774 p h) (sat_cons (step703 p h) (sat_cons (step700 p h) (sat_cons (step698 p h) (sat_cons (step696 p h) (sat_cons (step697 p h) (sat_cons (step695 p h) (sat_cons (step689 p h) (sat_cons (step691 p h) (sat_cons (step688 p h) (sat_cons (step201 p h) (sat_cons (step195 p h) (sat_cons (step198 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1359 : List Lit := [(1418, true), (7, false), (64, false)]
theorem step1359 (p : Nat → Bool) (h : Constraints p) : clause p c1359 = true :=
  Snake9.LocalRup.prove_clause [c782, c783, c24] c1359 (by decide) p (sat_cons (step782 p h) (sat_cons (step783 p h) (sat_cons (step24 p h) (sat_nil p))))
def c1360 : List Lit := [(1423, true), (130, true), (7, false), (64, false)]
theorem step1360 (p : Nat → Bool) (h : Constraints p) : clause p c1360 = true :=
  Snake9.LocalRup.prove_clause [c573, c1359, c792, c790, c786, c34, c38, c21, c19, c784] c1360 (by decide) p (sat_cons (step573 p h) (sat_cons (step1359 p h) (sat_cons (step792 p h) (sat_cons (step790 p h) (sat_cons (step786 p h) (sat_cons (step34 p h) (sat_cons (step38 p h) (sat_cons (step21 p h) (sat_cons (step19 p h) (sat_cons (step784 p h) (sat_nil p)))))))))))
def c1361 : List Lit := [(1648, true), (104, true), (103, false), (1638, false), (64, false)]
theorem step1361 (p : Nat → Bool) (h : Constraints p) : clause p c1361 = true :=
  Snake9.LocalRup.prove_clause [c1133, c1140, c1154, c1170, c1166, c1143, c1155, c1134, c1150, c466] c1361 (by decide) p (sat_cons (step1133 p h) (sat_cons (step1140 p h) (sat_cons (step1154 p h) (sat_cons (step1170 p h) (sat_cons (step1166 p h) (sat_cons (step1143 p h) (sat_cons (step1155 p h) (sat_cons (step1134 p h) (sat_cons (step1150 p h) (sat_cons (step466 p h) (sat_nil p)))))))))))
def c1362 : List Lit := [(1630, false), (115, true), (1649, true), (96, false), (104, false), (113, true), (1638, false)]
theorem step1362 (p : Nat → Bool) (h : Constraints p) : clause p c1362 = true :=
  Snake9.LocalRup.prove_clause [c618, c1150, c1155, c1171, c1140, c1141, c1167, c1135, c1136, c1156, c1158, c505, c1151, c1148, c523, c555] c1362 (by decide) p (sat_cons (step618 p h) (sat_cons (step1150 p h) (sat_cons (step1155 p h) (sat_cons (step1171 p h) (sat_cons (step1140 p h) (sat_cons (step1141 p h) (sat_cons (step1167 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step505 p h) (sat_cons (step1151 p h) (sat_cons (step1148 p h) (sat_cons (step523 p h) (sat_cons (step555 p h) (sat_nil p)))))))))))))))))
def c1363 : List Lit := [(95, false), (1612, true)]
theorem step1363 (p : Nat → Bool) (h : Constraints p) : clause p c1363 = true :=
  Snake9.LocalRup.prove_clause [c611, c1096, c1094, c1093, c1098, c360, c343, c337] c1363 (by decide) p (sat_cons (step611 p h) (sat_cons (step1096 p h) (sat_cons (step1094 p h) (sat_cons (step1093 p h) (sat_cons (step1098 p h) (sat_cons (step360 p h) (sat_cons (step343 p h) (sat_cons (step337 p h) (sat_nil p)))))))))
def c1364 : List Lit := [(1649, true), (115, true), (107, true), (96, false), (113, true), (1638, false)]
theorem step1364 (p : Nat → Bool) (h : Constraints p) : clause p c1364 = true :=
  Snake9.LocalRup.prove_clause [c1150, c1155, c1132, c1362, c1171, c1134, c1143] c1364 (by decide) p (sat_cons (step1150 p h) (sat_cons (step1155 p h) (sat_cons (step1132 p h) (sat_cons (step1362 p h) (sat_cons (step1171 p h) (sat_cons (step1134 p h) (sat_cons (step1143 p h) (sat_nil p))))))))
end B112E110
