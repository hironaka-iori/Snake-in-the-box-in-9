import B112E007Inputs
namespace B112E007
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1300 : List Lit := [(61, true)]
theorem step1300 (p : Nat → Bool) (h : Constraints p) : clause p c1300 = true :=
  Snake9.LocalRup.prove_clause [c233, c232] c1300 (by decide) p (sat_cons (step233 p h) (sat_cons (step232 p h) (sat_nil p)))
def c1301 : List Lit := [(466, false)]
theorem step1301 (p : Nat → Bool) (h : Constraints p) : clause p c1301 = true :=
  Snake9.LocalRup.prove_clause [c828, c825] c1301 (by decide) p (sat_cons (step828 p h) (sat_cons (step825 p h) (sat_nil p)))
def c1302 : List Lit := [(350, false)]
theorem step1302 (p : Nat → Bool) (h : Constraints p) : clause p c1302 = true :=
  Snake9.LocalRup.prove_clause [c828, c827] c1302 (by decide) p (sat_cons (step828 p h) (sat_cons (step827 p h) (sat_nil p)))
def c1303 : List Lit := [(464, false)]
theorem step1303 (p : Nat → Bool) (h : Constraints p) : clause p c1303 = true :=
  Snake9.LocalRup.prove_clause [c1301, c821] c1303 (by decide) p (sat_cons (step1301 p h) (sat_cons (step821 p h) (sat_nil p)))
def c1304 : List Lit := [(406, false)]
theorem step1304 (p : Nat → Bool) (h : Constraints p) : clause p c1304 = true :=
  Snake9.LocalRup.prove_clause [c1301, c824] c1304 (by decide) p (sat_cons (step1301 p h) (sat_cons (step824 p h) (sat_nil p)))
def c1305 : List Lit := [(348, false)]
theorem step1305 (p : Nat → Bool) (h : Constraints p) : clause p c1305 = true :=
  Snake9.LocalRup.prove_clause [c1302, c710] c1305 (by decide) p (sat_cons (step1302 p h) (sat_cons (step710 p h) (sat_nil p)))
def c1306 : List Lit := [(292, false)]
theorem step1306 (p : Nat → Bool) (h : Constraints p) : clause p c1306 = true :=
  Snake9.LocalRup.prove_clause [c1302, c713] c1306 (by decide) p (sat_cons (step1302 p h) (sat_cons (step713 p h) (sat_nil p)))
def c1307 : List Lit := [(462, false)]
theorem step1307 (p : Nat → Bool) (h : Constraints p) : clause p c1307 = true :=
  Snake9.LocalRup.prove_clause [c1303, c816] c1307 (by decide) p (sat_cons (step1303 p h) (sat_cons (step816 p h) (sat_nil p)))
def c1308 : List Lit := [(434, false)]
theorem step1308 (p : Nat → Bool) (h : Constraints p) : clause p c1308 = true :=
  Snake9.LocalRup.prove_clause [c1303, c819] c1308 (by decide) p (sat_cons (step1303 p h) (sat_cons (step819 p h) (sat_nil p)))
def c1309 : List Lit := [(404, false)]
theorem step1309 (p : Nat → Bool) (h : Constraints p) : clause p c1309 = true :=
  Snake9.LocalRup.prove_clause [c1304, c758] c1309 (by decide) p (sat_cons (step1304 p h) (sat_cons (step758 p h) (sat_nil p)))
def c1310 : List Lit := [(376, false)]
theorem step1310 (p : Nat → Bool) (h : Constraints p) : clause p c1310 = true :=
  Snake9.LocalRup.prove_clause [c1304, c761] c1310 (by decide) p (sat_cons (step1304 p h) (sat_cons (step761 p h) (sat_nil p)))
def c1311 : List Lit := [(346, false)]
theorem step1311 (p : Nat → Bool) (h : Constraints p) : clause p c1311 = true :=
  Snake9.LocalRup.prove_clause [c1305, c705] c1311 (by decide) p (sat_cons (step1305 p h) (sat_cons (step705 p h) (sat_nil p)))
def c1312 : List Lit := [(318, false)]
theorem step1312 (p : Nat → Bool) (h : Constraints p) : clause p c1312 = true :=
  Snake9.LocalRup.prove_clause [c1305, c708] c1312 (by decide) p (sat_cons (step1305 p h) (sat_cons (step708 p h) (sat_nil p)))
def c1313 : List Lit := [(290, false)]
theorem step1313 (p : Nat → Bool) (h : Constraints p) : clause p c1313 = true :=
  Snake9.LocalRup.prove_clause [c1306, c651] c1313 (by decide) p (sat_cons (step1306 p h) (sat_cons (step651 p h) (sat_nil p)))
def c1314 : List Lit := [(460, false)]
theorem step1314 (p : Nat → Bool) (h : Constraints p) : clause p c1314 = true :=
  Snake9.LocalRup.prove_clause [c1307, c811] c1314 (by decide) p (sat_cons (step1307 p h) (sat_cons (step811 p h) (sat_nil p)))
def c1315 : List Lit := [(446, false)]
theorem step1315 (p : Nat → Bool) (h : Constraints p) : clause p c1315 = true :=
  Snake9.LocalRup.prove_clause [c1307, c814] c1315 (by decide) p (sat_cons (step1307 p h) (sat_cons (step814 p h) (sat_nil p)))
def c1316 : List Lit := [(418, false)]
theorem step1316 (p : Nat → Bool) (h : Constraints p) : clause p c1316 = true :=
  Snake9.LocalRup.prove_clause [c1308, c785] c1316 (by decide) p (sat_cons (step1308 p h) (sat_cons (step785 p h) (sat_nil p)))
def c1317 : List Lit := [(374, false)]
theorem step1317 (p : Nat → Bool) (h : Constraints p) : clause p c1317 = true :=
  Snake9.LocalRup.prove_clause [c1310, c734] c1317 (by decide) p (sat_cons (step1310 p h) (sat_cons (step734 p h) (sat_nil p)))
def c1318 : List Lit := [(362, false)]
theorem step1318 (p : Nat → Bool) (h : Constraints p) : clause p c1318 = true :=
  Snake9.LocalRup.prove_clause [c1310, c737] c1318 (by decide) p (sat_cons (step1310 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1319 : List Lit := [(344, false)]
theorem step1319 (p : Nat → Bool) (h : Constraints p) : clause p c1319 = true :=
  Snake9.LocalRup.prove_clause [c1311, c700] c1319 (by decide) p (sat_cons (step1311 p h) (sat_cons (step700 p h) (sat_nil p)))
def c1320 : List Lit := [(330, false)]
theorem step1320 (p : Nat → Bool) (h : Constraints p) : clause p c1320 = true :=
  Snake9.LocalRup.prove_clause [c1311, c703] c1320 (by decide) p (sat_cons (step1311 p h) (sat_cons (step703 p h) (sat_nil p)))
def c1321 : List Lit := [(316, false)]
theorem step1321 (p : Nat → Bool) (h : Constraints p) : clause p c1321 = true :=
  Snake9.LocalRup.prove_clause [c1312, c673] c1321 (by decide) p (sat_cons (step1312 p h) (sat_cons (step673 p h) (sat_nil p)))
def c1322 : List Lit := [(288, false)]
theorem step1322 (p : Nat → Bool) (h : Constraints p) : clause p c1322 = true :=
  Snake9.LocalRup.prove_clause [c1313, c646] c1322 (by decide) p (sat_cons (step1313 p h) (sat_cons (step646 p h) (sat_nil p)))
def c1323 : List Lit := [(274, false)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true :=
  Snake9.LocalRup.prove_clause [c1313, c649] c1323 (by decide) p (sat_cons (step1313 p h) (sat_cons (step649 p h) (sat_nil p)))
def c1324 : List Lit := [(458, false)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true :=
  Snake9.LocalRup.prove_clause [c1314, c806] c1324 (by decide) p (sat_cons (step1314 p h) (sat_cons (step806 p h) (sat_nil p)))
def c1325 : List Lit := [(452, false)]
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true :=
  Snake9.LocalRup.prove_clause [c1314, c809] c1325 (by decide) p (sat_cons (step1314 p h) (sat_cons (step809 p h) (sat_nil p)))
def c1326 : List Lit := [(416, false)]
theorem step1326 (p : Nat → Bool) (h : Constraints p) : clause p c1326 = true :=
  Snake9.LocalRup.prove_clause [c1316, c771] c1326 (by decide) p (sat_cons (step1316 p h) (sat_cons (step771 p h) (sat_nil p)))
def c1327 : List Lit := [(354, false)]
theorem step1327 (p : Nat → Bool) (h : Constraints p) : clause p c1327 = true :=
  Snake9.LocalRup.prove_clause [c1318, c724] c1327 (by decide) p (sat_cons (step1318 p h) (sat_cons (step724 p h) (sat_nil p)))
def c1328 : List Lit := [(336, false)]
theorem step1328 (p : Nat → Bool) (h : Constraints p) : clause p c1328 = true :=
  Snake9.LocalRup.prove_clause [c1319, c698] c1328 (by decide) p (sat_cons (step1319 p h) (sat_cons (step698 p h) (sat_nil p)))
def c1329 : List Lit := [(314, false)]
theorem step1329 (p : Nat → Bool) (h : Constraints p) : clause p c1329 = true :=
  Snake9.LocalRup.prove_clause [c1321, c670] c1329 (by decide) p (sat_cons (step1321 p h) (sat_cons (step670 p h) (sat_nil p)))
def c1330 : List Lit := [(286, false)]
theorem step1330 (p : Nat → Bool) (h : Constraints p) : clause p c1330 = true :=
  Snake9.LocalRup.prove_clause [c1322, c642] c1330 (by decide) p (sat_cons (step1322 p h) (sat_cons (step642 p h) (sat_nil p)))
def c1331 : List Lit := [(272, false)]
theorem step1331 (p : Nat → Bool) (h : Constraints p) : clause p c1331 = true :=
  Snake9.LocalRup.prove_clause [c1323, c629] c1331 (by decide) p (sat_cons (step1323 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1332 : List Lit := [(332, false)]
theorem step1332 (p : Nat → Bool) (h : Constraints p) : clause p c1332 = true :=
  Snake9.LocalRup.prove_clause [c1328, c690] c1332 (by decide) p (sat_cons (step1328 p h) (sat_cons (step690 p h) (sat_nil p)))
def c1333 : List Lit := [(270, false)]
theorem step1333 (p : Nat → Bool) (h : Constraints p) : clause p c1333 = true :=
  Snake9.LocalRup.prove_clause [c1331, c627] c1333 (by decide) p (sat_cons (step1331 p h) (sat_cons (step627 p h) (sat_nil p)))
def c1334 : List Lit := [(121, true), (123, true), (125, true), (129, true), (130, true), (132, true), (135, true), (138, true), (139, true), (141, true), (143, true), (144, true), (146, true), (149, true), (152, true), (154, true), (155, true), (158, true), (160, true), (161, true), (164, true), (165, true), (169, true), (170, true), (172, true), (173, true), (175, true), (177, true), (179, true), (182, true), (183, true), (185, true), (186, true), (190, true), (192, true), (194, true), (195, true), (199, true), (201, true), (203, true), (204, true), (208, true), (210, true), (211, true), (212, true), (215, true), (216, true), (220, true), (222, true), (223, true), (224, true), (227, true), (229, true), (231, true), (233, true), (235, true)]
theorem step1334 (p : Nat → Bool) (h : Constraints p) : clause p c1334 = true :=
  Snake9.TreeRup.prove_clause [c544, c545, c546, c547, c548, c549, c550, c551, c552, c553, c554, c555, c556, c557, c558, c559, c560, c561, c562, c563, c564, c565, c566, c567, c568, c569, c570, c571, c572, c573, c574, c575, c576, c577, c578, c579, c580, c581, c582, c583, c584, c585, c586, c587, c588, c589, c590, c591, c592, c593, c594, c595, c596, c597, c598, c599, c600, c601, c602, c603, c604, c829] c1334 (by decide) p (sat_cons (step544 p h) (sat_cons (step545 p h) (sat_cons (step546 p h) (sat_cons (step547 p h) (sat_cons (step548 p h) (sat_cons (step549 p h) (sat_cons (step550 p h) (sat_cons (step551 p h) (sat_cons (step552 p h) (sat_cons (step553 p h) (sat_cons (step554 p h) (sat_cons (step555 p h) (sat_cons (step556 p h) (sat_cons (step557 p h) (sat_cons (step558 p h) (sat_cons (step559 p h) (sat_cons (step560 p h) (sat_cons (step561 p h) (sat_cons (step562 p h) (sat_cons (step563 p h) (sat_cons (step564 p h) (sat_cons (step565 p h) (sat_cons (step566 p h) (sat_cons (step567 p h) (sat_cons (step568 p h) (sat_cons (step569 p h) (sat_cons (step570 p h) (sat_cons (step571 p h) (sat_cons (step572 p h) (sat_cons (step573 p h) (sat_cons (step574 p h) (sat_cons (step575 p h) (sat_cons (step576 p h) (sat_cons (step577 p h) (sat_cons (step578 p h) (sat_cons (step579 p h) (sat_cons (step580 p h) (sat_cons (step581 p h) (sat_cons (step582 p h) (sat_cons (step583 p h) (sat_cons (step584 p h) (sat_cons (step585 p h) (sat_cons (step586 p h) (sat_cons (step587 p h) (sat_cons (step588 p h) (sat_cons (step589 p h) (sat_cons (step590 p h) (sat_cons (step591 p h) (sat_cons (step592 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step595 p h) (sat_cons (step596 p h) (sat_cons (step597 p h) (sat_cons (step598 p h) (sat_cons (step599 p h) (sat_cons (step600 p h) (sat_cons (step601 p h) (sat_cons (step602 p h) (sat_cons (step603 p h) (sat_cons (step604 p h) (sat_cons (step829 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1335 : List Lit := [(1602, true)]
theorem step1335 (p : Nat → Bool) (h : Constraints p) : clause p c1335 = true :=
  Snake9.LocalRup.prove_clause [c1092, c1096, c1084, c1086, c1073, c1081, c1082, c1078, c1079, c1070, c354, c405, c393, c409] c1335 (by decide) p (sat_cons (step1092 p h) (sat_cons (step1096 p h) (sat_cons (step1084 p h) (sat_cons (step1086 p h) (sat_cons (step1073 p h) (sat_cons (step1081 p h) (sat_cons (step1082 p h) (sat_cons (step1078 p h) (sat_cons (step1079 p h) (sat_cons (step1070 p h) (sat_cons (step354 p h) (sat_cons (step405 p h) (sat_cons (step393 p h) (sat_cons (step409 p h) (sat_nil p)))))))))))))))
def c1336 : List Lit := [(1609, true)]
theorem step1336 (p : Nat → Bool) (h : Constraints p) : clause p c1336 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1107] c1336 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1107 p h) (sat_nil p)))
def c1337 : List Lit := [(1582, true)]
theorem step1337 (p : Nat → Bool) (h : Constraints p) : clause p c1337 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1059, c1062, c1052, c1054, c1044, c1050, c1046, c1047, c1041, c270, c248, c252, c287, c727, c728, c732, c729] c1337 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1059 p h) (sat_cons (step1062 p h) (sat_cons (step1052 p h) (sat_cons (step1054 p h) (sat_cons (step1044 p h) (sat_cons (step1050 p h) (sat_cons (step1046 p h) (sat_cons (step1047 p h) (sat_cons (step1041 p h) (sat_cons (step270 p h) (sat_cons (step248 p h) (sat_cons (step252 p h) (sat_cons (step287 p h) (sat_cons (step727 p h) (sat_cons (step728 p h) (sat_cons (step732 p h) (sat_cons (step729 p h) (sat_nil p)))))))))))))))))))
def c1338 : List Lit := [(1610, true)]
theorem step1338 (p : Nat → Bool) (h : Constraints p) : clause p c1338 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1335, c1110] c1338 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1335 p h) (sat_cons (step1110 p h) (sat_nil p))))
def c1339 : List Lit := [(1594, true), (1596, true), (81, false)]
theorem step1339 (p : Nat → Bool) (h : Constraints p) : clause p c1339 = true :=
  Snake9.LocalRup.prove_clause [c1081, c1082, c393, c1078, c1079, c351, c405, c409] c1339 (by decide) p (sat_cons (step1081 p h) (sat_cons (step1082 p h) (sat_cons (step393 p h) (sat_cons (step1078 p h) (sat_cons (step1079 p h) (sat_cons (step351 p h) (sat_cons (step405 p h) (sat_cons (step409 p h) (sat_nil p)))))))))
def c1340 : List Lit := [(84, false), (90, false), (81, false), (1595, true)]
theorem step1340 (p : Nat → Bool) (h : Constraints p) : clause p c1340 = true :=
  Snake9.LocalRup.prove_clause [c349, c351, c1080] c1340 (by decide) p (sat_cons (step349 p h) (sat_cons (step351 p h) (sat_cons (step1080 p h) (sat_nil p))))
def c1341 : List Lit := [(1596, true), (92, false), (1624, true), (81, false), (1595, true)]
theorem step1341 (p : Nat → Bool) (h : Constraints p) : clause p c1341 = true :=
  Snake9.LocalRup.prove_clause [c1301, c1081, c1082, c393, c1340, c409, c413, c405, c762, c1080, c763, c343, c772, c783, c817, c823, c757, c754, c752, c751, c750, c359, c451, c452, c1137] c1341 (by decide) p (sat_cons (step1301 p h) (sat_cons (step1081 p h) (sat_cons (step1082 p h) (sat_cons (step393 p h) (sat_cons (step1340 p h) (sat_cons (step409 p h) (sat_cons (step413 p h) (sat_cons (step405 p h) (sat_cons (step762 p h) (sat_cons (step1080 p h) (sat_cons (step763 p h) (sat_cons (step343 p h) (sat_cons (step772 p h) (sat_cons (step783 p h) (sat_cons (step817 p h) (sat_cons (step823 p h) (sat_cons (step757 p h) (sat_cons (step754 p h) (sat_cons (step752 p h) (sat_cons (step751 p h) (sat_cons (step750 p h) (sat_cons (step359 p h) (sat_cons (step451 p h) (sat_cons (step452 p h) (sat_cons (step1137 p h) (sat_nil p))))))))))))))))))))))))))
def c1342 : List Lit := [(95, false), (85, false), (92, false), (1624, true)]
theorem step1342 (p : Nat → Bool) (h : Constraints p) : clause p c1342 = true :=
  Snake9.LocalRup.prove_clause [c451, c452, c1137] c1342 (by decide) p (sat_cons (step451 p h) (sat_cons (step452 p h) (sat_cons (step1137 p h) (sat_nil p))))
def c1343 : List Lit := [(90, false), (52, false), (208, true), (84, true), (81, false)]
theorem step1343 (p : Nat → Bool) (h : Constraints p) : clause p c1343 = true :=
  Snake9.LocalRup.prove_clause [c413, c384] c1343 (by decide) p (sat_cons (step413 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1344 : List Lit := [(211, true), (95, true), (93, false)]
theorem step1344 (p : Nat → Bool) (h : Constraints p) : clause p c1344 = true :=
  Snake9.LocalRup.prove_clause [c595, c446, c448, c482, c1296] c1344 (by decide) p (sat_cons (step595 p h) (sat_cons (step446 p h) (sat_cons (step448 p h) (sat_cons (step482 p h) (sat_cons (step1296 p h) (sat_nil p))))))
def c1345 : List Lit := [(58, false), (94, false), (1529, true)]
theorem step1345 (p : Nat → Bool) (h : Constraints p) : clause p c1345 = true :=
  Snake9.LocalRup.prove_clause [c1300, c221, c222, c965, c969, c974] c1345 (by decide) p (sat_cons (step1300 p h) (sat_cons (step221 p h) (sat_cons (step222 p h) (sat_cons (step965 p h) (sat_cons (step969 p h) (sat_cons (step974 p h) (sat_nil p)))))))
def c1346 : List Lit := [(84, false), (94, false), (81, false), (1595, true)]
theorem step1346 (p : Nat → Bool) (h : Constraints p) : clause p c1346 = true :=
  Snake9.LocalRup.prove_clause [c350, c352, c1080] c1346 (by decide) p (sat_cons (step350 p h) (sat_cons (step352 p h) (sat_cons (step1080 p h) (sat_nil p))))
def c1347 : List Lit := [(95, true), (84, true), (58, true), (93, false), (94, false)]
theorem step1347 (p : Nat → Bool) (h : Constraints p) : clause p c1347 = true :=
  Snake9.LocalRup.prove_clause [c1326, c1344, c450, c764, c766, c769] c1347 (by decide) p (sat_cons (step1326 p h) (sat_cons (step1344 p h) (sat_cons (step450 p h) (sat_cons (step764 p h) (sat_cons (step766 p h) (sat_cons (step769 p h) (sat_nil p)))))))
def c1348 : List Lit := [(1623, true), (81, false), (1599, true), (1529, true)]
theorem step1348 (p : Nat → Bool) (h : Constraints p) : clause p c1348 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1135, c1136, c1345, c1346, c1347, c453, c1078, c1080, c1087, c1081, c1082, c393, c405, c409] c1348 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step1345 p h) (sat_cons (step1346 p h) (sat_cons (step1347 p h) (sat_cons (step453 p h) (sat_cons (step1078 p h) (sat_cons (step1080 p h) (sat_cons (step1087 p h) (sat_cons (step1081 p h) (sat_cons (step1082 p h) (sat_cons (step393 p h) (sat_cons (step405 p h) (sat_cons (step409 p h) (sat_nil p))))))))))))))))
def c1349 : List Lit := [(85, true), (84, true), (81, false), (1599, true)]
theorem step1349 (p : Nat → Bool) (h : Constraints p) : clause p c1349 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1078, c1080, c1087, c1081, c1082, c393, c405, c409] c1349 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1078 p h) (sat_cons (step1080 p h) (sat_cons (step1087 p h) (sat_cons (step1081 p h) (sat_cons (step1082 p h) (sat_cons (step393 p h) (sat_cons (step405 p h) (sat_cons (step409 p h) (sat_nil p))))))))))
def c1350 : List Lit := [(1526, true), (60, false)]
theorem step1350 (p : Nat → Bool) (h : Constraints p) : clause p c1350 = true :=
  Snake9.LocalRup.prove_clause [c1300, c968, c969, c228] c1350 (by decide) p (sat_cons (step1300 p h) (sat_cons (step968 p h) (sat_cons (step969 p h) (sat_cons (step228 p h) (sat_nil p)))))
def c1351 : List Lit := [(1528, true), (58, true)]
theorem step1351 (p : Nat → Bool) (h : Constraints p) : clause p c1351 = true :=
  Snake9.LocalRup.prove_clause [c971, c973, c968, c969, c1350, c965, c966, c195, c213] c1351 (by decide) p (sat_cons (step971 p h) (sat_cons (step973 p h) (sat_cons (step968 p h) (sat_cons (step969 p h) (sat_cons (step1350 p h) (sat_cons (step965 p h) (sat_cons (step966 p h) (sat_cons (step195 p h) (sat_cons (step213 p h) (sat_nil p))))))))))
def c1352 : List Lit := [(1528, true)]
theorem step1352 (p : Nat → Bool) (h : Constraints p) : clause p c1352 = true :=
  Snake9.LocalRup.prove_clause [c1300, c971, c973, c1351, c969, c965, c220] c1352 (by decide) p (sat_cons (step1300 p h) (sat_cons (step971 p h) (sat_cons (step973 p h) (sat_cons (step1351 p h) (sat_cons (step969 p h) (sat_cons (step965 p h) (sat_cons (step220 p h) (sat_nil p))))))))
def c1353 : List Lit := [(1532, true)]
theorem step1353 (p : Nat → Bool) (h : Constraints p) : clause p c1353 = true :=
  Snake9.LocalRup.prove_clause [c1352, c979] c1353 (by decide) p (sat_cons (step1352 p h) (sat_cons (step979 p h) (sat_nil p)))
def c1354 : List Lit := [(1485, true)]
theorem step1354 (p : Nat → Bool) (h : Constraints p) : clause p c1354 = true :=
  Snake9.LocalRup.prove_clause [c1322, c901, c906, c887, c890, c852, c856, c880, c882, c869, c871, c844, c846, c833, c877, c878, c874, c875, c867, c841, c842, c838, c830, c89, c45, c103, c110, c55, c10, c98, c102, c633, c636, c634, c639, c644] c1354 (by decide) p (sat_cons (step1322 p h) (sat_cons (step901 p h) (sat_cons (step906 p h) (sat_cons (step887 p h) (sat_cons (step890 p h) (sat_cons (step852 p h) (sat_cons (step856 p h) (sat_cons (step880 p h) (sat_cons (step882 p h) (sat_cons (step869 p h) (sat_cons (step871 p h) (sat_cons (step844 p h) (sat_cons (step846 p h) (sat_cons (step833 p h) (sat_cons (step877 p h) (sat_cons (step878 p h) (sat_cons (step874 p h) (sat_cons (step875 p h) (sat_cons (step867 p h) (sat_cons (step841 p h) (sat_cons (step842 p h) (sat_cons (step838 p h) (sat_cons (step830 p h) (sat_cons (step89 p h) (sat_cons (step45 p h) (sat_cons (step103 p h) (sat_cons (step110 p h) (sat_cons (step55 p h) (sat_cons (step10 p h) (sat_cons (step98 p h) (sat_cons (step102 p h) (sat_cons (step633 p h) (sat_cons (step636 p h) (sat_cons (step634 p h) (sat_cons (step639 p h) (sat_cons (step644 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1355 : List Lit := [(1512, true)]
theorem step1355 (p : Nat → Bool) (h : Constraints p) : clause p c1355 = true :=
  Snake9.LocalRup.prove_clause [c1329, c945, c949, c937, c939, c927, c935, c931, c932, c925, c155, c127, c152, c146, c665, c663, c668] c1355 (by decide) p (sat_cons (step1329 p h) (sat_cons (step945 p h) (sat_cons (step949 p h) (sat_cons (step937 p h) (sat_cons (step939 p h) (sat_cons (step927 p h) (sat_cons (step935 p h) (sat_cons (step931 p h) (sat_cons (step932 p h) (sat_cons (step925 p h) (sat_cons (step155 p h) (sat_cons (step127 p h) (sat_cons (step152 p h) (sat_cons (step146 p h) (sat_cons (step665 p h) (sat_cons (step663 p h) (sat_cons (step668 p h) (sat_nil p))))))))))))))))))
def c1356 : List Lit := [(36, false), (1508, true)]
theorem step1356 (p : Nat → Bool) (h : Constraints p) : clause p c1356 = true :=
  Snake9.LocalRup.prove_clause [c1329, c939, c932, c931, c937, c935, c155, c127, c152, c146, c665, c663, c668] c1356 (by decide) p (sat_cons (step1329 p h) (sat_cons (step939 p h) (sat_cons (step932 p h) (sat_cons (step931 p h) (sat_cons (step937 p h) (sat_cons (step935 p h) (sat_cons (step155 p h) (sat_cons (step127 p h) (sat_cons (step152 p h) (sat_cons (step146 p h) (sat_cons (step665 p h) (sat_cons (step663 p h) (sat_cons (step668 p h) (sat_nil p))))))))))))))
def c1357 : List Lit := [(34, false), (33, true), (152, true), (38, true), (1478, true)]
theorem step1357 (p : Nat → Bool) (h : Constraints p) : clause p c1357 = true :=
  Snake9.LocalRup.prove_clause [c887, c882, c875, c890, c871, c51, c125] c1357 (by decide) p (sat_cons (step887 p h) (sat_cons (step882 p h) (sat_cons (step875 p h) (sat_cons (step890 p h) (sat_cons (step871 p h) (sat_cons (step51 p h) (sat_cons (step125 p h) (sat_nil p))))))))
def c1358 : List Lit := [(1529, true), (55, true), (177, true)]
theorem step1358 (p : Nat → Bool) (h : Constraints p) : clause p c1358 = true :=
  Snake9.LocalRup.prove_clause [c965, c976, c974, c967, c968, c969, c1350, c227, c196] c1358 (by decide) p (sat_cons (step965 p h) (sat_cons (step976 p h) (sat_cons (step974 p h) (sat_cons (step967 p h) (sat_cons (step968 p h) (sat_cons (step969 p h) (sat_cons (step1350 p h) (sat_cons (step227 p h) (sat_cons (step196 p h) (sat_nil p))))))))))
def c1359 : List Lit := [(1625, true), (1474, true)]
theorem step1359 (p : Nat → Bool) (h : Constraints p) : clause p c1359 = true :=
  Snake9.LocalRup.prove_clause [c828, c880, c878, c882, c874, c875, c90, c1138, c1140, c1135, c1136, c454, c105, c418, c1344, c95, c764, c633, c768, c634, c770, c643, c783, c645, c817, c650, c820, c711, c826] c1359 (by decide) p (sat_cons (step828 p h) (sat_cons (step880 p h) (sat_cons (step878 p h) (sat_cons (step882 p h) (sat_cons (step874 p h) (sat_cons (step875 p h) (sat_cons (step90 p h) (sat_cons (step1138 p h) (sat_cons (step1140 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step454 p h) (sat_cons (step105 p h) (sat_cons (step418 p h) (sat_cons (step1344 p h) (sat_cons (step95 p h) (sat_cons (step764 p h) (sat_cons (step633 p h) (sat_cons (step768 p h) (sat_cons (step634 p h) (sat_cons (step770 p h) (sat_cons (step643 p h) (sat_cons (step783 p h) (sat_cons (step645 p h) (sat_cons (step817 p h) (sat_cons (step650 p h) (sat_cons (step820 p h) (sat_cons (step711 p h) (sat_cons (step826 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1360 : List Lit := [(93, false), (95, true), (92, false), (1474, true)]
theorem step1360 (p : Nat → Bool) (h : Constraints p) : clause p c1360 = true :=
  Snake9.LocalRup.prove_clause [c828, c882, c875, c874, c105, c880, c878, c90, c418, c1344, c95, c764, c633, c768, c634, c770, c643, c783, c645, c817, c650, c820, c711, c826] c1360 (by decide) p (sat_cons (step828 p h) (sat_cons (step882 p h) (sat_cons (step875 p h) (sat_cons (step874 p h) (sat_cons (step105 p h) (sat_cons (step880 p h) (sat_cons (step878 p h) (sat_cons (step90 p h) (sat_cons (step418 p h) (sat_cons (step1344 p h) (sat_cons (step95 p h) (sat_cons (step764 p h) (sat_cons (step633 p h) (sat_cons (step768 p h) (sat_cons (step634 p h) (sat_cons (step770 p h) (sat_cons (step643 p h) (sat_cons (step783 p h) (sat_cons (step645 p h) (sat_cons (step817 p h) (sat_cons (step650 p h) (sat_cons (step820 p h) (sat_cons (step711 p h) (sat_cons (step826 p h) (sat_nil p)))))))))))))))))))))))))
def c1361 : List Lit := [(1540, true)]
theorem step1361 (p : Nat → Bool) (h : Constraints p) : clause p c1361 = true :=
  Snake9.LocalRup.prove_clause [c1355, c1353, c993] c1361 (by decide) p (sat_cons (step1355 p h) (sat_cons (step1353 p h) (sat_cons (step993 p h) (sat_nil p))))
def c1362 : List Lit := [(1529, true), (1524, false), (177, true)]
theorem step1362 (p : Nat → Bool) (h : Constraints p) : clause p c1362 = true :=
  Snake9.LocalRup.prove_clause [c1358, c974, c968, c969, c1350, c227, c197] c1362 (by decide) p (sat_cons (step1358 p h) (sat_cons (step974 p h) (sat_cons (step968 p h) (sat_cons (step969 p h) (sat_cons (step1350 p h) (sat_cons (step227 p h) (sat_cons (step197 p h) (sat_nil p))))))))
def c1363 : List Lit := [(1513, true), (34, true)]
theorem step1363 (p : Nat → Bool) (h : Constraints p) : clause p c1363 = true :=
  Snake9.LocalRup.prove_clause [c929, c954, c950, c930, c1356, c925] c1363 (by decide) p (sat_cons (step929 p h) (sat_cons (step954 p h) (sat_cons (step950 p h) (sat_cons (step930 p h) (sat_cons (step1356 p h) (sat_cons (step925 p h) (sat_nil p)))))))
end B112E007
