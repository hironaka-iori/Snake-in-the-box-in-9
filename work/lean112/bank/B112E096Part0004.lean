import B112E096Part0003
namespace B112E096
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1292 : List Lit := [(1439, false), (1452, true)]
theorem step1292 (p : Nat → Bool) (h : Constraints p) : clause p c1292 = true :=
  Snake9.LocalRup.prove_clause [c1065, c640] c1292 (by decide) p (sat_cons (step1065 p h) (sat_cons (step640 p h) (sat_nil p)))
def c1293 : List Lit := [(1450, false), (1460, true)]
theorem step1293 (p : Nat → Bool) (h : Constraints p) : clause p c1293 = true :=
  Snake9.LocalRup.prove_clause [c1172, c645] c1293 (by decide) p (sat_cons (step1172 p h) (sat_cons (step645 p h) (sat_nil p)))
def c1294 : List Lit := [(1451, false), (1461, true)]
theorem step1294 (p : Nat → Bool) (h : Constraints p) : clause p c1294 = true :=
  Snake9.LocalRup.prove_clause [c1172, c646] c1294 (by decide) p (sat_cons (step1172 p h) (sat_cons (step646 p h) (sat_nil p)))
def c1295 : List Lit := [(1452, false), (1462, true)]
theorem step1295 (p : Nat → Bool) (h : Constraints p) : clause p c1295 = true :=
  Snake9.LocalRup.prove_clause [c1172, c647] c1295 (by decide) p (sat_cons (step1172 p h) (sat_cons (step647 p h) (sat_nil p)))
def c1296 : List Lit := [(1428, false), (1460, true)]
theorem step1296 (p : Nat → Bool) (h : Constraints p) : clause p c1296 = true :=
  Snake9.LocalRup.prove_clause [c1066, c648] c1296 (by decide) p (sat_cons (step1066 p h) (sat_cons (step648 p h) (sat_nil p)))
def c1297 : List Lit := [(1429, false), (1461, true)]
theorem step1297 (p : Nat → Bool) (h : Constraints p) : clause p c1297 = true :=
  Snake9.LocalRup.prove_clause [c1066, c652] c1297 (by decide) p (sat_cons (step1066 p h) (sat_cons (step652 p h) (sat_nil p)))
def c1298 : List Lit := [(1430, false), (1462, true)]
theorem step1298 (p : Nat → Bool) (h : Constraints p) : clause p c1298 = true :=
  Snake9.LocalRup.prove_clause [c1066, c654] c1298 (by decide) p (sat_cons (step1066 p h) (sat_cons (step654 p h) (sat_nil p)))
def c1299 : List Lit := [(1496, false), (1509, true)]
theorem step1299 (p : Nat → Bool) (h : Constraints p) : clause p c1299 = true :=
  Snake9.LocalRup.prove_clause [c1058, c709] c1299 (by decide) p (sat_cons (step1058 p h) (sat_cons (step709 p h) (sat_nil p)))
def c1300 : List Lit := [(1497, false), (1510, true)]
theorem step1300 (p : Nat → Bool) (h : Constraints p) : clause p c1300 = true :=
  Snake9.LocalRup.prove_clause [c1058, c711] c1300 (by decide) p (sat_cons (step1058 p h) (sat_cons (step711 p h) (sat_nil p)))
def c1301 : List Lit := [(1498, false), (1511, true)]
theorem step1301 (p : Nat → Bool) (h : Constraints p) : clause p c1301 = true :=
  Snake9.LocalRup.prove_clause [c1058, c713] c1301 (by decide) p (sat_cons (step1058 p h) (sat_cons (step713 p h) (sat_nil p)))
def c1302 : List Lit := [(1485, false), (1517, true)]
theorem step1302 (p : Nat → Bool) (h : Constraints p) : clause p c1302 = true :=
  Snake9.LocalRup.prove_clause [c1059, c718] c1302 (by decide) p (sat_cons (step1059 p h) (sat_cons (step718 p h) (sat_nil p)))
def c1303 : List Lit := [(1486, false), (1518, true)]
theorem step1303 (p : Nat → Bool) (h : Constraints p) : clause p c1303 = true :=
  Snake9.LocalRup.prove_clause [c1059, c722] c1303 (by decide) p (sat_cons (step1059 p h) (sat_cons (step722 p h) (sat_nil p)))
def c1304 : List Lit := [(1487, false), (1519, true)]
theorem step1304 (p : Nat → Bool) (h : Constraints p) : clause p c1304 = true :=
  Snake9.LocalRup.prove_clause [c1059, c726] c1304 (by decide) p (sat_cons (step1059 p h) (sat_cons (step726 p h) (sat_nil p)))
def c1305 : List Lit := [(1488, false), (1520, true)]
theorem step1305 (p : Nat → Bool) (h : Constraints p) : clause p c1305 = true :=
  Snake9.LocalRup.prove_clause [c1059, c729] c1305 (by decide) p (sat_cons (step1059 p h) (sat_cons (step729 p h) (sat_nil p)))
def c1306 : List Lit := [(1519, false), (1537, true)]
theorem step1306 (p : Nat → Bool) (h : Constraints p) : clause p c1306 = true :=
  Snake9.LocalRup.prove_clause [c1067, c732] c1306 (by decide) p (sat_cons (step1067 p h) (sat_cons (step732 p h) (sat_nil p)))
def c1307 : List Lit := [(1520, false), (1538, true)]
theorem step1307 (p : Nat → Bool) (h : Constraints p) : clause p c1307 = true :=
  Snake9.LocalRup.prove_clause [c1067, c733] c1307 (by decide) p (sat_cons (step1067 p h) (sat_cons (step733 p h) (sat_nil p)))
def c1308 : List Lit := [(1521, false), (1539, true)]
theorem step1308 (p : Nat → Bool) (h : Constraints p) : clause p c1308 = true :=
  Snake9.LocalRup.prove_clause [c1067, c734] c1308 (by decide) p (sat_cons (step1067 p h) (sat_cons (step734 p h) (sat_nil p)))
def c1309 : List Lit := [(1537, true), (1462, false)]
theorem step1309 (p : Nat → Bool) (h : Constraints p) : clause p c1309 = true :=
  Snake9.LocalRup.prove_clause [c1060, c743] c1309 (by decide) p (sat_cons (step1060 p h) (sat_cons (step743 p h) (sat_nil p)))
def c1310 : List Lit := [(1588, false), (1597, true)]
theorem step1310 (p : Nat → Bool) (h : Constraints p) : clause p c1310 = true :=
  Snake9.LocalRup.prove_clause [c1061, c824] c1310 (by decide) p (sat_cons (step1061 p h) (sat_cons (step824 p h) (sat_nil p)))
def c1311 : List Lit := [(1589, false), (1598, true)]
theorem step1311 (p : Nat → Bool) (h : Constraints p) : clause p c1311 = true :=
  Snake9.LocalRup.prove_clause [c1061, c825] c1311 (by decide) p (sat_cons (step1061 p h) (sat_cons (step825 p h) (sat_nil p)))
def c1312 : List Lit := [(1590, false), (1599, true)]
theorem step1312 (p : Nat → Bool) (h : Constraints p) : clause p c1312 = true :=
  Snake9.LocalRup.prove_clause [c1061, c826] c1312 (by decide) p (sat_cons (step1061 p h) (sat_cons (step826 p h) (sat_nil p)))
def c1313 : List Lit := [(1565, false), (1597, true)]
theorem step1313 (p : Nat → Bool) (h : Constraints p) : clause p c1313 = true :=
  Snake9.LocalRup.prove_clause [c1062, c827] c1313 (by decide) p (sat_cons (step1062 p h) (sat_cons (step827 p h) (sat_nil p)))
def c1314 : List Lit := [(1566, false), (1598, true)]
theorem step1314 (p : Nat → Bool) (h : Constraints p) : clause p c1314 = true :=
  Snake9.LocalRup.prove_clause [c1062, c832] c1314 (by decide) p (sat_cons (step1062 p h) (sat_cons (step832 p h) (sat_nil p)))
def c1315 : List Lit := [(1567, false), (1599, true)]
theorem step1315 (p : Nat → Bool) (h : Constraints p) : clause p c1315 = true :=
  Snake9.LocalRup.prove_clause [c1062, c837] c1315 (by decide) p (sat_cons (step1062 p h) (sat_cons (step837 p h) (sat_nil p)))
def c1316 : List Lit := [(1660, false), (1677, true)]
theorem step1316 (p : Nat → Bool) (h : Constraints p) : clause p c1316 = true :=
  Snake9.LocalRup.prove_clause [c1063, c959] c1316 (by decide) p (sat_cons (step1063 p h) (sat_cons (step959 p h) (sat_nil p)))
def c1317 : List Lit := [(1661, false), (1678, true)]
theorem step1317 (p : Nat → Bool) (h : Constraints p) : clause p c1317 = true :=
  Snake9.LocalRup.prove_clause [c1063, c960] c1317 (by decide) p (sat_cons (step1063 p h) (sat_cons (step960 p h) (sat_nil p)))
def c1318 : List Lit := [(1662, false), (1679, true)]
theorem step1318 (p : Nat → Bool) (h : Constraints p) : clause p c1318 = true :=
  Snake9.LocalRup.prove_clause [c1063, c961] c1318 (by decide) p (sat_cons (step1063 p h) (sat_cons (step961 p h) (sat_nil p)))
def c1319 : List Lit := [(1663, false), (1680, true)]
theorem step1319 (p : Nat → Bool) (h : Constraints p) : clause p c1319 = true :=
  Snake9.LocalRup.prove_clause [c1063, c962] c1319 (by decide) p (sat_cons (step1063 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1320 : List Lit := [(1663, false), (1598, false)]
theorem step1320 (p : Nat → Bool) (h : Constraints p) : clause p c1320 = true :=
  Snake9.LocalRup.prove_clause [c1143, c972] c1320 (by decide) p (sat_cons (step1143 p h) (sat_cons (step972 p h) (sat_nil p)))
def c1321 : List Lit := [(1599, false), (1662, false)]
theorem step1321 (p : Nat → Bool) (h : Constraints p) : clause p c1321 = true :=
  Snake9.LocalRup.prove_clause [c1143, c977] c1321 (by decide) p (sat_cons (step1143 p h) (sat_cons (step977 p h) (sat_nil p)))
def c1322 : List Lit := [(1600, false), (1661, false)]
theorem step1322 (p : Nat → Bool) (h : Constraints p) : clause p c1322 = true :=
  Snake9.LocalRup.prove_clause [c1143, c981] c1322 (by decide) p (sat_cons (step1143 p h) (sat_cons (step981 p h) (sat_nil p)))
def c1323 : List Lit := [(1537, false), (1681, false)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true :=
  Snake9.LocalRup.prove_clause [c993, c988] c1323 (by decide) p (sat_cons (step993 p h) (sat_cons (step988 p h) (sat_nil p)))
def c1324 : List Lit := [(1538, false), (1680, false)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true :=
  Snake9.LocalRup.prove_clause [c993, c989] c1324 (by decide) p (sat_cons (step993 p h) (sat_cons (step989 p h) (sat_nil p)))
def c1325 : List Lit := [(1539, false), (1679, false)]
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true :=
  Snake9.LocalRup.prove_clause [c993, c990] c1325 (by decide) p (sat_cons (step993 p h) (sat_cons (step990 p h) (sat_nil p)))
def c1326 : List Lit := [(1540, false), (1678, false)]
theorem step1326 (p : Nat → Bool) (h : Constraints p) : clause p c1326 = true :=
  Snake9.LocalRup.prove_clause [c993, c991] c1326 (by decide) p (sat_cons (step993 p h) (sat_cons (step991 p h) (sat_nil p)))
def c1327 : List Lit := [(1541, false), (1677, false)]
theorem step1327 (p : Nat → Bool) (h : Constraints p) : clause p c1327 = true :=
  Snake9.LocalRup.prove_clause [c993, c992] c1327 (by decide) p (sat_cons (step993 p h) (sat_cons (step992 p h) (sat_nil p)))
def c1328 : List Lit := [(1433, false), (51, false), (1462, true), (1, false), (21, true)]
theorem step1328 (p : Nat → Bool) (h : Constraints p) : clause p c1328 = true :=
  Snake9.LocalRup.prove_clause [c1169, c1127] c1328 (by decide) p (sat_cons (step1169 p h) (sat_cons (step1127 p h) (sat_nil p)))
def c1329 : List Lit := [(51, false), (1443, false), (1462, true), (1, false), (39, false), (22, false)]
theorem step1329 (p : Nat → Bool) (h : Constraints p) : clause p c1329 = true :=
  Snake9.LocalRup.prove_clause [c1169, c1128] c1329 (by decide) p (sat_cons (step1169 p h) (sat_cons (step1128 p h) (sat_nil p)))
def c1330 : List Lit := [(1566, true), (60, true), (1560, false)]
theorem step1330 (p : Nat → Bool) (h : Constraints p) : clause p c1330 = true :=
  Snake9.LocalRup.prove_clause [c780, c1088, c755, c757, c758, c750, c1230, c148] c1330 (by decide) p (sat_cons (step780 p h) (sat_cons (step1088 p h) (sat_cons (step755 p h) (sat_cons (step757 p h) (sat_cons (step758 p h) (sat_cons (step750 p h) (sat_cons (step1230 p h) (sat_cons (step148 p h) (sat_nil p)))))))))
def c1331 : List Lit := [(1633, false), (1650, true), (113, true), (104, true)]
theorem step1331 (p : Nat → Bool) (h : Constraints p) : clause p c1331 = true :=
  Snake9.LocalRup.prove_clause [c894, c901, c926, c880, c889, c892, c922, c881, c1100] c1331 (by decide) p (sat_cons (step894 p h) (sat_cons (step901 p h) (sat_cons (step926 p h) (sat_cons (step880 p h) (sat_cons (step889 p h) (sat_cons (step892 p h) (sat_cons (step922 p h) (sat_cons (step881 p h) (sat_cons (step1100 p h) (sat_nil p))))))))))
def c1332 : List Lit := [(1643, true), (111, false), (113, true), (109, false)]
theorem step1332 (p : Nat → Bool) (h : Constraints p) : clause p c1332 = true :=
  Snake9.LocalRup.prove_clause [c894, c904, c902, c895, c896, c1079] c1332 (by decide) p (sat_cons (step894 p h) (sat_cons (step904 p h) (sat_cons (step902 p h) (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step1079 p h) (sat_nil p)))))))
def c1333 : List Lit := [(1681, true), (35, false), (1661, false), (1620, false), (1566, false), (77, true), (1650, false), (111, false)]
theorem step1333 (p : Nat → Bool) (h : Constraints p) : clause p c1333 = true :=
  Snake9.LocalRup.prove_clause [c786, c788, c1314, c971, c952, c976, c874, c833, c845, c816, c1087, c812, c789, c799, c801, c787, c796, c793, c794, c296, c218, c193, c1248, c1237, c207, c237, c843] c1333 (by decide) p (sat_cons (step786 p h) (sat_cons (step788 p h) (sat_cons (step1314 p h) (sat_cons (step971 p h) (sat_cons (step952 p h) (sat_cons (step976 p h) (sat_cons (step874 p h) (sat_cons (step833 p h) (sat_cons (step845 p h) (sat_cons (step816 p h) (sat_cons (step1087 p h) (sat_cons (step812 p h) (sat_cons (step789 p h) (sat_cons (step799 p h) (sat_cons (step801 p h) (sat_cons (step787 p h) (sat_cons (step796 p h) (sat_cons (step793 p h) (sat_cons (step794 p h) (sat_cons (step296 p h) (sat_cons (step218 p h) (sat_cons (step193 p h) (sat_cons (step1248 p h) (sat_cons (step1237 p h) (sat_cons (step207 p h) (sat_cons (step237 p h) (sat_cons (step843 p h) (sat_nil p))))))))))))))))))))))))))))
def c1334 : List Lit := [(1588, true), (78, false), (100, true), (1627, true), (1575, false), (1615, false), (99, true), (111, false)]
theorem step1334 (p : Nat → Bool) (h : Constraints p) : clause p c1334 = true :=
  Snake9.LocalRup.prove_clause [c1087, c1135, c812, c799, c801, c796, c793, c794, c193, c218, c1237, c1248, c237, c1018, c207, c854, c843, c859, c845, c875] c1334 (by decide) p (sat_cons (step1087 p h) (sat_cons (step1135 p h) (sat_cons (step812 p h) (sat_cons (step799 p h) (sat_cons (step801 p h) (sat_cons (step796 p h) (sat_cons (step793 p h) (sat_cons (step794 p h) (sat_cons (step193 p h) (sat_cons (step218 p h) (sat_cons (step1237 p h) (sat_cons (step1248 p h) (sat_cons (step237 p h) (sat_cons (step1018 p h) (sat_cons (step207 p h) (sat_cons (step854 p h) (sat_cons (step843 p h) (sat_cons (step859 p h) (sat_cons (step845 p h) (sat_cons (step875 p h) (sat_nil p)))))))))))))))))))))
def c1335 : List Lit := [(90, true), (86, false), (1626, true), (1617, false), (96, true)]
theorem step1335 (p : Nat → Bool) (h : Constraints p) : clause p c1335 = true :=
  Snake9.LocalRup.prove_clause [c849, c858, c874, c842, c844, c847, c1141] c1335 (by decide) p (sat_cons (step849 p h) (sat_cons (step858 p h) (sat_cons (step874 p h) (sat_cons (step842 p h) (sat_cons (step844 p h) (sat_cons (step847 p h) (sat_cons (step1141 p h) (sat_nil p))))))))
def c1336 : List Lit := [(86, false), (80, false), (1626, true), (78, false), (100, true), (1584, true), (1617, false), (96, true), (111, false)]
theorem step1336 (p : Nat → Bool) (h : Constraints p) : clause p c1336 = true :=
  Snake9.LocalRup.prove_clause [c193, c1335, c237, c1237, c218, c216, c797, c793, c802] c1336 (by decide) p (sat_cons (step193 p h) (sat_cons (step1335 p h) (sat_cons (step237 p h) (sat_cons (step1237 p h) (sat_cons (step218 p h) (sat_cons (step216 p h) (sat_cons (step797 p h) (sat_cons (step793 p h) (sat_cons (step802 p h) (sat_nil p))))))))))
def c1337 : List Lit := [(86, true), (82, false), (1626, true), (1584, true), (1615, false), (99, true)]
theorem step1337 (p : Nat → Bool) (h : Constraints p) : clause p c1337 = true :=
  Snake9.LocalRup.prove_clause [c800, c796, c798, c802, c793, c207, c208, c841, c854, c844, c859, c870] c1337 (by decide) p (sat_cons (step800 p h) (sat_cons (step796 p h) (sat_cons (step798 p h) (sat_cons (step802 p h) (sat_cons (step793 p h) (sat_cons (step207 p h) (sat_cons (step208 p h) (sat_cons (step841 p h) (sat_cons (step854 p h) (sat_cons (step844 p h) (sat_cons (step859 p h) (sat_cons (step870 p h) (sat_nil p)))))))))))))
def c1338 : List Lit := [(82, false), (1626, true), (78, false), (100, true), (1584, true), (1589, true), (99, true), (96, true), (111, false)]
theorem step1338 (p : Nat → Bool) (h : Constraints p) : clause p c1338 = true :=
  Snake9.LocalRup.prove_clause [c853, c849, c858, c874, c804, c1337, c1335, c1336, c237, c1160, c795, c1249, c1251, c207, c1021, c841, c847] c1338 (by decide) p (sat_cons (step853 p h) (sat_cons (step849 p h) (sat_cons (step858 p h) (sat_cons (step874 p h) (sat_cons (step804 p h) (sat_cons (step1337 p h) (sat_cons (step1335 p h) (sat_cons (step1336 p h) (sat_cons (step237 p h) (sat_cons (step1160 p h) (sat_cons (step795 p h) (sat_cons (step1249 p h) (sat_cons (step1251 p h) (sat_cons (step207 p h) (sat_cons (step1021 p h) (sat_cons (step841 p h) (sat_cons (step847 p h) (sat_nil p))))))))))))))))))
def c1339 : List Lit := [(86, false), (82, true), (1626, true), (78, false), (100, true), (1584, true), (1589, true), (1617, false), (96, true), (111, false)]
theorem step1339 (p : Nat → Bool) (h : Constraints p) : clause p c1339 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1160, c218, c1248] c1339 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1160 p h) (sat_cons (step218 p h) (sat_cons (step1248 p h) (sat_nil p)))))
def c1340 : List Lit := [(78, false), (100, true), (1575, false), (1566, false), (99, true), (96, true), (1650, false), (111, false)]
theorem step1340 (p : Nat → Bool) (h : Constraints p) : clause p c1340 = true :=
  Snake9.LocalRup.prove_clause [c853, c1104, c946, c1322, c834, c813, c800, c1314, c1320, c958, c849, c1334, c833, c1321, c952, c1338, c1339, c796, c798, c802, c1248, c793, c215] c1340 (by decide) p (sat_cons (step853 p h) (sat_cons (step1104 p h) (sat_cons (step946 p h) (sat_cons (step1322 p h) (sat_cons (step834 p h) (sat_cons (step813 p h) (sat_cons (step800 p h) (sat_cons (step1314 p h) (sat_cons (step1320 p h) (sat_cons (step958 p h) (sat_cons (step849 p h) (sat_cons (step1334 p h) (sat_cons (step833 p h) (sat_cons (step1321 p h) (sat_cons (step952 p h) (sat_cons (step1338 p h) (sat_cons (step1339 p h) (sat_cons (step796 p h) (sat_cons (step798 p h) (sat_cons (step802 p h) (sat_cons (step1248 p h) (sat_cons (step793 p h) (sat_cons (step215 p h) (sat_nil p))))))))))))))))))))))))
def c1341 : List Lit := [(1576, false), (1589, true), (1615, false), (1566, false), (99, true), (1650, false)]
theorem step1341 (p : Nat → Bool) (h : Constraints p) : clause p c1341 = true :=
  Snake9.LocalRup.prove_clause [c816, c817, c833, c799, c801, c1321, c796, c797, c793, c952, c221, c1248, c207, c208, c841, c854, c844, c859, c870] c1341 (by decide) p (sat_cons (step816 p h) (sat_cons (step817 p h) (sat_cons (step833 p h) (sat_cons (step799 p h) (sat_cons (step801 p h) (sat_cons (step1321 p h) (sat_cons (step796 p h) (sat_cons (step797 p h) (sat_cons (step793 p h) (sat_cons (step952 p h) (sat_cons (step221 p h) (sat_cons (step1248 p h) (sat_cons (step207 p h) (sat_cons (step208 p h) (sat_cons (step841 p h) (sat_cons (step854 p h) (sat_cons (step844 p h) (sat_cons (step859 p h) (sat_cons (step870 p h) (sat_nil p))))))))))))))))))))
def c1342 : List Lit := [(85, false), (82, true), (86, false), (78, false)]
theorem step1342 (p : Nat → Bool) (h : Constraints p) : clause p c1342 = true :=
  Snake9.LocalRup.prove_clause [c218, c1248] c1342 (by decide) p (sat_cons (step218 p h) (sat_cons (step1248 p h) (sat_nil p)))
def c1343 : List Lit := [(1626, true), (86, false), (89, true), (78, false), (1584, true), (1617, false), (96, true)]
theorem step1343 (p : Nat → Bool) (h : Constraints p) : clause p c1343 = true :=
  Snake9.LocalRup.prove_clause [c849, c858, c874, c1335, c1249, c1251, c1153, c1021, c870, c847, c861, c841, c851, c1132, c246, c1342, c797, c802, c793, c216, c214, c1243] c1343 (by decide) p (sat_cons (step849 p h) (sat_cons (step858 p h) (sat_cons (step874 p h) (sat_cons (step1335 p h) (sat_cons (step1249 p h) (sat_cons (step1251 p h) (sat_cons (step1153 p h) (sat_cons (step1021 p h) (sat_cons (step870 p h) (sat_cons (step847 p h) (sat_cons (step861 p h) (sat_cons (step841 p h) (sat_cons (step851 p h) (sat_cons (step1132 p h) (sat_cons (step246 p h) (sat_cons (step1342 p h) (sat_cons (step797 p h) (sat_cons (step802 p h) (sat_cons (step793 p h) (sat_cons (step216 p h) (sat_cons (step214 p h) (sat_cons (step1243 p h) (sat_nil p)))))))))))))))))))))))
def c1344 : List Lit := [(1662, false), (1560, false), (1474, false), (61, true), (1575, false), (60, true), (111, false)]
theorem step1344 (p : Nat → Bool) (h : Constraints p) : clause p c1344 = true :=
  Snake9.LocalRup.prove_clause [c679, c1302, c750, c755, c1151, c1314, c1321, c971, c1315, c833, c1323, c783, c781, c1087, c1135, c812, c1306, c739, c756, c801, c1304, c751, c794, c681, c1152, c1164, c766, c1226, c757, c305, c342, c664, c667, c672] c1344 (by decide) p (sat_cons (step679 p h) (sat_cons (step1302 p h) (sat_cons (step750 p h) (sat_cons (step755 p h) (sat_cons (step1151 p h) (sat_cons (step1314 p h) (sat_cons (step1321 p h) (sat_cons (step971 p h) (sat_cons (step1315 p h) (sat_cons (step833 p h) (sat_cons (step1323 p h) (sat_cons (step783 p h) (sat_cons (step781 p h) (sat_cons (step1087 p h) (sat_cons (step1135 p h) (sat_cons (step812 p h) (sat_cons (step1306 p h) (sat_cons (step739 p h) (sat_cons (step756 p h) (sat_cons (step801 p h) (sat_cons (step1304 p h) (sat_cons (step751 p h) (sat_cons (step794 p h) (sat_cons (step681 p h) (sat_cons (step1152 p h) (sat_cons (step1164 p h) (sat_cons (step766 p h) (sat_cons (step1226 p h) (sat_cons (step757 p h) (sat_cons (step305 p h) (sat_cons (step342 p h) (sat_cons (step664 p h) (sat_cons (step667 p h) (sat_cons (step672 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1345 : List Lit := [(1626, true), (89, true), (78, false), (1584, true), (99, true), (96, true)]
theorem step1345 (p : Nat → Bool) (h : Constraints p) : clause p c1345 = true :=
  Snake9.LocalRup.prove_clause [c800, c853, c849, c1343, c796, c798, c1337, c802, c1248, c793, c215] c1345 (by decide) p (sat_cons (step800 p h) (sat_cons (step853 p h) (sat_cons (step849 p h) (sat_cons (step1343 p h) (sat_cons (step796 p h) (sat_cons (step798 p h) (sat_cons (step1337 p h) (sat_cons (step802 p h) (sat_cons (step1248 p h) (sat_cons (step793 p h) (sat_cons (step215 p h) (sat_nil p))))))))))))
def c1346 : List Lit := [(98, false), (34, false), (1650, false), (111, false), (109, false)]
theorem step1346 (p : Nat → Bool) (h : Constraints p) : clause p c1346 = true :=
  Snake9.LocalRup.prove_clause [c268, c271, c273, c274, c1151, c786, c849, c853, c1314, c788, c1104, c946, c1322, c834, c813, c1341, c789, c787, c1340, c1016, c299, c296, c656, c659, c1345, c952, c1321, c971, c1344, c833, c1323, c763, c765, c1087, c1135, c1306, c760, c757, c1117, c342, c723, c667, c680, c669] c1346 (by decide) p (sat_cons (step268 p h) (sat_cons (step271 p h) (sat_cons (step273 p h) (sat_cons (step274 p h) (sat_cons (step1151 p h) (sat_cons (step786 p h) (sat_cons (step849 p h) (sat_cons (step853 p h) (sat_cons (step1314 p h) (sat_cons (step788 p h) (sat_cons (step1104 p h) (sat_cons (step946 p h) (sat_cons (step1322 p h) (sat_cons (step834 p h) (sat_cons (step813 p h) (sat_cons (step1341 p h) (sat_cons (step789 p h) (sat_cons (step787 p h) (sat_cons (step1340 p h) (sat_cons (step1016 p h) (sat_cons (step299 p h) (sat_cons (step296 p h) (sat_cons (step656 p h) (sat_cons (step659 p h) (sat_cons (step1345 p h) (sat_cons (step952 p h) (sat_cons (step1321 p h) (sat_cons (step971 p h) (sat_cons (step1344 p h) (sat_cons (step833 p h) (sat_cons (step1323 p h) (sat_cons (step763 p h) (sat_cons (step765 p h) (sat_cons (step1087 p h) (sat_cons (step1135 p h) (sat_cons (step1306 p h) (sat_cons (step760 p h) (sat_cons (step757 p h) (sat_cons (step1117 p h) (sat_cons (step342 p h) (sat_cons (step723 p h) (sat_cons (step667 p h) (sat_cons (step680 p h) (sat_cons (step669 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1347 : List Lit := [(116, true), (1644, true), (111, false), (113, true), (109, false)]
theorem step1347 (p : Nat → Bool) (h : Constraints p) : clause p c1347 = true :=
  Snake9.LocalRup.prove_clause [c894, c903, c897, c898, c905, c1079, c895] c1347 (by decide) p (sat_cons (step894 p h) (sat_cons (step903 p h) (sat_cons (step897 p h) (sat_cons (step898 p h) (sat_cons (step905 p h) (sat_cons (step1079 p h) (sat_cons (step895 p h) (sat_nil p))))))))
def c1348 : List Lit := [(61, true), (60, true), (1556, false), (1567, true), (111, false)]
theorem step1348 (p : Nat → Bool) (h : Constraints p) : clause p c1348 = true :=
  Snake9.LocalRup.prove_clause [c765, c783, c756, c750, c751, c755, c1152, c781, c766] c1348 (by decide) p (sat_cons (step765 p h) (sat_cons (step783 p h) (sat_cons (step756 p h) (sat_cons (step750 p h) (sat_cons (step751 p h) (sat_cons (step755 p h) (sat_cons (step1152 p h) (sat_cons (step781 p h) (sat_cons (step766 p h) (sat_nil p))))))))))
def c1349 : List Lit := [(1474, false), (1519, true), (1479, false), (38, false), (34, false)]
theorem step1349 (p : Nat → Bool) (h : Constraints p) : clause p c1349 = true :=
  Snake9.LocalRup.prove_clause [c1304, c669, c680, c681, c723, c672, c1299, c663, c692, c88, c690] c1349 (by decide) p (sat_cons (step1304 p h) (sat_cons (step669 p h) (sat_cons (step680 p h) (sat_cons (step681 p h) (sat_cons (step723 p h) (sat_cons (step672 p h) (sat_cons (step1299 p h) (sat_cons (step663 p h) (sat_cons (step692 p h) (sat_cons (step88 p h) (sat_cons (step690 p h) (sat_nil p))))))))))))
def c1350 : List Lit := [(1486, false), (1, false), (4, false), (1537, true)]
theorem step1350 (p : Nat → Bool) (h : Constraints p) : clause p c1350 = true :=
  Snake9.LocalRup.prove_clause [c1306, c1303, c723, c736, c1299, c1293, c692, c1290, c689, c618, c1, c616] c1350 (by decide) p (sat_cons (step1306 p h) (sat_cons (step1303 p h) (sat_cons (step723 p h) (sat_cons (step736 p h) (sat_cons (step1299 p h) (sat_cons (step1293 p h) (sat_cons (step692 p h) (sat_cons (step1290 p h) (sat_cons (step689 p h) (sat_cons (step618 p h) (sat_cons (step1 p h) (sat_cons (step616 p h) (sat_nil p)))))))))))))
def c1351 : List Lit := [(1482, true), (1519, true), (41, true), (38, false), (34, false)]
theorem step1351 (p : Nat → Bool) (h : Constraints p) : clause p c1351 = true :=
  Snake9.LocalRup.prove_clause [c667, c1349, c659, c656, c669, c676, c720, c1300, c670, c672, c668, c663, c664, c88, c1122, c690, c687, c695] c1351 (by decide) p (sat_cons (step667 p h) (sat_cons (step1349 p h) (sat_cons (step659 p h) (sat_cons (step656 p h) (sat_cons (step669 p h) (sat_cons (step676 p h) (sat_cons (step720 p h) (sat_cons (step1300 p h) (sat_cons (step670 p h) (sat_cons (step672 p h) (sat_cons (step668 p h) (sat_cons (step663 p h) (sat_cons (step664 p h) (sat_cons (step88 p h) (sat_cons (step1122 p h) (sat_cons (step690 p h) (sat_cons (step687 p h) (sat_cons (step695 p h) (sat_nil p)))))))))))))))))))
def c1352 : List Lit := [(1486, false), (1537, true)]
theorem step1352 (p : Nat → Bool) (h : Constraints p) : clause p c1352 = true :=
  Snake9.LocalRup.prove_clause [c1303, c736, c1296, c1054, c1288, c1163, c591, c1051, c1049, c6, c1183, c1350] c1352 (by decide) p (sat_cons (step1303 p h) (sat_cons (step736 p h) (sat_cons (step1296 p h) (sat_cons (step1054 p h) (sat_cons (step1288 p h) (sat_cons (step1163 p h) (sat_cons (step591 p h) (sat_cons (step1051 p h) (sat_cons (step1049 p h) (sat_cons (step6 p h) (sat_cons (step1183 p h) (sat_cons (step1350 p h) (sat_nil p)))))))))))))
def c1353 : List Lit := [(61, false), (65, true), (100, true), (1559, true), (111, false)]
theorem step1353 (p : Nat → Bool) (h : Constraints p) : clause p c1353 = true :=
  Snake9.LocalRup.prove_clause [c1223, c156, c155, c762] c1353 (by decide) p (sat_cons (step1223 p h) (sat_cons (step156 p h) (sat_cons (step155 p h) (sat_cons (step762 p h) (sat_nil p)))))
def c1354 : List Lit := [(61, true), (1557, false), (1567, true), (111, false)]
theorem step1354 (p : Nat → Bool) (h : Constraints p) : clause p c1354 = true :=
  Snake9.LocalRup.prove_clause [c768, c781, c753, c750, c751, c752, c1152, c778, c769] c1354 (by decide) p (sat_cons (step768 p h) (sat_cons (step781 p h) (sat_cons (step753 p h) (sat_cons (step750 p h) (sat_cons (step751 p h) (sat_cons (step752 p h) (sat_cons (step1152 p h) (sat_cons (step778 p h) (sat_cons (step769 p h) (sat_nil p))))))))))
def c1355 : List Lit := [(1496, true), (1482, true), (38, false), (34, false)]
theorem step1355 (p : Nat → Bool) (h : Constraints p) : clause p c1355 = true :=
  Snake9.LocalRup.prove_clause [c692, c694, c690, c687, c88, c1121] c1355 (by decide) p (sat_cons (step692 p h) (sat_cons (step694 p h) (sat_cons (step690 p h) (sat_cons (step687 p h) (sat_cons (step88 p h) (sat_cons (step1121 p h) (sat_nil p)))))))
end B112E096
