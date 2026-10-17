import B112E152Part0004
namespace B112E152
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1267 : List Lit := [(1550, false), (1559, true)]
theorem step1267 (p : Nat → Bool) (h : Constraints p) : clause p c1267 = true :=
  Snake9.LocalRup.prove_clause [c970, c671] c1267 (by decide) p (sat_cons (step970 p h) (sat_cons (step671 p h) (sat_nil p)))
def c1268 : List Lit := [(1526, false), (1558, true)]
theorem step1268 (p : Nat → Bool) (h : Constraints p) : clause p c1268 = true :=
  Snake9.LocalRup.prove_clause [c972, c676] c1268 (by decide) p (sat_cons (step972 p h) (sat_cons (step676 p h) (sat_nil p)))
def c1269 : List Lit := [(1558, false), (1576, true)]
theorem step1269 (p : Nat → Bool) (h : Constraints p) : clause p c1269 = true :=
  Snake9.LocalRup.prove_clause [c975, c681] c1269 (by decide) p (sat_cons (step975 p h) (sat_cons (step681 p h) (sat_nil p)))
def c1270 : List Lit := [(1559, false), (1577, true)]
theorem step1270 (p : Nat → Bool) (h : Constraints p) : clause p c1270 = true :=
  Snake9.LocalRup.prove_clause [c975, c682] c1270 (by decide) p (sat_cons (step975 p h) (sat_cons (step682 p h) (sat_nil p)))
def c1271 : List Lit := [(1560, false), (1578, true)]
theorem step1271 (p : Nat → Bool) (h : Constraints p) : clause p c1271 = true :=
  Snake9.LocalRup.prove_clause [c975, c683] c1271 (by decide) p (sat_cons (step975 p h) (sat_cons (step683 p h) (sat_nil p)))
def c1272 : List Lit := [(1500, false), (1576, true)]
theorem step1272 (p : Nat → Bool) (h : Constraints p) : clause p c1272 = true :=
  Snake9.LocalRup.prove_clause [c1144, c685] c1272 (by decide) p (sat_cons (step1144 p h) (sat_cons (step685 p h) (sat_nil p)))
def c1273 : List Lit := [(1501, false), (1577, true)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true :=
  Snake9.LocalRup.prove_clause [c1144, c689] c1273 (by decide) p (sat_cons (step1144 p h) (sat_cons (step689 p h) (sat_nil p)))
def c1274 : List Lit := [(1502, false), (1578, true)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true :=
  Snake9.LocalRup.prove_clause [c1144, c691] c1274 (by decide) p (sat_cons (step1144 p h) (sat_cons (step691 p h) (sat_nil p)))
def c1275 : List Lit := [(1625, false), (1634, true)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true :=
  Snake9.LocalRup.prove_clause [c976, c762] c1275 (by decide) p (sat_cons (step976 p h) (sat_cons (step762 p h) (sat_nil p)))
def c1276 : List Lit := [(1626, false), (1635, true)]
theorem step1276 (p : Nat → Bool) (h : Constraints p) : clause p c1276 = true :=
  Snake9.LocalRup.prove_clause [c976, c763] c1276 (by decide) p (sat_cons (step976 p h) (sat_cons (step763 p h) (sat_nil p)))
def c1277 : List Lit := [(1627, false), (1636, true)]
theorem step1277 (p : Nat → Bool) (h : Constraints p) : clause p c1277 = true :=
  Snake9.LocalRup.prove_clause [c976, c764] c1277 (by decide) p (sat_cons (step976 p h) (sat_cons (step764 p h) (sat_nil p)))
def c1278 : List Lit := [(1635, false), (1701, false)]
theorem step1278 (p : Nat → Bool) (h : Constraints p) : clause p c1278 = true :=
  Snake9.LocalRup.prove_clause [c986, c893] c1278 (by decide) p (sat_cons (step986 p h) (sat_cons (step893 p h) (sat_nil p)))
def c1279 : List Lit := [(1636, false), (1700, false)]
theorem step1279 (p : Nat → Bool) (h : Constraints p) : clause p c1279 = true :=
  Snake9.LocalRup.prove_clause [c986, c898] c1279 (by decide) p (sat_cons (step986 p h) (sat_cons (step898 p h) (sat_nil p)))
def c1280 : List Lit := [(1637, false), (1699, false)]
theorem step1280 (p : Nat → Bool) (h : Constraints p) : clause p c1280 = true :=
  Snake9.LocalRup.prove_clause [c986, c904] c1280 (by decide) p (sat_cons (step986 p h) (sat_cons (step904 p h) (sat_nil p)))
def c1281 : List Lit := [(1638, false), (1698, false)]
theorem step1281 (p : Nat → Bool) (h : Constraints p) : clause p c1281 = true :=
  Snake9.LocalRup.prove_clause [c986, c908] c1281 (by decide) p (sat_cons (step986 p h) (sat_cons (step908 p h) (sat_nil p)))
def c1282 : List Lit := [(1639, false), (1697, false)]
theorem step1282 (p : Nat → Bool) (h : Constraints p) : clause p c1282 = true :=
  Snake9.LocalRup.prove_clause [c986, c912] c1282 (by decide) p (sat_cons (step986 p h) (sat_cons (step912 p h) (sat_nil p)))
def c1283 : List Lit := [(1576, false), (1718, false)]
theorem step1283 (p : Nat → Bool) (h : Constraints p) : clause p c1283 = true :=
  Snake9.LocalRup.prove_clause [c921, c916] c1283 (by decide) p (sat_cons (step921 p h) (sat_cons (step916 p h) (sat_nil p)))
def c1284 : List Lit := [(1577, false), (1717, false)]
theorem step1284 (p : Nat → Bool) (h : Constraints p) : clause p c1284 = true :=
  Snake9.LocalRup.prove_clause [c921, c917] c1284 (by decide) p (sat_cons (step921 p h) (sat_cons (step917 p h) (sat_nil p)))
def c1285 : List Lit := [(1578, false), (1716, false)]
theorem step1285 (p : Nat → Bool) (h : Constraints p) : clause p c1285 = true :=
  Snake9.LocalRup.prove_clause [c921, c918] c1285 (by decide) p (sat_cons (step921 p h) (sat_cons (step918 p h) (sat_nil p)))
def c1286 : List Lit := [(1579, false), (1715, false)]
theorem step1286 (p : Nat → Bool) (h : Constraints p) : clause p c1286 = true :=
  Snake9.LocalRup.prove_clause [c921, c919] c1286 (by decide) p (sat_cons (step921 p h) (sat_cons (step919 p h) (sat_nil p)))
def c1287 : List Lit := [(1580, false), (1714, false)]
theorem step1287 (p : Nat → Bool) (h : Constraints p) : clause p c1287 = true :=
  Snake9.LocalRup.prove_clause [c921, c920] c1287 (by decide) p (sat_cons (step921 p h) (sat_cons (step920 p h) (sat_nil p)))
def c1288 : List Lit := [(1627, false), (1699, false)]
theorem step1288 (p : Nat → Bool) (h : Constraints p) : clause p c1288 = true :=
  Snake9.LocalRup.prove_clause [c1144, c1019] c1288 (by decide) p (sat_cons (step1144 p h) (sat_cons (step1019 p h) (sat_nil p)))
def c1289 : List Lit := [(1698, false), (1637, false), (1622, false), (1604, false), (114, false)]
theorem step1289 (p : Nat → Bool) (h : Constraints p) : clause p c1289 = true :=
  Snake9.LocalRup.prove_clause [c1281, c903, c773, c1283, c756, c1272, c732, c1259, c1013, c1143, c725, c591, c576, c1148, c1209, c588, c573, c574, c1147, c1156, c29, c444, c582, c445, c1159, c453, c33, c459, c475, c492, c1258, c543, c516, c509, c508, c503, c502, c132, c1201, c1190] c1289 (by decide) p (sat_cons (step1281 p h) (sat_cons (step903 p h) (sat_cons (step773 p h) (sat_cons (step1283 p h) (sat_cons (step756 p h) (sat_cons (step1272 p h) (sat_cons (step732 p h) (sat_cons (step1259 p h) (sat_cons (step1013 p h) (sat_cons (step1143 p h) (sat_cons (step725 p h) (sat_cons (step591 p h) (sat_cons (step576 p h) (sat_cons (step1148 p h) (sat_cons (step1209 p h) (sat_cons (step588 p h) (sat_cons (step573 p h) (sat_cons (step574 p h) (sat_cons (step1147 p h) (sat_cons (step1156 p h) (sat_cons (step29 p h) (sat_cons (step444 p h) (sat_cons (step582 p h) (sat_cons (step445 p h) (sat_cons (step1159 p h) (sat_cons (step453 p h) (sat_cons (step33 p h) (sat_cons (step459 p h) (sat_cons (step475 p h) (sat_cons (step492 p h) (sat_cons (step1258 p h) (sat_cons (step543 p h) (sat_cons (step516 p h) (sat_cons (step509 p h) (sat_cons (step508 p h) (sat_cons (step503 p h) (sat_cons (step502 p h) (sat_cons (step132 p h) (sat_cons (step1201 p h) (sat_cons (step1190 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c1290 : List Lit := [(1668, true), (106, false), (50, false)]
theorem step1290 (p : Nat → Bool) (h : Constraints p) : clause p c1290 = true :=
  Snake9.LocalRup.prove_clause [c815, c816, c316] c1290 (by decide) p (sat_cons (step815 p h) (sat_cons (step816 p h) (sat_cons (step316 p h) (sat_nil p))))
def c1291 : List Lit := [(1687, true), (117, true), (1669, false)]
theorem step1291 (p : Nat → Bool) (h : Constraints p) : clause p c1291 = true :=
  Snake9.LocalRup.prove_clause [c833, c835, c1138, c855, c819, c827] c1291 (by decide) p (sat_cons (step833 p h) (sat_cons (step835 p h) (sat_cons (step1138 p h) (sat_cons (step855 p h) (sat_cons (step819 p h) (sat_cons (step827 p h) (sat_nil p)))))))
def c1292 : List Lit := [(1484, true), (88, false), (81, false), (114, false)]
theorem step1292 (p : Nat → Bool) (h : Constraints p) : clause p c1292 = true :=
  Snake9.LocalRup.prove_clause [c583, c584, c181, c46, c1221, c1222, c933] c1292 (by decide) p (sat_cons (step583 p h) (sat_cons (step584 p h) (sat_cons (step181 p h) (sat_cons (step46 p h) (sat_cons (step1221 p h) (sat_cons (step1222 p h) (sat_cons (step933 p h) (sat_nil p))))))))
def c1293 : List Lit := [(88, false), (67, true), (1604, false), (1699, false), (114, false)]
theorem step1293 (p : Nat → Bool) (h : Constraints p) : clause p c1293 = true :=
  Snake9.LocalRup.prove_clause [c1280, c772, c990, c1292, c979, c1259, c1272, c1283, c897, c1012, c771, c744, c754, c736, c730, c991] c1293 (by decide) p (sat_cons (step1280 p h) (sat_cons (step772 p h) (sat_cons (step990 p h) (sat_cons (step1292 p h) (sat_cons (step979 p h) (sat_cons (step1259 p h) (sat_cons (step1272 p h) (sat_cons (step1283 p h) (sat_cons (step897 p h) (sat_cons (step1012 p h) (sat_cons (step771 p h) (sat_cons (step744 p h) (sat_cons (step754 p h) (sat_cons (step736 p h) (sat_cons (step730 p h) (sat_cons (step991 p h) (sat_nil p)))))))))))))))))
def c1294 : List Lit := [(1604, false), (112, true), (1699, false), (1664, false), (1680, false), (1669, false), (114, false), (106, false), (50, false)]
theorem step1294 (p : Nat → Bool) (h : Constraints p) : clause p c1294 = true :=
  Snake9.LocalRup.prove_clause [c1280, c772, c751, c990, c1062, c305, c1293, c739, c742, c745, c1012, c755, c736, c1279, c730, c888, c727, c728, c860, c202, c161, c182, c828, c1217, c1218, c820, c932] c1294 (by decide) p (sat_cons (step1280 p h) (sat_cons (step772 p h) (sat_cons (step751 p h) (sat_cons (step990 p h) (sat_cons (step1062 p h) (sat_cons (step305 p h) (sat_cons (step1293 p h) (sat_cons (step739 p h) (sat_cons (step742 p h) (sat_cons (step745 p h) (sat_cons (step1012 p h) (sat_cons (step755 p h) (sat_cons (step736 p h) (sat_cons (step1279 p h) (sat_cons (step730 p h) (sat_cons (step888 p h) (sat_cons (step727 p h) (sat_cons (step728 p h) (sat_cons (step860 p h) (sat_cons (step202 p h) (sat_cons (step161 p h) (sat_cons (step182 p h) (sat_cons (step828 p h) (sat_cons (step1217 p h) (sat_cons (step1218 p h) (sat_cons (step820 p h) (sat_cons (step932 p h) (sat_nil p))))))))))))))))))))))))))))
def c1295 : List Lit := [(1594, false), (1604, true), (64, true), (114, false)]
theorem step1295 (p : Nat → Bool) (h : Constraints p) : clause p c1295 = true :=
  Snake9.LocalRup.prove_clause [c693, c696, c715, c706, c707, c718, c704, c697, c1201, c695, c1190, c1196] c1295 (by decide) p (sat_cons (step693 p h) (sat_cons (step696 p h) (sat_cons (step715 p h) (sat_cons (step706 p h) (sat_cons (step707 p h) (sat_cons (step718 p h) (sat_cons (step704 p h) (sat_cons (step697 p h) (sat_cons (step1201 p h) (sat_cons (step695 p h) (sat_cons (step1190 p h) (sat_cons (step1196 p h) (sat_nil p)))))))))))))
def c1296 : List Lit := [(1604, true), (106, false), (50, false), (1627, true), (64, true), (88, true), (114, false)]
theorem step1296 (p : Nat → Bool) (h : Constraints p) : clause p c1296 = true :=
  Snake9.LocalRup.prove_clause [c721, c1295, c701, c702, c1189, c305, c127, c741, c695, c743, c697, c700, c756, c718, c732, c705, c724, c704, c122, c1201, c1211, c1190, c1204] c1296 (by decide) p (sat_cons (step721 p h) (sat_cons (step1295 p h) (sat_cons (step701 p h) (sat_cons (step702 p h) (sat_cons (step1189 p h) (sat_cons (step305 p h) (sat_cons (step127 p h) (sat_cons (step741 p h) (sat_cons (step695 p h) (sat_cons (step743 p h) (sat_cons (step697 p h) (sat_cons (step700 p h) (sat_cons (step756 p h) (sat_cons (step718 p h) (sat_cons (step732 p h) (sat_cons (step705 p h) (sat_cons (step724 p h) (sat_cons (step704 p h) (sat_cons (step122 p h) (sat_cons (step1201 p h) (sat_cons (step1211 p h) (sat_cons (step1190 p h) (sat_cons (step1204 p h) (sat_nil p))))))))))))))))))))))))
def c1297 : List Lit := [(106, false), (50, false), (1699, false), (1664, false), (81, false), (88, true), (114, false)]
theorem step1297 (p : Nat → Bool) (h : Constraints p) : clause p c1297 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1280, c1058, c739, c742, c750, c1296, c772, c771, c751, c1062, c755, c897, c745, c312, c311, c310, c730, c1283, c736, c833, c817, c727, c728, c1269, c835, c202, c161, c182, c1268, c1294, c1225, c1213, c1016, c254, c612, c1037, c630] c1297 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1280 p h) (sat_cons (step1058 p h) (sat_cons (step739 p h) (sat_cons (step742 p h) (sat_cons (step750 p h) (sat_cons (step1296 p h) (sat_cons (step772 p h) (sat_cons (step771 p h) (sat_cons (step751 p h) (sat_cons (step1062 p h) (sat_cons (step755 p h) (sat_cons (step897 p h) (sat_cons (step745 p h) (sat_cons (step312 p h) (sat_cons (step311 p h) (sat_cons (step310 p h) (sat_cons (step730 p h) (sat_cons (step1283 p h) (sat_cons (step736 p h) (sat_cons (step833 p h) (sat_cons (step817 p h) (sat_cons (step727 p h) (sat_cons (step728 p h) (sat_cons (step1269 p h) (sat_cons (step835 p h) (sat_cons (step202 p h) (sat_cons (step161 p h) (sat_cons (step182 p h) (sat_cons (step1268 p h) (sat_cons (step1294 p h) (sat_cons (step1225 p h) (sat_cons (step1213 p h) (sat_cons (step1016 p h) (sat_cons (step254 p h) (sat_cons (step612 p h) (sat_cons (step1037 p h) (sat_cons (step630 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1298 : List Lit := [(106, true), (1637, true), (64, true), (1619, false), (114, false)]
theorem step1298 (p : Nat → Bool) (h : Constraints p) : clause p c1298 = true :=
  Snake9.LocalRup.prove_clause [c1188, c701, c1295, c772, c751, c1062, c745, c1223, c1224, c736, c934] c1298 (by decide) p (sat_cons (step1188 p h) (sat_cons (step701 p h) (sat_cons (step1295 p h) (sat_cons (step772 p h) (sat_cons (step751 p h) (sat_cons (step1062 p h) (sat_cons (step745 p h) (sat_cons (step1223 p h) (sat_cons (step1224 p h) (sat_cons (step736 p h) (sat_cons (step934 p h) (sat_nil p))))))))))))
def c1299 : List Lit := [(1636, true), (64, true), (1621, false), (114, false)]
theorem step1299 (p : Nat → Bool) (h : Constraints p) : clause p c1299 = true :=
  Snake9.LocalRup.prove_clause [c750, c1012, c771, c1189, c721, c1295, c702, c127, c695, c697, c700, c717, c718, c767, c705, c755, c704, c732, c1201, c724, c1190, c122, c1204, c1211] c1299 (by decide) p (sat_cons (step750 p h) (sat_cons (step1012 p h) (sat_cons (step771 p h) (sat_cons (step1189 p h) (sat_cons (step721 p h) (sat_cons (step1295 p h) (sat_cons (step702 p h) (sat_cons (step127 p h) (sat_cons (step695 p h) (sat_cons (step697 p h) (sat_cons (step700 p h) (sat_cons (step717 p h) (sat_cons (step718 p h) (sat_cons (step767 p h) (sat_cons (step705 p h) (sat_cons (step755 p h) (sat_cons (step704 p h) (sat_cons (step732 p h) (sat_cons (step1201 p h) (sat_cons (step724 p h) (sat_cons (step1190 p h) (sat_cons (step122 p h) (sat_cons (step1204 p h) (sat_cons (step1211 p h) (sat_nil p)))))))))))))))))))))))))
def c1300 : List Lit := [(76, false), (77, true), (62, false), (65, false)]
theorem step1300 (p : Nat → Bool) (h : Constraints p) : clause p c1300 = true :=
  Snake9.LocalRup.prove_clause [c122, c1211] c1300 (by decide) p (sat_cons (step122 p h) (sat_cons (step1211 p h) (sat_nil p)))
def c1301 : List Lit := [(1626, true), (1609, false)]
theorem step1301 (p : Nat → Bool) (h : Constraints p) : clause p c1301 = true :=
  Snake9.LocalRup.prove_clause [c732, c758, c733, c755, c742, c744, c739, c736, c991] c1301 (by decide) p (sat_cons (step732 p h) (sat_cons (step758 p h) (sat_cons (step733 p h) (sat_cons (step755 p h) (sat_cons (step742 p h) (sat_cons (step744 p h) (sat_cons (step739 p h) (sat_cons (step736 p h) (sat_cons (step991 p h) (sat_nil p))))))))))
def c1302 : List Lit := [(1621, true), (1636, false), (1500, false), (67, false), (1676, true)]
theorem step1302 (p : Nat → Bool) (h : Constraints p) : clause p c1302 = true :=
  Snake9.LocalRup.prove_clause [c1188, c830, c1041, c829, c742, c977, c740, c612, c305, c992, c319, c322, c1264, c1139, c792, c1291, c674, c987, c874, c687, c895, c1285] c1302 (by decide) p (sat_cons (step1188 p h) (sat_cons (step830 p h) (sat_cons (step1041 p h) (sat_cons (step829 p h) (sat_cons (step742 p h) (sat_cons (step977 p h) (sat_cons (step740 p h) (sat_cons (step612 p h) (sat_cons (step305 p h) (sat_cons (step992 p h) (sat_cons (step319 p h) (sat_cons (step322 p h) (sat_cons (step1264 p h) (sat_cons (step1139 p h) (sat_cons (step792 p h) (sat_cons (step1291 p h) (sat_cons (step674 p h) (sat_cons (step987 p h) (sat_cons (step874 p h) (sat_cons (step687 p h) (sat_cons (step895 p h) (sat_cons (step1285 p h) (sat_nil p)))))))))))))))))))))))
def c1303 : List Lit := [(86, false), (1621, false), (1609, false), (1500, false), (1603, false), (67, false), (81, false)]
theorem step1303 (p : Nat → Bool) (h : Constraints p) : clause p c1303 = true :=
  Snake9.LocalRup.prove_clause [c1301, c767, c1188, c1189, c931, c305, c992, c319, c322, c1079, c792, c1291, c686, c987, c874, c1284, c902, c896, c768, c881, c759, c995, c1039, c733, c794, c1099] c1303 (by decide) p (sat_cons (step1301 p h) (sat_cons (step767 p h) (sat_cons (step1188 p h) (sat_cons (step1189 p h) (sat_cons (step931 p h) (sat_cons (step305 p h) (sat_cons (step992 p h) (sat_cons (step319 p h) (sat_cons (step322 p h) (sat_cons (step1079 p h) (sat_cons (step792 p h) (sat_cons (step1291 p h) (sat_cons (step686 p h) (sat_cons (step987 p h) (sat_cons (step874 p h) (sat_cons (step1284 p h) (sat_cons (step902 p h) (sat_cons (step896 p h) (sat_cons (step768 p h) (sat_cons (step881 p h) (sat_cons (step759 p h) (sat_cons (step995 p h) (sat_cons (step1039 p h) (sat_cons (step733 p h) (sat_cons (step794 p h) (sat_cons (step1099 p h) (sat_nil p)))))))))))))))))))))))))))
def c1304 : List Lit := [(1627, true), (86, true), (1621, false), (1609, false)]
theorem step1304 (p : Nat → Bool) (h : Constraints p) : clause p c1304 = true :=
  Snake9.LocalRup.prove_clause [c740, c732, c756, c759, c743, c745, c733, c741, c736, c991] c1304 (by decide) p (sat_cons (step740 p h) (sat_cons (step732 p h) (sat_cons (step756 p h) (sat_cons (step759 p h) (sat_cons (step743 p h) (sat_cons (step745 p h) (sat_cons (step733 p h) (sat_cons (step741 p h) (sat_cons (step736 p h) (sat_cons (step991 p h) (sat_nil p)))))))))))
def c1305 : List Lit := [(1662, true), (62, false), (65, false)]
theorem step1305 (p : Nat → Bool) (h : Constraints p) : clause p c1305 = true :=
  Snake9.LocalRup.prove_clause [c987, c1021, c793, c107, c261, c1178] c1305 (by decide) p (sat_cons (step987 p h) (sat_cons (step1021 p h) (sat_cons (step793 p h) (sat_cons (step107 p h) (sat_cons (step261 p h) (sat_cons (step1178 p h) (sat_nil p)))))))
def c1306 : List Lit := [(1655, true), (1675, true), (1598, true), (62, false), (106, false), (114, false)]
theorem step1306 (p : Nat → Bool) (h : Constraints p) : clause p c1306 = true :=
  Snake9.LocalRup.prove_clause [c792, c793, c1045, c1088, c263] c1306 (by decide) p (sat_cons (step792 p h) (sat_cons (step793 p h) (sat_cons (step1045 p h) (sat_cons (step1088 p h) (sat_cons (step263 p h) (sat_nil p))))))
def c1307 : List Lit := [(101, false), (100, false), (1655, false), (1697, true), (113, true), (62, false), (1668, false)]
theorem step1307 (p : Nat → Bool) (h : Constraints p) : clause p c1307 = true :=
  Snake9.LocalRup.prove_clause [c261, c263, c1039, c820, c880, c825, c854] c1307 (by decide) p (sat_cons (step261 p h) (sat_cons (step263 p h) (sat_cons (step1039 p h) (sat_cons (step820 p h) (sat_cons (step880 p h) (sat_cons (step825 p h) (sat_cons (step854 p h) (sat_nil p))))))))
def c1308 : List Lit := [(101, true), (62, false), (65, false)]
theorem step1308 (p : Nat → Bool) (h : Constraints p) : clause p c1308 = true :=
  Snake9.LocalRup.prove_clause [c1178, c1177, c928] c1308 (by decide) p (sat_cons (step1178 p h) (sat_cons (step1177 p h) (sat_cons (step928 p h) (sat_nil p))))
def c1309 : List Lit := [(1686, true), (1670, false), (67, false)]
theorem step1309 (p : Nat → Bool) (h : Constraints p) : clause p c1309 = true :=
  Snake9.LocalRup.prove_clause [c1188, c1189, c931, c816, c824, c854, c851, c827, c835, c817, c833, c328] c1309 (by decide) p (sat_cons (step1188 p h) (sat_cons (step1189 p h) (sat_cons (step931 p h) (sat_cons (step816 p h) (sat_cons (step824 p h) (sat_cons (step854 p h) (sat_cons (step851 p h) (sat_cons (step827 p h) (sat_cons (step835 p h) (sat_cons (step817 p h) (sat_cons (step833 p h) (sat_cons (step328 p h) (sat_nil p)))))))))))))
def c1310 : List Lit := [(1717, true), (1686, false), (101, false), (1662, false), (1637, false), (1627, false), (1598, true), (62, false), (1668, false), (106, false), (1591, false), (114, false)]
theorem step1310 (p : Nat → Bool) (h : Constraints p) : clause p c1310 = true :=
  Snake9.LocalRup.prove_clause [c705, c704, c1201, c1190, c1198, c818, c902, c874, c859, c1306, c1307, c880, c995, c1039, c794, c262, c1049] c1310 (by decide) p (sat_cons (step705 p h) (sat_cons (step704 p h) (sat_cons (step1201 p h) (sat_cons (step1190 p h) (sat_cons (step1198 p h) (sat_cons (step818 p h) (sat_cons (step902 p h) (sat_cons (step874 p h) (sat_cons (step859 p h) (sat_cons (step1306 p h) (sat_cons (step1307 p h) (sat_cons (step880 p h) (sat_cons (step995 p h) (sat_cons (step1039 p h) (sat_cons (step794 p h) (sat_cons (step262 p h) (sat_cons (step1049 p h) (sat_nil p))))))))))))))))))
def c1311 : List Lit := [(1604, true), (81, false), (1676, true)]
theorem step1311 (p : Nat → Bool) (h : Constraints p) : clause p c1311 = true :=
  Snake9.TreeRup.prove_clause [c830, c1058, c693, c696, c721, c1295, c701, c702, c1188, c1189, c127, c931, c695, c816, c697, c700, c717, c718, c705, c704, c1201, c1190, c1204, c1194, c1198, c573, c818, c576, c1013, c1272, c1283, c1300, c724, c1301, c767, c1302, c1303, c1304, c768, c1305, c1308, c1309, c1310, c903, c875, c1284, c686, c1079, c306, c308, c307, c792, c833, c817, c835, c1291, c860, c881, c828, c995, c1039, c820, c794, c267] c1311 (by decide) p (sat_cons (step830 p h) (sat_cons (step1058 p h) (sat_cons (step693 p h) (sat_cons (step696 p h) (sat_cons (step721 p h) (sat_cons (step1295 p h) (sat_cons (step701 p h) (sat_cons (step702 p h) (sat_cons (step1188 p h) (sat_cons (step1189 p h) (sat_cons (step127 p h) (sat_cons (step931 p h) (sat_cons (step695 p h) (sat_cons (step816 p h) (sat_cons (step697 p h) (sat_cons (step700 p h) (sat_cons (step717 p h) (sat_cons (step718 p h) (sat_cons (step705 p h) (sat_cons (step704 p h) (sat_cons (step1201 p h) (sat_cons (step1190 p h) (sat_cons (step1204 p h) (sat_cons (step1194 p h) (sat_cons (step1198 p h) (sat_cons (step573 p h) (sat_cons (step818 p h) (sat_cons (step576 p h) (sat_cons (step1013 p h) (sat_cons (step1272 p h) (sat_cons (step1283 p h) (sat_cons (step1300 p h) (sat_cons (step724 p h) (sat_cons (step1301 p h) (sat_cons (step767 p h) (sat_cons (step1302 p h) (sat_cons (step1303 p h) (sat_cons (step1304 p h) (sat_cons (step768 p h) (sat_cons (step1305 p h) (sat_cons (step1308 p h) (sat_cons (step1309 p h) (sat_cons (step1310 p h) (sat_cons (step903 p h) (sat_cons (step875 p h) (sat_cons (step1284 p h) (sat_cons (step686 p h) (sat_cons (step1079 p h) (sat_cons (step306 p h) (sat_cons (step308 p h) (sat_cons (step307 p h) (sat_cons (step792 p h) (sat_cons (step833 p h) (sat_cons (step817 p h) (sat_cons (step835 p h) (sat_cons (step1291 p h) (sat_cons (step860 p h) (sat_cons (step881 p h) (sat_cons (step828 p h) (sat_cons (step995 p h) (sat_cons (step1039 p h) (sat_cons (step820 p h) (sat_cons (step794 p h) (sat_cons (step267 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1312 : List Lit := [(1678, true), (1676, true)]
theorem step1312 (p : Nat → Bool) (h : Constraints p) : clause p c1312 = true :=
  Snake9.LocalRup.prove_clause [c832, c833, c1054] c1312 (by decide) p (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step1054 p h) (sat_nil p))))
def c1313 : List Lit := [(112, false), (100, false), (99, false), (114, false)]
theorem step1313 (p : Nat → Bool) (h : Constraints p) : clause p c1313 = true :=
  Snake9.LocalRup.prove_clause [c1088, c267] c1313 (by decide) p (sat_cons (step1088 p h) (sat_cons (step267 p h) (sat_nil p)))
def c1314 : List Lit := [(1650, true), (81, false), (114, false)]
theorem step1314 (p : Nat → Bool) (h : Constraints p) : clause p c1314 = true :=
  Snake9.LocalRup.prove_clause [c784, c786, c781, c782, c220, c211, c1227] c1314 (by decide) p (sat_cons (step784 p h) (sat_cons (step786 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step220 p h) (sat_cons (step211 p h) (sat_cons (step1227 p h) (sat_nil p))))))))
def c1315 : List Lit := [(1626, false), (1558, false), (1697, false), (67, true), (1604, false), (1591, false), (114, false)]
theorem step1315 (p : Nat → Bool) (h : Constraints p) : clause p c1315 = true :=
  Snake9.LocalRup.prove_clause [c772, c1134, c902, c1284] c1315 (by decide) p (sat_cons (step772 p h) (sat_cons (step1134 p h) (sat_cons (step902 p h) (sat_cons (step1284 p h) (sat_nil p)))))
def c1316 : List Lit := [(1626, true), (104, false), (106, false)]
theorem step1316 (p : Nat → Bool) (h : Constraints p) : clause p c1316 = true :=
  Snake9.LocalRup.prove_clause [c751, c1062, c935, c1225, c1101, c755, c730, c727, c204, c202, c739, c736, c745] c1316 (by decide) p (sat_cons (step751 p h) (sat_cons (step1062 p h) (sat_cons (step935 p h) (sat_cons (step1225 p h) (sat_cons (step1101 p h) (sat_cons (step755 p h) (sat_cons (step730 p h) (sat_cons (step727 p h) (sat_cons (step204 p h) (sat_cons (step202 p h) (sat_cons (step739 p h) (sat_cons (step736 p h) (sat_cons (step745 p h) (sat_nil p))))))))))))))
def c1317 : List Lit := [(1626, true), (99, false), (100, false), (1663, true), (106, false), (81, false), (114, false)]
theorem step1317 (p : Nat → Bool) (h : Constraints p) : clause p c1317 = true :=
  Snake9.LocalRup.prove_clause [c1099, c730, c291, c758, c1062, c1100, c755, c731, c792, c742, c744, c1101, c795, c739, c736, c1225, c812, c192, c785, c783, c221, c1219, c184, c185, c729] c1317 (by decide) p (sat_cons (step1099 p h) (sat_cons (step730 p h) (sat_cons (step291 p h) (sat_cons (step758 p h) (sat_cons (step1062 p h) (sat_cons (step1100 p h) (sat_cons (step755 p h) (sat_cons (step731 p h) (sat_cons (step792 p h) (sat_cons (step742 p h) (sat_cons (step744 p h) (sat_cons (step1101 p h) (sat_cons (step795 p h) (sat_cons (step739 p h) (sat_cons (step736 p h) (sat_cons (step1225 p h) (sat_cons (step812 p h) (sat_cons (step192 p h) (sat_cons (step785 p h) (sat_cons (step783 p h) (sat_cons (step221 p h) (sat_cons (step1219 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step729 p h) (sat_nil p))))))))))))))))))))))))))
def c1318 : List Lit := [(93, false), (1651, true), (81, false), (114, false)]
theorem step1318 (p : Nat → Bool) (h : Constraints p) : clause p c1318 = true :=
  Snake9.LocalRup.prove_clause [c220, c221, c787, c782] c1318 (by decide) p (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step787 p h) (sat_cons (step782 p h) (sat_nil p)))))
def c1319 : List Lit := [(1663, true), (107, true), (113, true), (81, false), (1680, false), (50, false), (104, true), (1655, false), (1637, false), (1697, false), (1604, false), (114, false), (106, false)]
theorem step1319 (p : Nat → Bool) (h : Constraints p) : clause p c1319 = true :=
  Snake9.LocalRup.prove_clause [c987, c795, c995, c1039, c812, c794, c1099, c1313, c291, c730, c820, c1318, c1219, c1220, c924, c583, c979, c1259, c1272, c1283, c907, c903, c773, c875, c756, c860, c743, c828, c817, c311, c740, c741, c742, c184, c185, c759, c729, c731] c1319 (by decide) p (sat_cons (step987 p h) (sat_cons (step795 p h) (sat_cons (step995 p h) (sat_cons (step1039 p h) (sat_cons (step812 p h) (sat_cons (step794 p h) (sat_cons (step1099 p h) (sat_cons (step1313 p h) (sat_cons (step291 p h) (sat_cons (step730 p h) (sat_cons (step820 p h) (sat_cons (step1318 p h) (sat_cons (step1219 p h) (sat_cons (step1220 p h) (sat_cons (step924 p h) (sat_cons (step583 p h) (sat_cons (step979 p h) (sat_cons (step1259 p h) (sat_cons (step1272 p h) (sat_cons (step1283 p h) (sat_cons (step907 p h) (sat_cons (step903 p h) (sat_cons (step773 p h) (sat_cons (step875 p h) (sat_cons (step756 p h) (sat_cons (step860 p h) (sat_cons (step743 p h) (sat_cons (step828 p h) (sat_cons (step817 p h) (sat_cons (step311 p h) (sat_cons (step740 p h) (sat_cons (step741 p h) (sat_cons (step742 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step759 p h) (sat_cons (step729 p h) (sat_cons (step731 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1320 : List Lit := [(100, false), (119, true), (112, false), (1605, true), (103, true), (93, true), (1589, false), (114, false), (1594, false)]
theorem step1320 (p : Nat → Bool) (h : Constraints p) : clause p c1320 = true :=
  Snake9.LocalRup.prove_clause [c953, c360, c1088, c1246, c263, c1201, c699, c704, c719, c707] c1320 (by decide) p (sat_cons (step953 p h) (sat_cons (step360 p h) (sat_cons (step1088 p h) (sat_cons (step1246 p h) (sat_cons (step263 p h) (sat_cons (step1201 p h) (sat_cons (step699 p h) (sat_cons (step704 p h) (sat_cons (step719 p h) (sat_cons (step707 p h) (sat_nil p)))))))))))
def c1321 : List Lit := [(103, true), (93, true), (1663, false), (107, true), (113, true), (81, false), (1676, true), (104, true), (1637, false), (1626, false), (1697, false), (114, false), (1558, true), (106, false), (1594, false)]
theorem step1321 (p : Nat → Bool) (h : Constraints p) : clause p c1321 = true :=
  Snake9.LocalRup.prove_clause [c1312, c835, c1041, c1266, c829, c1139, c1290, c818, c824, c851, c1058, c693, c1314, c1219, c1220, c924, c583, c979, c1259, c1272, c1283, c907, c903, c776, c886, c881, c810, c852, c855, c836, c825, c827, c820, c817, c318, c834, c394, c1320, c794, c799, c789, c355, c1118, c256, c1249, c1037, c1123, c627, c654, c673, c658] c1321 (by decide) p (sat_cons (step1312 p h) (sat_cons (step835 p h) (sat_cons (step1041 p h) (sat_cons (step1266 p h) (sat_cons (step829 p h) (sat_cons (step1139 p h) (sat_cons (step1290 p h) (sat_cons (step818 p h) (sat_cons (step824 p h) (sat_cons (step851 p h) (sat_cons (step1058 p h) (sat_cons (step693 p h) (sat_cons (step1314 p h) (sat_cons (step1219 p h) (sat_cons (step1220 p h) (sat_cons (step924 p h) (sat_cons (step583 p h) (sat_cons (step979 p h) (sat_cons (step1259 p h) (sat_cons (step1272 p h) (sat_cons (step1283 p h) (sat_cons (step907 p h) (sat_cons (step903 p h) (sat_cons (step776 p h) (sat_cons (step886 p h) (sat_cons (step881 p h) (sat_cons (step810 p h) (sat_cons (step852 p h) (sat_cons (step855 p h) (sat_cons (step836 p h) (sat_cons (step825 p h) (sat_cons (step827 p h) (sat_cons (step820 p h) (sat_cons (step817 p h) (sat_cons (step318 p h) (sat_cons (step834 p h) (sat_cons (step394 p h) (sat_cons (step1320 p h) (sat_cons (step794 p h) (sat_cons (step799 p h) (sat_cons (step789 p h) (sat_cons (step355 p h) (sat_cons (step1118 p h) (sat_cons (step256 p h) (sat_cons (step1249 p h) (sat_cons (step1037 p h) (sat_cons (step1123 p h) (sat_cons (step627 p h) (sat_cons (step654 p h) (sat_cons (step673 p h) (sat_cons (step658 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1322 : List Lit := [(1531, false), (116, false), (1539, false), (1549, true)]
theorem step1322 (p : Nat → Bool) (h : Constraints p) : clause p c1322 = true :=
  Snake9.LocalRup.prove_clause [c653, c664, c641, c642, c661, c637, c654, c649, c650, c1123, c1141] c1322 (by decide) p (sat_cons (step653 p h) (sat_cons (step664 p h) (sat_cons (step641 p h) (sat_cons (step642 p h) (sat_cons (step661 p h) (sat_cons (step637 p h) (sat_cons (step654 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step1123 p h) (sat_cons (step1141 p h) (sat_nil p))))))))))))
def c1323 : List Lit := [(107, true), (113, true), (81, false), (1676, true), (104, true), (1655, false), (1626, false), (1697, false), (1604, false), (114, false), (1558, true), (106, false), (1594, false)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true :=
  Snake9.LocalRup.prove_clause [c1312, c835, c1041, c1266, c829, c1139, c1290, c818, c824, c851, c772, c1322, c633, c634, c73, c1140, c1272, c1283, c903, c886, c282, c1319, c1321, c1318, c881, c813, c855, c796, c798, c825, c794, c789, c820, c1313] c1323 (by decide) p (sat_cons (step1312 p h) (sat_cons (step835 p h) (sat_cons (step1041 p h) (sat_cons (step1266 p h) (sat_cons (step829 p h) (sat_cons (step1139 p h) (sat_cons (step1290 p h) (sat_cons (step818 p h) (sat_cons (step824 p h) (sat_cons (step851 p h) (sat_cons (step772 p h) (sat_cons (step1322 p h) (sat_cons (step633 p h) (sat_cons (step634 p h) (sat_cons (step73 p h) (sat_cons (step1140 p h) (sat_cons (step1272 p h) (sat_cons (step1283 p h) (sat_cons (step903 p h) (sat_cons (step886 p h) (sat_cons (step282 p h) (sat_cons (step1319 p h) (sat_cons (step1321 p h) (sat_cons (step1318 p h) (sat_cons (step881 p h) (sat_cons (step813 p h) (sat_cons (step855 p h) (sat_cons (step796 p h) (sat_cons (step798 p h) (sat_cons (step825 p h) (sat_cons (step794 p h) (sat_cons (step789 p h) (sat_cons (step820 p h) (sat_cons (step1313 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1324 : List Lit := [(1549, true), (44, false), (1513, true), (1531, false), (1539, false)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true :=
  Snake9.LocalRup.prove_clause [c641, c653, c664, c642, c661, c637, c654, c998, c1015] c1324 (by decide) p (sat_cons (step641 p h) (sat_cons (step653 p h) (sat_cons (step664 p h) (sat_cons (step642 p h) (sat_cons (step661 p h) (sat_cons (step637 p h) (sat_cons (step654 p h) (sat_cons (step998 p h) (sat_cons (step1015 p h) (sat_nil p))))))))))
def c1325 : List Lit := [(48, false), (1541, true), (1513, true), (44, false)]
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true :=
  Snake9.LocalRup.prove_clause [c1015, c998] c1325 (by decide) p (sat_cons (step1015 p h) (sat_cons (step998 p h) (sat_nil p)))
def c1326 : List Lit := [(64, false), (103, true), (114, false)]
theorem step1326 (p : Nat → Bool) (h : Constraints p) : clause p c1326 = true :=
  Snake9.LocalRup.prove_clause [c1200, c1184] c1326 (by decide) p (sat_cons (step1200 p h) (sat_cons (step1184 p h) (sat_nil p)))
def c1327 : List Lit := [(64, true), (114, false), (1604, true), (101, true), (67, false)]
theorem step1327 (p : Nat → Bool) (h : Constraints p) : clause p c1327 = true :=
  Snake9.LocalRup.prove_clause [c721, c1189, c1295, c702, c1308, c127, c700, c695] c1327 (by decide) p (sat_cons (step721 p h) (sat_cons (step1189 p h) (sat_cons (step1295 p h) (sat_cons (step702 p h) (sat_cons (step1308 p h) (sat_cons (step127 p h) (sat_cons (step700 p h) (sat_cons (step695 p h) (sat_nil p)))))))))
def c1328 : List Lit := [(114, false), (1604, true), (101, true), (100, false), (67, false)]
theorem step1328 (p : Nat → Bool) (h : Constraints p) : clause p c1328 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1200, c288, c1184] c1328 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1200 p h) (sat_cons (step288 p h) (sat_cons (step1184 p h) (sat_nil p)))))
def c1329 : List Lit := [(1718, true), (101, true), (100, false), (99, false), (1670, false), (1669, false), (117, true), (50, false), (1626, false), (1662, false), (1698, false), (67, false), (1676, false)]
theorem step1329 (p : Nat → Bool) (h : Constraints p) : clause p c1329 = true :=
  Snake9.LocalRup.prove_clause [c1032, c1096, c767, c827, c833, c838, c903, c897, c772, c876, c1017, c861, c857, c828, c841, c1106, c820, c1328, c831, c356, c390, c1247] c1329 (by decide) p (sat_cons (step1032 p h) (sat_cons (step1096 p h) (sat_cons (step767 p h) (sat_cons (step827 p h) (sat_cons (step833 p h) (sat_cons (step838 p h) (sat_cons (step903 p h) (sat_cons (step897 p h) (sat_cons (step772 p h) (sat_cons (step876 p h) (sat_cons (step1017 p h) (sat_cons (step861 p h) (sat_cons (step857 p h) (sat_cons (step828 p h) (sat_cons (step841 p h) (sat_cons (step1106 p h) (sat_cons (step820 p h) (sat_cons (step1328 p h) (sat_cons (step831 p h) (sat_cons (step356 p h) (sat_cons (step390 p h) (sat_cons (step1247 p h) (sat_nil p)))))))))))))))))))))))
def c1330 : List Lit := [(1663, true), (1670, false), (1669, false), (117, true), (50, false), (1626, false), (44, false), (104, true), (1698, false), (67, false), (1676, false)]
theorem step1330 (p : Nat → Bool) (h : Constraints p) : clause p c1330 = true :=
  Snake9.LocalRup.prove_clause [c792, c987, c995, c1039, c794, c255, c1168, c1169, c68, c634, c641, c1329, c1283, c1269, c1266, c1105, c661, c84, c649, c652, c654, c664, c1008, c644, c635] c1330 (by decide) p (sat_cons (step792 p h) (sat_cons (step987 p h) (sat_cons (step995 p h) (sat_cons (step1039 p h) (sat_cons (step794 p h) (sat_cons (step255 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step68 p h) (sat_cons (step634 p h) (sat_cons (step641 p h) (sat_cons (step1329 p h) (sat_cons (step1283 p h) (sat_cons (step1269 p h) (sat_cons (step1266 p h) (sat_cons (step1105 p h) (sat_cons (step661 p h) (sat_cons (step84 p h) (sat_cons (step649 p h) (sat_cons (step652 p h) (sat_cons (step654 p h) (sat_cons (step664 p h) (sat_cons (step1008 p h) (sat_cons (step644 p h) (sat_cons (step635 p h) (sat_nil p))))))))))))))))))))))))))
end B112E152
