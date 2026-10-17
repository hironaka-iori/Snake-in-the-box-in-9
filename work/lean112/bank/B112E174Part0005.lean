import B112E174Part0004
namespace B112E174
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1341 : List Lit := [(60, false), (61, true), (59, true)]
theorem step1341 (p : Nat → Bool) (h : Constraints p) : clause p c1341 = true :=
  Snake9.LocalRup.prove_clause [c282, c184] c1341 (by decide) p (sat_cons (step282 p h) (sat_cons (step184 p h) (sat_nil p)))
def c1342 : List Lit := [(62, false), (66, true)]
theorem step1342 (p : Nat → Bool) (h : Constraints p) : clause p c1342 = true :=
  Snake9.LocalRup.prove_clause [c283, c191] c1342 (by decide) p (sat_cons (step283 p h) (sat_cons (step191 p h) (sat_nil p)))
def c1343 : List Lit := [(62, false), (61, true)]
theorem step1343 (p : Nat → Bool) (h : Constraints p) : clause p c1343 = true :=
  Snake9.LocalRup.prove_clause [c283, c192] c1343 (by decide) p (sat_cons (step283 p h) (sat_cons (step192 p h) (sat_nil p)))
def c1344 : List Lit := [(59, true), (63, false), (64, true)]
theorem step1344 (p : Nat → Bool) (h : Constraints p) : clause p c1344 = true :=
  Snake9.LocalRup.prove_clause [c284, c194] c1344 (by decide) p (sat_cons (step284 p h) (sat_cons (step194 p h) (sat_nil p)))
def c1345 : List Lit := [(4, true), (64, true), (63, false)]
theorem step1345 (p : Nat → Bool) (h : Constraints p) : clause p c1345 = true :=
  Snake9.LocalRup.prove_clause [c284, c195] c1345 (by decide) p (sat_cons (step284 p h) (sat_cons (step195 p h) (sat_nil p)))
def c1346 : List Lit := [(59, true), (63, false), (4, true)]
theorem step1346 (p : Nat → Bool) (h : Constraints p) : clause p c1346 = true :=
  Snake9.LocalRup.prove_clause [c284, c196] c1346 (by decide) p (sat_cons (step284 p h) (sat_cons (step196 p h) (sat_nil p)))
def c1347 : List Lit := [(66, true), (56, true), (65, false)]
theorem step1347 (p : Nat → Bool) (h : Constraints p) : clause p c1347 = true :=
  Snake9.LocalRup.prove_clause [c285, c202] c1347 (by decide) p (sat_cons (step285 p h) (sat_cons (step202 p h) (sat_nil p)))
def c1348 : List Lit := [(68, false), (17, true)]
theorem step1348 (p : Nat → Bool) (h : Constraints p) : clause p c1348 = true :=
  Snake9.LocalRup.prove_clause [c286, c211] c1348 (by decide) p (sat_cons (step286 p h) (sat_cons (step211 p h) (sat_nil p)))
def c1349 : List Lit := [(78, false), (77, true)]
theorem step1349 (p : Nat → Bool) (h : Constraints p) : clause p c1349 = true :=
  Snake9.LocalRup.prove_clause [c290, c229] c1349 (by decide) p (sat_cons (step290 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1350 : List Lit := [(78, false), (75, true)]
theorem step1350 (p : Nat → Bool) (h : Constraints p) : clause p c1350 = true :=
  Snake9.LocalRup.prove_clause [c290, c230] c1350 (by decide) p (sat_cons (step290 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1351 : List Lit := [(85, false), (84, true)]
theorem step1351 (p : Nat → Bool) (h : Constraints p) : clause p c1351 = true :=
  Snake9.LocalRup.prove_clause [c294, c236] c1351 (by decide) p (sat_cons (step294 p h) (sat_cons (step236 p h) (sat_nil p)))
def c1352 : List Lit := [(217, false), (227, false)]
theorem step1352 (p : Nat → Bool) (h : Constraints p) : clause p c1352 = true :=
  Snake9.LocalRup.prove_clause [c1035, c320] c1352 (by decide) p (sat_cons (step1035 p h) (sat_cons (step320 p h) (sat_nil p)))
def c1353 : List Lit := [(229, false), (253, false)]
theorem step1353 (p : Nat → Bool) (h : Constraints p) : clause p c1353 = true :=
  Snake9.LocalRup.prove_clause [c1029, c345] c1353 (by decide) p (sat_cons (step1029 p h) (sat_cons (step345 p h) (sat_nil p)))
def c1354 : List Lit := [(269, false), (275, false)]
theorem step1354 (p : Nat → Bool) (h : Constraints p) : clause p c1354 = true :=
  Snake9.LocalRup.prove_clause [c1040, c363] c1354 (by decide) p (sat_cons (step1040 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1355 : List Lit := [(265, false), (277, false)]
theorem step1355 (p : Nat → Bool) (h : Constraints p) : clause p c1355 = true :=
  Snake9.LocalRup.prove_clause [c1033, c367] c1355 (by decide) p (sat_cons (step1033 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1356 : List Lit := [(295, false), (297, false)]
theorem step1356 (p : Nat → Bool) (h : Constraints p) : clause p c1356 = true :=
  Snake9.LocalRup.prove_clause [c1046, c380] c1356 (by decide) p (sat_cons (step1046 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1357 : List Lit := [(289, false), (301, false)]
theorem step1357 (p : Nat → Bool) (h : Constraints p) : clause p c1357 = true :=
  Snake9.LocalRup.prove_clause [c1032, c387] c1357 (by decide) p (sat_cons (step1032 p h) (sat_cons (step387 p h) (sat_nil p)))
def c1358 : List Lit := [(279, false), (303, false)]
theorem step1358 (p : Nat → Bool) (h : Constraints p) : clause p c1358 = true :=
  Snake9.LocalRup.prove_clause [c1028, c391] c1358 (by decide) p (sat_cons (step1028 p h) (sat_cons (step391 p h) (sat_nil p)))
def c1359 : List Lit := [(255, false), (305, false)]
theorem step1359 (p : Nat → Bool) (h : Constraints p) : clause p c1359 = true :=
  Snake9.LocalRup.prove_clause [c1025, c396] c1359 (by decide) p (sat_cons (step1025 p h) (sat_cons (step396 p h) (sat_nil p)))
def c1360 : List Lit := [(331, false), (355, false)]
theorem step1360 (p : Nat → Bool) (h : Constraints p) : clause p c1360 = true :=
  Snake9.LocalRup.prove_clause [c1027, c451] c1360 (by decide) p (sat_cons (step1027 p h) (sat_cons (step451 p h) (sat_nil p)))
def c1361 : List Lit := [(381, false), (405, false)]
theorem step1361 (p : Nat → Bool) (h : Constraints p) : clause p c1361 = true :=
  Snake9.LocalRup.prove_clause [c1026, c490] c1361 (by decide) p (sat_cons (step1026 p h) (sat_cons (step490 p h) (sat_nil p)))
def c1362 : List Lit := [(357, false), (407, false)]
theorem step1362 (p : Nat → Bool) (h : Constraints p) : clause p c1362 = true :=
  Snake9.LocalRup.prove_clause [c1024, c494] c1362 (by decide) p (sat_cons (step1024 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1363 : List Lit := [(307, false), (409, false)]
theorem step1363 (p : Nat → Bool) (h : Constraints p) : clause p c1363 = true :=
  Snake9.LocalRup.prove_clause [c499, c497] c1363 (by decide) p (sat_cons (step499 p h) (sat_cons (step497 p h) (sat_nil p)))
def c1364 : List Lit := [(734, false), (778, false)]
theorem step1364 (p : Nat → Bool) (h : Constraints p) : clause p c1364 = true :=
  Snake9.LocalRup.prove_clause [c1135, c646] c1364 (by decide) p (sat_cons (step1135 p h) (sat_cons (step646 p h) (sat_nil p)))
def c1365 : List Lit := [(790, false), (898, false)]
theorem step1365 (p : Nat → Bool) (h : Constraints p) : clause p c1365 = true :=
  Snake9.LocalRup.prove_clause [c762, c756] c1365 (by decide) p (sat_cons (step762 p h) (sat_cons (step756 p h) (sat_nil p)))
def c1366 : List Lit := [(791, false), (897, false)]
theorem step1366 (p : Nat → Bool) (h : Constraints p) : clause p c1366 = true :=
  Snake9.LocalRup.prove_clause [c762, c757] c1366 (by decide) p (sat_cons (step762 p h) (sat_cons (step757 p h) (sat_nil p)))
def c1367 : List Lit := [(792, false), (896, false)]
theorem step1367 (p : Nat → Bool) (h : Constraints p) : clause p c1367 = true :=
  Snake9.LocalRup.prove_clause [c762, c758] c1367 (by decide) p (sat_cons (step762 p h) (sat_cons (step758 p h) (sat_nil p)))
def c1368 : List Lit := [(793, false), (895, false)]
theorem step1368 (p : Nat → Bool) (h : Constraints p) : clause p c1368 = true :=
  Snake9.LocalRup.prove_clause [c762, c759] c1368 (by decide) p (sat_cons (step762 p h) (sat_cons (step759 p h) (sat_nil p)))
def c1369 : List Lit := [(1270, true), (1266, false)]
theorem step1369 (p : Nat → Bool) (h : Constraints p) : clause p c1369 = true :=
  Snake9.LocalRup.prove_clause [c1074, c844] c1369 (by decide) p (sat_cons (step1074 p h) (sat_cons (step844 p h) (sat_nil p)))
def c1370 : List Lit := [(1267, false), (1271, true)]
theorem step1370 (p : Nat → Bool) (h : Constraints p) : clause p c1370 = true :=
  Snake9.LocalRup.prove_clause [c1074, c845] c1370 (by decide) p (sat_cons (step1074 p h) (sat_cons (step845 p h) (sat_nil p)))
def c1371 : List Lit := [(1289, false), (1297, true)]
theorem step1371 (p : Nat → Bool) (h : Constraints p) : clause p c1371 = true :=
  Snake9.LocalRup.prove_clause [c1110, c876] c1371 (by decide) p (sat_cons (step1110 p h) (sat_cons (step876 p h) (sat_nil p)))
def c1372 : List Lit := [(1297, true), (1270, false)]
theorem step1372 (p : Nat → Bool) (h : Constraints p) : clause p c1372 = true :=
  Snake9.LocalRup.prove_clause [c1112, c878] c1372 (by decide) p (sat_cons (step1112 p h) (sat_cons (step878 p h) (sat_nil p)))
def c1373 : List Lit := [(1298, true), (1271, false)]
theorem step1373 (p : Nat → Bool) (h : Constraints p) : clause p c1373 = true :=
  Snake9.LocalRup.prove_clause [c1112, c881] c1373 (by decide) p (sat_cons (step1112 p h) (sat_cons (step881 p h) (sat_nil p)))
def c1374 : List Lit := [(1272, false), (1299, true)]
theorem step1374 (p : Nat → Bool) (h : Constraints p) : clause p c1374 = true :=
  Snake9.LocalRup.prove_clause [c1112, c883] c1374 (by decide) p (sat_cons (step1112 p h) (sat_cons (step883 p h) (sat_nil p)))
def c1375 : List Lit := [(1297, false), (1313, true)]
theorem step1375 (p : Nat → Bool) (h : Constraints p) : clause p c1375 = true :=
  Snake9.LocalRup.prove_clause [c1072, c885] c1375 (by decide) p (sat_cons (step1072 p h) (sat_cons (step885 p h) (sat_nil p)))
def c1376 : List Lit := [(1384, false), (1412, true)]
theorem step1376 (p : Nat → Bool) (h : Constraints p) : clause p c1376 = true :=
  Snake9.LocalRup.prove_clause [c1172, c988] c1376 (by decide) p (sat_cons (step1172 p h) (sat_cons (step988 p h) (sat_nil p)))
def c1377 : List Lit := [(1385, false), (1413, true)]
theorem step1377 (p : Nat → Bool) (h : Constraints p) : clause p c1377 = true :=
  Snake9.LocalRup.prove_clause [c1172, c990] c1377 (by decide) p (sat_cons (step1172 p h) (sat_cons (step990 p h) (sat_nil p)))
def c1378 : List Lit := [(1425, true), (1357, false)]
theorem step1378 (p : Nat → Bool) (h : Constraints p) : clause p c1378 = true :=
  Snake9.LocalRup.prove_clause [c1200, c991] c1378 (by decide) p (sat_cons (step1200 p h) (sat_cons (step991 p h) (sat_nil p)))
def c1379 : List Lit := [(1426, true), (1358, false)]
theorem step1379 (p : Nat → Bool) (h : Constraints p) : clause p c1379 = true :=
  Snake9.LocalRup.prove_clause [c1200, c994] c1379 (by decide) p (sat_cons (step1200 p h) (sat_cons (step994 p h) (sat_nil p)))
def c1380 : List Lit := [(1426, true), (1359, false)]
theorem step1380 (p : Nat → Bool) (h : Constraints p) : clause p c1380 = true :=
  Snake9.LocalRup.prove_clause [c1173, c996] c1380 (by decide) p (sat_cons (step1173 p h) (sat_cons (step996 p h) (sat_nil p)))
def c1381 : List Lit := [(1359, false), (1427, true)]
theorem step1381 (p : Nat → Bool) (h : Constraints p) : clause p c1381 = true :=
  Snake9.LocalRup.prove_clause [c1200, c997] c1381 (by decide) p (sat_cons (step1200 p h) (sat_cons (step997 p h) (sat_nil p)))
def c1382 : List Lit := [(1360, false), (1428, true)]
theorem step1382 (p : Nat → Bool) (h : Constraints p) : clause p c1382 = true :=
  Snake9.LocalRup.prove_clause [c1200, c1000] c1382 (by decide) p (sat_cons (step1200 p h) (sat_cons (step1000 p h) (sat_nil p)))
def c1383 : List Lit := [(1361, false), (1429, true)]
theorem step1383 (p : Nat → Bool) (h : Constraints p) : clause p c1383 = true :=
  Snake9.LocalRup.prove_clause [c1200, c1002] c1383 (by decide) p (sat_cons (step1200 p h) (sat_cons (step1002 p h) (sat_nil p)))
def c1384 : List Lit := [(1313, false), (1429, false)]
theorem step1384 (p : Nat → Bool) (h : Constraints p) : clause p c1384 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1008] c1384 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1008 p h) (sat_nil p)))
def c1385 : List Lit := [(1314, false), (1428, false)]
theorem step1385 (p : Nat → Bool) (h : Constraints p) : clause p c1385 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1009] c1385 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1009 p h) (sat_nil p)))
def c1386 : List Lit := [(1315, false), (1427, false)]
theorem step1386 (p : Nat → Bool) (h : Constraints p) : clause p c1386 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1010] c1386 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1010 p h) (sat_nil p)))
def c1387 : List Lit := [(1316, false), (1426, false)]
theorem step1387 (p : Nat → Bool) (h : Constraints p) : clause p c1387 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1011] c1387 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c1388 : List Lit := [(1317, false), (1425, false)]
theorem step1388 (p : Nat → Bool) (h : Constraints p) : clause p c1388 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1012] c1388 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1012 p h) (sat_nil p)))
def c1389 : List Lit := [(61, true), (62, true), (59, true), (64, false), (56, false), (1, false)]
theorem step1389 (p : Nat → Bool) (h : Constraints p) : clause p c1389 = true :=
  Snake9.LocalRup.prove_clause [c1201, c1175] c1389 (by decide) p (sat_cons (step1201 p h) (sat_cons (step1175 p h) (sat_nil p)))
def c1390 : List Lit := [(1297, true)]
theorem step1390 (p : Nat → Bool) (h : Constraints p) : clause p c1390 = true :=
  Snake9.LocalRup.prove_clause [c1371, c1372, c1077, c846, c1369, c861, c838, c840, c1336, c836, c1118, c95, c827, c833] c1390 (by decide) p (sat_cons (step1371 p h) (sat_cons (step1372 p h) (sat_cons (step1077 p h) (sat_cons (step846 p h) (sat_cons (step1369 p h) (sat_cons (step861 p h) (sat_cons (step838 p h) (sat_cons (step840 p h) (sat_cons (step1336 p h) (sat_cons (step836 p h) (sat_cons (step1118 p h) (sat_cons (step95 p h) (sat_cons (step827 p h) (sat_cons (step833 p h) (sat_nil p)))))))))))))))
def c1391 : List Lit := [(1313, true)]
theorem step1391 (p : Nat → Bool) (h : Constraints p) : clause p c1391 = true :=
  Snake9.LocalRup.prove_clause [c1390, c1375] c1391 (by decide) p (sat_cons (step1390 p h) (sat_cons (step1375 p h) (sat_nil p)))
def c1392 : List Lit := [(1429, false)]
theorem step1392 (p : Nat → Bool) (h : Constraints p) : clause p c1392 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1384] c1392 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1384 p h) (sat_nil p)))
def c1393 : List Lit := [(1361, false)]
theorem step1393 (p : Nat → Bool) (h : Constraints p) : clause p c1393 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1383] c1393 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1383 p h) (sat_nil p)))
def c1394 : List Lit := [(63, true), (59, false)]
theorem step1394 (p : Nat → Bool) (h : Constraints p) : clause p c1394 = true :=
  Snake9.LocalRup.prove_clause [c1390, c1392, c1314, c930, c1290, c1312, c682, c694, c933, c939, c941, c1379, c1387, c895, c1313, c450, c419, c416, c406, c405, c180, c182, c1187, c1376, c1001, c947, c1226, c908, c1343, c187, c183, c901, c1340, c903, c913, c920] c1394 (by decide) p (sat_cons (step1390 p h) (sat_cons (step1392 p h) (sat_cons (step1314 p h) (sat_cons (step930 p h) (sat_cons (step1290 p h) (sat_cons (step1312 p h) (sat_cons (step682 p h) (sat_cons (step694 p h) (sat_cons (step933 p h) (sat_cons (step939 p h) (sat_cons (step941 p h) (sat_cons (step1379 p h) (sat_cons (step1387 p h) (sat_cons (step895 p h) (sat_cons (step1313 p h) (sat_cons (step450 p h) (sat_cons (step419 p h) (sat_cons (step416 p h) (sat_cons (step406 p h) (sat_cons (step405 p h) (sat_cons (step180 p h) (sat_cons (step182 p h) (sat_cons (step1187 p h) (sat_cons (step1376 p h) (sat_cons (step1001 p h) (sat_cons (step947 p h) (sat_cons (step1226 p h) (sat_cons (step908 p h) (sat_cons (step1343 p h) (sat_cons (step187 p h) (sat_cons (step183 p h) (sat_cons (step901 p h) (sat_cons (step1340 p h) (sat_cons (step903 p h) (sat_cons (step913 p h) (sat_cons (step920 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1395 : List Lit := [(66, false), (1223, true), (357, true), (59, false)]
theorem step1395 (p : Nat → Bool) (h : Constraints p) : clause p c1395 = true :=
  Snake9.LocalRup.prove_clause [c1394, c1314, c450, c419, c414, c411, c410, c198, c1345, c1253, c448, c445, c432, c427, c425, c1290, c208, c1257, c344, c1261, c23, c22, c1319, c1316, c1265] c1395 (by decide) p (sat_cons (step1394 p h) (sat_cons (step1314 p h) (sat_cons (step450 p h) (sat_cons (step419 p h) (sat_cons (step414 p h) (sat_cons (step411 p h) (sat_cons (step410 p h) (sat_cons (step198 p h) (sat_cons (step1345 p h) (sat_cons (step1253 p h) (sat_cons (step448 p h) (sat_cons (step445 p h) (sat_cons (step432 p h) (sat_cons (step427 p h) (sat_cons (step425 p h) (sat_cons (step1290 p h) (sat_cons (step208 p h) (sat_cons (step1257 p h) (sat_cons (step344 p h) (sat_cons (step1261 p h) (sat_cons (step23 p h) (sat_cons (step22 p h) (sat_cons (step1319 p h) (sat_cons (step1316 p h) (sat_cons (step1265 p h) (sat_nil p))))))))))))))))))))))))))
def c1396 : List Lit := [(76, false), (357, true), (59, false)]
theorem step1396 (p : Nat → Bool) (h : Constraints p) : clause p c1396 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1390, c450, c1394, c1314, c930, c931, c937, c179, c1187, c909, c1376, c911, c1001, c916, c949, c943, c918, c995, c1386, c891, c1068, c1395, c1342, c910, c1309, c915, c1340] c1396 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1390 p h) (sat_cons (step450 p h) (sat_cons (step1394 p h) (sat_cons (step1314 p h) (sat_cons (step930 p h) (sat_cons (step931 p h) (sat_cons (step937 p h) (sat_cons (step179 p h) (sat_cons (step1187 p h) (sat_cons (step909 p h) (sat_cons (step1376 p h) (sat_cons (step911 p h) (sat_cons (step1001 p h) (sat_cons (step916 p h) (sat_cons (step949 p h) (sat_cons (step943 p h) (sat_cons (step918 p h) (sat_cons (step995 p h) (sat_cons (step1386 p h) (sat_cons (step891 p h) (sat_cons (step1068 p h) (sat_cons (step1395 p h) (sat_cons (step1342 p h) (sat_cons (step910 p h) (sat_cons (step1309 p h) (sat_cons (step915 p h) (sat_cons (step1340 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1397 : List Lit := [(357, true), (59, false)]
theorem step1397 (p : Nat → Bool) (h : Constraints p) : clause p c1397 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1390, c1314, c930, c931, c448, c450, c444, c419, c442, c416, c440, c406, c439, c405, c1396, c934, c228, c181, c935, c1349, c938, c1185, c941, c1376, c995, c1001, c1386, c947, c891, c1226, c1068, c908, c1395, c1342] c1397 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1390 p h) (sat_cons (step1314 p h) (sat_cons (step930 p h) (sat_cons (step931 p h) (sat_cons (step448 p h) (sat_cons (step450 p h) (sat_cons (step444 p h) (sat_cons (step419 p h) (sat_cons (step442 p h) (sat_cons (step416 p h) (sat_cons (step440 p h) (sat_cons (step406 p h) (sat_cons (step439 p h) (sat_cons (step405 p h) (sat_cons (step1396 p h) (sat_cons (step934 p h) (sat_cons (step228 p h) (sat_cons (step181 p h) (sat_cons (step935 p h) (sat_cons (step1349 p h) (sat_cons (step938 p h) (sat_cons (step1185 p h) (sat_cons (step941 p h) (sat_cons (step1376 p h) (sat_cons (step995 p h) (sat_cons (step1001 p h) (sat_cons (step1386 p h) (sat_cons (step947 p h) (sat_cons (step891 p h) (sat_cons (step1226 p h) (sat_cons (step1068 p h) (sat_cons (step908 p h) (sat_cons (step1395 p h) (sat_cons (step1342 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1398 : List Lit := [(4, false), (66, false), (59, false)]
theorem step1398 (p : Nat → Bool) (h : Constraints p) : clause p c1398 = true :=
  Snake9.LocalRup.prove_clause [c1397, c493, c1363, c395, c344, c1394, c1314, c1290, c193, c1257, c1253] c1398 (by decide) p (sat_cons (step1397 p h) (sat_cons (step493 p h) (sat_cons (step1363 p h) (sat_cons (step395 p h) (sat_cons (step344 p h) (sat_cons (step1394 p h) (sat_cons (step1314 p h) (sat_cons (step1290 p h) (sat_cons (step193 p h) (sat_cons (step1257 p h) (sat_cons (step1253 p h) (sat_nil p))))))))))))
def c1399 : List Lit := [(66, false), (59, false)]
theorem step1399 (p : Nat → Bool) (h : Constraints p) : clause p c1399 = true :=
  Snake9.TreeRup.prove_clause [c1397, c493, c1363, c395, c344, c317, c315, c312, c311, c1324, c342, c339, c328, c322, c321, c41, c511, c513, c1290, c1312, c682, c694, c1362, c489, c469, c1079, c746, c1367, c393, c388, c384, c381, c379, c375, c1109, c605, c641, c558, c525, c1326, c319, c310, c305, c304, c309, c307, c306, c644, c327, c326, c1398, c1320, c1285, c1288, c503, c505, c508, c524, c22, c556, c528, c537] c1399 (by decide) p (sat_cons (step1397 p h) (sat_cons (step493 p h) (sat_cons (step1363 p h) (sat_cons (step395 p h) (sat_cons (step344 p h) (sat_cons (step317 p h) (sat_cons (step315 p h) (sat_cons (step312 p h) (sat_cons (step311 p h) (sat_cons (step1324 p h) (sat_cons (step342 p h) (sat_cons (step339 p h) (sat_cons (step328 p h) (sat_cons (step322 p h) (sat_cons (step321 p h) (sat_cons (step41 p h) (sat_cons (step511 p h) (sat_cons (step513 p h) (sat_cons (step1290 p h) (sat_cons (step1312 p h) (sat_cons (step682 p h) (sat_cons (step694 p h) (sat_cons (step1362 p h) (sat_cons (step489 p h) (sat_cons (step469 p h) (sat_cons (step1079 p h) (sat_cons (step746 p h) (sat_cons (step1367 p h) (sat_cons (step393 p h) (sat_cons (step388 p h) (sat_cons (step384 p h) (sat_cons (step381 p h) (sat_cons (step379 p h) (sat_cons (step375 p h) (sat_cons (step1109 p h) (sat_cons (step605 p h) (sat_cons (step641 p h) (sat_cons (step558 p h) (sat_cons (step525 p h) (sat_cons (step1326 p h) (sat_cons (step319 p h) (sat_cons (step310 p h) (sat_cons (step305 p h) (sat_cons (step304 p h) (sat_cons (step309 p h) (sat_cons (step307 p h) (sat_cons (step306 p h) (sat_cons (step644 p h) (sat_cons (step327 p h) (sat_cons (step326 p h) (sat_cons (step1398 p h) (sat_cons (step1320 p h) (sat_cons (step1285 p h) (sat_cons (step1288 p h) (sat_cons (step503 p h) (sat_cons (step505 p h) (sat_cons (step508 p h) (sat_cons (step524 p h) (sat_cons (step22 p h) (sat_cons (step556 p h) (sat_cons (step528 p h) (sat_cons (step537 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1400 : List Lit := [(59, false)]
theorem step1400 (p : Nat → Bool) (h : Constraints p) : clause p c1400 = true :=
  Snake9.TreeRup.prove_clause [c1390, c1290, c1312, c682, c694, c1314, c930, c931, c937, c1394, c1397, c493, c1362, c1363, c489, c393, c395, c469, c388, c342, c344, c1079, c384, c339, c317, c319, c381, c327, c328, c315, c309, c379, c325, c326, c322, c312, c308, c375, c323, c321, c311, c1109, c41, c1324, c511, c1326, c513, c788, c518, c1059, c808, c1399, c1342, c673, c1225, c686, c1380, c1381, c695, c1387, c1386, c749, c895, c891, c1366, c1308, c819, c1105, c13, c1056, c51, c1319, c1222, c1233, c769] c1400 (by decide) p (sat_cons (step1390 p h) (sat_cons (step1290 p h) (sat_cons (step1312 p h) (sat_cons (step682 p h) (sat_cons (step694 p h) (sat_cons (step1314 p h) (sat_cons (step930 p h) (sat_cons (step931 p h) (sat_cons (step937 p h) (sat_cons (step1394 p h) (sat_cons (step1397 p h) (sat_cons (step493 p h) (sat_cons (step1362 p h) (sat_cons (step1363 p h) (sat_cons (step489 p h) (sat_cons (step393 p h) (sat_cons (step395 p h) (sat_cons (step469 p h) (sat_cons (step388 p h) (sat_cons (step342 p h) (sat_cons (step344 p h) (sat_cons (step1079 p h) (sat_cons (step384 p h) (sat_cons (step339 p h) (sat_cons (step317 p h) (sat_cons (step319 p h) (sat_cons (step381 p h) (sat_cons (step327 p h) (sat_cons (step328 p h) (sat_cons (step315 p h) (sat_cons (step309 p h) (sat_cons (step379 p h) (sat_cons (step325 p h) (sat_cons (step326 p h) (sat_cons (step322 p h) (sat_cons (step312 p h) (sat_cons (step308 p h) (sat_cons (step375 p h) (sat_cons (step323 p h) (sat_cons (step321 p h) (sat_cons (step311 p h) (sat_cons (step1109 p h) (sat_cons (step41 p h) (sat_cons (step1324 p h) (sat_cons (step511 p h) (sat_cons (step1326 p h) (sat_cons (step513 p h) (sat_cons (step788 p h) (sat_cons (step518 p h) (sat_cons (step1059 p h) (sat_cons (step808 p h) (sat_cons (step1399 p h) (sat_cons (step1342 p h) (sat_cons (step673 p h) (sat_cons (step1225 p h) (sat_cons (step686 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step695 p h) (sat_cons (step1387 p h) (sat_cons (step1386 p h) (sat_cons (step749 p h) (sat_cons (step895 p h) (sat_cons (step891 p h) (sat_cons (step1366 p h) (sat_cons (step1308 p h) (sat_cons (step819 p h) (sat_cons (step1105 p h) (sat_cons (step13 p h) (sat_cons (step1056 p h) (sat_cons (step51 p h) (sat_cons (step1319 p h) (sat_cons (step1222 p h) (sat_cons (step1233 p h) (sat_cons (step769 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1401 : List Lit := [(805, true)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true :=
  Snake9.LocalRup.prove_clause [c1400, c660] c1401 (by decide) p (sat_cons (step1400 p h) (sat_cons (step660 p h) (sat_nil p)))
def c1402 : List Lit := [(808, true)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c1401, c663] c1402 (by decide) p (sat_cons (step1401 p h) (sat_cons (step663 p h) (sat_nil p)))
def c1403 : List Lit := [(357, false), (723, true), (731, false), (835, false)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c535, c532, c531, c533, c537, c527, c526, c59, c493, c1362, c1363, c489, c393, c395, c469, c388, c342, c1079, c384, c339, c742, c381, c327, c1368, c379, c325, c635, c375, c323, c1109, c58, c57, c618, c62, c61, c567, c561, c570, c580, c564, c566, c562, c80] c1403 (by decide) p (sat_cons (step535 p h) (sat_cons (step532 p h) (sat_cons (step531 p h) (sat_cons (step533 p h) (sat_cons (step537 p h) (sat_cons (step527 p h) (sat_cons (step526 p h) (sat_cons (step59 p h) (sat_cons (step493 p h) (sat_cons (step1362 p h) (sat_cons (step1363 p h) (sat_cons (step489 p h) (sat_cons (step393 p h) (sat_cons (step395 p h) (sat_cons (step469 p h) (sat_cons (step388 p h) (sat_cons (step342 p h) (sat_cons (step1079 p h) (sat_cons (step384 p h) (sat_cons (step339 p h) (sat_cons (step742 p h) (sat_cons (step381 p h) (sat_cons (step327 p h) (sat_cons (step1368 p h) (sat_cons (step379 p h) (sat_cons (step325 p h) (sat_cons (step635 p h) (sat_cons (step375 p h) (sat_cons (step323 p h) (sat_cons (step1109 p h) (sat_cons (step58 p h) (sat_cons (step57 p h) (sat_cons (step618 p h) (sat_cons (step62 p h) (sat_cons (step61 p h) (sat_cons (step567 p h) (sat_cons (step561 p h) (sat_cons (step570 p h) (sat_cons (step580 p h) (sat_cons (step564 p h) (sat_cons (step566 p h) (sat_cons (step562 p h) (sat_cons (step80 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c1404 : List Lit := [(723, true), (731, false), (1229, false), (1221, false), (835, false), (62, true)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c1390, c1400, c535, c537, c532, c533, c527, c531, c526, c59, c795, c800, c809, c816, c891, c1386, c1381, c948, c918, c1403, c450, c419, c421, c414, c403, c412, c399, c409, c398, c1096, c1337, c1341, c156, c910, c1340, c915] c1404 (by decide) p (sat_cons (step1390 p h) (sat_cons (step1400 p h) (sat_cons (step535 p h) (sat_cons (step537 p h) (sat_cons (step532 p h) (sat_cons (step533 p h) (sat_cons (step527 p h) (sat_cons (step531 p h) (sat_cons (step526 p h) (sat_cons (step59 p h) (sat_cons (step795 p h) (sat_cons (step800 p h) (sat_cons (step809 p h) (sat_cons (step816 p h) (sat_cons (step891 p h) (sat_cons (step1386 p h) (sat_cons (step1381 p h) (sat_cons (step948 p h) (sat_cons (step918 p h) (sat_cons (step1403 p h) (sat_cons (step450 p h) (sat_cons (step419 p h) (sat_cons (step421 p h) (sat_cons (step414 p h) (sat_cons (step403 p h) (sat_cons (step412 p h) (sat_cons (step399 p h) (sat_cons (step409 p h) (sat_cons (step398 p h) (sat_cons (step1096 p h) (sat_cons (step1337 p h) (sat_cons (step1341 p h) (sat_cons (step156 p h) (sat_cons (step910 p h) (sat_cons (step1340 p h) (sat_cons (step915 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
end B112E174
