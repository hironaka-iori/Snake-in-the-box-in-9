import B112E183Part0009
namespace B112E183
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1468 : List Lit := [(134, false)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c1459, c339] c1468 (by decide) p (sat_cons (step1459 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1469 : List Lit := [(123, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c1461, c321] c1469 (by decide) p (sat_cons (step1461 p h) (sat_cons (step321 p h) (sat_nil p)))
def c1470 : List Lit := [(106, true)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c1462, c1072] c1470 (by decide) p (sat_cons (step1462 p h) (sat_cons (step1072 p h) (sat_nil p)))
def c1471 : List Lit := [(107, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1071] c1471 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1071 p h) (sat_nil p)))
def c1472 : List Lit := [(101, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c1464, c1069] c1472 (by decide) p (sat_cons (step1464 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c1473 : List Lit := [(1358, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1407, c1137] c1473 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1407 p h) (sat_cons (step1137 p h) (sat_nil p))))
def c1474 : List Lit := [(105, true)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c1470, c1452, c266] c1474 (by decide) p (sat_cons (step1470 p h) (sat_cons (step1452 p h) (sat_cons (step266 p h) (sat_nil p))))
def c1475 : List Lit := [(103, true)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c1471, c1451, c268] c1475 (by decide) p (sat_cons (step1471 p h) (sat_cons (step1451 p h) (sat_cons (step268 p h) (sat_nil p))))
def c1476 : List Lit := [(97, true)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c1472, c1453, c257] c1476 (by decide) p (sat_cons (step1472 p h) (sat_cons (step1453 p h) (sat_cons (step257 p h) (sat_nil p))))
def c1477 : List Lit := [(1371, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c1473, c1448, c966] c1477 (by decide) p (sat_cons (step1473 p h) (sat_cons (step1448 p h) (sat_cons (step966 p h) (sat_nil p))))
def c1478 : List Lit := [(104, false)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1474, c1475, c263] c1478 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1474 p h) (sat_cons (step1475 p h) (sat_cons (step263 p h) (sat_nil p)))))
def c1479 : List Lit := [(1419, false)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c1477, c1294, c643] c1479 (by decide) p (sat_cons (step1477 p h) (sat_cons (step1294 p h) (sat_cons (step643 p h) (sat_nil p))))
def c1480 : List Lit := [(54, true)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1475, c1070] c1480 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1475 p h) (sat_cons (step1070 p h) (sat_nil p))))
def c1481 : List Lit := [(1392, false)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c1479, c1099] c1481 (by decide) p (sat_cons (step1479 p h) (sat_cons (step1099 p h) (sat_nil p)))
def c1482 : List Lit := [(1383, false)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1479, c1480, c1471, c1416, c594, c595, c626, c588, c909, c585, c586, c608, c1396] c1482 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step1471 p h) (sat_cons (step1416 p h) (sat_cons (step594 p h) (sat_cons (step595 p h) (sat_cons (step626 p h) (sat_cons (step588 p h) (sat_cons (step909 p h) (sat_cons (step585 p h) (sat_cons (step586 p h) (sat_cons (step608 p h) (sat_cons (step1396 p h) (sat_nil p)))))))))))))))
def c1483 : List Lit := [(1381, false)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c1482, c580] c1483 (by decide) p (sat_cons (step1482 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1484 : List Lit := [(32, true)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c1483, c577] c1484 (by decide) p (sat_cons (step1483 p h) (sat_cons (step577 p h) (sat_nil p)))
def c1485 : List Lit := [(31, true)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c1483, c578] c1485 (by decide) p (sat_cons (step1483 p h) (sat_cons (step578 p h) (sat_nil p)))
def c1486 : List Lit := [(28, false)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c1484, c1407, c1480, c81] c1486 (by decide) p (sat_cons (step1484 p h) (sat_cons (step1407 p h) (sat_cons (step1480 p h) (sat_cons (step81 p h) (sat_nil p)))))
def c1487 : List Lit := [(36, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c1485, c1456, c90] c1487 (by decide) p (sat_cons (step1485 p h) (sat_cons (step1456 p h) (sat_cons (step90 p h) (sat_nil p))))
def c1488 : List Lit := [(30, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c1485, c1456, c91] c1488 (by decide) p (sat_cons (step1485 p h) (sat_cons (step1456 p h) (sat_cons (step91 p h) (sat_nil p))))
def c1489 : List Lit := [(22, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c1486, c1408, c1407, c1466, c85] c1489 (by decide) p (sat_cons (step1486 p h) (sat_cons (step1408 p h) (sat_cons (step1407 p h) (sat_cons (step1466 p h) (sat_cons (step85 p h) (sat_nil p))))))
def c1490 : List Lit := [(23, false)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c1488, c1485, c1407, c86] c1490 (by decide) p (sat_cons (step1488 p h) (sat_cons (step1485 p h) (sat_cons (step1407 p h) (sat_cons (step86 p h) (sat_nil p)))))
def c1491 : List Lit := [(26, true)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c1489, c1490, c1031] c1491 (by decide) p (sat_cons (step1489 p h) (sat_cons (step1490 p h) (sat_cons (step1031 p h) (sat_nil p))))
def c1492 : List Lit := [(27, true)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c1491, c1467, c76] c1492 (by decide) p (sat_cons (step1491 p h) (sat_cons (step1467 p h) (sat_cons (step76 p h) (sat_nil p))))
def c1493 : List Lit := [(24, true)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c1492, c1033] c1493 (by decide) p (sat_cons (step1492 p h) (sat_cons (step1033 p h) (sat_nil p)))
def c1494 : List Lit := [(21, true)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c1490, c1297, c1294, c1448, c1456, c1485, c1465, c1486, c1487, c1484, c1468, c1493, c1469, c1460, c536, c545, c558, c1238, c1200, c96, c531, c519, c1260, c92, c93, c515, c527, c529, c100, c44, c533, c67, c513, c1029, c34, c38, c43, c7] c1494 (by decide) p (sat_cons (step1490 p h) (sat_cons (step1297 p h) (sat_cons (step1294 p h) (sat_cons (step1448 p h) (sat_cons (step1456 p h) (sat_cons (step1485 p h) (sat_cons (step1465 p h) (sat_cons (step1486 p h) (sat_cons (step1487 p h) (sat_cons (step1484 p h) (sat_cons (step1468 p h) (sat_cons (step1493 p h) (sat_cons (step1469 p h) (sat_cons (step1460 p h) (sat_cons (step536 p h) (sat_cons (step545 p h) (sat_cons (step558 p h) (sat_cons (step1238 p h) (sat_cons (step1200 p h) (sat_cons (step96 p h) (sat_cons (step531 p h) (sat_cons (step519 p h) (sat_cons (step1260 p h) (sat_cons (step92 p h) (sat_cons (step93 p h) (sat_cons (step515 p h) (sat_cons (step527 p h) (sat_cons (step529 p h) (sat_cons (step100 p h) (sat_cons (step44 p h) (sat_cons (step533 p h) (sat_cons (step67 p h) (sat_cons (step513 p h) (sat_cons (step1029 p h) (sat_cons (step34 p h) (sat_cons (step38 p h) (sat_cons (step43 p h) (sat_cons (step7 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1495 : List Lit := [(56, false)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c1494, c1283, c1179] c1495 (by decide) p (sat_cons (step1494 p h) (sat_cons (step1283 p h) (sat_cons (step1179 p h) (sat_nil p))))
def c1496 : List Lit := [(34, true)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c1494, c1465, c1484, c1485, c1407, c1456, c1341] c1496 (by decide) p (sat_cons (step1494 p h) (sat_cons (step1465 p h) (sat_cons (step1484 p h) (sat_cons (step1485 p h) (sat_cons (step1407 p h) (sat_cons (step1456 p h) (sat_cons (step1341 p h) (sat_nil p))))))))
def c1497 : List Lit := [(1404, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c1495, c608] c1497 (by decide) p (sat_cons (step1495 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1498 : List Lit := [(35, false)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c1496, c1493, c1484, c96] c1498 (by decide) p (sat_cons (step1496 p h) (sat_cons (step1493 p h) (sat_cons (step1484 p h) (sat_cons (step96 p h) (sat_nil p)))))
def c1499 : List Lit := [(1411, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c1497, c909] c1499 (by decide) p (sat_cons (step1497 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1500 : List Lit := [(1388, true)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c1498, c590] c1500 (by decide) p (sat_cons (step1498 p h) (sat_cons (step590 p h) (sat_nil p)))
def c1501 : List Lit := [(1391, false)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1479, c626] c1501 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1479 p h) (sat_cons (step626 p h) (sat_nil p))))
def c1502 : List Lit := []
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c1500, c1501, c592] c1502 (by decide) p (sat_cons (step1500 p h) (sat_cons (step1501 p h) (sat_cons (step592 p h) (sat_nil p))))
end B112E183
