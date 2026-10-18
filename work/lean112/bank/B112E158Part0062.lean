import B112E158Part0061
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5538 : List Lit := [(1523, true), (1477, false), (1498, false)]
theorem step5538 (p : Nat → Bool) (h : Constraints p) : clause p c5538 = true :=
  Snake9.LocalRup.prove_clause [c5282, c2575] c5538 (by decide) p (sat_cons (step5282 p h) (sat_cons (step2575 p h) (sat_nil p)))
def c5539 : List Lit := [(1542, true), (1477, false), (1456, false), (37, true), (1498, false)]
theorem step5539 (p : Nat → Bool) (h : Constraints p) : clause p c5539 = true :=
  Snake9.LocalRup.prove_clause [c5281, c2584] c5539 (by decide) p (sat_cons (step5281 p h) (sat_cons (step2584 p h) (sat_nil p)))
def c5540 : List Lit := [(1477, false), (1523, true), (1497, false), (48, true)]
theorem step5540 (p : Nat → Bool) (h : Constraints p) : clause p c5540 = true :=
  Snake9.LocalRup.prove_clause [c5282, c2755] c5540 (by decide) p (sat_cons (step5282 p h) (sat_cons (step2755 p h) (sat_nil p)))
def c5541 : List Lit := [(32, true), (59, false), (52, true), (50, true), (37, true), (1526, true), (1506, false)]
theorem step5541 (p : Nat → Bool) (h : Constraints p) : clause p c5541 = true :=
  Snake9.LocalRup.prove_clause [c4399, c5280, c2396] c5541 (by decide) p (sat_cons (step4399 p h) (sat_cons (step5280 p h) (sat_cons (step2396 p h) (sat_nil p))))
def c5542 : List Lit := [(32, true), (1506, false), (37, true), (1499, false), (52, true), (1525, true)]
theorem step5542 (p : Nat → Bool) (h : Constraints p) : clause p c5542 = true :=
  Snake9.LocalRup.prove_clause [c5280, c4399, c2490] c5542 (by decide) p (sat_cons (step5280 p h) (sat_cons (step4399 p h) (sat_cons (step2490 p h) (sat_nil p))))
def c5543 : List Lit := [(1508, false), (1497, false), (1523, true)]
theorem step5543 (p : Nat → Bool) (h : Constraints p) : clause p c5543 = true :=
  Snake9.LocalRup.prove_clause [c4400, c2280] c5543 (by decide) p (sat_cons (step4400 p h) (sat_cons (step2280 p h) (sat_nil p)))
def c5544 : List Lit := [(32, true), (1498, false), (1526, true), (1509, false), (37, true)]
theorem step5544 (p : Nat → Bool) (h : Constraints p) : clause p c5544 = true :=
  Snake9.LocalRup.prove_clause [c4399, c3494] c5544 (by decide) p (sat_cons (step4399 p h) (sat_cons (step3494 p h) (sat_nil p)))
def c5545 : List Lit := [(32, true), (59, false), (37, true), (1497, false), (1464, false), (55, true), (1649, false), (1563, true), (1555, false)]
theorem step5545 (p : Nat → Bool) (h : Constraints p) : clause p c5545 = true :=
  Snake9.LocalRup.prove_clause [c5280, c4163] c5545 (by decide) p (sat_cons (step5280 p h) (sat_cons (step4163 p h) (sat_nil p)))
def c5546 : List Lit := [(32, true), (1508, false), (37, true), (1524, true), (1497, false)]
theorem step5546 (p : Nat → Bool) (h : Constraints p) : clause p c5546 = true :=
  Snake9.LocalRup.prove_clause [c4399, c3606] c5546 (by decide) p (sat_cons (step4399 p h) (sat_cons (step3606 p h) (sat_nil p)))
def c5547 : List Lit := [(32, true), (1498, false), (1524, true), (37, true)]
theorem step5547 (p : Nat → Bool) (h : Constraints p) : clause p c5547 = true :=
  Snake9.LocalRup.prove_clause [c4399, c5282, c3784] c5547 (by decide) p (sat_cons (step4399 p h) (sat_cons (step5282 p h) (sat_cons (step3784 p h) (sat_nil p))))
def c5548 : List Lit := [(1508, true), (55, false), (28, false), (37, true), (1680, true), (1612, false)]
theorem step5548 (p : Nat → Bool) (h : Constraints p) : clause p c5548 = true :=
  Snake9.LocalRup.prove_clause [c5280, c3339] c5548 (by decide) p (sat_cons (step5280 p h) (sat_cons (step3339 p h) (sat_nil p)))
def c5549 : List Lit := [(1498, false), (1477, false), (1525, true), (48, true), (1515, true), (39, true)]
theorem step5549 (p : Nat → Bool) (h : Constraints p) : clause p c5549 = true :=
  Snake9.LocalRup.prove_clause [c5282, c3977] c5549 (by decide) p (sat_cons (step5282 p h) (sat_cons (step3977 p h) (sat_nil p)))
def c5550 : List Lit := [(32, true), (4, true), (37, true), (50, true), (1464, false), (55, false)]
theorem step5550 (p : Nat → Bool) (h : Constraints p) : clause p c5550 = true :=
  Snake9.LocalRup.prove_clause [c4399, c5280, c3940] c5550 (by decide) p (sat_cons (step4399 p h) (sat_cons (step5280 p h) (sat_cons (step3940 p h) (sat_nil p))))
def c5551 : List Lit := [(32, true), (59, false), (1464, false), (1649, false), (50, true), (37, true), (55, true)]
theorem step5551 (p : Nat → Bool) (h : Constraints p) : clause p c5551 = true :=
  Snake9.LocalRup.prove_clause [c4399, c5280, c3837] c5551 (by decide) p (sat_cons (step4399 p h) (sat_cons (step5280 p h) (sat_cons (step3837 p h) (sat_nil p))))
def c5552 : List Lit := [(1522, true), (1505, false), (37, true)]
theorem step5552 (p : Nat → Bool) (h : Constraints p) : clause p c5552 = true :=
  Snake9.LocalRup.prove_clause [c4399, c5281, c3273] c5552 (by decide) p (sat_cons (step4399 p h) (sat_cons (step5281 p h) (sat_cons (step3273 p h) (sat_nil p))))
def c5553 : List Lit := [(19, false), (59, false), (37, true), (1509, true), (55, true)]
theorem step5553 (p : Nat → Bool) (h : Constraints p) : clause p c5553 = true :=
  Snake9.LocalRup.prove_clause [c5280, c4010] c5553 (by decide) p (sat_cons (step5280 p h) (sat_cons (step4010 p h) (sat_nil p)))
def c5554 : List Lit := [(32, true), (55, false), (1463, false), (37, true), (58, false), (39, true), (1498, false), (1525, true), (1555, false)]
theorem step5554 (p : Nat → Bool) (h : Constraints p) : clause p c5554 = true :=
  Snake9.LocalRup.prove_clause [c5282, c4399, c3921] c5554 (by decide) p (sat_cons (step5282 p h) (sat_cons (step4399 p h) (sat_cons (step3921 p h) (sat_nil p))))
def c5555 : List Lit := [(1478, false), (39, true), (1525, true), (48, true), (1497, false)]
theorem step5555 (p : Nat → Bool) (h : Constraints p) : clause p c5555 = true :=
  Snake9.LocalRup.prove_clause [c5282, c3923] c5555 (by decide) p (sat_cons (step5282 p h) (sat_cons (step3923 p h) (sat_nil p)))
def c5556 : List Lit := [(1477, false), (1505, false), (1497, false), (58, false), (1526, true), (48, true), (37, true), (19, false), (1563, true)]
theorem step5556 (p : Nat → Bool) (h : Constraints p) : clause p c5556 = true :=
  Snake9.LocalRup.prove_clause [c5280, c3600] c5556 (by decide) p (sat_cons (step5280 p h) (sat_cons (step3600 p h) (sat_nil p)))
def c5557 : List Lit := [(32, true), (24, true), (37, true)]
theorem step5557 (p : Nat → Bool) (h : Constraints p) : clause p c5557 = true :=
  Snake9.LocalRup.prove_clause [c5280, c4210] c5557 (by decide) p (sat_cons (step5280 p h) (sat_cons (step4210 p h) (sat_nil p)))
def c5558 : List Lit := [(32, true), (1506, false), (1485, false), (1526, true), (52, true), (37, true), (1491, true)]
theorem step5558 (p : Nat → Bool) (h : Constraints p) : clause p c5558 = true :=
  Snake9.LocalRup.prove_clause [c5280, c3495] c5558 (by decide) p (sat_cons (step5280 p h) (sat_cons (step3495 p h) (sat_nil p)))
def c5559 : List Lit := [(32, true), (55, false), (1464, false), (37, true), (59, false), (50, true)]
theorem step5559 (p : Nat → Bool) (h : Constraints p) : clause p c5559 = true :=
  Snake9.LocalRup.prove_clause [c5280, c3946] c5559 (by decide) p (sat_cons (step5280 p h) (sat_cons (step3946 p h) (sat_nil p)))
def c5560 : List Lit := [(91, false), (2, false), (15, false), (52, true), (24, true), (50, true), (3, true), (17, true)]
theorem step5560 (p : Nat → Bool) (h : Constraints p) : clause p c5560 = true :=
  Snake9.LocalRup.prove_clause [c5280, c3421] c5560 (by decide) p (sat_cons (step5280 p h) (sat_cons (step3421 p h) (sat_nil p)))
def c5561 : List Lit := [(1496, false), (1514, true), (30, false)]
theorem step5561 (p : Nat → Bool) (h : Constraints p) : clause p c5561 = true :=
  Snake9.LocalRup.prove_clause [c5280, c4258] c5561 (by decide) p (sat_cons (step5280 p h) (sat_cons (step4258 p h) (sat_nil p)))
def c5562 : List Lit := [(1496, false), (63, false), (1515, true), (1505, false)]
theorem step5562 (p : Nat → Bool) (h : Constraints p) : clause p c5562 = true :=
  Snake9.LocalRup.prove_clause [c5280, c4362] c5562 (by decide) p (sat_cons (step5280 p h) (sat_cons (step4362 p h) (sat_nil p)))
def c5563 : List Lit := [(1495, false), (1567, true), (1515, true), (52, true), (58, true)]
theorem step5563 (p : Nat → Bool) (h : Constraints p) : clause p c5563 = true :=
  Snake9.LocalRup.prove_clause [c5280, c4418] c5563 (by decide) p (sat_cons (step5280 p h) (sat_cons (step4418 p h) (sat_nil p)))
def c5564 : List Lit := [(1490, false), (32, true), (1495, false), (58, true), (1525, true), (34, true)]
theorem step5564 (p : Nat → Bool) (h : Constraints p) : clause p c5564 = true :=
  Snake9.LocalRup.prove_clause [c5281, c4447] c5564 (by decide) p (sat_cons (step5281 p h) (sat_cons (step4447 p h) (sat_nil p)))
def c5565 : List Lit := [(1523, true), (1498, false), (37, true)]
theorem step5565 (p : Nat → Bool) (h : Constraints p) : clause p c5565 = true :=
  Snake9.LocalRup.prove_clause [c5282, c4510] c5565 (by decide) p (sat_cons (step5282 p h) (sat_cons (step4510 p h) (sat_nil p)))
def c5566 : List Lit := [(45, false), (1423, false), (37, true), (63, false), (58, false), (1498, false), (1555, false), (1659, false), (46, false), (39, false), (1649, false), (48, false)]
theorem step5566 (p : Nat → Bool) (h : Constraints p) : clause p c5566 = true :=
  Snake9.LocalRup.prove_clause [c5281, c4541] c5566 (by decide) p (sat_cons (step5281 p h) (sat_cons (step4541 p h) (sat_nil p)))
def c5567 : List Lit := [(1509, false), (48, true), (1524, true)]
theorem step5567 (p : Nat → Bool) (h : Constraints p) : clause p c5567 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1147, c5516, c1174, c1179, c1206, c1150, c1124, c5341] c5567 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1147 p h) (sat_cons (step5516 p h) (sat_cons (step1174 p h) (sat_cons (step1179 p h) (sat_cons (step1206 p h) (sat_cons (step1150 p h) (sat_cons (step1124 p h) (sat_cons (step5341 p h) (sat_nil p))))))))))
def c5568 : List Lit := [(1505, false), (48, true), (52, true), (1524, true), (50, false)]
theorem step5568 (p : Nat → Bool) (h : Constraints p) : clause p c5568 = true :=
  Snake9.LocalRup.prove_clause [c5567, c1139, c5519, c1165, c5533, c2048, c1148, c5357, c1178, c2287, c1206, c5521] c5568 (by decide) p (sat_cons (step5567 p h) (sat_cons (step1139 p h) (sat_cons (step5519 p h) (sat_cons (step1165 p h) (sat_cons (step5533 p h) (sat_cons (step2048 p h) (sat_cons (step1148 p h) (sat_cons (step5357 p h) (sat_cons (step1178 p h) (sat_cons (step2287 p h) (sat_cons (step1206 p h) (sat_cons (step5521 p h) (sat_nil p)))))))))))))
def c5569 : List Lit := [(1542, true), (1497, false), (48, true), (1464, false), (37, true), (58, false), (50, false)]
theorem step5569 (p : Nat → Bool) (h : Constraints p) : clause p c5569 = true :=
  Snake9.LocalRup.prove_clause [c1139, c4651, c1247, c5424, c5524, c5301, c2287, c5522, c1996, c1151, c1141] c5569 (by decide) p (sat_cons (step1139 p h) (sat_cons (step4651 p h) (sat_cons (step1247 p h) (sat_cons (step5424 p h) (sat_cons (step5524 p h) (sat_cons (step5301 p h) (sat_cons (step2287 p h) (sat_cons (step5522 p h) (sat_cons (step1996 p h) (sat_cons (step1151 p h) (sat_cons (step1141 p h) (sat_nil p))))))))))))
def c5570 : List Lit := [(37, true), (58, false), (50, false), (30, true), (1612, false), (1543, true)]
theorem step5570 (p : Nat → Bool) (h : Constraints p) : clause p c5570 = true :=
  Snake9.LocalRup.prove_clause [c5467, c1392, c5506, c1045, c4586, c1248, c5511, c1859, c5513, c1047, c4870, c5568, c1157, c1718, c1142, c5569, c1943, c5492, c5548, c5337, c1816, c1779, c2230, c1255, c5007, c388] c5570 (by decide) p (sat_cons (step5467 p h) (sat_cons (step1392 p h) (sat_cons (step5506 p h) (sat_cons (step1045 p h) (sat_cons (step4586 p h) (sat_cons (step1248 p h) (sat_cons (step5511 p h) (sat_cons (step1859 p h) (sat_cons (step5513 p h) (sat_cons (step1047 p h) (sat_cons (step4870 p h) (sat_cons (step5568 p h) (sat_cons (step1157 p h) (sat_cons (step1718 p h) (sat_cons (step1142 p h) (sat_cons (step5569 p h) (sat_cons (step1943 p h) (sat_cons (step5492 p h) (sat_cons (step5548 p h) (sat_cons (step5337 p h) (sat_cons (step1816 p h) (sat_cons (step1779 p h) (sat_cons (step2230 p h) (sat_cons (step1255 p h) (sat_cons (step5007 p h) (sat_cons (step388 p h) (sat_nil p)))))))))))))))))))))))))))
def c5571 : List Lit := [(1497, false), (48, true), (1524, true), (37, false), (58, false)]
theorem step5571 (p : Nat → Bool) (h : Constraints p) : clause p c5571 = true :=
  Snake9.LocalRup.prove_clause [c4563, c5438, c5437] c5571 (by decide) p (sat_cons (step4563 p h) (sat_cons (step5438 p h) (sat_cons (step5437 p h) (sat_nil p))))
def c5572 : List Lit := [(48, true), (1524, true), (37, false), (58, false), (50, false), (102, false)]
theorem step5572 (p : Nat → Bool) (h : Constraints p) : clause p c5572 = true :=
  Snake9.LocalRup.prove_clause [c5571, c1142, c320, c5568, c1718, c1157] c5572 (by decide) p (sat_cons (step5571 p h) (sat_cons (step1142 p h) (sat_cons (step320 p h) (sat_cons (step5568 p h) (sat_cons (step1718 p h) (sat_cons (step1157 p h) (sat_nil p)))))))
def c5573 : List Lit := [(1497, true), (1509, true), (50, false), (102, false)]
theorem step5573 (p : Nat → Bool) (h : Constraints p) : clause p c5573 = true :=
  Snake9.LocalRup.prove_clause [c1142, c320, c2048, c1718, c5533, c1157, c1165] c5573 (by decide) p (sat_cons (step1142 p h) (sat_cons (step320 p h) (sat_cons (step2048 p h) (sat_cons (step1718 p h) (sat_cons (step5533 p h) (sat_cons (step1157 p h) (sat_cons (step1165 p h) (sat_nil p))))))))
def c5574 : List Lit := [(1524, true), (37, false), (102, false), (58, false), (50, false)]
theorem step5574 (p : Nat → Bool) (h : Constraints p) : clause p c5574 = true :=
  Snake9.LocalRup.prove_clause [c5572, c210, c4589, c5527, c1212, c1169, c5528, c5573, c1145, c1148, c5306, c1140, c1996] c5574 (by decide) p (sat_cons (step5572 p h) (sat_cons (step210 p h) (sat_cons (step4589 p h) (sat_cons (step5527 p h) (sat_cons (step1212 p h) (sat_cons (step1169 p h) (sat_cons (step5528 p h) (sat_cons (step5573 p h) (sat_cons (step1145 p h) (sat_cons (step1148 p h) (sat_cons (step5306 p h) (sat_cons (step1140 p h) (sat_cons (step1996 p h) (sat_nil p))))))))))))))
def c5575 : List Lit := [(58, false), (50, false), (30, true), (1612, false), (1543, true)]
theorem step5575 (p : Nat → Bool) (h : Constraints p) : clause p c5575 = true :=
  Snake9.LocalRup.prove_clause [c5467, c1392, c5506, c5570, c4621, c1248, c5574] c5575 (by decide) p (sat_cons (step5467 p h) (sat_cons (step1392 p h) (sat_cons (step5506 p h) (sat_cons (step5570 p h) (sat_cons (step4621 p h) (sat_cons (step1248 p h) (sat_cons (step5574 p h) (sat_nil p))))))))
def c5576 : List Lit := [(37, false), (58, true), (50, false), (30, true), (1525, true), (102, false), (1543, true)]
theorem step5576 (p : Nat → Bool) (h : Constraints p) : clause p c5576 = true :=
  Snake9.LocalRup.prove_clause [c1156, c5519, c1168, c5506, c4621, c1248, c5374, c1217, c1142, c5573, c320, c3253, c5567, c1860, c1718, c1255, c2227, c1158, c5265, c4736] c5576 (by decide) p (sat_cons (step1156 p h) (sat_cons (step5519 p h) (sat_cons (step1168 p h) (sat_cons (step5506 p h) (sat_cons (step4621 p h) (sat_cons (step1248 p h) (sat_cons (step5374 p h) (sat_cons (step1217 p h) (sat_cons (step1142 p h) (sat_cons (step5573 p h) (sat_cons (step320 p h) (sat_cons (step3253 p h) (sat_cons (step5567 p h) (sat_cons (step1860 p h) (sat_cons (step1718 p h) (sat_cons (step1255 p h) (sat_cons (step2227 p h) (sat_cons (step1158 p h) (sat_cons (step5265 p h) (sat_cons (step4736 p h) (sat_nil p)))))))))))))))))))))
def c5577 : List Lit := [(1497, true), (1524, true), (58, true), (50, false), (1448, false), (102, false), (1543, true)]
theorem step5577 (p : Nat → Bool) (h : Constraints p) : clause p c5577 = true :=
  Snake9.LocalRup.prove_clause [c1142, c5573, c320, c3253, c2048, c1718, c1812, c1255, c1158, c2157, c5514, c5218] c5577 (by decide) p (sat_cons (step1142 p h) (sat_cons (step5573 p h) (sat_cons (step320 p h) (sat_cons (step3253 p h) (sat_cons (step2048 p h) (sat_cons (step1718 p h) (sat_cons (step1812 p h) (sat_cons (step1255 p h) (sat_cons (step1158 p h) (sat_cons (step2157 p h) (sat_cons (step5514 p h) (sat_cons (step5218 p h) (sat_nil p)))))))))))))
def c5578 : List Lit := [(30, true), (1463, false), (1612, false), (1543, true)]
theorem step5578 (p : Nat → Bool) (h : Constraints p) : clause p c5578 = true :=
  Snake9.LocalRup.prove_clause [c1240, c5467, c1392, c1045, c5505, c5506, c5575, c1156, c5519, c5576, c4756, c4586, c1248, c5577, c5543, c5324, c5332, c5493, c1255, c1247, c3481, c1089, c1943, c1294, c2047, c1914, c1047, c1486, c4216, c502, c1295, c2035, c3470, c1472] c5578 (by decide) p (sat_cons (step1240 p h) (sat_cons (step5467 p h) (sat_cons (step1392 p h) (sat_cons (step1045 p h) (sat_cons (step5505 p h) (sat_cons (step5506 p h) (sat_cons (step5575 p h) (sat_cons (step1156 p h) (sat_cons (step5519 p h) (sat_cons (step5576 p h) (sat_cons (step4756 p h) (sat_cons (step4586 p h) (sat_cons (step1248 p h) (sat_cons (step5577 p h) (sat_cons (step5543 p h) (sat_cons (step5324 p h) (sat_cons (step5332 p h) (sat_cons (step5493 p h) (sat_cons (step1255 p h) (sat_cons (step1247 p h) (sat_cons (step3481 p h) (sat_cons (step1089 p h) (sat_cons (step1943 p h) (sat_cons (step1294 p h) (sat_cons (step2047 p h) (sat_cons (step1914 p h) (sat_cons (step1047 p h) (sat_cons (step1486 p h) (sat_cons (step4216 p h) (sat_cons (step502 p h) (sat_cons (step1295 p h) (sat_cons (step2035 p h) (sat_cons (step3470 p h) (sat_cons (step1472 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c5579 : List Lit := [(1524, true), (58, true), (52, true), (50, false), (30, false)]
theorem step5579 (p : Nat → Bool) (h : Constraints p) : clause p c5579 = true :=
  Snake9.LocalRup.prove_clause [c1156, c5519, c2143, c5568, c5408] c5579 (by decide) p (sat_cons (step1156 p h) (sat_cons (step5519 p h) (sat_cons (step2143 p h) (sat_cons (step5568 p h) (sat_cons (step5408 p h) (sat_nil p))))))
def c5580 : List Lit := [(1448, false), (48, false), (1491, true), (1464, true), (58, true), (1428, false), (50, false), (1525, true)]
theorem step5580 (p : Nat → Bool) (h : Constraints p) : clause p c5580 = true :=
  Snake9.LocalRup.prove_clause [c1011, c1656, c4586, c1088, c1024, c1002, c5218, c5377, c181, c185, c5527, c1134, c5564, c1996, c1140] c5580 (by decide) p (sat_cons (step1011 p h) (sat_cons (step1656 p h) (sat_cons (step4586 p h) (sat_cons (step1088 p h) (sat_cons (step1024 p h) (sat_cons (step1002 p h) (sat_cons (step5218 p h) (sat_cons (step5377 p h) (sat_cons (step181 p h) (sat_cons (step185 p h) (sat_cons (step5527 p h) (sat_cons (step1134 p h) (sat_cons (step5564 p h) (sat_cons (step1996 p h) (sat_cons (step1140 p h) (sat_nil p))))))))))))))))
def c5581 : List Lit := [(37, false), (28, false), (48, false), (1491, true), (1680, true), (1464, true), (58, true), (1430, false), (1525, true), (1612, false), (1543, true)]
theorem step5581 (p : Nat → Bool) (h : Constraints p) : clause p c5581 = true :=
  Snake9.LocalRup.prove_clause [c5470, c5392, c2730, c2075, c2068, c4703, c5377, c188, c181, c5527, c1134, c5564, c1996, c1140] c5581 (by decide) p (sat_cons (step5470 p h) (sat_cons (step5392 p h) (sat_cons (step2730 p h) (sat_cons (step2075 p h) (sat_cons (step2068 p h) (sat_cons (step4703 p h) (sat_cons (step5377 p h) (sat_cons (step188 p h) (sat_cons (step181 p h) (sat_cons (step5527 p h) (sat_cons (step1134 p h) (sat_cons (step5564 p h) (sat_cons (step1996 p h) (sat_cons (step1140 p h) (sat_nil p)))))))))))))))
def c5582 : List Lit := [(1650, false), (1662, true), (1568, false), (1680, true), (1612, false)]
theorem step5582 (p : Nat → Bool) (h : Constraints p) : clause p c5582 = true :=
  Snake9.LocalRup.prove_clause [c3470, c1472] c5582 (by decide) p (sat_cons (step3470 p h) (sat_cons (step1472 p h) (sat_nil p)))
def c5583 : List Lit := [(48, false), (1491, true), (1680, true), (1464, true), (58, true), (50, false), (1525, true), (1612, false), (1543, true)]
theorem step5583 (p : Nat → Bool) (h : Constraints p) : clause p c5583 = true :=
  Snake9.LocalRup.prove_clause [c5467, c1392, c5506, c1011, c5470, c5580, c1046, c5581, c3481, c1808, c4216, c1294, c502, c1295, c2730, c1914, c1276, c1486, c5582, c2162] c5583 (by decide) p (sat_cons (step5467 p h) (sat_cons (step1392 p h) (sat_cons (step5506 p h) (sat_cons (step1011 p h) (sat_cons (step5470 p h) (sat_cons (step5580 p h) (sat_cons (step1046 p h) (sat_cons (step5581 p h) (sat_cons (step3481 p h) (sat_cons (step1808 p h) (sat_cons (step4216 p h) (sat_cons (step1294 p h) (sat_cons (step502 p h) (sat_cons (step1295 p h) (sat_cons (step2730 p h) (sat_cons (step1914 p h) (sat_cons (step1276 p h) (sat_cons (step1486 p h) (sat_cons (step5582 p h) (sat_cons (step2162 p h) (sat_nil p)))))))))))))))))))))
def c5584 : List Lit := [(1497, false), (58, true), (50, false), (1463, false), (1612, false), (1543, true)]
theorem step5584 (p : Nat → Bool) (h : Constraints p) : clause p c5584 = true :=
  Snake9.LocalRup.prove_clause [c5578, c5467, c1392, c311, c5579, c1239, c1943, c1248, c1156, c5519, c1240, c1145, c1173, c1218, c5583, c1139, c1148, c1178, c1213, c5527, c2283, c2130, c1783, c1705, c2211, c1104] c5584 (by decide) p (sat_cons (step5578 p h) (sat_cons (step5467 p h) (sat_cons (step1392 p h) (sat_cons (step311 p h) (sat_cons (step5579 p h) (sat_cons (step1239 p h) (sat_cons (step1943 p h) (sat_cons (step1248 p h) (sat_cons (step1156 p h) (sat_cons (step5519 p h) (sat_cons (step1240 p h) (sat_cons (step1145 p h) (sat_cons (step1173 p h) (sat_cons (step1218 p h) (sat_cons (step5583 p h) (sat_cons (step1139 p h) (sat_cons (step1148 p h) (sat_cons (step1178 p h) (sat_cons (step1213 p h) (sat_cons (step5527 p h) (sat_cons (step2283 p h) (sat_cons (step2130 p h) (sat_cons (step1783 p h) (sat_cons (step1705 p h) (sat_cons (step2211 p h) (sat_cons (step1104 p h) (sat_nil p)))))))))))))))))))))))))))
def c5585 : List Lit := [(58, true), (50, false), (1463, false), (1612, false), (1543, true)]
theorem step5585 (p : Nat → Bool) (h : Constraints p) : clause p c5585 = true :=
  Snake9.LocalRup.prove_clause [c5578, c1240, c5584, c2176, c5346, c1158] c5585 (by decide) p (sat_cons (step5578 p h) (sat_cons (step1240 p h) (sat_cons (step5584 p h) (sat_cons (step2176 p h) (sat_cons (step5346 p h) (sat_cons (step1158 p h) (sat_nil p)))))))
def c5586 : List Lit := [(48, true), (39, true), (1509, false), (1477, false), (1525, true)]
theorem step5586 (p : Nat → Bool) (h : Constraints p) : clause p c5586 = true :=
  Snake9.LocalRup.prove_clause [c5521, c1207, c1179, c1150, c1139, c1141, c1147, c1996, c1174, c1129, c1213] c5586 (by decide) p (sat_cons (step5521 p h) (sat_cons (step1207 p h) (sat_cons (step1179 p h) (sat_cons (step1150 p h) (sat_cons (step1139 p h) (sat_cons (step1141 p h) (sat_cons (step1147 p h) (sat_cons (step1996 p h) (sat_cons (step1174 p h) (sat_cons (step1129 p h) (sat_cons (step1213 p h) (sat_nil p))))))))))))
def c5587 : List Lit := [(1564, true), (48, false), (58, false), (50, false), (102, false), (1543, true)]
theorem step5587 (p : Nat → Bool) (h : Constraints p) : clause p c5587 = true :=
  Snake9.LocalRup.prove_clause [c5506, c1011, c3320, c191, c2109, c5574, c4703, c1248] c5587 (by decide) p (sat_cons (step5506 p h) (sat_cons (step1011 p h) (sat_cons (step3320 p h) (sat_cons (step191 p h) (sat_cons (step2109 p h) (sat_cons (step5574 p h) (sat_cons (step4703 p h) (sat_cons (step1248 p h) (sat_nil p)))))))))
def c5588 : List Lit := [(1497, true), (50, false), (1463, false), (1612, false), (1543, true)]
theorem step5588 (p : Nat → Bool) (h : Constraints p) : clause p c5588 = true :=
  Snake9.LocalRup.prove_clause [c5578, c5585, c5418, c5467, c1392, c311, c1860, c5506, c1240, c5470, c1142, c2197, c5573, c1812, c1274, c3253, c285, c2130, c5586, c5587, c2730, c1943, c1247, c5421, c5434, c1088, c4756] c5588 (by decide) p (sat_cons (step5578 p h) (sat_cons (step5585 p h) (sat_cons (step5418 p h) (sat_cons (step5467 p h) (sat_cons (step1392 p h) (sat_cons (step311 p h) (sat_cons (step1860 p h) (sat_cons (step5506 p h) (sat_cons (step1240 p h) (sat_cons (step5470 p h) (sat_cons (step1142 p h) (sat_cons (step2197 p h) (sat_cons (step5573 p h) (sat_cons (step1812 p h) (sat_cons (step1274 p h) (sat_cons (step3253 p h) (sat_cons (step285 p h) (sat_cons (step2130 p h) (sat_cons (step5586 p h) (sat_cons (step5587 p h) (sat_cons (step2730 p h) (sat_cons (step1943 p h) (sat_cons (step1247 p h) (sat_cons (step5421 p h) (sat_cons (step5434 p h) (sat_cons (step1088 p h) (sat_cons (step4756 p h) (sat_nil p))))))))))))))))))))))))))))
def c5589 : List Lit := [(1509, false), (39, true), (1497, false), (1515, true), (1525, true)]
theorem step5589 (p : Nat → Bool) (h : Constraints p) : clause p c5589 = true :=
  Snake9.LocalRup.prove_clause [c5471, c1179, c1996, c1148, c1140] c5589 (by decide) p (sat_cons (step5471 p h) (sat_cons (step1179 p h) (sat_cons (step1996 p h) (sat_cons (step1148 p h) (sat_cons (step1140 p h) (sat_nil p))))))
def c5590 : List Lit := [(1542, true), (1523, false), (58, false), (50, false), (1463, false), (102, false)]
theorem step5590 (p : Nat → Bool) (h : Constraints p) : clause p c5590 = true :=
  Snake9.LocalRup.prove_clause [c5506, c1239, c1247, c5421, c5574, c1088, c4756] c5590 (by decide) p (sat_cons (step5506 p h) (sat_cons (step1239 p h) (sat_cons (step1247 p h) (sat_cons (step5421 p h) (sat_cons (step5574 p h) (sat_cons (step1088 p h) (sat_cons (step4756 p h) (sat_nil p))))))))
def c5591 : List Lit := [(1523, false), (1564, false), (48, false), (58, false), (107, true), (105, false), (50, false), (1463, false), (1649, false), (102, false), (1612, false)]
theorem step5591 (p : Nat → Bool) (h : Constraints p) : clause p c5591 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1915, c1238, c1942, c1492, c5590, c1943, c2730, c5582, c1276, c2160, c2209, c516, c419, c2291] c5591 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1915 p h) (sat_cons (step1238 p h) (sat_cons (step1942 p h) (sat_cons (step1492 p h) (sat_cons (step5590 p h) (sat_cons (step1943 p h) (sat_cons (step2730 p h) (sat_cons (step5582 p h) (sat_cons (step1276 p h) (sat_cons (step2160 p h) (sat_cons (step2209 p h) (sat_cons (step516 p h) (sat_cons (step419 p h) (sat_cons (step2291 p h) (sat_nil p))))))))))))))))
def c5592 : List Lit := [(1523, true), (1497, false), (1489, false), (52, true), (50, false), (30, false)]
theorem step5592 (p : Nat → Bool) (h : Constraints p) : clause p c5592 = true :=
  Snake9.LocalRup.prove_clause [c1145, c5517, c5301, c1211, c1205, c5527, c5528, c2283, c1148, c2130, c1140, c1996] c5592 (by decide) p (sat_cons (step1145 p h) (sat_cons (step5517 p h) (sat_cons (step5301 p h) (sat_cons (step1211 p h) (sat_cons (step1205 p h) (sat_cons (step5527 p h) (sat_cons (step5528 p h) (sat_cons (step2283 p h) (sat_cons (step1148 p h) (sat_cons (step2130 p h) (sat_cons (step1140 p h) (sat_cons (step1996 p h) (sat_nil p)))))))))))))
def c5593 : List Lit := [(48, false), (50, false), (1463, false), (1612, false), (1543, true)]
theorem step5593 (p : Nat → Bool) (h : Constraints p) : clause p c5593 = true :=
  Snake9.LocalRup.prove_clause [c5578, c5467, c1392, c311, c5585, c5418, c5521, c5588, c5592, c1860, c615, c1859, c5470, c5587, c5591] c5593 (by decide) p (sat_cons (step5578 p h) (sat_cons (step5467 p h) (sat_cons (step1392 p h) (sat_cons (step311 p h) (sat_cons (step5585 p h) (sat_cons (step5418 p h) (sat_cons (step5521 p h) (sat_cons (step5588 p h) (sat_cons (step5592 p h) (sat_cons (step1860 p h) (sat_cons (step615 p h) (sat_cons (step1859 p h) (sat_cons (step5470 p h) (sat_cons (step5587 p h) (sat_cons (step5591 p h) (sat_nil p))))))))))))))))
def c5594 : List Lit := [(39, false), (1500, false), (1430, false), (101, false), (52, true), (50, false), (30, false), (1525, true), (1543, true)]
theorem step5594 (p : Nat → Bool) (h : Constraints p) : clause p c5594 = true :=
  Snake9.LocalRup.prove_clause [c5528, c5218, c2130, c1024, c2283, c277, c5527, c1763, c1213, c1212, c1178, c1248, c5519, c2262, c1088, c1157, c1025, c1656, c4927, c1012, c1046, c4301, c1010] c5594 (by decide) p (sat_cons (step5528 p h) (sat_cons (step5218 p h) (sat_cons (step2130 p h) (sat_cons (step1024 p h) (sat_cons (step2283 p h) (sat_cons (step277 p h) (sat_cons (step5527 p h) (sat_cons (step1763 p h) (sat_cons (step1213 p h) (sat_cons (step1212 p h) (sat_cons (step1178 p h) (sat_cons (step1248 p h) (sat_cons (step5519 p h) (sat_cons (step2262 p h) (sat_cons (step1088 p h) (sat_cons (step1157 p h) (sat_cons (step1025 p h) (sat_cons (step1656 p h) (sat_cons (step4927 p h) (sat_cons (step1012 p h) (sat_cons (step1046 p h) (sat_cons (step4301 p h) (sat_cons (step1010 p h) (sat_nil p))))))))))))))))))))))))
def c5595 : List Lit := [(1485, true), (33, false), (39, true), (48, true), (52, true), (50, false), (30, false), (1525, true)]
theorem step5595 (p : Nat → Bool) (h : Constraints p) : clause p c5595 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1996, c1118, c1141, c1112, c5561, c1213, c150, c2977] c5595 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1996 p h) (sat_cons (step1118 p h) (sat_cons (step1141 p h) (sat_cons (step1112 p h) (sat_cons (step5561 p h) (sat_cons (step1213 p h) (sat_cons (step150 p h) (sat_cons (step2977 p h) (sat_nil p))))))))))
def c5596 : List Lit := [(50, false), (1463, false), (1612, false), (1543, true)]
theorem step5596 (p : Nat → Bool) (h : Constraints p) : clause p c5596 = true :=
  Snake9.TreeRup.prove_clause [c5578, c1240, c5470, c5467, c1392, c311, c5506, c1860, c1011, c5585, c5418, c5521, c5588, c5592, c5590, c1943, c2928, c5593, c1139, c1148, c5528, c1218, c1130, c5594, c1110, c1705, c5555, c1164, c5519, c1105, c2283, c5533, c1157, c1784, c1783, c359, c265, c2211, c5595, c1119, c1107, c1129, c150, c1213, c1112, c1114, c5561, c1121, c1141, c1111, c3955, c1712, c227, c1272, c447, c2876, c448, c1805, c1274, c4264, c1287, c1281, c255, c2730, c4818, c1290, c1291, c1103, c1277, c1299, c1283, c196, c4723, c1558, c1818] c5596 (by decide) p (sat_cons (step5578 p h) (sat_cons (step1240 p h) (sat_cons (step5470 p h) (sat_cons (step5467 p h) (sat_cons (step1392 p h) (sat_cons (step311 p h) (sat_cons (step5506 p h) (sat_cons (step1860 p h) (sat_cons (step1011 p h) (sat_cons (step5585 p h) (sat_cons (step5418 p h) (sat_cons (step5521 p h) (sat_cons (step5588 p h) (sat_cons (step5592 p h) (sat_cons (step5590 p h) (sat_cons (step1943 p h) (sat_cons (step2928 p h) (sat_cons (step5593 p h) (sat_cons (step1139 p h) (sat_cons (step1148 p h) (sat_cons (step5528 p h) (sat_cons (step1218 p h) (sat_cons (step1130 p h) (sat_cons (step5594 p h) (sat_cons (step1110 p h) (sat_cons (step1705 p h) (sat_cons (step5555 p h) (sat_cons (step1164 p h) (sat_cons (step5519 p h) (sat_cons (step1105 p h) (sat_cons (step2283 p h) (sat_cons (step5533 p h) (sat_cons (step1157 p h) (sat_cons (step1784 p h) (sat_cons (step1783 p h) (sat_cons (step359 p h) (sat_cons (step265 p h) (sat_cons (step2211 p h) (sat_cons (step5595 p h) (sat_cons (step1119 p h) (sat_cons (step1107 p h) (sat_cons (step1129 p h) (sat_cons (step150 p h) (sat_cons (step1213 p h) (sat_cons (step1112 p h) (sat_cons (step1114 p h) (sat_cons (step5561 p h) (sat_cons (step1121 p h) (sat_cons (step1141 p h) (sat_cons (step1111 p h) (sat_cons (step3955 p h) (sat_cons (step1712 p h) (sat_cons (step227 p h) (sat_cons (step1272 p h) (sat_cons (step447 p h) (sat_cons (step2876 p h) (sat_cons (step448 p h) (sat_cons (step1805 p h) (sat_cons (step1274 p h) (sat_cons (step4264 p h) (sat_cons (step1287 p h) (sat_cons (step1281 p h) (sat_cons (step255 p h) (sat_cons (step2730 p h) (sat_cons (step4818 p h) (sat_cons (step1290 p h) (sat_cons (step1291 p h) (sat_cons (step1103 p h) (sat_cons (step1277 p h) (sat_cons (step1299 p h) (sat_cons (step1283 p h) (sat_cons (step196 p h) (sat_cons (step4723 p h) (sat_cons (step1558 p h) (sat_cons (step1818 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5597 : List Lit := [(1490, false), (1477, false), (1500, false), (39, true), (52, true), (50, true), (1525, true), (1463, false), (1649, false), (1612, false)]
theorem step5597 (p : Nat → Bool) (h : Constraints p) : clause p c5597 = true :=
  Snake9.LocalRup.prove_clause [c5521, c1207, c5528, c1218, c1130, c1213, c1212, c5522, c1178, c1239, c1164, c5519, c1943, c5533, c1156, c1157, c1718, c1144, c5549, c1149, c5480, c1140, c4589, c4812, c3320, c4719, c2730, c1272, c1274] c5597 (by decide) p (sat_cons (step5521 p h) (sat_cons (step1207 p h) (sat_cons (step5528 p h) (sat_cons (step1218 p h) (sat_cons (step1130 p h) (sat_cons (step1213 p h) (sat_cons (step1212 p h) (sat_cons (step5522 p h) (sat_cons (step1178 p h) (sat_cons (step1239 p h) (sat_cons (step1164 p h) (sat_cons (step5519 p h) (sat_cons (step1943 p h) (sat_cons (step5533 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step1718 p h) (sat_cons (step1144 p h) (sat_cons (step5549 p h) (sat_cons (step1149 p h) (sat_cons (step5480 p h) (sat_cons (step1140 p h) (sat_cons (step4589 p h) (sat_cons (step4812 p h) (sat_cons (step3320 p h) (sat_cons (step4719 p h) (sat_cons (step2730 p h) (sat_cons (step1272 p h) (sat_cons (step1274 p h) (sat_nil p))))))))))))))))))))))))))))))
def c5598 : List Lit := [(29, true), (1500, false), (39, true), (52, true), (50, true), (30, false), (1525, true), (1463, false), (1649, false), (1612, false)]
theorem step5598 (p : Nat → Bool) (h : Constraints p) : clause p c5598 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1784, c1783, c2211, c1104, c5597, c5527, c1129, c1107, c1118, c150, c1112] c5598 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1784 p h) (sat_cons (step1783 p h) (sat_cons (step2211 p h) (sat_cons (step1104 p h) (sat_cons (step5597 p h) (sat_cons (step5527 p h) (sat_cons (step1129 p h) (sat_cons (step1107 p h) (sat_cons (step1118 p h) (sat_cons (step150 p h) (sat_cons (step1112 p h) (sat_nil p)))))))))))))
def c5599 : List Lit := [(32, false), (47, false), (43, true), (1555, false), (44, false), (1495, false), (1681, true), (93, true), (1478, true), (29, false), (39, true), (52, true), (50, true), (30, false), (1525, true), (1649, false), (100, false)]
theorem step5599 (p : Nat → Bool) (h : Constraints p) : clause p c5599 = true :=
  Snake9.LocalRup.prove_clause [c1105, c2022, c5521, c1207, c150, c130, c1782, c1802, c1103, c609, c169, c1390, c1810, c1397, c1144, c2058, c5549, c1149, c1466, c1183, c5325, c5519, c1300, c1156, c3320, c4589] c5599 (by decide) p (sat_cons (step1105 p h) (sat_cons (step2022 p h) (sat_cons (step5521 p h) (sat_cons (step1207 p h) (sat_cons (step150 p h) (sat_cons (step130 p h) (sat_cons (step1782 p h) (sat_cons (step1802 p h) (sat_cons (step1103 p h) (sat_cons (step609 p h) (sat_cons (step169 p h) (sat_cons (step1390 p h) (sat_cons (step1810 p h) (sat_cons (step1397 p h) (sat_cons (step1144 p h) (sat_cons (step2058 p h) (sat_cons (step5549 p h) (sat_cons (step1149 p h) (sat_cons (step1466 p h) (sat_cons (step1183 p h) (sat_cons (step5325 p h) (sat_cons (step5519 p h) (sat_cons (step1300 p h) (sat_cons (step1156 p h) (sat_cons (step3320 p h) (sat_cons (step4589 p h) (sat_nil p)))))))))))))))))))))))))))
def c5600 : List Lit := [(1505, true), (48, false), (32, true), (1555, false), (1478, true), (39, true), (52, true), (50, true), (1525, true), (1463, false)]
theorem step5600 (p : Nat → Bool) (h : Constraints p) : clause p c5600 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1157, c4589, c1718, c5554, c1144] c5600 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step4589 p h) (sat_cons (step1718 p h) (sat_cons (step5554 p h) (sat_cons (step1144 p h) (sat_nil p)))))))
def c5601 : List Lit := [(48, false), (32, true), (1553, false), (1495, false), (1478, true), (1477, false), (39, true), (52, true), (50, true), (1525, true), (1463, false), (1649, false), (1612, false)]
theorem step5601 (p : Nat → Bool) (h : Constraints p) : clause p c5601 = true :=
  Snake9.LocalRup.prove_clause [c1107, c1102, c1101, c1274, c5521, c1207, c1143, c2068, c4371, c5600, c5519, c1183, c1707, c1149, c1239, c1144, c1943, c2108, c2928, c1277, c1304] c5601 (by decide) p (sat_cons (step1107 p h) (sat_cons (step1102 p h) (sat_cons (step1101 p h) (sat_cons (step1274 p h) (sat_cons (step5521 p h) (sat_cons (step1207 p h) (sat_cons (step1143 p h) (sat_cons (step2068 p h) (sat_cons (step4371 p h) (sat_cons (step5600 p h) (sat_cons (step5519 p h) (sat_cons (step1183 p h) (sat_cons (step1707 p h) (sat_cons (step1149 p h) (sat_cons (step1239 p h) (sat_cons (step1144 p h) (sat_cons (step1943 p h) (sat_cons (step2108 p h) (sat_cons (step2928 p h) (sat_cons (step1277 p h) (sat_cons (step1304 p h) (sat_nil p))))))))))))))))))))))
end B112E158
