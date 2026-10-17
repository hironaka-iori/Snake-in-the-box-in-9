import B112E050Part0035
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4120 : List Lit := [(103, true), (108, true), (1829, true), (1773, false)]
theorem step4120 (p : Nat → Bool) (h : Constraints p) : clause p c4120 = true :=
  Snake9.LocalRup.prove_clause [c3863, c1524] c4120 (by decide) p (sat_cons (step3863 p h) (sat_cons (step1524 p h) (sat_nil p)))
def c4121 : List Lit := [(106, false), (96, false), (1829, true), (65, false)]
theorem step4121 (p : Nat → Bool) (h : Constraints p) : clause p c4121 = true :=
  Snake9.LocalRup.prove_clause [c623, c621, c622, c1522, c4120] c4121 (by decide) p (sat_cons (step623 p h) (sat_cons (step621 p h) (sat_cons (step622 p h) (sat_cons (step1522 p h) (sat_cons (step4120 p h) (sat_nil p))))))
def c4122 : List Lit := [(1662, false), (1670, false), (33, true), (1694, true), (87, false)]
theorem step4122 (p : Nat → Bool) (h : Constraints p) : clause p c4122 = true :=
  Snake9.LocalRup.prove_clause [c1887, c2201, c1334, c1301, c3467, c1889, c2202, c1188, c3178] c4122 (by decide) p (sat_cons (step1887 p h) (sat_cons (step2201 p h) (sat_cons (step1334 p h) (sat_cons (step1301 p h) (sat_cons (step3467 p h) (sat_cons (step1889 p h) (sat_cons (step2202 p h) (sat_cons (step1188 p h) (sat_cons (step3178 p h) (sat_nil p))))))))))
def c4123 : List Lit := [(96, true), (103, true), (1829, true), (123, true), (87, false), (66, false)]
theorem step4123 (p : Nat → Bool) (h : Constraints p) : clause p c4123 = true :=
  Snake9.LocalRup.prove_clause [c1533, c1540, c3614, c1519, c3159, c1526, c1534, c1553, c3511, c1551, c3799, c1635, c2234, c2235, c1641, c2278, c3803, c2413, c1520] c4123 (by decide) p (sat_cons (step1533 p h) (sat_cons (step1540 p h) (sat_cons (step3614 p h) (sat_cons (step1519 p h) (sat_cons (step3159 p h) (sat_cons (step1526 p h) (sat_cons (step1534 p h) (sat_cons (step1553 p h) (sat_cons (step3511 p h) (sat_cons (step1551 p h) (sat_cons (step3799 p h) (sat_cons (step1635 p h) (sat_cons (step2234 p h) (sat_cons (step2235 p h) (sat_cons (step1641 p h) (sat_cons (step2278 p h) (sat_cons (step3803 p h) (sat_cons (step2413 p h) (sat_cons (step1520 p h) (sat_nil p))))))))))))))))))))
def c4124 : List Lit := [(96, false), (1662, true), (1829, true), (67, true), (62, true), (1707, true), (65, false)]
theorem step4124 (p : Nat → Bool) (h : Constraints p) : clause p c4124 = true :=
  Snake9.LocalRup.prove_clause [c1369, c3026, c4121, c4023, c3446, c1272, c1998, c1239] c4124 (by decide) p (sat_cons (step1369 p h) (sat_cons (step3026 p h) (sat_cons (step4121 p h) (sat_cons (step4023 p h) (sat_cons (step3446 p h) (sat_cons (step1272 p h) (sat_cons (step1998 p h) (sat_cons (step1239 p h) (sat_nil p)))))))))
def c4125 : List Lit := [(85, false), (1733, false), (1707, true), (7, false), (1745, false), (1762, true)]
theorem step4125 (p : Nat → Bool) (h : Constraints p) : clause p c4125 = true :=
  Snake9.LocalRup.prove_clause [c1449, c1507, c4119, c1454, c2274, c318, c316, c313, c1895, c1388, c1399, c2918] c4125 (by decide) p (sat_cons (step1449 p h) (sat_cons (step1507 p h) (sat_cons (step4119 p h) (sat_cons (step1454 p h) (sat_cons (step2274 p h) (sat_cons (step318 p h) (sat_cons (step316 p h) (sat_cons (step313 p h) (sat_cons (step1895 p h) (sat_cons (step1388 p h) (sat_cons (step1399 p h) (sat_cons (step2918 p h) (sat_nil p)))))))))))))
def c4126 : List Lit := [(1718, false), (72, true), (1733, false), (1750, false), (1745, false), (1762, true)]
theorem step4126 (p : Nat → Bool) (h : Constraints p) : clause p c4126 = true :=
  Snake9.LocalRup.prove_clause [c1384, c1393, c1399, c2918] c4126 (by decide) p (sat_cons (step1384 p h) (sat_cons (step1393 p h) (sat_cons (step1399 p h) (sat_cons (step2918 p h) (sat_nil p)))))
def c4127 : List Lit := [(106, false), (123, true), (1829, true), (87, false), (66, false), (65, false)]
theorem step4127 (p : Nat → Bool) (h : Constraints p) : clause p c4127 = true :=
  Snake9.LocalRup.prove_clause [c4121, c1519, c4123, c625, c629, c628, c1522, c3073, c1527] c4127 (by decide) p (sat_cons (step4121 p h) (sat_cons (step1519 p h) (sat_cons (step4123 p h) (sat_cons (step625 p h) (sat_cons (step629 p h) (sat_cons (step628 p h) (sat_cons (step1522 p h) (sat_cons (step3073 p h) (sat_cons (step1527 p h) (sat_nil p))))))))))
def c4128 : List Lit := [(108, true), (96, true), (123, true), (1829, true), (87, false), (66, false)]
theorem step4128 (p : Nat → Bool) (h : Constraints p) : clause p c4128 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1526, c3626, c1536, c3511, c1538, c1532, c1551, c4078, c1635, c3130, c2235, c2234, c2278, c1641, c2413, c2142, c1520, c490] c4128 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1526 p h) (sat_cons (step3626 p h) (sat_cons (step1536 p h) (sat_cons (step3511 p h) (sat_cons (step1538 p h) (sat_cons (step1532 p h) (sat_cons (step1551 p h) (sat_cons (step4078 p h) (sat_cons (step1635 p h) (sat_cons (step3130 p h) (sat_cons (step2235 p h) (sat_cons (step2234 p h) (sat_cons (step2278 p h) (sat_cons (step1641 p h) (sat_cons (step2413 p h) (sat_cons (step2142 p h) (sat_cons (step1520 p h) (sat_cons (step490 p h) (sat_nil p))))))))))))))))))))
def c4129 : List Lit := [(1779, true), (1812, true), (108, false), (123, true), (66, false)]
theorem step4129 (p : Nat → Bool) (h : Constraints p) : clause p c4129 = true :=
  Snake9.LocalRup.prove_clause [c1532, c3382, c2278] c4129 (by decide) p (sat_cons (step1532 p h) (sat_cons (step3382 p h) (sat_cons (step2278 p h) (sat_nil p))))
def c4130 : List Lit := [(1776, true), (108, false), (96, true), (87, false)]
theorem step4130 (p : Nat → Bool) (h : Constraints p) : clause p c4130 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1529, c1527, c1520, c2645] c4130 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1529 p h) (sat_cons (step1527 p h) (sat_cons (step1520 p h) (sat_cons (step2645 p h) (sat_nil p))))))
def c4131 : List Lit := [(1779, false), (1776, false), (123, true), (1829, true)]
theorem step4131 (p : Nat → Bool) (h : Constraints p) : clause p c4131 = true :=
  Snake9.LocalRup.prove_clause [c3614, c1557, c1540, c1556, c1641, c1541, c2234, c1535, c2442] c4131 (by decide) p (sat_cons (step3614 p h) (sat_cons (step1557 p h) (sat_cons (step1540 p h) (sat_cons (step1556 p h) (sat_cons (step1641 p h) (sat_cons (step1541 p h) (sat_cons (step2234 p h) (sat_cons (step1535 p h) (sat_cons (step2442 p h) (sat_nil p))))))))))
def c4132 : List Lit := [(96, true), (123, true), (66, false), (1829, true), (87, false)]
theorem step4132 (p : Nat → Bool) (h : Constraints p) : clause p c4132 = true :=
  Snake9.LocalRup.prove_clause [c4128, c4130, c4131, c1555, c4129, c1635, c2235] c4132 (by decide) p (sat_cons (step4128 p h) (sat_cons (step4130 p h) (sat_cons (step4131 p h) (sat_cons (step1555 p h) (sat_cons (step4129 p h) (sat_cons (step1635 p h) (sat_cons (step2235 p h) (sat_nil p))))))))
def c4133 : List Lit := [(1776, false), (108, false), (123, true), (1829, true), (66, false)]
theorem step4133 (p : Nat → Bool) (h : Constraints p) : clause p c4133 = true :=
  Snake9.LocalRup.prove_clause [c1555, c4131, c1635, c4129, c2235] c4133 (by decide) p (sat_cons (step1555 p h) (sat_cons (step4131 p h) (sat_cons (step1635 p h) (sat_cons (step4129 p h) (sat_cons (step2235 p h) (sat_nil p))))))
def c4134 : List Lit := [(1779, true), (1776, true), (67, true), (108, false), (106, true), (87, false), (66, false)]
theorem step4134 (p : Nat → Bool) (h : Constraints p) : clause p c4134 = true :=
  Snake9.LocalRup.prove_clause [c1532, c2643, c2623, c663, c1518, c2145, c1527, c2661] c4134 (by decide) p (sat_cons (step1532 p h) (sat_cons (step2643 p h) (sat_cons (step2623 p h) (sat_cons (step663 p h) (sat_cons (step1518 p h) (sat_cons (step2145 p h) (sat_cons (step1527 p h) (sat_cons (step2661 p h) (sat_nil p)))))))))
def c4135 : List Lit := [(1773, true), (1597, true), (1637, true), (1662, false), (108, false), (96, false), (44, true), (1695, true), (7, false)]
theorem step4135 (p : Nat → Bool) (h : Constraints p) : clause p c4135 = true :=
  Snake9.LocalRup.prove_clause [c1522, c2661, c1978, c3833, c3670, c3608, c2202, c3453, c1344, c1301] c4135 (by decide) p (sat_cons (step1522 p h) (sat_cons (step2661 p h) (sat_cons (step1978 p h) (sat_cons (step3833 p h) (sat_cons (step3670 p h) (sat_cons (step3608 p h) (sat_cons (step2202 p h) (sat_cons (step3453 p h) (sat_cons (step1344 p h) (sat_cons (step1301 p h) (sat_nil p)))))))))))
def c4136 : List Lit := [(1673, true), (103, false), (109, false), (35, true), (1818, true), (1656, false), (1662, false), (1645, false), (96, false), (1635, false)]
theorem step4136 (p : Nat → Bool) (h : Constraints p) : clause p c4136 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1301, c1277, c3431, c1242, c1233] c4136 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1301 p h) (sat_cons (step1277 p h) (sat_cons (step3431 p h) (sat_cons (step1242 p h) (sat_cons (step1233 p h) (sat_nil p)))))))
def c4137 : List Lit := [(108, false), (123, true), (62, true), (1635, false), (44, true), (1829, true), (87, false), (1707, true), (65, false), (1695, true), (7, false)]
theorem step4137 (p : Nat → Bool) (h : Constraints p) : clause p c4137 = true :=
  Snake9.LocalRup.prove_clause [c1369, c4127, c3446, c4132, c1998, c1887, c2201, c1335, c3103, c3712, c4124, c2085, c1294, c1308, c4023, c1352, c2203, c4133, c4134, c1540, c1551, c1635, c2235, c4135, c1527, c1518, c3523, c3803, c2234, c1613, c1641, c2561, c1552, c1543, c4097, c1534, c4136, c1344, c2202, c1898, c2371, c1125, c2878] c4137 (by decide) p (sat_cons (step1369 p h) (sat_cons (step4127 p h) (sat_cons (step3446 p h) (sat_cons (step4132 p h) (sat_cons (step1998 p h) (sat_cons (step1887 p h) (sat_cons (step2201 p h) (sat_cons (step1335 p h) (sat_cons (step3103 p h) (sat_cons (step3712 p h) (sat_cons (step4124 p h) (sat_cons (step2085 p h) (sat_cons (step1294 p h) (sat_cons (step1308 p h) (sat_cons (step4023 p h) (sat_cons (step1352 p h) (sat_cons (step2203 p h) (sat_cons (step4133 p h) (sat_cons (step4134 p h) (sat_cons (step1540 p h) (sat_cons (step1551 p h) (sat_cons (step1635 p h) (sat_cons (step2235 p h) (sat_cons (step4135 p h) (sat_cons (step1527 p h) (sat_cons (step1518 p h) (sat_cons (step3523 p h) (sat_cons (step3803 p h) (sat_cons (step2234 p h) (sat_cons (step1613 p h) (sat_cons (step1641 p h) (sat_cons (step2561 p h) (sat_cons (step1552 p h) (sat_cons (step1543 p h) (sat_cons (step4097 p h) (sat_cons (step1534 p h) (sat_cons (step4136 p h) (sat_cons (step1344 p h) (sat_cons (step2202 p h) (sat_cons (step1898 p h) (sat_cons (step2371 p h) (sat_cons (step1125 p h) (sat_cons (step2878 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c4138 : List Lit := [(1580, true), (96, false), (57, false)]
theorem step4138 (p : Nat → Bool) (h : Constraints p) : clause p c4138 = true :=
  Snake9.LocalRup.prove_clause [c1125, c1126, c2820, c1754, c514, c2028] c4138 (by decide) p (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step2820 p h) (sat_cons (step1754 p h) (sat_cons (step514 p h) (sat_cons (step2028 p h) (sat_nil p)))))))
def c4139 : List Lit := [(1761, true), (80, false), (1750, false), (7, false), (1745, false)]
theorem step4139 (p : Nat → Bool) (h : Constraints p) : clause p c4139 = true :=
  Snake9.LocalRup.prove_clause [c2636, c2863, c1486, c1494, c1459, c2632, c1403, c1373, c1375] c4139 (by decide) p (sat_cons (step2636 p h) (sat_cons (step2863 p h) (sat_cons (step1486 p h) (sat_cons (step1494 p h) (sat_cons (step1459 p h) (sat_cons (step2632 p h) (sat_cons (step1403 p h) (sat_cons (step1373 p h) (sat_cons (step1375 p h) (sat_nil p))))))))))
def c4140 : List Lit := [(63, false), (80, false), (1733, false), (1707, true), (7, false), (1745, false), (1762, true)]
theorem step4140 (p : Nat → Bool) (h : Constraints p) : clause p c4140 = true :=
  Snake9.LocalRup.prove_clause [c2863, c1487, c1464, c1431, c2390, c3148, c2614, c1428, c1495, c1459] c4140 (by decide) p (sat_cons (step2863 p h) (sat_cons (step1487 p h) (sat_cons (step1464 p h) (sat_cons (step1431 p h) (sat_cons (step2390 p h) (sat_cons (step3148 p h) (sat_cons (step2614 p h) (sat_cons (step1428 p h) (sat_cons (step1495 p h) (sat_cons (step1459 p h) (sat_nil p)))))))))))
def c4141 : List Lit := [(1721, true), (73, true), (80, false), (7, false)]
theorem step4141 (p : Nat → Bool) (h : Constraints p) : clause p c4141 = true :=
  Snake9.LocalRup.prove_clause [c1383, c2635, c1395, c1393, c1385, c2357] c4141 (by decide) p (sat_cons (step1383 p h) (sat_cons (step2635 p h) (sat_cons (step1395 p h) (sat_cons (step1393 p h) (sat_cons (step1385 p h) (sat_cons (step2357 p h) (sat_nil p)))))))
def c4142 : List Lit := [(123, false), (80, false), (1733, false), (7, false), (1745, false), (1762, true)]
theorem step4142 (p : Nat → Bool) (h : Constraints p) : clause p c4142 = true :=
  Snake9.LocalRup.prove_clause [c1449, c1507, c4119, c1454, c314, c3084, c4126] c4142 (by decide) p (sat_cons (step1449 p h) (sat_cons (step1507 p h) (sat_cons (step4119 p h) (sat_cons (step1454 p h) (sat_cons (step314 p h) (sat_cons (step3084 p h) (sat_cons (step4126 p h) (sat_nil p))))))))
def c4143 : List Lit := [(63, false), (1718, false), (1732, true), (1733, false), (1707, true), (1745, false), (1762, true)]
theorem step4143 (p : Nat → Bool) (h : Constraints p) : clause p c4143 = true :=
  Snake9.LocalRup.prove_clause [c2390, c3148, c1383, c1428, c1393, c1459, c1399, c1495] c4143 (by decide) p (sat_cons (step2390 p h) (sat_cons (step3148 p h) (sat_cons (step1383 p h) (sat_cons (step1428 p h) (sat_cons (step1393 p h) (sat_cons (step1459 p h) (sat_cons (step1399 p h) (sat_cons (step1495 p h) (sat_nil p)))))))))
def c4144 : List Lit := [(123, true), (1662, true), (60, true), (1652, false), (1829, true), (87, false), (1707, true), (65, false)]
theorem step4144 (p : Nat → Bool) (h : Constraints p) : clause p c4144 = true :=
  Snake9.LocalRup.prove_clause [c1369, c4127, c4132, c3446, c1998, c209, c1239, c1248, c1272, c1258] c4144 (by decide) p (sat_cons (step1369 p h) (sat_cons (step4127 p h) (sat_cons (step4132 p h) (sat_cons (step3446 p h) (sat_cons (step1998 p h) (sat_cons (step209 p h) (sat_cons (step1239 p h) (sat_cons (step1248 p h) (sat_cons (step1272 p h) (sat_cons (step1258 p h) (sat_nil p)))))))))))
def c4145 : List Lit := [(1721, false), (62, false), (63, true), (72, false), (80, true), (1829, true), (87, false), (1733, false), (1707, true), (65, false), (5, false), (1750, false), (1745, false), (1762, true)]
theorem step4145 (p : Nat → Bool) (h : Constraints p) : clause p c4145 = true :=
  Snake9.LocalRup.prove_clause [c1993, c2079, c1947, c1524, c2082, c1249, c1369, c1501, c1399, c1404, c1495, c1494, c1375, c1459, c3620, c1372, c1373, c1428, c2251, c3043, c274, c2919, c2097, c270, c265, c297, c1236, c1017, c2920, c1018, c1026, c1028, c1047, c1091, c2200, c1005, c1000, c995, c992, c993, c991, c987, c990, c986, c216, c2368, c225, c172, c2093, c3, c1186, c1194, c1963, c1292, c4122, c4144, c587, c3985, c3562] c4145 (by decide) p (sat_cons (step1993 p h) (sat_cons (step2079 p h) (sat_cons (step1947 p h) (sat_cons (step1524 p h) (sat_cons (step2082 p h) (sat_cons (step1249 p h) (sat_cons (step1369 p h) (sat_cons (step1501 p h) (sat_cons (step1399 p h) (sat_cons (step1404 p h) (sat_cons (step1495 p h) (sat_cons (step1494 p h) (sat_cons (step1375 p h) (sat_cons (step1459 p h) (sat_cons (step3620 p h) (sat_cons (step1372 p h) (sat_cons (step1373 p h) (sat_cons (step1428 p h) (sat_cons (step2251 p h) (sat_cons (step3043 p h) (sat_cons (step274 p h) (sat_cons (step2919 p h) (sat_cons (step2097 p h) (sat_cons (step270 p h) (sat_cons (step265 p h) (sat_cons (step297 p h) (sat_cons (step1236 p h) (sat_cons (step1017 p h) (sat_cons (step2920 p h) (sat_cons (step1018 p h) (sat_cons (step1026 p h) (sat_cons (step1028 p h) (sat_cons (step1047 p h) (sat_cons (step1091 p h) (sat_cons (step2200 p h) (sat_cons (step1005 p h) (sat_cons (step1000 p h) (sat_cons (step995 p h) (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step991 p h) (sat_cons (step987 p h) (sat_cons (step990 p h) (sat_cons (step986 p h) (sat_cons (step216 p h) (sat_cons (step2368 p h) (sat_cons (step225 p h) (sat_cons (step172 p h) (sat_cons (step2093 p h) (sat_cons (step3 p h) (sat_cons (step1186 p h) (sat_cons (step1194 p h) (sat_cons (step1963 p h) (sat_cons (step1292 p h) (sat_cons (step4122 p h) (sat_cons (step4144 p h) (sat_cons (step587 p h) (sat_cons (step3985 p h) (sat_cons (step3562 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c4146 : List Lit := [(123, false), (1721, true), (102, false), (62, false), (1829, true), (1726, true)]
theorem step4146 (p : Nat → Bool) (h : Constraints p) : clause p c4146 = true :=
  Snake9.LocalRup.prove_clause [c3875, c586, c584, c1536, c1523, c1538, c1525, c3025, c1556] c4146 (by decide) p (sat_cons (step3875 p h) (sat_cons (step586 p h) (sat_cons (step584 p h) (sat_cons (step1536 p h) (sat_cons (step1523 p h) (sat_cons (step1538 p h) (sat_cons (step1525 p h) (sat_cons (step3025 p h) (sat_cons (step1556 p h) (sat_nil p))))))))))
def c4147 : List Lit := [(1789, true), (1812, true), (104, false), (108, true), (123, true), (1773, false), (87, false)]
theorem step4147 (p : Nat → Bool) (h : Constraints p) : clause p c4147 = true :=
  Snake9.LocalRup.prove_clause [c2278, c1536, c1538, c1524, c1552, c1556, c1539, c1527, c1537, c1518, c1975, c4003, c1587] c4147 (by decide) p (sat_cons (step2278 p h) (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1524 p h) (sat_cons (step1552 p h) (sat_cons (step1556 p h) (sat_cons (step1539 p h) (sat_cons (step1527 p h) (sat_cons (step1537 p h) (sat_cons (step1518 p h) (sat_cons (step1975 p h) (sat_cons (step4003 p h) (sat_cons (step1587 p h) (sat_nil p))))))))))))))
def c4148 : List Lit := [(108, true), (123, true), (1773, false), (1829, true), (87, false), (66, false)]
theorem step4148 (p : Nat → Bool) (h : Constraints p) : clause p c4148 = true :=
  Snake9.LocalRup.prove_clause [c1584, c1524, c1536, c3511, c1538, c1532, c1551, c1635, c2235, c4147, c1641, c2234, c3130, c1599, c664, c1590, c1587] c4148 (by decide) p (sat_cons (step1584 p h) (sat_cons (step1524 p h) (sat_cons (step1536 p h) (sat_cons (step3511 p h) (sat_cons (step1538 p h) (sat_cons (step1532 p h) (sat_cons (step1551 p h) (sat_cons (step1635 p h) (sat_cons (step2235 p h) (sat_cons (step4147 p h) (sat_cons (step1641 p h) (sat_cons (step2234 p h) (sat_cons (step3130 p h) (sat_cons (step1599 p h) (sat_cons (step664 p h) (sat_cons (step1590 p h) (sat_cons (step1587 p h) (sat_nil p))))))))))))))))))
def c4149 : List Lit := [(62, false), (63, true), (72, false), (80, true), (1829, true), (87, false), (1733, false), (1707, true), (65, false), (5, false), (1750, false), (1745, false), (1762, true)]
theorem step4149 (p : Nat → Bool) (h : Constraints p) : clause p c4149 = true :=
  Snake9.LocalRup.prove_clause [c1369, c1501, c1993, c2079, c1947, c4145, c4146, c4148, c2680, c4133, c1525] c4149 (by decide) p (sat_cons (step1369 p h) (sat_cons (step1501 p h) (sat_cons (step1993 p h) (sat_cons (step2079 p h) (sat_cons (step1947 p h) (sat_cons (step4145 p h) (sat_cons (step4146 p h) (sat_cons (step4148 p h) (sat_cons (step2680 p h) (sat_cons (step4133 p h) (sat_cons (step1525 p h) (sat_nil p))))))))))))
def c4150 : List Lit := [(1761, true), (72, false), (1720, false), (80, true), (1733, false), (1750, false), (1724, false), (1745, false)]
theorem step4150 (p : Nat → Bool) (h : Constraints p) : clause p c4150 = true :=
  Snake9.LocalRup.prove_clause [c1486, c1494, c1459, c1399, c1403, c1428, c1375, c3708] c4150 (by decide) p (sat_cons (step1486 p h) (sat_cons (step1494 p h) (sat_cons (step1459 p h) (sat_cons (step1399 p h) (sat_cons (step1403 p h) (sat_cons (step1428 p h) (sat_cons (step1375 p h) (sat_cons (step3708 p h) (sat_nil p)))))))))
def c4151 : List Lit := [(1709, true), (72, false), (1718, true), (80, true)]
theorem step4151 (p : Nat → Bool) (h : Constraints p) : clause p c4151 = true :=
  Snake9.LocalRup.prove_clause [c1372, c1373, c1973, c274] c4151 (by decide) p (sat_cons (step1372 p h) (sat_cons (step1373 p h) (sat_cons (step1973 p h) (sat_cons (step274 p h) (sat_nil p)))))
def c4152 : List Lit := [(1692, true), (1660, false), (123, false), (87, false)]
theorem step4152 (p : Nat → Bool) (h : Constraints p) : clause p c4152 = true :=
  Snake9.LocalRup.prove_clause [c2293, c1292, c1887, c2201, c1332, c1341, c1299, c2202, c3426, c3178] c4152 (by decide) p (sat_cons (step2293 p h) (sat_cons (step1292 p h) (sat_cons (step1887 p h) (sat_cons (step2201 p h) (sat_cons (step1332 p h) (sat_cons (step1341 p h) (sat_cons (step1299 p h) (sat_cons (step2202 p h) (sat_cons (step3426 p h) (sat_cons (step3178 p h) (sat_nil p)))))))))))
def c4153 : List Lit := [(96, true), (102, false), (123, false), (1829, true)]
theorem step4153 (p : Nat → Bool) (h : Constraints p) : clause p c4153 = true :=
  Snake9.LocalRup.prove_clause [c3626, c2263, c1530, c1519, c1520, c1528, c1527, c2662, c3492] c4153 (by decide) p (sat_cons (step3626 p h) (sat_cons (step2263 p h) (sat_cons (step1530 p h) (sat_cons (step1519 p h) (sat_cons (step1520 p h) (sat_cons (step1528 p h) (sat_cons (step1527 p h) (sat_cons (step2662 p h) (sat_cons (step3492 p h) (sat_nil p))))))))))
def c4154 : List Lit := [(1801, false), (1829, true), (87, false), (66, false), (1831, true), (1830, true)]
theorem step4154 (p : Nat → Bool) (h : Constraints p) : clause p c4154 = true :=
  Snake9.LocalRup.prove_clause [c1616, c3721, c1641, c1636, c1635, c1618, c1617, c3723, c2693, c3151, c1521, c1556, c1518, c1527] c4154 (by decide) p (sat_cons (step1616 p h) (sat_cons (step3721 p h) (sat_cons (step1641 p h) (sat_cons (step1636 p h) (sat_cons (step1635 p h) (sat_cons (step1618 p h) (sat_cons (step1617 p h) (sat_cons (step3723 p h) (sat_cons (step2693 p h) (sat_cons (step3151 p h) (sat_cons (step1521 p h) (sat_cons (step1556 p h) (sat_cons (step1518 p h) (sat_cons (step1527 p h) (sat_nil p)))))))))))))))
def c4155 : List Lit := [(1695, true), (1662, false), (27, true), (1607, false), (1583, false), (123, false)]
theorem step4155 (p : Nat → Bool) (h : Constraints p) : clause p c4155 = true :=
  Snake9.LocalRup.prove_clause [c1344, c3470, c1301, c1352, c3426, c2203, c3129, c1156] c4155 (by decide) p (sat_cons (step1344 p h) (sat_cons (step3470 p h) (sat_cons (step1301 p h) (sat_cons (step1352 p h) (sat_cons (step3426 p h) (sat_cons (step2203 p h) (sat_cons (step3129 p h) (sat_cons (step1156 p h) (sat_nil p)))))))))
def c4156 : List Lit := [(96, false), (7, false), (1580, true), (1852, true), (1707, true)]
theorem step4156 (p : Nat → Bool) (h : Constraints p) : clause p c4156 = true :=
  Snake9.LocalRup.prove_clause [c1370, c1979, c4138, c4118, c3446, c1696, c4121] c4156 (by decide) p (sat_cons (step1370 p h) (sat_cons (step1979 p h) (sat_cons (step4138 p h) (sat_cons (step4118 p h) (sat_cons (step3446 p h) (sat_cons (step1696 p h) (sat_cons (step4121 p h) (sat_nil p))))))))
def c4157 : List Lit := [(1744, false), (1789, false), (1760, true), (7, false), (1852, true), (123, false)]
theorem step4157 (p : Nat → Bool) (h : Constraints p) : clause p c4157 = true :=
  Snake9.LocalRup.prove_clause [c3620, c2860, c1448, c1506, c4119, c1453, c1484, c1689, c1493, c3142, c1642, c4027, c1617, c3157] c4157 (by decide) p (sat_cons (step3620 p h) (sat_cons (step2860 p h) (sat_cons (step1448 p h) (sat_cons (step1506 p h) (sat_cons (step4119 p h) (sat_cons (step1453 p h) (sat_cons (step1484 p h) (sat_cons (step1689 p h) (sat_cons (step1493 p h) (sat_cons (step3142 p h) (sat_cons (step1642 p h) (sat_cons (step4027 p h) (sat_cons (step1617 p h) (sat_cons (step3157 p h) (sat_nil p)))))))))))))))
def c4158 : List Lit := [(1749, true), (1760, true), (91, true), (123, false)]
theorem step4158 (p : Nat → Bool) (h : Constraints p) : clause p c4158 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1441, c1457, c3042, c3138, c3361, c1893] c4158 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1441 p h) (sat_cons (step1457 p h) (sat_cons (step3042 p h) (sat_cons (step3138 p h) (sat_cons (step3361 p h) (sat_cons (step1893 p h) (sat_nil p))))))))
def c4159 : List Lit := [(1851, true), (91, true), (108, true), (1775, false), (123, false)]
theorem step4159 (p : Nat → Bool) (h : Constraints p) : clause p c4159 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1441, c2860, c3618, c4158, c1484, c1493, c1688, c4049, c3562] c4159 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1441 p h) (sat_cons (step2860 p h) (sat_cons (step3618 p h) (sat_cons (step4158 p h) (sat_cons (step1484 p h) (sat_cons (step1493 p h) (sat_cons (step1688 p h) (sat_cons (step4049 p h) (sat_cons (step3562 p h) (sat_nil p)))))))))))
def c4160 : List Lit := [(7, false), (80, false), (1721, true), (123, false)]
theorem step4160 (p : Nat → Bool) (h : Constraints p) : clause p c4160 = true :=
  Snake9.LocalRup.prove_clause [c314, c3084, c1384, c1393] c4160 (by decide) p (sat_cons (step314 p h) (sat_cons (step3084 p h) (sat_cons (step1384 p h) (sat_cons (step1393 p h) (sat_nil p)))))
def c4161 : List Lit := [(62, false), (1774, true), (102, false), (123, false)]
theorem step4161 (p : Nat → Bool) (h : Constraints p) : clause p c4161 = true :=
  Snake9.LocalRup.prove_clause [c586, c584, c1523] c4161 (by decide) p (sat_cons (step586 p h) (sat_cons (step584 p h) (sat_cons (step1523 p h) (sat_nil p))))
def c4162 : List Lit := [(1831, true), (103, true), (127, true), (64, true), (56, false), (96, true), (108, true), (1773, false), (66, false)]
theorem step4162 (p : Nat → Bool) (h : Constraints p) : clause p c4162 = true :=
  Snake9.LocalRup.prove_clause [c1533, c1519, c1527, c1536, c3022, c1530, c1520, c4101, c657, c659, c1534, c1589, c1544, c1591, c1558, c1596, c1655, c2234] c4162 (by decide) p (sat_cons (step1533 p h) (sat_cons (step1519 p h) (sat_cons (step1527 p h) (sat_cons (step1536 p h) (sat_cons (step3022 p h) (sat_cons (step1530 p h) (sat_cons (step1520 p h) (sat_cons (step4101 p h) (sat_cons (step657 p h) (sat_cons (step659 p h) (sat_cons (step1534 p h) (sat_cons (step1589 p h) (sat_cons (step1544 p h) (sat_cons (step1591 p h) (sat_cons (step1558 p h) (sat_cons (step1596 p h) (sat_cons (step1655 p h) (sat_cons (step2234 p h) (sat_nil p)))))))))))))))))))
def c4163 : List Lit := [(96, false), (100, false), (1645, true), (1707, true)]
theorem step4163 (p : Nat → Bool) (h : Constraints p) : clause p c4163 = true :=
  Snake9.LocalRup.prove_clause [c1370, c621, c1998, c3446] c4163 (by decide) p (sat_cons (step1370 p h) (sat_cons (step621 p h) (sat_cons (step1998 p h) (sat_cons (step3446 p h) (sat_nil p)))))
def c4164 : List Lit := [(1583, true), (1741, true)]
theorem step4164 (p : Nat → Bool) (h : Constraints p) : clause p c4164 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1864, c1132, c1125, c1862, c2760, c49, c2032] c4164 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1864 p h) (sat_cons (step1132 p h) (sat_cons (step1125 p h) (sat_cons (step1862 p h) (sat_cons (step2760 p h) (sat_cons (step49 p h) (sat_cons (step2032 p h) (sat_nil p)))))))))
def c4165 : List Lit := [(1760, true), (1725, false), (91, true), (123, false)]
theorem step4165 (p : Nat → Bool) (h : Constraints p) : clause p c4165 = true :=
  Snake9.LocalRup.prove_clause [c4158, c1493] c4165 (by decide) p (sat_cons (step4158 p h) (sat_cons (step1493 p h) (sat_nil p)))
def c4166 : List Lit := [(1644, false), (1817, true), (87, false), (1647, true), (1670, true), (123, false)]
theorem step4166 (p : Nat → Bool) (h : Constraints p) : clause p c4166 = true :=
  Snake9.LocalRup.prove_clause [c1241, c3734, c1233, c1298, c3610] c4166 (by decide) p (sat_cons (step1241 p h) (sat_cons (step3734 p h) (sat_cons (step1233 p h) (sat_cons (step1298 p h) (sat_cons (step3610 p h) (sat_nil p))))))
def c4167 : List Lit := [(57, true), (49, true), (51, false), (54, false), (87, false), (1745, true), (1792, true), (93, false), (1781, false), (91, true), (1773, false)]
theorem step4167 (p : Nat → Bool) (h : Constraints p) : clause p c4167 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1443, c3533, c1909, c1445, c2071, c1435, c191, c1438, c466, c369, c2287, c2123, c1534, c486, c1544, c1563, c1530, c1520] c4167 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1443 p h) (sat_cons (step3533 p h) (sat_cons (step1909 p h) (sat_cons (step1445 p h) (sat_cons (step2071 p h) (sat_cons (step1435 p h) (sat_cons (step191 p h) (sat_cons (step1438 p h) (sat_cons (step466 p h) (sat_cons (step369 p h) (sat_cons (step2287 p h) (sat_cons (step2123 p h) (sat_cons (step1534 p h) (sat_cons (step486 p h) (sat_cons (step1544 p h) (sat_cons (step1563 p h) (sat_cons (step1530 p h) (sat_cons (step1520 p h) (sat_nil p))))))))))))))))))))
def c4168 : List Lit := [(51, false), (53, false), (54, false), (87, false), (1745, true), (1792, true), (93, false), (1651, true), (1781, false), (91, true), (1773, false)]
theorem step4168 (p : Nat → Bool) (h : Constraints p) : clause p c4168 = true :=
  Snake9.LocalRup.prove_clause [c167, c4167, c200, c186, c1248, c2594] c4168 (by decide) p (sat_cons (step167 p h) (sat_cons (step4167 p h) (sat_cons (step200 p h) (sat_cons (step186 p h) (sat_cons (step1248 p h) (sat_cons (step2594 p h) (sat_nil p)))))))
def c4169 : List Lit := [(1655, true), (1732, true), (1726, true), (1737, true), (1707, false), (62, true), (123, false)]
theorem step4169 (p : Nat → Bool) (h : Constraints p) : clause p c4169 = true :=
  Snake9.LocalRup.prove_clause [c1377, c1404, c3347, c3738, c1253, c3707, c2656, c1251, c3341, c1383, c1385, c3709, c1393, c1408, c4151, c1378] c4169 (by decide) p (sat_cons (step1377 p h) (sat_cons (step1404 p h) (sat_cons (step3347 p h) (sat_cons (step3738 p h) (sat_cons (step1253 p h) (sat_cons (step3707 p h) (sat_cons (step2656 p h) (sat_cons (step1251 p h) (sat_cons (step3341 p h) (sat_cons (step1383 p h) (sat_cons (step1385 p h) (sat_cons (step3709 p h) (sat_cons (step1393 p h) (sat_cons (step1408 p h) (sat_cons (step4151 p h) (sat_cons (step1378 p h) (sat_nil p)))))))))))))))))
def c4170 : List Lit := [(51, false), (53, false), (54, false), (95, false), (93, true)]
theorem step4170 (p : Nat → Bool) (h : Constraints p) : clause p c4170 = true :=
  Snake9.LocalRup.prove_clause [c167, c191, c2070] c4170 (by decide) p (sat_cons (step167 p h) (sat_cons (step191 p h) (sat_cons (step2070 p h) (sat_nil p))))
def c4171 : List Lit := [(19, false), (16, false), (95, false), (93, true)]
theorem step4171 (p : Nat → Bool) (h : Constraints p) : clause p c4171 = true :=
  Snake9.LocalRup.prove_clause [c2032, c49] c4171 (by decide) p (sat_cons (step2032 p h) (sat_cons (step49 p h) (sat_nil p)))
def c4172 : List Lit := [(1818, true), (125, false), (95, false), (104, false), (123, false), (93, true)]
theorem step4172 (p : Nat → Bool) (h : Constraints p) : clause p c4172 = true :=
  Snake9.LocalRup.prove_clause [c3515, c2235, c1613, c2929, c2295, c2332, c2374, c2165, c765, c764, c1574, c1571, c1579] c4172 (by decide) p (sat_cons (step3515 p h) (sat_cons (step2235 p h) (sat_cons (step1613 p h) (sat_cons (step2929 p h) (sat_cons (step2295 p h) (sat_cons (step2332 p h) (sat_cons (step2374 p h) (sat_cons (step2165 p h) (sat_cons (step765 p h) (sat_cons (step764 p h) (sat_cons (step1574 p h) (sat_cons (step1571 p h) (sat_cons (step1579 p h) (sat_nil p))))))))))))))
def c4173 : List Lit := [(1597, true), (95, false), (1591, false), (1588, false), (93, true)]
theorem step4173 (p : Nat → Bool) (h : Constraints p) : clause p c4173 = true :=
  Snake9.LocalRup.prove_clause [c2330, c1156, c1862, c1864, c4171, c1125] c4173 (by decide) p (sat_cons (step2330 p h) (sat_cons (step1156 p h) (sat_cons (step1862 p h) (sat_cons (step1864 p h) (sat_cons (step4171 p h) (sat_cons (step1125 p h) (sat_nil p)))))))
def c4174 : List Lit := [(107, true), (20, false), (125, true), (95, false), (104, false)]
theorem step4174 (p : Nat → Bool) (h : Constraints p) : clause p c4174 = true :=
  Snake9.LocalRup.prove_clause [c2142, c2141, c503] c4174 (by decide) p (sat_cons (step2142 p h) (sat_cons (step2141 p h) (sat_cons (step503 p h) (sat_nil p))))
def c4175 : List Lit := [(1761, true), (1745, true), (114, true), (7, false), (93, true), (91, true), (123, false), (95, true)]
theorem step4175 (p : Nat → Bool) (h : Constraints p) : clause p c4175 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1445, c1435, c1433, c1443, c1438, c3019, c1442, c2860, c1486, c3581, c1463, c3274, c4054, c1424, c1429] c4175 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1445 p h) (sat_cons (step1435 p h) (sat_cons (step1433 p h) (sat_cons (step1443 p h) (sat_cons (step1438 p h) (sat_cons (step3019 p h) (sat_cons (step1442 p h) (sat_cons (step2860 p h) (sat_cons (step1486 p h) (sat_cons (step3581 p h) (sat_cons (step1463 p h) (sat_cons (step3274 p h) (sat_cons (step4054 p h) (sat_cons (step1424 p h) (sat_cons (step1429 p h) (sat_nil p)))))))))))))))))
def c4176 : List Lit := [(1608, false), (1693, true), (1761, false), (1782, false), (35, true), (1812, true), (1636, true), (93, true), (1652, false), (1775, false), (123, false)]
theorem step4176 (p : Nat → Bool) (h : Constraints p) : clause p c4176 = true :=
  Snake9.LocalRup.prove_clause [c2293, c2709, c1291, c1349, c1350, c2249, c1292, c1705, c2724, c3610, c3395, c1648, c2058, c1553, c2270, c1542, c1532] c4176 (by decide) p (sat_cons (step2293 p h) (sat_cons (step2709 p h) (sat_cons (step1291 p h) (sat_cons (step1349 p h) (sat_cons (step1350 p h) (sat_cons (step2249 p h) (sat_cons (step1292 p h) (sat_cons (step1705 p h) (sat_cons (step2724 p h) (sat_cons (step3610 p h) (sat_cons (step3395 p h) (sat_cons (step1648 p h) (sat_cons (step2058 p h) (sat_cons (step1553 p h) (sat_cons (step2270 p h) (sat_cons (step1542 p h) (sat_cons (step1532 p h) (sat_nil p))))))))))))))))))
def c4177 : List Lit := [(1790, true), (88, false), (1771, false), (1782, false), (123, false)]
theorem step4177 (p : Nat → Bool) (h : Constraints p) : clause p c4177 = true :=
  Snake9.LocalRup.prove_clause [c1526, c1539, c1553, c1557, c1542, c1527, c2707, c1533, c1521, c1522, c2263, c631, c419, c543, c2129] c4177 (by decide) p (sat_cons (step1526 p h) (sat_cons (step1539 p h) (sat_cons (step1553 p h) (sat_cons (step1557 p h) (sat_cons (step1542 p h) (sat_cons (step1527 p h) (sat_cons (step2707 p h) (sat_cons (step1533 p h) (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step2263 p h) (sat_cons (step631 p h) (sat_cons (step419 p h) (sat_cons (step543 p h) (sat_cons (step2129 p h) (sat_nil p))))))))))))))))
def c4178 : List Lit := [(1608, true), (1637, true), (21, true), (1580, false), (102, true)]
theorem step4178 (p : Nat → Bool) (h : Constraints p) : clause p c4178 = true :=
  Snake9.LocalRup.prove_clause [c1864, c1136, c1143, c1155, c2203, c1176, c3833, c1896, c1099] c4178 (by decide) p (sat_cons (step1864 p h) (sat_cons (step1136 p h) (sat_cons (step1143 p h) (sat_cons (step1155 p h) (sat_cons (step2203 p h) (sat_cons (step1176 p h) (sat_cons (step3833 p h) (sat_cons (step1896 p h) (sat_cons (step1099 p h) (sat_nil p))))))))))
def c4179 : List Lit := [(1745, false), (1708, true), (1655, true), (1761, true), (102, true), (123, false)]
theorem step4179 (p : Nat → Bool) (h : Constraints p) : clause p c4179 = true :=
  Snake9.LocalRup.prove_clause [c1253, c1879, c3665, c1454, c3358, c1494, c3328] c4179 (by decide) p (sat_cons (step1253 p h) (sat_cons (step1879 p h) (sat_cons (step3665 p h) (sat_cons (step1454 p h) (sat_cons (step3358 p h) (sat_cons (step1494 p h) (sat_cons (step3328 p h) (sat_nil p))))))))
def c4180 : List Lit := [(1659, false), (1668, false), (1580, false), (1692, true), (102, true), (123, false)]
theorem step4180 (p : Nat → Bool) (h : Constraints p) : clause p c4180 = true :=
  Snake9.LocalRup.prove_clause [c1864, c1154, c2293, c3714, c3828, c1873, c2202, c3633, c1896, c1156, c3670, c1099, c3920, c138] c4180 (by decide) p (sat_cons (step1864 p h) (sat_cons (step1154 p h) (sat_cons (step2293 p h) (sat_cons (step3714 p h) (sat_cons (step3828 p h) (sat_cons (step1873 p h) (sat_cons (step2202 p h) (sat_cons (step3633 p h) (sat_cons (step1896 p h) (sat_cons (step1156 p h) (sat_cons (step3670 p h) (sat_cons (step1099 p h) (sat_cons (step3920 p h) (sat_cons (step138 p h) (sat_nil p)))))))))))))))
def c4181 : List Lit := [(1596, true), (1580, false), (1692, true), (102, true), (123, false)]
theorem step4181 (p : Nat → Bool) (h : Constraints p) : clause p c4181 = true :=
  Snake9.LocalRup.prove_clause [c1864, c1154, c2476, c3670, c1155, c1141, c1139, c138, c147, c149, c150, c1099, c1190, c1200, c1204, c1896, c1198, c1209, c1175, c1228, c1341, c1309] c4181 (by decide) p (sat_cons (step1864 p h) (sat_cons (step1154 p h) (sat_cons (step2476 p h) (sat_cons (step3670 p h) (sat_cons (step1155 p h) (sat_cons (step1141 p h) (sat_cons (step1139 p h) (sat_cons (step138 p h) (sat_cons (step147 p h) (sat_cons (step149 p h) (sat_cons (step150 p h) (sat_cons (step1099 p h) (sat_cons (step1190 p h) (sat_cons (step1200 p h) (sat_cons (step1204 p h) (sat_cons (step1896 p h) (sat_cons (step1198 p h) (sat_cons (step1209 p h) (sat_cons (step1175 p h) (sat_cons (step1228 p h) (sat_cons (step1341 p h) (sat_cons (step1309 p h) (sat_nil p)))))))))))))))))))))))
def c4182 : List Lit := [(1608, false), (1636, false), (1668, false), (1692, true), (1745, false), (102, true), (123, false)]
theorem step4182 (p : Nat → Bool) (h : Constraints p) : clause p c4182 = true :=
  Snake9.LocalRup.prove_clause [c1348, c1349, c2248, c1297, c3622, c1260, c1264, c3660, c1240, c1232] c4182 (by decide) p (sat_cons (step1348 p h) (sat_cons (step1349 p h) (sat_cons (step2248 p h) (sat_cons (step1297 p h) (sat_cons (step3622 p h) (sat_cons (step1260 p h) (sat_cons (step1264 p h) (sat_cons (step3660 p h) (sat_cons (step1240 p h) (sat_cons (step1232 p h) (sat_nil p)))))))))))
def c4183 : List Lit := [(44, false), (1658, false), (7, false), (1596, false), (1583, false), (1692, true), (123, false)]
theorem step4183 (p : Nat → Bool) (h : Constraints p) : clause p c4183 = true :=
  Snake9.LocalRup.prove_clause [c3654, c138] c4183 (by decide) p (sat_cons (step3654 p h) (sat_cons (step138 p h) (sat_nil p)))
end B112E050
