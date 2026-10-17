import B112E036Part0086
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c7213 : List Lit := [(1852, true), (95, true), (1785, true)]
theorem step7213 (p : Nat → Bool) (h : Constraints p) : clause p c7213 = true :=
  Snake9.LocalRup.prove_clause [c7210, c5368, c3331, c1335, c6652, c1460, c2267, c6690, c6671, c6860, c3263, c1361, c3275, c3424, c2004, c1287, c2466, c3297, c1281, c1280, c6207, c1371, c2314, c3472, c1524, c3665, c3602, c1461, c6054, c1456, c1410, c7211, c6651, c6245, c1405, c1519, c1435, c2313, c6674, c2016, c1388, c4907, c2970, c447, c1635, c1916, c549, c3247, c476, c1885, c7212, c6187, c435, c1283, c1285, c1286, c3154, c1311, c7086, c5260] c7213 (by decide) p (sat_cons (step7210 p h) (sat_cons (step5368 p h) (sat_cons (step3331 p h) (sat_cons (step1335 p h) (sat_cons (step6652 p h) (sat_cons (step1460 p h) (sat_cons (step2267 p h) (sat_cons (step6690 p h) (sat_cons (step6671 p h) (sat_cons (step6860 p h) (sat_cons (step3263 p h) (sat_cons (step1361 p h) (sat_cons (step3275 p h) (sat_cons (step3424 p h) (sat_cons (step2004 p h) (sat_cons (step1287 p h) (sat_cons (step2466 p h) (sat_cons (step3297 p h) (sat_cons (step1281 p h) (sat_cons (step1280 p h) (sat_cons (step6207 p h) (sat_cons (step1371 p h) (sat_cons (step2314 p h) (sat_cons (step3472 p h) (sat_cons (step1524 p h) (sat_cons (step3665 p h) (sat_cons (step3602 p h) (sat_cons (step1461 p h) (sat_cons (step6054 p h) (sat_cons (step1456 p h) (sat_cons (step1410 p h) (sat_cons (step7211 p h) (sat_cons (step6651 p h) (sat_cons (step6245 p h) (sat_cons (step1405 p h) (sat_cons (step1519 p h) (sat_cons (step1435 p h) (sat_cons (step2313 p h) (sat_cons (step6674 p h) (sat_cons (step2016 p h) (sat_cons (step1388 p h) (sat_cons (step4907 p h) (sat_cons (step2970 p h) (sat_cons (step447 p h) (sat_cons (step1635 p h) (sat_cons (step1916 p h) (sat_cons (step549 p h) (sat_cons (step3247 p h) (sat_cons (step476 p h) (sat_cons (step1885 p h) (sat_cons (step7212 p h) (sat_cons (step6187 p h) (sat_cons (step435 p h) (sat_cons (step1283 p h) (sat_cons (step1285 p h) (sat_cons (step1286 p h) (sat_cons (step3154 p h) (sat_cons (step1311 p h) (sat_cons (step7086 p h) (sat_cons (step5260 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c7214 : List Lit := [(95, true), (1785, true)]
theorem step7214 (p : Nat → Bool) (h : Constraints p) : clause p c7214 = true :=
  Snake9.LocalRup.prove_clause [c7210, c2009, c3444, c1338, c3297, c1281, c1280, c5368, c3424, c6860, c3331, c1335, c7213, c2015, c6290, c6197, c6187] c7214 (by decide) p (sat_cons (step7210 p h) (sat_cons (step2009 p h) (sat_cons (step3444 p h) (sat_cons (step1338 p h) (sat_cons (step3297 p h) (sat_cons (step1281 p h) (sat_cons (step1280 p h) (sat_cons (step5368 p h) (sat_cons (step3424 p h) (sat_cons (step6860 p h) (sat_cons (step3331 p h) (sat_cons (step1335 p h) (sat_cons (step7213 p h) (sat_cons (step2015 p h) (sat_cons (step6290 p h) (sat_cons (step6197 p h) (sat_cons (step6187 p h) (sat_nil p))))))))))))))))))
def c7215 : List Lit := [(89, true), (1785, true)]
theorem step7215 (p : Nat → Bool) (h : Constraints p) : clause p c7215 = true :=
  Snake9.LocalRup.prove_clause [c6860, c7214, c7174, c6708, c2312, c2017, c7210, c5368, c2466, c6637, c2009, c3444, c1338, c3297, c1281, c1280, c6207, c3424, c2132, c6058, c1361, c6245, c3428, c1337, c1335, c7212, c6652, c2016, c1460, c2313, c7177] c7215 (by decide) p (sat_cons (step6860 p h) (sat_cons (step7214 p h) (sat_cons (step7174 p h) (sat_cons (step6708 p h) (sat_cons (step2312 p h) (sat_cons (step2017 p h) (sat_cons (step7210 p h) (sat_cons (step5368 p h) (sat_cons (step2466 p h) (sat_cons (step6637 p h) (sat_cons (step2009 p h) (sat_cons (step3444 p h) (sat_cons (step1338 p h) (sat_cons (step3297 p h) (sat_cons (step1281 p h) (sat_cons (step1280 p h) (sat_cons (step6207 p h) (sat_cons (step3424 p h) (sat_cons (step2132 p h) (sat_cons (step6058 p h) (sat_cons (step1361 p h) (sat_cons (step6245 p h) (sat_cons (step3428 p h) (sat_cons (step1337 p h) (sat_cons (step1335 p h) (sat_cons (step7212 p h) (sat_cons (step6652 p h) (sat_cons (step2016 p h) (sat_cons (step1460 p h) (sat_cons (step2313 p h) (sat_cons (step7177 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c7216 : List Lit := [(106, false), (1785, true)]
theorem step7216 (p : Nat → Bool) (h : Constraints p) : clause p c7216 = true :=
  Snake9.LocalRup.prove_clause [c7215, c7214, c7210, c5368, c6688, c3424, c6860, c3395, c519, c532, c1335, c3870, c5793, c442, c2015, c3472, c1487, c6564] c7216 (by decide) p (sat_cons (step7215 p h) (sat_cons (step7214 p h) (sat_cons (step7210 p h) (sat_cons (step5368 p h) (sat_cons (step6688 p h) (sat_cons (step3424 p h) (sat_cons (step6860 p h) (sat_cons (step3395 p h) (sat_cons (step519 p h) (sat_cons (step532 p h) (sat_cons (step1335 p h) (sat_cons (step3870 p h) (sat_cons (step5793 p h) (sat_cons (step442 p h) (sat_cons (step2015 p h) (sat_cons (step3472 p h) (sat_cons (step1487 p h) (sat_cons (step6564 p h) (sat_nil p)))))))))))))))))))
def c7217 : List Lit := [(73, false), (1807, false), (1852, true), (1785, true)]
theorem step7217 (p : Nat → Bool) (h : Constraints p) : clause p c7217 = true :=
  Snake9.LocalRup.prove_clause [c3472, c1463, c1487, c2314, c7216, c1404, c6860, c7214, c7215, c420, c7210, c5368, c6688, c520, c7184, c6564, c1409, c3453] c7217 (by decide) p (sat_cons (step3472 p h) (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step2314 p h) (sat_cons (step7216 p h) (sat_cons (step1404 p h) (sat_cons (step6860 p h) (sat_cons (step7214 p h) (sat_cons (step7215 p h) (sat_cons (step420 p h) (sat_cons (step7210 p h) (sat_cons (step5368 p h) (sat_cons (step6688 p h) (sat_cons (step520 p h) (sat_cons (step7184 p h) (sat_cons (step6564 p h) (sat_cons (step1409 p h) (sat_cons (step3453 p h) (sat_nil p)))))))))))))))))))
def c7218 : List Lit := [(1807, false), (1852, true), (1785, true)]
theorem step7218 (p : Nat → Bool) (h : Constraints p) : clause p c7218 = true :=
  Snake9.LocalRup.prove_clause [c3472, c2314, c7216, c7215, c7214, c7210, c5368, c6860, c1463, c1487, c7217, c2130, c1361, c3428, c6245, c1337, c1335, c442, c7187] c7218 (by decide) p (sat_cons (step3472 p h) (sat_cons (step2314 p h) (sat_cons (step7216 p h) (sat_cons (step7215 p h) (sat_cons (step7214 p h) (sat_cons (step7210 p h) (sat_cons (step5368 p h) (sat_cons (step6860 p h) (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step7217 p h) (sat_cons (step2130 p h) (sat_cons (step1361 p h) (sat_cons (step3428 p h) (sat_cons (step6245 p h) (sat_cons (step1337 p h) (sat_cons (step1335 p h) (sat_cons (step442 p h) (sat_cons (step7187 p h) (sat_nil p))))))))))))))))))))
def c7219 : List Lit := [(1807, true), (1785, true)]
theorem step7219 (p : Nat → Bool) (h : Constraints p) : clause p c7219 = true :=
  Snake9.LocalRup.prove_clause [c7216, c1404, c1412, c7210, c5368, c1460, c2033, c6670, c1402, c6655] c7219 (by decide) p (sat_cons (step7216 p h) (sat_cons (step1404 p h) (sat_cons (step1412 p h) (sat_cons (step7210 p h) (sat_cons (step5368 p h) (sat_cons (step1460 p h) (sat_cons (step2033 p h) (sat_cons (step6670 p h) (sat_cons (step1402 p h) (sat_cons (step6655 p h) (sat_nil p)))))))))))
def c7220 : List Lit := [(73, false), (1785, true)]
theorem step7220 (p : Nat → Bool) (h : Constraints p) : clause p c7220 = true :=
  Snake9.LocalRup.prove_clause [c7219, c7218, c2015, c7214, c7210, c3297, c1281, c1280, c5368, c3424, c6860, c502, c4954, c5046, c5818, c6191, c6003] c7220 (by decide) p (sat_cons (step7219 p h) (sat_cons (step7218 p h) (sat_cons (step2015 p h) (sat_cons (step7214 p h) (sat_cons (step7210 p h) (sat_cons (step3297 p h) (sat_cons (step1281 p h) (sat_cons (step1280 p h) (sat_cons (step5368 p h) (sat_cons (step3424 p h) (sat_cons (step6860 p h) (sat_cons (step502 p h) (sat_cons (step4954 p h) (sat_cons (step5046 p h) (sat_cons (step5818 p h) (sat_cons (step6191 p h) (sat_cons (step6003 p h) (sat_nil p))))))))))))))))))
def c7221 : List Lit := [(1785, true)]
theorem step7221 (p : Nat → Bool) (h : Constraints p) : clause p c7221 = true :=
  Snake9.LocalRup.prove_clause [c6860, c7210, c2009, c3424, c3297, c5368, c3444, c1280, c1281, c1338, c7219, c7218, c2015, c7220, c2130, c2437, c1361, c4089, c3428, c6197, c1337, c1335] c7221 (by decide) p (sat_cons (step6860 p h) (sat_cons (step7210 p h) (sat_cons (step2009 p h) (sat_cons (step3424 p h) (sat_cons (step3297 p h) (sat_cons (step5368 p h) (sat_cons (step3444 p h) (sat_cons (step1280 p h) (sat_cons (step1281 p h) (sat_cons (step1338 p h) (sat_cons (step7219 p h) (sat_cons (step7218 p h) (sat_cons (step2015 p h) (sat_cons (step7220 p h) (sat_cons (step2130 p h) (sat_cons (step2437 p h) (sat_cons (step1361 p h) (sat_cons (step4089 p h) (sat_cons (step3428 p h) (sat_cons (step6197 p h) (sat_cons (step1337 p h) (sat_cons (step1335 p h) (sat_nil p)))))))))))))))))))))))
def c7222 : List Lit := [(1791, true)]
theorem step7222 (p : Nat → Bool) (h : Constraints p) : clause p c7222 = true :=
  Snake9.LocalRup.prove_clause [c7221, c6644] c7222 (by decide) p (sat_cons (step7221 p h) (sat_cons (step6644 p h) (sat_nil p)))
def c7223 : List Lit := [(1830, true)]
theorem step7223 (p : Nat → Bool) (h : Constraints p) : clause p c7223 = true :=
  Snake9.LocalRup.prove_clause [c7222, c6640] c7223 (by decide) p (sat_cons (step7222 p h) (sat_cons (step6640 p h) (sat_nil p)))
def c7224 : List Lit := [(1760, false)]
theorem step7224 (p : Nat → Bool) (h : Constraints p) : clause p c7224 = true :=
  Snake9.LocalRup.prove_clause [c7223, c4703] c7224 (by decide) p (sat_cons (step7223 p h) (sat_cons (step4703 p h) (sat_nil p)))
def c7225 : List Lit := [(1852, true), (1758, false), (95, true)]
theorem step7225 (p : Nat → Bool) (h : Constraints p) : clause p c7225 = true :=
  Snake9.LocalRup.prove_clause [c7223, c7222, c7221, c1783, c1550, c1556, c6638, c5838, c1519, c1431, c1445, c2044, c2267, c3827, c1478, c6637, c1447, c1470, c5001, c1439, c3444, c6693, c1362, c1454, c2003, c1759] c7225 (by decide) p (sat_cons (step7223 p h) (sat_cons (step7222 p h) (sat_cons (step7221 p h) (sat_cons (step1783 p h) (sat_cons (step1550 p h) (sat_cons (step1556 p h) (sat_cons (step6638 p h) (sat_cons (step5838 p h) (sat_cons (step1519 p h) (sat_cons (step1431 p h) (sat_cons (step1445 p h) (sat_cons (step2044 p h) (sat_cons (step2267 p h) (sat_cons (step3827 p h) (sat_cons (step1478 p h) (sat_cons (step6637 p h) (sat_cons (step1447 p h) (sat_cons (step1470 p h) (sat_cons (step5001 p h) (sat_cons (step1439 p h) (sat_cons (step3444 p h) (sat_cons (step6693 p h) (sat_cons (step1362 p h) (sat_cons (step1454 p h) (sat_cons (step2003 p h) (sat_cons (step1759 p h) (sat_nil p)))))))))))))))))))))))))))
def c7226 : List Lit := [(1817, false), (1724, false), (1832, true)]
theorem step7226 (p : Nat → Bool) (h : Constraints p) : clause p c7226 = true :=
  Snake9.LocalRup.prove_clause [c7222, c7221, c1519, c1524, c4704, c1431, c1362, c6637, c3444, c5001] c7226 (by decide) p (sat_cons (step7222 p h) (sat_cons (step7221 p h) (sat_cons (step1519 p h) (sat_cons (step1524 p h) (sat_cons (step4704 p h) (sat_cons (step1431 p h) (sat_cons (step1362 p h) (sat_cons (step6637 p h) (sat_cons (step3444 p h) (sat_cons (step5001 p h) (sat_nil p)))))))))))
def c7227 : List Lit := [(1800, true), (89, true), (1758, false), (88, true), (95, true)]
theorem step7227 (p : Nat → Bool) (h : Constraints p) : clause p c7227 = true :=
  Snake9.LocalRup.prove_clause [c7222, c4698, c7225, c2015, c6502, c7226, c2267, c1460, c1458, c1455, c1766, c3827, c1520, c1445, c2044, c1447, c1439, c2220, c6693, c6701, c766, c1941, c974, c684, c975, c947, c976, c948, c978, c951, c1983, c955] c7227 (by decide) p (sat_cons (step7222 p h) (sat_cons (step4698 p h) (sat_cons (step7225 p h) (sat_cons (step2015 p h) (sat_cons (step6502 p h) (sat_cons (step7226 p h) (sat_cons (step2267 p h) (sat_cons (step1460 p h) (sat_cons (step1458 p h) (sat_cons (step1455 p h) (sat_cons (step1766 p h) (sat_cons (step3827 p h) (sat_cons (step1520 p h) (sat_cons (step1445 p h) (sat_cons (step2044 p h) (sat_cons (step1447 p h) (sat_cons (step1439 p h) (sat_cons (step2220 p h) (sat_cons (step6693 p h) (sat_cons (step6701 p h) (sat_cons (step766 p h) (sat_cons (step1941 p h) (sat_cons (step974 p h) (sat_cons (step684 p h) (sat_cons (step975 p h) (sat_cons (step947 p h) (sat_cons (step976 p h) (sat_cons (step948 p h) (sat_cons (step978 p h) (sat_cons (step951 p h) (sat_cons (step1983 p h) (sat_cons (step955 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c7228 : List Lit := [(1800, false), (1758, false), (1748, false), (95, true)]
theorem step7228 (p : Nat → Bool) (h : Constraints p) : clause p c7228 = true :=
  Snake9.LocalRup.prove_clause [c7224, c7221, c4698, c7225, c2015, c6502, c7226, c2267, c1458, c1456, c1460, c1455, c767, c2033, c1363, c6639, c1436, c6674, c5841, c1482, c1466, c1758, c2304, c1452, c3531, c2148, c1959, c1955, c6653, c6706, c1334, c6638, c5002, c4704] c7228 (by decide) p (sat_cons (step7224 p h) (sat_cons (step7221 p h) (sat_cons (step4698 p h) (sat_cons (step7225 p h) (sat_cons (step2015 p h) (sat_cons (step6502 p h) (sat_cons (step7226 p h) (sat_cons (step2267 p h) (sat_cons (step1458 p h) (sat_cons (step1456 p h) (sat_cons (step1460 p h) (sat_cons (step1455 p h) (sat_cons (step767 p h) (sat_cons (step2033 p h) (sat_cons (step1363 p h) (sat_cons (step6639 p h) (sat_cons (step1436 p h) (sat_cons (step6674 p h) (sat_cons (step5841 p h) (sat_cons (step1482 p h) (sat_cons (step1466 p h) (sat_cons (step1758 p h) (sat_cons (step2304 p h) (sat_cons (step1452 p h) (sat_cons (step3531 p h) (sat_cons (step2148 p h) (sat_cons (step1959 p h) (sat_cons (step1955 p h) (sat_cons (step6653 p h) (sat_cons (step6706 p h) (sat_cons (step1334 p h) (sat_cons (step6638 p h) (sat_cons (step5002 p h) (sat_cons (step4704 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c7229 : List Lit := [(1758, false), (88, true), (95, true)]
theorem step7229 (p : Nat → Bool) (h : Constraints p) : clause p c7229 = true :=
  Snake9.LocalRup.prove_clause [c7224, c1333, c1339, c3428, c1783, c4698, c7225, c2015, c6502, c7226, c2267, c3827, c1478, c1458, c1460, c2033, c1470, c1455, c1456, c1401, c767, c7228, c1445, c2044, c1447, c7227, c1439, c6693, c1454, c3531, c2148, c6700, c1959, c2004, c1707, c6548, c1409] c7229 (by decide) p (sat_cons (step7224 p h) (sat_cons (step1333 p h) (sat_cons (step1339 p h) (sat_cons (step3428 p h) (sat_cons (step1783 p h) (sat_cons (step4698 p h) (sat_cons (step7225 p h) (sat_cons (step2015 p h) (sat_cons (step6502 p h) (sat_cons (step7226 p h) (sat_cons (step2267 p h) (sat_cons (step3827 p h) (sat_cons (step1478 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step2033 p h) (sat_cons (step1470 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step1401 p h) (sat_cons (step767 p h) (sat_cons (step7228 p h) (sat_cons (step1445 p h) (sat_cons (step2044 p h) (sat_cons (step1447 p h) (sat_cons (step7227 p h) (sat_cons (step1439 p h) (sat_cons (step6693 p h) (sat_cons (step1454 p h) (sat_cons (step3531 p h) (sat_cons (step2148 p h) (sat_cons (step6700 p h) (sat_cons (step1959 p h) (sat_cons (step2004 p h) (sat_cons (step1707 p h) (sat_cons (step6548 p h) (sat_cons (step1409 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c7230 : List Lit := [(88, true), (95, true)]
theorem step7230 (p : Nat → Bool) (h : Constraints p) : clause p c7230 = true :=
  Snake9.LocalRup.prove_clause [c7221, c1333, c1339, c3428, c7229, c5368, c3331, c5848, c1335, c1771, c2015, c6652, c6637, c2314, c1460, c1431, c2267, c1524] c7230 (by decide) p (sat_cons (step7221 p h) (sat_cons (step1333 p h) (sat_cons (step1339 p h) (sat_cons (step3428 p h) (sat_cons (step7229 p h) (sat_cons (step5368 p h) (sat_cons (step3331 p h) (sat_cons (step5848 p h) (sat_cons (step1335 p h) (sat_cons (step1771 p h) (sat_cons (step2015 p h) (sat_cons (step6652 p h) (sat_cons (step6637 p h) (sat_cons (step2314 p h) (sat_cons (step1460 p h) (sat_cons (step1431 p h) (sat_cons (step2267 p h) (sat_cons (step1524 p h) (sat_nil p)))))))))))))))))))
def c7231 : List Lit := [(1741, true), (124, false)]
theorem step7231 (p : Nat → Bool) (h : Constraints p) : clause p c7231 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1335, c6652] c7231 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step6652 p h) (sat_nil p))))
def c7232 : List Lit := [(1758, false), (95, true)]
theorem step7232 (p : Nat → Bool) (h : Constraints p) : clause p c7232 = true :=
  Snake9.LocalRup.prove_clause [c7224, c7221, c7230, c3263, c1363, c1783, c4698, c6639, c7226, c1436, c2267, c3827, c1478, c6674, c1458, c1460, c2033, c1470, c1455, c1456, c767, c7231, c1337, c3428, c7228, c1445, c2044, c1447, c1439, c6693, c1454, c1759, c3531, c1960, c1959, c1955, c5002, c4704, c6638, c1431, c6706, c6637, c662, c1387] c7232 (by decide) p (sat_cons (step7224 p h) (sat_cons (step7221 p h) (sat_cons (step7230 p h) (sat_cons (step3263 p h) (sat_cons (step1363 p h) (sat_cons (step1783 p h) (sat_cons (step4698 p h) (sat_cons (step6639 p h) (sat_cons (step7226 p h) (sat_cons (step1436 p h) (sat_cons (step2267 p h) (sat_cons (step3827 p h) (sat_cons (step1478 p h) (sat_cons (step6674 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step2033 p h) (sat_cons (step1470 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step767 p h) (sat_cons (step7231 p h) (sat_cons (step1337 p h) (sat_cons (step3428 p h) (sat_cons (step7228 p h) (sat_cons (step1445 p h) (sat_cons (step2044 p h) (sat_cons (step1447 p h) (sat_cons (step1439 p h) (sat_cons (step6693 p h) (sat_cons (step1454 p h) (sat_cons (step1759 p h) (sat_cons (step3531 p h) (sat_cons (step1960 p h) (sat_cons (step1959 p h) (sat_cons (step1955 p h) (sat_cons (step5002 p h) (sat_cons (step4704 p h) (sat_cons (step6638 p h) (sat_cons (step1431 p h) (sat_cons (step6706 p h) (sat_cons (step6637 p h) (sat_cons (step662 p h) (sat_cons (step1387 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c7233 : List Lit := [(95, true)]
theorem step7233 (p : Nat → Bool) (h : Constraints p) : clause p c7233 = true :=
  Snake9.LocalRup.prove_clause [c7221, c7230, c7232, c2009, c3424, c3297, c5368, c3331, c3444, c1280, c1281, c2466, c1335, c7231, c1338, c6637, c1460, c1431, c2267, c1524, c2314, c2015, c6290, c6197, c6187] c7233 (by decide) p (sat_cons (step7221 p h) (sat_cons (step7230 p h) (sat_cons (step7232 p h) (sat_cons (step2009 p h) (sat_cons (step3424 p h) (sat_cons (step3297 p h) (sat_cons (step5368 p h) (sat_cons (step3331 p h) (sat_cons (step3444 p h) (sat_cons (step1280 p h) (sat_cons (step1281 p h) (sat_cons (step2466 p h) (sat_cons (step1335 p h) (sat_cons (step7231 p h) (sat_cons (step1338 p h) (sat_cons (step6637 p h) (sat_cons (step1460 p h) (sat_cons (step1431 p h) (sat_cons (step2267 p h) (sat_cons (step1524 p h) (sat_cons (step2314 p h) (sat_cons (step2015 p h) (sat_cons (step6290 p h) (sat_cons (step6197 p h) (sat_cons (step6187 p h) (sat_nil p))))))))))))))))))))))))))
def c7234 : List Lit := [(1831, true)]
theorem step7234 (p : Nat → Bool) (h : Constraints p) : clause p c7234 = true :=
  Snake9.LocalRup.prove_clause [c7233, c7221, c5851] c7234 (by decide) p (sat_cons (step7233 p h) (sat_cons (step7221 p h) (sat_cons (step5851 p h) (sat_nil p))))
def c7235 : List Lit := [(1851, true)]
theorem step7235 (p : Nat → Bool) (h : Constraints p) : clause p c7235 = true :=
  Snake9.LocalRup.prove_clause [c7234, c2313] c7235 (by decide) p (sat_cons (step7234 p h) (sat_cons (step2313 p h) (sat_nil p)))
def c7236 : List Lit := [(1759, false)]
theorem step7236 (p : Nat → Bool) (h : Constraints p) : clause p c7236 = true :=
  Snake9.LocalRup.prove_clause [c7234, c4704] c7236 (by decide) p (sat_cons (step7234 p h) (sat_cons (step4704 p h) (sat_nil p)))
def c7237 : List Lit := [(1695, false)]
theorem step7237 (p : Nat → Bool) (h : Constraints p) : clause p c7237 = true :=
  Snake9.LocalRup.prove_clause [c7235, c2016] c7237 (by decide) p (sat_cons (step7235 p h) (sat_cons (step2016 p h) (sat_nil p)))
def c7238 : List Lit := [(1750, false)]
theorem step7238 (p : Nat → Bool) (h : Constraints p) : clause p c7238 = true :=
  Snake9.LocalRup.prove_clause [c7236, c2010] c7238 (by decide) p (sat_cons (step7236 p h) (sat_cons (step2010 p h) (sat_nil p)))
def c7239 : List Lit := [(1771, true)]
theorem step7239 (p : Nat → Bool) (h : Constraints p) : clause p c7239 = true :=
  Snake9.LocalRup.prove_clause [c7236, c7233, c5853] c7239 (by decide) p (sat_cons (step7236 p h) (sat_cons (step7233 p h) (sat_cons (step5853 p h) (sat_nil p))))
def c7240 : List Lit := [(1745, false)]
theorem step7240 (p : Nat → Bool) (h : Constraints p) : clause p c7240 = true :=
  Snake9.LocalRup.prove_clause [c7238, c3443] c7240 (by decide) p (sat_cons (step7238 p h) (sat_cons (step3443 p h) (sat_nil p)))
def c7241 : List Lit := [(1777, true)]
theorem step7241 (p : Nat → Bool) (h : Constraints p) : clause p c7241 = true :=
  Snake9.LocalRup.prove_clause [c7239, c6637] c7241 (by decide) p (sat_cons (step7239 p h) (sat_cons (step6637 p h) (sat_nil p)))
def c7242 : List Lit := [(1792, true)]
theorem step7242 (p : Nat → Bool) (h : Constraints p) : clause p c7242 = true :=
  Snake9.LocalRup.prove_clause [c7241, c7221, c1431] c7242 (by decide) p (sat_cons (step7241 p h) (sat_cons (step7221 p h) (sat_cons (step1431 p h) (sat_nil p))))
def c7243 : List Lit := [(1818, false)]
theorem step7243 (p : Nat → Bool) (h : Constraints p) : clause p c7243 = true :=
  Snake9.LocalRup.prove_clause [c7242, c4706] c7243 (by decide) p (sat_cons (step7242 p h) (sat_cons (step4706 p h) (sat_nil p)))
def c7244 : List Lit := [(1739, false), (1758, false)]
theorem step7244 (p : Nat → Bool) (h : Constraints p) : clause p c7244 = true :=
  Snake9.LocalRup.prove_clause [c7242, c7234, c7221, c7240, c7236, c7237, c7223, c7233, c4698, c6639, c1436, c6674, c1550, c2015, c1524, c1339, c1341, c3428, c1367, c6331, c2032, c1460, c7231, c1340, c3444, c1362, c2003, c2130, c2659, c6811, c1286, c1288, c2202, c1748, c5818, c5003, c1283, c1280, c6604, c1439, c6842] c7244 (by decide) p (sat_cons (step7242 p h) (sat_cons (step7234 p h) (sat_cons (step7221 p h) (sat_cons (step7240 p h) (sat_cons (step7236 p h) (sat_cons (step7237 p h) (sat_cons (step7223 p h) (sat_cons (step7233 p h) (sat_cons (step4698 p h) (sat_cons (step6639 p h) (sat_cons (step1436 p h) (sat_cons (step6674 p h) (sat_cons (step1550 p h) (sat_cons (step2015 p h) (sat_cons (step1524 p h) (sat_cons (step1339 p h) (sat_cons (step1341 p h) (sat_cons (step3428 p h) (sat_cons (step1367 p h) (sat_cons (step6331 p h) (sat_cons (step2032 p h) (sat_cons (step1460 p h) (sat_cons (step7231 p h) (sat_cons (step1340 p h) (sat_cons (step3444 p h) (sat_cons (step1362 p h) (sat_cons (step2003 p h) (sat_cons (step2130 p h) (sat_cons (step2659 p h) (sat_cons (step6811 p h) (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step2202 p h) (sat_cons (step1748 p h) (sat_cons (step5818 p h) (sat_cons (step5003 p h) (sat_cons (step1283 p h) (sat_cons (step1280 p h) (sat_cons (step6604 p h) (sat_cons (step1439 p h) (sat_cons (step6842 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c7245 : List Lit := [(1758, false)]
theorem step7245 (p : Nat → Bool) (h : Constraints p) : clause p c7245 = true :=
  Snake9.LocalRup.prove_clause [c7234, c7242, c7221, c7233, c7236, c4698, c1550, c6639, c1524, c2015, c1436, c6674, c7244, c1333, c2465, c5209, c7159, c6614, c2032, c1367, c1460, c3428, c7231, c1337] c7245 (by decide) p (sat_cons (step7234 p h) (sat_cons (step7242 p h) (sat_cons (step7221 p h) (sat_cons (step7233 p h) (sat_cons (step7236 p h) (sat_cons (step4698 p h) (sat_cons (step1550 p h) (sat_cons (step6639 p h) (sat_cons (step1524 p h) (sat_cons (step2015 p h) (sat_cons (step1436 p h) (sat_cons (step6674 p h) (sat_cons (step7244 p h) (sat_cons (step1333 p h) (sat_cons (step2465 p h) (sat_cons (step5209 p h) (sat_cons (step7159 p h) (sat_cons (step6614 p h) (sat_cons (step2032 p h) (sat_cons (step1367 p h) (sat_cons (step1460 p h) (sat_cons (step3428 p h) (sat_cons (step7231 p h) (sat_cons (step1337 p h) (sat_nil p)))))))))))))))))))))))))
def c7246 : List Lit := [(1749, false)]
theorem step7246 (p : Nat → Bool) (h : Constraints p) : clause p c7246 = true :=
  Snake9.LocalRup.prove_clause [c7245, c2009] c7246 (by decide) p (sat_cons (step7245 p h) (sat_cons (step2009 p h) (sat_nil p)))
def c7247 : List Lit := [(1725, false)]
theorem step7247 (p : Nat → Bool) (h : Constraints p) : clause p c7247 = true :=
  Snake9.LocalRup.prove_clause [c7245, c3424] c7247 (by decide) p (sat_cons (step7245 p h) (sat_cons (step3424 p h) (sat_nil p)))
def c7248 : List Lit := [(1707, false)]
theorem step7248 (p : Nat → Bool) (h : Constraints p) : clause p c7248 = true :=
  Snake9.LocalRup.prove_clause [c7245, c3297] c7248 (by decide) p (sat_cons (step7245 p h) (sat_cons (step3297 p h) (sat_nil p)))
def c7249 : List Lit := [(93, true)]
theorem step7249 (p : Nat → Bool) (h : Constraints p) : clause p c7249 = true :=
  Snake9.LocalRup.prove_clause [c7245, c5368] c7249 (by decide) p (sat_cons (step7245 p h) (sat_cons (step5368 p h) (sat_nil p)))
def c7250 : List Lit := [(58, false)]
theorem step7250 (p : Nat → Bool) (h : Constraints p) : clause p c7250 = true :=
  Snake9.LocalRup.prove_clause [c7245, c6207] c7250 (by decide) p (sat_cons (step7245 p h) (sat_cons (step6207 p h) (sat_nil p)))
def c7251 : List Lit := [(1744, false)]
theorem step7251 (p : Nat → Bool) (h : Constraints p) : clause p c7251 = true :=
  Snake9.LocalRup.prove_clause [c7246, c3444] c7251 (by decide) p (sat_cons (step7246 p h) (sat_cons (step3444 p h) (sat_nil p)))
def c7252 : List Lit := [(64, true)]
theorem step7252 (p : Nat → Bool) (h : Constraints p) : clause p c7252 = true :=
  Snake9.LocalRup.prove_clause [c7248, c1280] c7252 (by decide) p (sat_cons (step7248 p h) (sat_cons (step1280 p h) (sat_nil p)))
def c7253 : List Lit := [(63, true)]
theorem step7253 (p : Nat → Bool) (h : Constraints p) : clause p c7253 = true :=
  Snake9.LocalRup.prove_clause [c7248, c1281] c7253 (by decide) p (sat_cons (step7248 p h) (sat_cons (step1281 p h) (sat_nil p)))
def c7254 : List Lit := [(119, true)]
theorem step7254 (p : Nat → Bool) (h : Constraints p) : clause p c7254 = true :=
  Snake9.LocalRup.prove_clause [c7249, c6688] c7254 (by decide) p (sat_cons (step7249 p h) (sat_cons (step6688 p h) (sat_nil p)))
def c7255 : List Lit := [(1739, false)]
theorem step7255 (p : Nat → Bool) (h : Constraints p) : clause p c7255 = true :=
  Snake9.LocalRup.prove_clause [c7251, c7245, c7250, c7246, c7234, c7221, c7253, c7252, c7249, c7233, c1339, c1340, c3428, c1335, c2929, c7231, c1361, c1460, c1308, c2003, c2130, c2659, c2713, c1286, c2202, c1283, c1284, c3292, c6855, c6859, c5692, c2015, c5854, c5046, c2032, c4954, c506] c7255 (by decide) p (sat_cons (step7251 p h) (sat_cons (step7245 p h) (sat_cons (step7250 p h) (sat_cons (step7246 p h) (sat_cons (step7234 p h) (sat_cons (step7221 p h) (sat_cons (step7253 p h) (sat_cons (step7252 p h) (sat_cons (step7249 p h) (sat_cons (step7233 p h) (sat_cons (step1339 p h) (sat_cons (step1340 p h) (sat_cons (step3428 p h) (sat_cons (step1335 p h) (sat_cons (step2929 p h) (sat_cons (step7231 p h) (sat_cons (step1361 p h) (sat_cons (step1460 p h) (sat_cons (step1308 p h) (sat_cons (step2003 p h) (sat_cons (step2130 p h) (sat_cons (step2659 p h) (sat_cons (step2713 p h) (sat_cons (step1286 p h) (sat_cons (step2202 p h) (sat_cons (step1283 p h) (sat_cons (step1284 p h) (sat_cons (step3292 p h) (sat_cons (step6855 p h) (sat_cons (step6859 p h) (sat_cons (step5692 p h) (sat_cons (step2015 p h) (sat_cons (step5854 p h) (sat_cons (step5046 p h) (sat_cons (step2032 p h) (sat_cons (step4954 p h) (sat_cons (step506 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c7256 : List Lit := [(88, true)]
theorem step7256 (p : Nat → Bool) (h : Constraints p) : clause p c7256 = true :=
  Snake9.LocalRup.prove_clause [c7255, c1333] c7256 (by decide) p (sat_cons (step7255 p h) (sat_cons (step1333 p h) (sat_nil p)))
def c7257 : List Lit := [(1832, true), (1807, false)]
theorem step7257 (p : Nat → Bool) (h : Constraints p) : clause p c7257 = true :=
  Snake9.LocalRup.prove_clause [c7242, c7221, c7256, c7233, c6639, c1524, c1436, c2032, c6674, c7159] c7257 (by decide) p (sat_cons (step7242 p h) (sat_cons (step7221 p h) (sat_cons (step7256 p h) (sat_cons (step7233 p h) (sat_cons (step6639 p h) (sat_cons (step1524 p h) (sat_cons (step1436 p h) (sat_cons (step2032 p h) (sat_cons (step6674 p h) (sat_cons (step7159 p h) (sat_nil p)))))))))))
def c7258 : List Lit := [(1807, false)]
theorem step7258 (p : Nat → Bool) (h : Constraints p) : clause p c7258 = true :=
  Snake9.LocalRup.prove_clause [c7245, c7236, c7243, c7254, c7233, c7256, c7247, c1463, c1487, c7257, c2314, c2015, c6290, c6285, c6564, c510, c520, c6614] c7258 (by decide) p (sat_cons (step7245 p h) (sat_cons (step7236 p h) (sat_cons (step7243 p h) (sat_cons (step7254 p h) (sat_cons (step7233 p h) (sat_cons (step7256 p h) (sat_cons (step7247 p h) (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step7257 p h) (sat_cons (step2314 p h) (sat_cons (step2015 p h) (sat_cons (step6290 p h) (sat_cons (step6285 p h) (sat_cons (step6564 p h) (sat_cons (step510 p h) (sat_cons (step520 p h) (sat_cons (step6614 p h) (sat_nil p)))))))))))))))))))
def c7259 : List Lit := [(1805, false)]
theorem step7259 (p : Nat → Bool) (h : Constraints p) : clause p c7259 = true :=
  Snake9.LocalRup.prove_clause [c7258, c1458] c7259 (by decide) p (sat_cons (step7258 p h) (sat_cons (step1458 p h) (sat_nil p)))
def c7260 : List Lit := [(124, true)]
theorem step7260 (p : Nat → Bool) (h : Constraints p) : clause p c7260 = true :=
  Snake9.LocalRup.prove_clause [c7258, c1460] c7260 (by decide) p (sat_cons (step7258 p h) (sat_cons (step1460 p h) (sat_nil p)))
def c7261 : List Lit := [(126, true)]
theorem step7261 (p : Nat → Bool) (h : Constraints p) : clause p c7261 = true :=
  Snake9.LocalRup.prove_clause [c7259, c1455] c7261 (by decide) p (sat_cons (step7259 p h) (sat_cons (step1455 p h) (sat_nil p)))
def c7262 : List Lit := [(1741, true)]
theorem step7262 (p : Nat → Bool) (h : Constraints p) : clause p c7262 = true :=
  Snake9.LocalRup.prove_clause [c7260, c7231] c7262 (by decide) p (sat_cons (step7260 p h) (sat_cons (step7231 p h) (sat_nil p)))
def c7263 : List Lit := [(113, false)]
theorem step7263 (p : Nat → Bool) (h : Constraints p) : clause p c7263 = true :=
  Snake9.LocalRup.prove_clause [c7260, c7249, c6653] c7263 (by decide) p (sat_cons (step7260 p h) (sat_cons (step7249 p h) (sat_cons (step6653 p h) (sat_nil p))))
def c7264 : List Lit := [(1743, true)]
theorem step7264 (p : Nat → Bool) (h : Constraints p) : clause p c7264 = true :=
  Snake9.LocalRup.prove_clause [c7262, c1337] c7264 (by decide) p (sat_cons (step7262 p h) (sat_cons (step1337 p h) (sat_nil p)))
def c7265 : List Lit := [(121, true)]
theorem step7265 (p : Nat → Bool) (h : Constraints p) : clause p c7265 = true :=
  Snake9.LocalRup.prove_clause [c7263, c7261, c7260, c2148] c7265 (by decide) p (sat_cons (step7263 p h) (sat_cons (step7261 p h) (sat_cons (step7260 p h) (sat_cons (step2148 p h) (sat_nil p)))))
def c7266 : List Lit := [(1748, true)]
theorem step7266 (p : Nat → Bool) (h : Constraints p) : clause p c7266 = true :=
  Snake9.LocalRup.prove_clause [c7264, c3428] c7266 (by decide) p (sat_cons (step7264 p h) (sat_cons (step3428 p h) (sat_nil p)))
def c7267 : List Lit := [(122, false)]
theorem step7267 (p : Nat → Bool) (h : Constraints p) : clause p c7267 = true :=
  Snake9.LocalRup.prove_clause [c7265, c7258, c3531] c7267 (by decide) p (sat_cons (step7265 p h) (sat_cons (step7258 p h) (sat_cons (step3531 p h) (sat_nil p))))
def c7268 : List Lit := [(1724, false)]
theorem step7268 (p : Nat → Bool) (h : Constraints p) : clause p c7268 = true :=
  Snake9.LocalRup.prove_clause [c7266, c7245, c1361] c7268 (by decide) p (sat_cons (step7266 p h) (sat_cons (step7245 p h) (sat_cons (step1361 p h) (sat_nil p))))
def c7269 : List Lit := [(1803, true)]
theorem step7269 (p : Nat → Bool) (h : Constraints p) : clause p c7269 = true :=
  Snake9.LocalRup.prove_clause [c7267, c1452] c7269 (by decide) p (sat_cons (step7267 p h) (sat_cons (step1452 p h) (sat_nil p)))
def c7270 : List Lit := [(1711, false)]
theorem step7270 (p : Nat → Bool) (h : Constraints p) : clause p c7270 = true :=
  Snake9.LocalRup.prove_clause [c7268, c2003] c7270 (by decide) p (sat_cons (step7268 p h) (sat_cons (step2003 p h) (sat_nil p)))
def c7271 : List Lit := [(73, true)]
theorem step7271 (p : Nat → Bool) (h : Constraints p) : clause p c7271 = true :=
  Snake9.LocalRup.prove_clause [c7268, c2130] c7271 (by decide) p (sat_cons (step7268 p h) (sat_cons (step2130 p h) (sat_nil p)))
def c7272 : List Lit := [(89, true)]
theorem step7272 (p : Nat → Bool) (h : Constraints p) : clause p c7272 = true :=
  Snake9.LocalRup.prove_clause [c7268, c7256, c2132] c7272 (by decide) p (sat_cons (step7268 p h) (sat_cons (step7256 p h) (sat_cons (step2132 p h) (sat_nil p))))
def c7273 : List Lit := [(1810, true)]
theorem step7273 (p : Nat → Bool) (h : Constraints p) : clause p c7273 = true :=
  Snake9.LocalRup.prove_clause [c7269, c1466] c7273 (by decide) p (sat_cons (step7269 p h) (sat_cons (step1466 p h) (sat_nil p)))
def c7274 : List Lit := [(1709, false)]
theorem step7274 (p : Nat → Bool) (h : Constraints p) : clause p c7274 = true :=
  Snake9.LocalRup.prove_clause [c7270, c1286] c7274 (by decide) p (sat_cons (step7270 p h) (sat_cons (step1286 p h) (sat_nil p)))
def c7275 : List Lit := [(115, false)]
theorem step7275 (p : Nat → Bool) (h : Constraints p) : clause p c7275 = true :=
  Snake9.LocalRup.prove_clause [c7271, c7256, c7233, c520] c7275 (by decide) p (sat_cons (step7271 p h) (sat_cons (step7256 p h) (sat_cons (step7233 p h) (sat_cons (step520 p h) (sat_nil p)))))
def c7276 : List Lit := [(1801, false)]
theorem step7276 (p : Nat → Bool) (h : Constraints p) : clause p c7276 = true :=
  Snake9.LocalRup.prove_clause [c7273, c7243, c1487] c7276 (by decide) p (sat_cons (step7273 p h) (sat_cons (step7243 p h) (sat_cons (step1487 p h) (sat_nil p))))
end B112E036
