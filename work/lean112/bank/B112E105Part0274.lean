import B112E105Part0273
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c19465 : List Lit := [(1674, false), (1700, true), (1672, false), (95, false), (67, true)]
theorem step19465 (p : Nat → Bool) (h : Constraints p) : clause p c19465 = true :=
  Snake9.LocalRup.prove_clause [c18799, c19346, c18797, c19075, c18796, c19344, c19433, c18798, c19464, c1615, c1598, c16722, c16512, c1564, c1567, c1522, c1524, c1593, c1594, c1520, c1622, c630, c609, c1545, c19404, c1532, c5597, c1830, c1529, c2262, c19084] c19465 (by decide) p (sat_cons (step18799 p h) (sat_cons (step19346 p h) (sat_cons (step18797 p h) (sat_cons (step19075 p h) (sat_cons (step18796 p h) (sat_cons (step19344 p h) (sat_cons (step19433 p h) (sat_cons (step18798 p h) (sat_cons (step19464 p h) (sat_cons (step1615 p h) (sat_cons (step1598 p h) (sat_cons (step16722 p h) (sat_cons (step16512 p h) (sat_cons (step1564 p h) (sat_cons (step1567 p h) (sat_cons (step1522 p h) (sat_cons (step1524 p h) (sat_cons (step1593 p h) (sat_cons (step1594 p h) (sat_cons (step1520 p h) (sat_cons (step1622 p h) (sat_cons (step630 p h) (sat_cons (step609 p h) (sat_cons (step1545 p h) (sat_cons (step19404 p h) (sat_cons (step1532 p h) (sat_cons (step5597 p h) (sat_cons (step1830 p h) (sat_cons (step1529 p h) (sat_cons (step2262 p h) (sat_cons (step19084 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c19466 : List Lit := [(67, true), (1787, true)]
theorem step19466 (p : Nat → Bool) (h : Constraints p) : clause p c19466 = true :=
  Snake9.LocalRup.prove_clause [c19440, c19075, c19439, c18796, c19344, c19433, c19441, c19461, c1556, c19463, c1628, c1552, c19465, c1558, c623, c613, c19434, c1520, c12511, c1522, c1525, c1532, c1548, c10313, c1529, c1621, c19447, c19084, c2262] c19466 (by decide) p (sat_cons (step19440 p h) (sat_cons (step19075 p h) (sat_cons (step19439 p h) (sat_cons (step18796 p h) (sat_cons (step19344 p h) (sat_cons (step19433 p h) (sat_cons (step19441 p h) (sat_cons (step19461 p h) (sat_cons (step1556 p h) (sat_cons (step19463 p h) (sat_cons (step1628 p h) (sat_cons (step1552 p h) (sat_cons (step19465 p h) (sat_cons (step1558 p h) (sat_cons (step623 p h) (sat_cons (step613 p h) (sat_cons (step19434 p h) (sat_cons (step1520 p h) (sat_cons (step12511 p h) (sat_cons (step1522 p h) (sat_cons (step1525 p h) (sat_cons (step1532 p h) (sat_cons (step1548 p h) (sat_cons (step10313 p h) (sat_cons (step1529 p h) (sat_cons (step1621 p h) (sat_cons (step19447 p h) (sat_cons (step19084 p h) (sat_cons (step2262 p h) (sat_nil p))))))))))))))))))))))))))))))
def c19467 : List Lit := [(85, false), (67, false)]
theorem step19467 (p : Nat → Bool) (h : Constraints p) : clause p c19467 = true :=
  Snake9.LocalRup.prove_clause [c19344, c19433, c632, c623, c2121] c19467 (by decide) p (sat_cons (step19344 p h) (sat_cons (step19433 p h) (sat_cons (step632 p h) (sat_cons (step623 p h) (sat_cons (step2121 p h) (sat_nil p))))))
def c19468 : List Lit := [(1700, true), (84, true), (48, true), (116, true), (1653, false), (85, true)]
theorem step19468 (p : Nat → Bool) (h : Constraints p) : clause p c19468 = true :=
  Snake9.LocalRup.prove_clause [c18799, c19076, c19440, c19075, c19439, c19072, c19271, c19345, c19346, c19344, c19433, c1522, c1548, c1621, c1558, c1615, c1633, c1628, c1622, c1598, c1550, c1552, c1549, c1593, c1589, c1567, c1525, c1532, c14853, c1564, c1576, c1530, c18988, c1555, c1556, c19399, c2262, c1830, c1755, c1674, c1649, c1647, c13931, c1642, c1641, c1645, c1572, c522, c1574, c14230, c731] c19468 (by decide) p (sat_cons (step18799 p h) (sat_cons (step19076 p h) (sat_cons (step19440 p h) (sat_cons (step19075 p h) (sat_cons (step19439 p h) (sat_cons (step19072 p h) (sat_cons (step19271 p h) (sat_cons (step19345 p h) (sat_cons (step19346 p h) (sat_cons (step19344 p h) (sat_cons (step19433 p h) (sat_cons (step1522 p h) (sat_cons (step1548 p h) (sat_cons (step1621 p h) (sat_cons (step1558 p h) (sat_cons (step1615 p h) (sat_cons (step1633 p h) (sat_cons (step1628 p h) (sat_cons (step1622 p h) (sat_cons (step1598 p h) (sat_cons (step1550 p h) (sat_cons (step1552 p h) (sat_cons (step1549 p h) (sat_cons (step1593 p h) (sat_cons (step1589 p h) (sat_cons (step1567 p h) (sat_cons (step1525 p h) (sat_cons (step1532 p h) (sat_cons (step14853 p h) (sat_cons (step1564 p h) (sat_cons (step1576 p h) (sat_cons (step1530 p h) (sat_cons (step18988 p h) (sat_cons (step1555 p h) (sat_cons (step1556 p h) (sat_cons (step19399 p h) (sat_cons (step2262 p h) (sat_cons (step1830 p h) (sat_cons (step1755 p h) (sat_cons (step1674 p h) (sat_cons (step1649 p h) (sat_cons (step1647 p h) (sat_cons (step13931 p h) (sat_cons (step1642 p h) (sat_cons (step1641 p h) (sat_cons (step1645 p h) (sat_cons (step1572 p h) (sat_cons (step522 p h) (sat_cons (step1574 p h) (sat_cons (step14230 p h) (sat_cons (step731 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))
def c19469 : List Lit := [(68, true), (1787, true)]
theorem step19469 (p : Nat → Bool) (h : Constraints p) : clause p c19469 = true :=
  Snake9.LocalRup.prove_clause [c18796, c19433, c19344, c19345, c19271, c19072, c19466, c19467, c1558, c1520, c2121, c2122, c1522, c639, c616, c581, c1548, c18940, c19468, c19446, c1836, c2262, c11991, c2242, c1255, c1257, c1252, c1185, c1216, c1180, c1214, c1202, c1201, c19364, c1674, c1754, c1755, c1842, c18988, c1623, c12353, c14613, c1555, c1594, c1564] c19469 (by decide) p (sat_cons (step18796 p h) (sat_cons (step19433 p h) (sat_cons (step19344 p h) (sat_cons (step19345 p h) (sat_cons (step19271 p h) (sat_cons (step19072 p h) (sat_cons (step19466 p h) (sat_cons (step19467 p h) (sat_cons (step1558 p h) (sat_cons (step1520 p h) (sat_cons (step2121 p h) (sat_cons (step2122 p h) (sat_cons (step1522 p h) (sat_cons (step639 p h) (sat_cons (step616 p h) (sat_cons (step581 p h) (sat_cons (step1548 p h) (sat_cons (step18940 p h) (sat_cons (step19468 p h) (sat_cons (step19446 p h) (sat_cons (step1836 p h) (sat_cons (step2262 p h) (sat_cons (step11991 p h) (sat_cons (step2242 p h) (sat_cons (step1255 p h) (sat_cons (step1257 p h) (sat_cons (step1252 p h) (sat_cons (step1185 p h) (sat_cons (step1216 p h) (sat_cons (step1180 p h) (sat_cons (step1214 p h) (sat_cons (step1202 p h) (sat_cons (step1201 p h) (sat_cons (step19364 p h) (sat_cons (step1674 p h) (sat_cons (step1754 p h) (sat_cons (step1755 p h) (sat_cons (step1842 p h) (sat_cons (step18988 p h) (sat_cons (step1623 p h) (sat_cons (step12353 p h) (sat_cons (step14613 p h) (sat_cons (step1555 p h) (sat_cons (step1594 p h) (sat_cons (step1564 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c19470 : List Lit := [(1655, false), (1787, true)]
theorem step19470 (p : Nat → Bool) (h : Constraints p) : clause p c19470 = true :=
  Snake9.LocalRup.prove_clause [c18798, c18799, c19440, c19072, c19075, c19439, c19271, c19346, c19344, c19433, c19466, c19467, c1558, c19469, c19455, c1615, c1598, c1567, c1628, c1546, c1893, c2140, c630, c3575, c1548, c1549, c1621, c1622, c1532, c14853, c1831, c1593, c1589, c1530, c18988, c1564, c1576, c1763, c1555, c1556, c1675, c1649, c1647, c13931, c1642, c1641, c1645, c1572, c522, c1574, c14230, c731] c19470 (by decide) p (sat_cons (step18798 p h) (sat_cons (step18799 p h) (sat_cons (step19440 p h) (sat_cons (step19072 p h) (sat_cons (step19075 p h) (sat_cons (step19439 p h) (sat_cons (step19271 p h) (sat_cons (step19346 p h) (sat_cons (step19344 p h) (sat_cons (step19433 p h) (sat_cons (step19466 p h) (sat_cons (step19467 p h) (sat_cons (step1558 p h) (sat_cons (step19469 p h) (sat_cons (step19455 p h) (sat_cons (step1615 p h) (sat_cons (step1598 p h) (sat_cons (step1567 p h) (sat_cons (step1628 p h) (sat_cons (step1546 p h) (sat_cons (step1893 p h) (sat_cons (step2140 p h) (sat_cons (step630 p h) (sat_cons (step3575 p h) (sat_cons (step1548 p h) (sat_cons (step1549 p h) (sat_cons (step1621 p h) (sat_cons (step1622 p h) (sat_cons (step1532 p h) (sat_cons (step14853 p h) (sat_cons (step1831 p h) (sat_cons (step1593 p h) (sat_cons (step1589 p h) (sat_cons (step1530 p h) (sat_cons (step18988 p h) (sat_cons (step1564 p h) (sat_cons (step1576 p h) (sat_cons (step1763 p h) (sat_cons (step1555 p h) (sat_cons (step1556 p h) (sat_cons (step1675 p h) (sat_cons (step1649 p h) (sat_cons (step1647 p h) (sat_cons (step13931 p h) (sat_cons (step1642 p h) (sat_cons (step1641 p h) (sat_cons (step1645 p h) (sat_cons (step1572 p h) (sat_cons (step522 p h) (sat_cons (step1574 p h) (sat_cons (step14230 p h) (sat_cons (step731 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))
def c19471 : List Lit := [(1690, true), (1787, true)]
theorem step19471 (p : Nat → Bool) (h : Constraints p) : clause p c19471 = true :=
  Snake9.LocalRup.prove_clause [c18797, c19344, c19075, c19439, c19433, c19271, c19469, c630, c14532, c3575, c1670, c609, c19466, c19467, c1558, c19470, c1524, c19398, c1756, c1741, c1893, c18940, c16872, c2120, c1593, c1589, c1564, c1555, c12353, c18988, c1763, c1675, c1647, c13931, c1644, c16369, c16129, c1696, c1693, c1704] c19471 (by decide) p (sat_cons (step18797 p h) (sat_cons (step19344 p h) (sat_cons (step19075 p h) (sat_cons (step19439 p h) (sat_cons (step19433 p h) (sat_cons (step19271 p h) (sat_cons (step19469 p h) (sat_cons (step630 p h) (sat_cons (step14532 p h) (sat_cons (step3575 p h) (sat_cons (step1670 p h) (sat_cons (step609 p h) (sat_cons (step19466 p h) (sat_cons (step19467 p h) (sat_cons (step1558 p h) (sat_cons (step19470 p h) (sat_cons (step1524 p h) (sat_cons (step19398 p h) (sat_cons (step1756 p h) (sat_cons (step1741 p h) (sat_cons (step1893 p h) (sat_cons (step18940 p h) (sat_cons (step16872 p h) (sat_cons (step2120 p h) (sat_cons (step1593 p h) (sat_cons (step1589 p h) (sat_cons (step1564 p h) (sat_cons (step1555 p h) (sat_cons (step12353 p h) (sat_cons (step18988 p h) (sat_cons (step1763 p h) (sat_cons (step1675 p h) (sat_cons (step1647 p h) (sat_cons (step13931 p h) (sat_cons (step1644 p h) (sat_cons (step16369 p h) (sat_cons (step16129 p h) (sat_cons (step1696 p h) (sat_cons (step1693 p h) (sat_cons (step1704 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c19472 : List Lit := [(1787, true)]
theorem step19472 (p : Nat → Bool) (h : Constraints p) : clause p c19472 = true :=
  Snake9.LocalRup.prove_clause [c19344, c19433, c18799, c19075, c18797, c18798, c19072, c19271, c18429, c19466, c19467, c1558, c19469, c3575, c630, c1893, c609, c19455, c1670, c2140, c1615, c1598, c1567, c19470, c1524, c19398, c1756, c19471, c1622, c1545, c14853, c18988, c1763, c1675, c1647, c1644, c16152, c16173, c16129, c1707, c1718, c1693, c1737, c1703] c19472 (by decide) p (sat_cons (step19344 p h) (sat_cons (step19433 p h) (sat_cons (step18799 p h) (sat_cons (step19075 p h) (sat_cons (step18797 p h) (sat_cons (step18798 p h) (sat_cons (step19072 p h) (sat_cons (step19271 p h) (sat_cons (step18429 p h) (sat_cons (step19466 p h) (sat_cons (step19467 p h) (sat_cons (step1558 p h) (sat_cons (step19469 p h) (sat_cons (step3575 p h) (sat_cons (step630 p h) (sat_cons (step1893 p h) (sat_cons (step609 p h) (sat_cons (step19455 p h) (sat_cons (step1670 p h) (sat_cons (step2140 p h) (sat_cons (step1615 p h) (sat_cons (step1598 p h) (sat_cons (step1567 p h) (sat_cons (step19470 p h) (sat_cons (step1524 p h) (sat_cons (step19398 p h) (sat_cons (step1756 p h) (sat_cons (step19471 p h) (sat_cons (step1622 p h) (sat_cons (step1545 p h) (sat_cons (step14853 p h) (sat_cons (step18988 p h) (sat_cons (step1763 p h) (sat_cons (step1675 p h) (sat_cons (step1647 p h) (sat_cons (step1644 p h) (sat_cons (step16152 p h) (sat_cons (step16173 p h) (sat_cons (step16129 p h) (sat_cons (step1707 p h) (sat_cons (step1718 p h) (sat_cons (step1693 p h) (sat_cons (step1737 p h) (sat_cons (step1703 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c19473 : List Lit := [(1638, false)]
theorem step19473 (p : Nat → Bool) (h : Constraints p) : clause p c19473 = true :=
  Snake9.LocalRup.prove_clause [c19472, c2261] c19473 (by decide) p (sat_cons (step19472 p h) (sat_cons (step2261 p h) (sat_nil p)))
def c19474 : List Lit := [(1561, false)]
theorem step19474 (p : Nat → Bool) (h : Constraints p) : clause p c19474 = true :=
  Snake9.LocalRup.prove_clause [c19473, c3505] c19474 (by decide) p (sat_cons (step19473 p h) (sat_cons (step3505 p h) (sat_nil p)))
def c19475 : List Lit := [(1619, false)]
theorem step19475 (p : Nat → Bool) (h : Constraints p) : clause p c19475 = true :=
  Snake9.LocalRup.prove_clause [c19473, c4264] c19475 (by decide) p (sat_cons (step19473 p h) (sat_cons (step4264 p h) (sat_nil p)))
def c19476 : List Lit := [(365, true)]
theorem step19476 (p : Nat → Bool) (h : Constraints p) : clause p c19476 = true :=
  Snake9.LocalRup.prove_clause [c19475, c18445] c19476 (by decide) p (sat_cons (step19475 p h) (sat_cons (step18445 p h) (sat_nil p)))
def c19477 : List Lit := [(367, true)]
theorem step19477 (p : Nat → Bool) (h : Constraints p) : clause p c19477 = true :=
  Snake9.LocalRup.prove_clause [c19476, c1121] c19477 (by decide) p (sat_cons (step19476 p h) (sat_cons (step1121 p h) (sat_nil p)))
def c19478 : List Lit := [(305, false)]
theorem step19478 (p : Nat → Bool) (h : Constraints p) : clause p c19478 = true :=
  Snake9.LocalRup.prove_clause [c19476, c2218] c19478 (by decide) p (sat_cons (step19476 p h) (sat_cons (step2218 p h) (sat_nil p)))
def c19479 : List Lit := [(489, false)]
theorem step19479 (p : Nat → Bool) (h : Constraints p) : clause p c19479 = true :=
  Snake9.LocalRup.prove_clause [c19477, c2242] c19479 (by decide) p (sat_cons (step19477 p h) (sat_cons (step2242 p h) (sat_nil p)))
def c19480 : List Lit := [(275, false)]
theorem step19480 (p : Nat → Bool) (h : Constraints p) : clause p c19480 = true :=
  Snake9.LocalRup.prove_clause [c19478, c1058] c19480 (by decide) p (sat_cons (step19478 p h) (sat_cons (step1058 p h) (sat_nil p)))
def c19481 : List Lit := [(487, false)]
theorem step19481 (p : Nat → Bool) (h : Constraints p) : clause p c19481 = true :=
  Snake9.LocalRup.prove_clause [c19479, c1255] c19481 (by decide) p (sat_cons (step19479 p h) (sat_cons (step1255 p h) (sat_nil p)))
def c19482 : List Lit := [(427, false)]
theorem step19482 (p : Nat → Bool) (h : Constraints p) : clause p c19482 = true :=
  Snake9.LocalRup.prove_clause [c19479, c1257] c19482 (by decide) p (sat_cons (step19479 p h) (sat_cons (step1257 p h) (sat_nil p)))
def c19483 : List Lit := [(455, false)]
theorem step19483 (p : Nat → Bool) (h : Constraints p) : clause p c19483 = true :=
  Snake9.LocalRup.prove_clause [c19481, c1252] c19483 (by decide) p (sat_cons (step19481 p h) (sat_cons (step1252 p h) (sat_nil p)))
def c19484 : List Lit := [(425, false)]
theorem step19484 (p : Nat → Bool) (h : Constraints p) : clause p c19484 = true :=
  Snake9.LocalRup.prove_clause [c19482, c1185] c19484 (by decide) p (sat_cons (step19482 p h) (sat_cons (step1185 p h) (sat_nil p)))
def c19485 : List Lit := [(395, false)]
theorem step19485 (p : Nat → Bool) (h : Constraints p) : clause p c19485 = true :=
  Snake9.LocalRup.prove_clause [c19482, c1187] c19485 (by decide) p (sat_cons (step19482 p h) (sat_cons (step1187 p h) (sat_nil p)))
def c19486 : List Lit := [(453, false)]
theorem step19486 (p : Nat → Bool) (h : Constraints p) : clause p c19486 = true :=
  Snake9.LocalRup.prove_clause [c19483, c1216] c19486 (by decide) p (sat_cons (step19483 p h) (sat_cons (step1216 p h) (sat_nil p)))
def c19487 : List Lit := [(423, false)]
theorem step19487 (p : Nat → Bool) (h : Constraints p) : clause p c19487 = true :=
  Snake9.LocalRup.prove_clause [c19484, c1180] c19487 (by decide) p (sat_cons (step19484 p h) (sat_cons (step1180 p h) (sat_nil p)))
def c19488 : List Lit := [(409, false)]
theorem step19488 (p : Nat → Bool) (h : Constraints p) : clause p c19488 = true :=
  Snake9.LocalRup.prove_clause [c19484, c1182] c19488 (by decide) p (sat_cons (step19484 p h) (sat_cons (step1182 p h) (sat_nil p)))
def c19489 : List Lit := [(393, false)]
theorem step19489 (p : Nat → Bool) (h : Constraints p) : clause p c19489 = true :=
  Snake9.LocalRup.prove_clause [c19485, c1150] c19489 (by decide) p (sat_cons (step19485 p h) (sat_cons (step1150 p h) (sat_nil p)))
def c19490 : List Lit := [(445, false)]
theorem step19490 (p : Nat → Bool) (h : Constraints p) : clause p c19490 = true :=
  Snake9.LocalRup.prove_clause [c19486, c1214] c19490 (by decide) p (sat_cons (step19486 p h) (sat_cons (step1214 p h) (sat_nil p)))
def c19491 : List Lit := [(421, false)]
theorem step19491 (p : Nat → Bool) (h : Constraints p) : clause p c19491 = true :=
  Snake9.LocalRup.prove_clause [c19487, c1176] c19491 (by decide) p (sat_cons (step19487 p h) (sat_cons (step1176 p h) (sat_nil p)))
def c19492 : List Lit := [(415, false)]
theorem step19492 (p : Nat → Bool) (h : Constraints p) : clause p c19492 = true :=
  Snake9.LocalRup.prove_clause [c19487, c1178] c19492 (by decide) p (sat_cons (step19487 p h) (sat_cons (step1178 p h) (sat_nil p)))
def c19493 : List Lit := [(401, false)]
theorem step19493 (p : Nat → Bool) (h : Constraints p) : clause p c19493 = true :=
  Snake9.LocalRup.prove_clause [c19488, c1166] c19493 (by decide) p (sat_cons (step19488 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c19494 : List Lit := [(391, false)]
theorem step19494 (p : Nat → Bool) (h : Constraints p) : clause p c19494 = true :=
  Snake9.LocalRup.prove_clause [c19489, c1146] c19494 (by decide) p (sat_cons (step19489 p h) (sat_cons (step1146 p h) (sat_nil p)))
def c19495 : List Lit := [(385, false)]
theorem step19495 (p : Nat → Bool) (h : Constraints p) : clause p c19495 = true :=
  Snake9.LocalRup.prove_clause [c19489, c1148] c19495 (by decide) p (sat_cons (step19489 p h) (sat_cons (step1148 p h) (sat_nil p)))
def c19496 : List Lit := [(441, false)]
theorem step19496 (p : Nat → Bool) (h : Constraints p) : clause p c19496 = true :=
  Snake9.LocalRup.prove_clause [c19490, c1202] c19496 (by decide) p (sat_cons (step19490 p h) (sat_cons (step1202 p h) (sat_nil p)))
def c19497 : List Lit := [(419, false)]
theorem step19497 (p : Nat → Bool) (h : Constraints p) : clause p c19497 = true :=
  Snake9.LocalRup.prove_clause [c19491, c1173] c19497 (by decide) p (sat_cons (step19491 p h) (sat_cons (step1173 p h) (sat_nil p)))
def c19498 : List Lit := [(413, false)]
theorem step19498 (p : Nat → Bool) (h : Constraints p) : clause p c19498 = true :=
  Snake9.LocalRup.prove_clause [c19492, c1170] c19498 (by decide) p (sat_cons (step19492 p h) (sat_cons (step1170 p h) (sat_nil p)))
def c19499 : List Lit := [(397, false)]
theorem step19499 (p : Nat → Bool) (h : Constraints p) : clause p c19499 = true :=
  Snake9.LocalRup.prove_clause [c19493, c1158] c19499 (by decide) p (sat_cons (step19493 p h) (sat_cons (step1158 p h) (sat_nil p)))
def c19500 : List Lit := [(389, false)]
theorem step19500 (p : Nat → Bool) (h : Constraints p) : clause p c19500 = true :=
  Snake9.LocalRup.prove_clause [c19494, c1143] c19500 (by decide) p (sat_cons (step19494 p h) (sat_cons (step1143 p h) (sat_nil p)))
def c19501 : List Lit := [(387, false)]
theorem step19501 (p : Nat → Bool) (h : Constraints p) : clause p c19501 = true :=
  Snake9.LocalRup.prove_clause [c19494, c1144] c19501 (by decide) p (sat_cons (step19494 p h) (sat_cons (step1144 p h) (sat_nil p)))
def c19502 : List Lit := [(383, false)]
theorem step19502 (p : Nat → Bool) (h : Constraints p) : clause p c19502 = true :=
  Snake9.LocalRup.prove_clause [c19495, c1139] c19502 (by decide) p (sat_cons (step19495 p h) (sat_cons (step1139 p h) (sat_nil p)))
def c19503 : List Lit := [(225, false)]
theorem step19503 (p : Nat → Bool) (h : Constraints p) : clause p c19503 = true :=
  Snake9.LocalRup.prove_clause [c19496, c1201] c19503 (by decide) p (sat_cons (step19496 p h) (sat_cons (step1201 p h) (sat_nil p)))
def c19504 : List Lit := [(217, false)]
theorem step19504 (p : Nat → Bool) (h : Constraints p) : clause p c19504 = true :=
  Snake9.LocalRup.prove_clause [c19497, c1172] c19504 (by decide) p (sat_cons (step19497 p h) (sat_cons (step1172 p h) (sat_nil p)))
def c19505 : List Lit := [(213, false)]
theorem step19505 (p : Nat → Bool) (h : Constraints p) : clause p c19505 = true :=
  Snake9.LocalRup.prove_clause [c19498, c1168] c19505 (by decide) p (sat_cons (step19498 p h) (sat_cons (step1168 p h) (sat_nil p)))
def c19506 : List Lit := [(202, false)]
theorem step19506 (p : Nat → Bool) (h : Constraints p) : clause p c19506 = true :=
  Snake9.LocalRup.prove_clause [c19499, c1155] c19506 (by decide) p (sat_cons (step19499 p h) (sat_cons (step1155 p h) (sat_nil p)))
def c19507 : List Lit := [(200, false)]
theorem step19507 (p : Nat → Bool) (h : Constraints p) : clause p c19507 = true :=
  Snake9.LocalRup.prove_clause [c19500, c1142] c19507 (by decide) p (sat_cons (step19500 p h) (sat_cons (step1142 p h) (sat_nil p)))
def c19508 : List Lit := [(198, false)]
theorem step19508 (p : Nat → Bool) (h : Constraints p) : clause p c19508 = true :=
  Snake9.LocalRup.prove_clause [c19501, c1141] c19508 (by decide) p (sat_cons (step19501 p h) (sat_cons (step1141 p h) (sat_nil p)))
def c19509 : List Lit := [(196, false)]
theorem step19509 (p : Nat → Bool) (h : Constraints p) : clause p c19509 = true :=
  Snake9.LocalRup.prove_clause [c19502, c1138] c19509 (by decide) p (sat_cons (step19502 p h) (sat_cons (step1138 p h) (sat_nil p)))
def c19510 : List Lit := [(95, true)]
theorem step19510 (p : Nat → Bool) (h : Constraints p) : clause p c19510 = true :=
  Snake9.LocalRup.prove_clause [c19503, c19072, c12394] c19510 (by decide) p (sat_cons (step19503 p h) (sat_cons (step19072 p h) (sat_cons (step12394 p h) (sat_nil p))))
def c19511 : List Lit := [(1655, true)]
theorem step19511 (p : Nat → Bool) (h : Constraints p) : clause p c19511 = true :=
  Snake9.LocalRup.prove_clause [c18797, c18796, c19475, c19344, c19433, c1522, c1524, c1520, c18955, c609] c19511 (by decide) p (sat_cons (step18797 p h) (sat_cons (step18796 p h) (sat_cons (step19475 p h) (sat_cons (step19344 p h) (sat_cons (step19433 p h) (sat_cons (step1522 p h) (sat_cons (step1524 p h) (sat_cons (step1520 p h) (sat_cons (step18955 p h) (sat_cons (step609 p h) (sat_nil p)))))))))))
def c19512 : List Lit := [(1666, true)]
theorem step19512 (p : Nat → Bool) (h : Constraints p) : clause p c19512 = true :=
  Snake9.LocalRup.prove_clause [c19511, c1548] c19512 (by decide) p (sat_cons (step19511 p h) (sat_cons (step1548 p h) (sat_nil p)))
def c19513 : List Lit := [(1700, true), (1674, false)]
theorem step19513 (p : Nat → Bool) (h : Constraints p) : clause p c19513 = true :=
  Snake9.LocalRup.prove_clause [c19440, c19512, c19511, c19075, c19474, c19507, c19480, c1628, c1622, c1549, c1593, c18562, c1564, c1556] c19513 (by decide) p (sat_cons (step19440 p h) (sat_cons (step19512 p h) (sat_cons (step19511 p h) (sat_cons (step19075 p h) (sat_cons (step19474 p h) (sat_cons (step19507 p h) (sat_cons (step19480 p h) (sat_cons (step1628 p h) (sat_cons (step1622 p h) (sat_cons (step1549 p h) (sat_cons (step1593 p h) (sat_cons (step18562 p h) (sat_cons (step1564 p h) (sat_cons (step1556 p h) (sat_nil p)))))))))))))))
def c19514 : List Lit := [(1715, true), (116, true), (89, false), (1674, false)]
theorem step19514 (p : Nat → Bool) (h : Constraints p) : clause p c19514 = true :=
  Snake9.LocalRup.prove_clause [c19511, c19503, c19433, c19344, c19479, c19072, c19513, c1649, c19364, c1641, c613, c616, c14719, c2140] c19514 (by decide) p (sat_cons (step19511 p h) (sat_cons (step19503 p h) (sat_cons (step19433 p h) (sat_cons (step19344 p h) (sat_cons (step19479 p h) (sat_cons (step19072 p h) (sat_cons (step19513 p h) (sat_cons (step1649 p h) (sat_cons (step19364 p h) (sat_cons (step1641 p h) (sat_cons (step613 p h) (sat_cons (step616 p h) (sat_cons (step14719 p h) (sat_cons (step2140 p h) (sat_nil p)))))))))))))))
def c19515 : List Lit := [(84, false), (85, true), (1669, true), (1672, true), (1653, false)]
theorem step19515 (p : Nat → Bool) (h : Constraints p) : clause p c19515 = true :=
  Snake9.LocalRup.prove_clause [c19433, c19344, c19475, c19509, c19506, c19346, c19510, c1556, c1555, c2140, c616, c581, c18955, c3923, c1525, c3118, c1554] c19515 (by decide) p (sat_cons (step19433 p h) (sat_cons (step19344 p h) (sat_cons (step19475 p h) (sat_cons (step19509 p h) (sat_cons (step19506 p h) (sat_cons (step19346 p h) (sat_cons (step19510 p h) (sat_cons (step1556 p h) (sat_cons (step1555 p h) (sat_cons (step2140 p h) (sat_cons (step616 p h) (sat_cons (step581 p h) (sat_cons (step18955 p h) (sat_cons (step3923 p h) (sat_cons (step1525 p h) (sat_cons (step3118 p h) (sat_cons (step1554 p h) (sat_nil p))))))))))))))))))
def c19516 : List Lit := [(84, true), (89, false)]
theorem step19516 (p : Nat → Bool) (h : Constraints p) : clause p c19516 = true :=
  Snake9.LocalRup.prove_clause [c19072, c19505, c19479, c14719, c14617, c1641, c1644, c1650] c19516 (by decide) p (sat_cons (step19072 p h) (sat_cons (step19505 p h) (sat_cons (step19479 p h) (sat_cons (step14719 p h) (sat_cons (step14617 p h) (sat_cons (step1641 p h) (sat_cons (step1644 p h) (sat_cons (step1650 p h) (sat_nil p)))))))))
def c19517 : List Lit := [(116, true), (89, false), (1672, true), (1674, false)]
theorem step19517 (p : Nat → Bool) (h : Constraints p) : clause p c19517 = true :=
  Snake9.LocalRup.prove_clause [c18796, c19271, c19345, c19440, c19433, c19344, c19516, c19513, c19455, c1520, c18940, c19514, c1674, c1754, c4256, c1639, c19515, c3859, c613, c19349] c19517 (by decide) p (sat_cons (step18796 p h) (sat_cons (step19271 p h) (sat_cons (step19345 p h) (sat_cons (step19440 p h) (sat_cons (step19433 p h) (sat_cons (step19344 p h) (sat_cons (step19516 p h) (sat_cons (step19513 p h) (sat_cons (step19455 p h) (sat_cons (step1520 p h) (sat_cons (step18940 p h) (sat_cons (step19514 p h) (sat_cons (step1674 p h) (sat_cons (step1754 p h) (sat_cons (step4256 p h) (sat_cons (step1639 p h) (sat_cons (step19515 p h) (sat_cons (step3859 p h) (sat_cons (step613 p h) (sat_cons (step19349 p h) (sat_nil p)))))))))))))))))))))
def c19518 : List Lit := [(89, false), (1672, true), (1674, false)]
theorem step19518 (p : Nat → Bool) (h : Constraints p) : clause p c19518 = true :=
  Snake9.LocalRup.prove_clause [c19433, c19344, c19516, c19517, c636, c639, c2140] c19518 (by decide) p (sat_cons (step19433 p h) (sat_cons (step19344 p h) (sat_cons (step19516 p h) (sat_cons (step19517 p h) (sat_cons (step636 p h) (sat_cons (step639 p h) (sat_cons (step2140 p h) (sat_nil p))))))))
def c19519 : List Lit := [(116, false), (1766, true)]
theorem step19519 (p : Nat → Bool) (h : Constraints p) : clause p c19519 = true :=
  Snake9.LocalRup.prove_clause [c19433, c19344, c19473, c10644, c620, c19379, c14639] c19519 (by decide) p (sat_cons (step19433 p h) (sat_cons (step19344 p h) (sat_cons (step19473 p h) (sat_cons (step10644 p h) (sat_cons (step620 p h) (sat_cons (step19379 p h) (sat_cons (step14639 p h) (sat_nil p))))))))
def c19520 : List Lit := [(48, true), (1690, false), (1661, false), (1653, false)]
theorem step19520 (p : Nat → Bool) (h : Constraints p) : clause p c19520 = true :=
  Snake9.LocalRup.prove_clause [c19473, c19475, c19271, c18429, c19345, c14639, c18955, c14195, c1525, c4256, c1553, c1635] c19520 (by decide) p (sat_cons (step19473 p h) (sat_cons (step19475 p h) (sat_cons (step19271 p h) (sat_cons (step18429 p h) (sat_cons (step19345 p h) (sat_cons (step14639 p h) (sat_cons (step18955 p h) (sat_cons (step14195 p h) (sat_cons (step1525 p h) (sat_cons (step4256 p h) (sat_cons (step1553 p h) (sat_cons (step1635 p h) (sat_nil p)))))))))))))
def c19521 : List Lit := [(1672, true), (1674, false)]
theorem step19521 (p : Nat → Bool) (h : Constraints p) : clause p c19521 = true :=
  Snake9.LocalRup.prove_clause [c18796, c19474, c19507, c19480, c19072, c19439, c19433, c19344, c18429, c19271, c19509, c19506, c19511, c19346, c19510, c19513, c19455, c1520, c1555, c1556, c837, c18562, c19518, c16916, c1589, c19520, c2610, c616, c14211, c2121, c4256, c3923, c3283] c19521 (by decide) p (sat_cons (step18796 p h) (sat_cons (step19474 p h) (sat_cons (step19507 p h) (sat_cons (step19480 p h) (sat_cons (step19072 p h) (sat_cons (step19439 p h) (sat_cons (step19433 p h) (sat_cons (step19344 p h) (sat_cons (step18429 p h) (sat_cons (step19271 p h) (sat_cons (step19509 p h) (sat_cons (step19506 p h) (sat_cons (step19511 p h) (sat_cons (step19346 p h) (sat_cons (step19510 p h) (sat_cons (step19513 p h) (sat_cons (step19455 p h) (sat_cons (step1520 p h) (sat_cons (step1555 p h) (sat_cons (step1556 p h) (sat_cons (step837 p h) (sat_cons (step18562 p h) (sat_cons (step19518 p h) (sat_cons (step16916 p h) (sat_cons (step1589 p h) (sat_cons (step19520 p h) (sat_cons (step2610 p h) (sat_cons (step616 p h) (sat_cons (step14211 p h) (sat_cons (step2121 p h) (sat_cons (step4256 p h) (sat_cons (step3923 p h) (sat_cons (step3283 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c19522 : List Lit := [(48, false), (1674, false)]
theorem step19522 (p : Nat → Bool) (h : Constraints p) : clause p c19522 = true :=
  Snake9.LocalRup.prove_clause [c19433, c19344, c18429, c19271, c19512, c19504, c19072, c19489, c19511, c19521, c1564, c19513, c19455, c2610, c613, c616, c14211, c2121, c2140, c4256, c19516, c1624, c10811, c10315] c19522 (by decide) p (sat_cons (step19433 p h) (sat_cons (step19344 p h) (sat_cons (step18429 p h) (sat_cons (step19271 p h) (sat_cons (step19512 p h) (sat_cons (step19504 p h) (sat_cons (step19072 p h) (sat_cons (step19489 p h) (sat_cons (step19511 p h) (sat_cons (step19521 p h) (sat_cons (step1564 p h) (sat_cons (step19513 p h) (sat_cons (step19455 p h) (sat_cons (step2610 p h) (sat_cons (step613 p h) (sat_cons (step616 p h) (sat_cons (step14211 p h) (sat_cons (step2121 p h) (sat_cons (step2140 p h) (sat_cons (step4256 p h) (sat_cons (step19516 p h) (sat_cons (step1624 p h) (sat_cons (step10811 p h) (sat_cons (step10315 p h) (sat_nil p)))))))))))))))))))))))))
def c19523 : List Lit := [(1674, false)]
theorem step19523 (p : Nat → Bool) (h : Constraints p) : clause p c19523 = true :=
  Snake9.LocalRup.prove_clause [c18796, c19075, c19473, c19512, c19073, c19478, c19508, c19474, c19475, c19271, c19433, c19345, c19513, c19455, c1520, c19521, c1564, c1593, c19522, c14639, c18993, c19520, c1645, c1646, c19519, c1532, c14413, c1647, c16152, c16173, c1530, c4294, c1674, c1707, c1718, c1755, c1732] c19523 (by decide) p (sat_cons (step18796 p h) (sat_cons (step19075 p h) (sat_cons (step19473 p h) (sat_cons (step19512 p h) (sat_cons (step19073 p h) (sat_cons (step19478 p h) (sat_cons (step19508 p h) (sat_cons (step19474 p h) (sat_cons (step19475 p h) (sat_cons (step19271 p h) (sat_cons (step19433 p h) (sat_cons (step19345 p h) (sat_cons (step19513 p h) (sat_cons (step19455 p h) (sat_cons (step1520 p h) (sat_cons (step19521 p h) (sat_cons (step1564 p h) (sat_cons (step1593 p h) (sat_cons (step19522 p h) (sat_cons (step14639 p h) (sat_cons (step18993 p h) (sat_cons (step19520 p h) (sat_cons (step1645 p h) (sat_cons (step1646 p h) (sat_cons (step19519 p h) (sat_cons (step1532 p h) (sat_cons (step14413 p h) (sat_cons (step1647 p h) (sat_cons (step16152 p h) (sat_cons (step16173 p h) (sat_cons (step1530 p h) (sat_cons (step4294 p h) (sat_cons (step1674 p h) (sat_cons (step1707 p h) (sat_cons (step1718 p h) (sat_cons (step1755 p h) (sat_cons (step1732 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c19524 : List Lit := [(85, true)]
theorem step19524 (p : Nat → Bool) (h : Constraints p) : clause p c19524 = true :=
  Snake9.LocalRup.prove_clause [c19523, c1558] c19524 (by decide) p (sat_cons (step19523 p h) (sat_cons (step1558 p h) (sat_nil p)))
def c19525 : List Lit := [(1724, true)]
theorem step19525 (p : Nat → Bool) (h : Constraints p) : clause p c19525 = true :=
  Snake9.LocalRup.prove_clause [c19524, c19344, c3859] c19525 (by decide) p (sat_cons (step19524 p h) (sat_cons (step19344 p h) (sat_cons (step3859 p h) (sat_nil p))))
def c19526 : List Lit := [(116, false)]
theorem step19526 (p : Nat → Bool) (h : Constraints p) : clause p c19526 = true :=
  Snake9.LocalRup.prove_clause [c19524, c19344, c19433, c636] c19526 (by decide) p (sat_cons (step19524 p h) (sat_cons (step19344 p h) (sat_cons (step19433 p h) (sat_cons (step636 p h) (sat_nil p)))))
def c19527 : List Lit := [(48, false)]
theorem step19527 (p : Nat → Bool) (h : Constraints p) : clause p c19527 = true :=
  Snake9.LocalRup.prove_clause [c19524, c19344, c19433, c613] c19527 (by decide) p (sat_cons (step19524 p h) (sat_cons (step19344 p h) (sat_cons (step19433 p h) (sat_cons (step613 p h) (sat_nil p)))))
def c19528 : List Lit := [(67, false)]
theorem step19528 (p : Nat → Bool) (h : Constraints p) : clause p c19528 = true :=
  Snake9.LocalRup.prove_clause [c19524, c19467] c19528 (by decide) p (sat_cons (step19524 p h) (sat_cons (step19467 p h) (sat_nil p)))
end B112E105
