import B112E036Part0077
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6637 : List Lit := [(1777, true), (1771, false)]
theorem step6637 (p : Nat → Bool) (h : Constraints p) : clause p c6637 = true :=
  Snake9.LocalRup.prove_clause [c5659, c1396] c6637 (by decide) p (sat_cons (step5659 p h) (sat_cons (step1396 p h) (sat_nil p)))
def c6638 : List Lit := [(1792, false), (1831, true)]
theorem step6638 (p : Nat → Bool) (h : Constraints p) : clause p c6638 = true :=
  Snake9.LocalRup.prove_clause [c5662, c1523] c6638 (by decide) p (sat_cons (step5662 p h) (sat_cons (step1523 p h) (sat_nil p)))
def c6639 : List Lit := [(1793, false), (1832, true)]
theorem step6639 (p : Nat → Bool) (h : Constraints p) : clause p c6639 = true :=
  Snake9.LocalRup.prove_clause [c5662, c1529] c6639 (by decide) p (sat_cons (step5662 p h) (sat_cons (step1529 p h) (sat_nil p)))
def c6640 : List Lit := [(1791, false), (1830, true)]
theorem step6640 (p : Nat → Bool) (h : Constraints p) : clause p c6640 = true :=
  Snake9.LocalRup.prove_clause [c5662, c1518] c6640 (by decide) p (sat_cons (step5662 p h) (sat_cons (step1518 p h) (sat_nil p)))
def c6641 : List Lit := [(1789, true), (1783, false)]
theorem step6641 (p : Nat → Bool) (h : Constraints p) : clause p c6641 = true :=
  Snake9.LocalRup.prove_clause [c5661, c1424] c6641 (by decide) p (sat_cons (step5661 p h) (sat_cons (step1424 p h) (sat_nil p)))
def c6642 : List Lit := [(1790, false), (1829, true)]
theorem step6642 (p : Nat → Bool) (h : Constraints p) : clause p c6642 = true :=
  Snake9.LocalRup.prove_clause [c5662, c1512] c6642 (by decide) p (sat_cons (step5662 p h) (sat_cons (step1512 p h) (sat_nil p)))
def c6643 : List Lit := [(227, true), (99, false), (93, true), (98, true)]
theorem step6643 (p : Nat → Bool) (h : Constraints p) : clause p c6643 = true :=
  Snake9.LocalRup.prove_clause [c4849, c575] c6643 (by decide) p (sat_cons (step4849 p h) (sat_cons (step575 p h) (sat_nil p)))
def c6644 : List Lit := [(1791, true), (1785, false)]
theorem step6644 (p : Nat → Bool) (h : Constraints p) : clause p c6644 = true :=
  Snake9.LocalRup.prove_clause [c5661, c1426] c6644 (by decide) p (sat_cons (step5661 p h) (sat_cons (step1426 p h) (sat_nil p)))
def c6645 : List Lit := [(1784, false), (1790, true)]
theorem step6645 (p : Nat → Bool) (h : Constraints p) : clause p c6645 = true :=
  Snake9.LocalRup.prove_clause [c5661, c1425] c6645 (by decide) p (sat_cons (step5661 p h) (sat_cons (step1425 p h) (sat_nil p)))
def c6646 : List Lit := [(112, true), (92, false), (93, false), (1817, true), (1810, false)]
theorem step6646 (p : Nat → Bool) (h : Constraints p) : clause p c6646 = true :=
  Snake9.LocalRup.prove_clause [c5657, c2216] c6646 (by decide) p (sat_cons (step5657 p h) (sat_cons (step2216 p h) (sat_nil p)))
def c6647 : List Lit := [(248, true), (112, true), (120, false)]
theorem step6647 (p : Nat → Bool) (h : Constraints p) : clause p c6647 = true :=
  Snake9.LocalRup.prove_clause [c5657, c737] c6647 (by decide) p (sat_cons (step5657 p h) (sat_cons (step737 p h) (sat_nil p)))
def c6648 : List Lit := [(1791, true), (39, false), (58, true), (38, false), (1772, false), (106, true)]
theorem step6648 (p : Nat → Bool) (h : Constraints p) : clause p c6648 = true :=
  Snake9.LocalRup.prove_clause [c5657, c2029] c6648 (by decide) p (sat_cons (step5657 p h) (sat_cons (step2029 p h) (sat_nil p)))
def c6649 : List Lit := [(107, false), (235, true), (106, true)]
theorem step6649 (p : Nat → Bool) (h : Constraints p) : clause p c6649 = true :=
  Snake9.LocalRup.prove_clause [c5657, c654] c6649 (by decide) p (sat_cons (step5657 p h) (sat_cons (step654 p h) (sat_nil p)))
def c6650 : List Lit := [(122, true), (119, false), (1807, false), (1818, true), (95, true)]
theorem step6650 (p : Nat → Bool) (h : Constraints p) : clause p c6650 = true :=
  Snake9.LocalRup.prove_clause [c6298, c2238] c6650 (by decide) p (sat_cons (step6298 p h) (sat_cons (step2238 p h) (sat_nil p)))
def c6651 : List Lit := [(95, true), (93, false), (88, false), (1771, false), (106, true), (1791, true), (1779, false)]
theorem step6651 (p : Nat → Bool) (h : Constraints p) : clause p c6651 = true :=
  Snake9.LocalRup.prove_clause [c5657, c2272] c6651 (by decide) p (sat_cons (step5657 p h) (sat_cons (step2272 p h) (sat_nil p)))
def c6652 : List Lit := [(92, false), (93, false), (124, false)]
theorem step6652 (p : Nat → Bool) (h : Constraints p) : clause p c6652 = true :=
  Snake9.LocalRup.prove_clause [c6298, c2263] c6652 (by decide) p (sat_cons (step6298 p h) (sat_cons (step2263 p h) (sat_nil p)))
def c6653 : List Lit := [(93, false), (113, false), (124, false)]
theorem step6653 (p : Nat → Bool) (h : Constraints p) : clause p c6653 = true :=
  Snake9.LocalRup.prove_clause [c6298, c693] c6653 (by decide) p (sat_cons (step6298 p h) (sat_cons (step693 p h) (sat_nil p)))
def c6654 : List Lit := [(1772, false), (1777, true)]
theorem step6654 (p : Nat → Bool) (h : Constraints p) : clause p c6654 = true :=
  Snake9.LocalRup.prove_clause [c4850, c1398] c6654 (by decide) p (sat_cons (step4850 p h) (sat_cons (step1398 p h) (sat_nil p)))
def c6655 : List Lit := [(93, false), (94, false), (105, false)]
theorem step6655 (p : Nat → Bool) (h : Constraints p) : clause p c6655 = true :=
  Snake9.LocalRup.prove_clause [c6298, c500] c6655 (by decide) p (sat_cons (step6298 p h) (sat_cons (step500 p h) (sat_nil p)))
def c6656 : List Lit := [(72, false), (94, false), (105, false)]
theorem step6656 (p : Nat → Bool) (h : Constraints p) : clause p c6656 = true :=
  Snake9.LocalRup.prove_clause [c6298, c491] c6656 (by decide) p (sat_cons (step6298 p h) (sat_cons (step491 p h) (sat_nil p)))
def c6657 : List Lit := [(92, false), (94, false), (105, false)]
theorem step6657 (p : Nat → Bool) (h : Constraints p) : clause p c6657 = true :=
  Snake9.LocalRup.prove_clause [c6298, c497] c6657 (by decide) p (sat_cons (step6298 p h) (sat_cons (step497 p h) (sat_nil p)))
def c6658 : List Lit := [(92, false), (93, false), (94, false)]
theorem step6658 (p : Nat → Bool) (h : Constraints p) : clause p c6658 = true :=
  Snake9.LocalRup.prove_clause [c6298, c494] c6658 (by decide) p (sat_cons (step6298 p h) (sat_cons (step494 p h) (sat_nil p)))
def c6659 : List Lit := [(72, false), (94, false), (92, false)]
theorem step6659 (p : Nat → Bool) (h : Constraints p) : clause p c6659 = true :=
  Snake9.LocalRup.prove_clause [c6298, c485] c6659 (by decide) p (sat_cons (step6298 p h) (sat_cons (step485 p h) (sat_nil p)))
def c6660 : List Lit := [(118, true), (112, true), (1811, true)]
theorem step6660 (p : Nat → Bool) (h : Constraints p) : clause p c6660 = true :=
  Snake9.LocalRup.prove_clause [c5657, c2093] c6660 (by decide) p (sat_cons (step5657 p h) (sat_cons (step2093 p h) (sat_nil p)))
def c6661 : List Lit := [(118, false), (117, false), (119, false)]
theorem step6661 (p : Nat → Bool) (h : Constraints p) : clause p c6661 = true :=
  Snake9.LocalRup.prove_clause [c6298, c730] c6661 (by decide) p (sat_cons (step6298 p h) (sat_cons (step730 p h) (sat_nil p)))
def c6662 : List Lit := [(55, false), (93, false), (113, false)]
theorem step6662 (p : Nat → Bool) (h : Constraints p) : clause p c6662 = true :=
  Snake9.LocalRup.prove_clause [c6298, c691] c6662 (by decide) p (sat_cons (step6298 p h) (sat_cons (step691 p h) (sat_nil p)))
def c6663 : List Lit := [(118, true), (247, true), (119, false), (117, true)]
theorem step6663 (p : Nat → Bool) (h : Constraints p) : clause p c6663 = true :=
  Snake9.LocalRup.prove_clause [c4849, c731] c6663 (by decide) p (sat_cons (step4849 p h) (sat_cons (step731 p h) (sat_nil p)))
def c6664 : List Lit := [(1801, false), (1830, true), (1818, true)]
theorem step6664 (p : Nat → Bool) (h : Constraints p) : clause p c6664 = true :=
  Snake9.LocalRup.prove_clause [c4850, c2084] c6664 (by decide) p (sat_cons (step4850 p h) (sat_cons (step2084 p h) (sat_nil p)))
def c6665 : List Lit := [(70, true), (206, true), (78, false)]
theorem step6665 (p : Nat → Bool) (h : Constraints p) : clause p c6665 = true :=
  Snake9.LocalRup.prove_clause [c5657, c384] c6665 (by decide) p (sat_cons (step5657 p h) (sat_cons (step384 p h) (sat_nil p)))
def c6666 : List Lit := [(1851, true), (1760, false)]
theorem step6666 (p : Nat → Bool) (h : Constraints p) : clause p c6666 = true :=
  Snake9.LocalRup.prove_clause [c5658, c1562] c6666 (by decide) p (sat_cons (step5658 p h) (sat_cons (step1562 p h) (sat_nil p)))
def c6667 : List Lit := [(1761, false), (1852, true)]
theorem step6667 (p : Nat → Bool) (h : Constraints p) : clause p c6667 = true :=
  Snake9.LocalRup.prove_clause [c5658, c1568] c6667 (by decide) p (sat_cons (step5658 p h) (sat_cons (step1568 p h) (sat_nil p)))
def c6668 : List Lit := [(109, true), (96, true), (1792, true), (91, true), (1771, false), (1778, true), (1779, false), (88, false)]
theorem step6668 (p : Nat → Bool) (h : Constraints p) : clause p c6668 = true :=
  Snake9.LocalRup.prove_clause [c5659, c2159] c6668 (by decide) p (sat_cons (step5659 p h) (sat_cons (step2159 p h) (sat_nil p)))
def c6669 : List Lit := [(72, false), (93, false), (94, false)]
theorem step6669 (p : Nat → Bool) (h : Constraints p) : clause p c6669 = true :=
  Snake9.LocalRup.prove_clause [c6298, c488] c6669 (by decide) p (sat_cons (step6298 p h) (sat_cons (step488 p h) (sat_nil p)))
def c6670 : List Lit := [(93, false), (94, true), (124, false)]
theorem step6670 (p : Nat → Bool) (h : Constraints p) : clause p c6670 = true :=
  Snake9.LocalRup.prove_clause [c6298, c1767] c6670 (by decide) p (sat_cons (step6298 p h) (sat_cons (step1767 p h) (sat_nil p)))
def c6671 : List Lit := [(113, true), (94, true)]
theorem step6671 (p : Nat → Bool) (h : Constraints p) : clause p c6671 = true :=
  Snake9.LocalRup.prove_clause [c6298, c1944] c6671 (by decide) p (sat_cons (step6298 p h) (sat_cons (step1944 p h) (sat_nil p)))
def c6672 : List Lit := [(107, false), (235, true), (109, true)]
theorem step6672 (p : Nat → Bool) (h : Constraints p) : clause p c6672 = true :=
  Snake9.LocalRup.prove_clause [c5657, c653] c6672 (by decide) p (sat_cons (step5657 p h) (sat_cons (step653 p h) (sat_nil p)))
def c6673 : List Lit := [(110, false), (50, true), (109, true), (238, true)]
theorem step6673 (p : Nat → Bool) (h : Constraints p) : clause p c6673 = true :=
  Snake9.LocalRup.prove_clause [c4849, c679] c6673 (by decide) p (sat_cons (step4849 p h) (sat_cons (step679 p h) (sat_nil p)))
def c6674 : List Lit := [(1772, false), (1778, true)]
theorem step6674 (p : Nat → Bool) (h : Constraints p) : clause p c6674 = true :=
  Snake9.LocalRup.prove_clause [c5659, c1399] c6674 (by decide) p (sat_cons (step5659 p h) (sat_cons (step1399 p h) (sat_nil p)))
def c6675 : List Lit := [(119, true), (94, true)]
theorem step6675 (p : Nat → Bool) (h : Constraints p) : clause p c6675 = true :=
  Snake9.LocalRup.prove_clause [c6298, c1943] c6675 (by decide) p (sat_cons (step6298 p h) (sat_cons (step1943 p h) (sat_nil p)))
def c6676 : List Lit := [(1726, false), (1750, false)]
theorem step6676 (p : Nat → Bool) (h : Constraints p) : clause p c6676 = true :=
  Snake9.LocalRup.prove_clause [c5660, c1375] c6676 (by decide) p (sat_cons (step5660 p h) (sat_cons (step1375 p h) (sat_nil p)))
def c6677 : List Lit := [(94, false), (1742, true), (105, false)]
theorem step6677 (p : Nat → Bool) (h : Constraints p) : clause p c6677 = true :=
  Snake9.LocalRup.prove_clause [c6298, c2326] c6677 (by decide) p (sat_cons (step6298 p h) (sat_cons (step2326 p h) (sat_nil p)))
def c6678 : List Lit := [(1829, true), (1807, false), (1789, false), (73, false)]
theorem step6678 (p : Nat → Bool) (h : Constraints p) : clause p c6678 = true :=
  Snake9.LocalRup.prove_clause [c4849, c2470] c6678 (by decide) p (sat_cons (step4849 p h) (sat_cons (step2470 p h) (sat_nil p)))
def c6679 : List Lit := [(1789, true), (1779, false)]
theorem step6679 (p : Nat → Bool) (h : Constraints p) : clause p c6679 = true :=
  Snake9.LocalRup.prove_clause [c4849, c3003] c6679 (by decide) p (sat_cons (step4849 p h) (sat_cons (step3003 p h) (sat_nil p)))
def c6680 : List Lit := [(1750, false), (1851, true), (1779, false)]
theorem step6680 (p : Nat → Bool) (h : Constraints p) : clause p c6680 = true :=
  Snake9.LocalRup.prove_clause [c5658, c3213] c6680 (by decide) p (sat_cons (step5658 p h) (sat_cons (step3213 p h) (sat_nil p)))
def c6681 : List Lit := [(1790, true), (1779, false), (95, false)]
theorem step6681 (p : Nat → Bool) (h : Constraints p) : clause p c6681 = true :=
  Snake9.LocalRup.prove_clause [c5659, c3387] c6681 (by decide) p (sat_cons (step5659 p h) (sat_cons (step3387 p h) (sat_nil p)))
def c6682 : List Lit := [(96, true), (1790, true), (88, false), (1777, false), (95, true)]
theorem step6682 (p : Nat → Bool) (h : Constraints p) : clause p c6682 = true :=
  Snake9.LocalRup.prove_clause [c5659, c3254] c6682 (by decide) p (sat_cons (step5659 p h) (sat_cons (step3254 p h) (sat_nil p)))
def c6683 : List Lit := [(1777, false), (1790, true), (95, false), (88, false)]
theorem step6683 (p : Nat → Bool) (h : Constraints p) : clause p c6683 = true :=
  Snake9.LocalRup.prove_clause [c5659, c3383] c6683 (by decide) p (sat_cons (step5659 p h) (sat_cons (step3383 p h) (sat_nil p)))
def c6684 : List Lit := [(1807, true), (1817, true), (1830, true), (95, true), (106, false)]
theorem step6684 (p : Nat → Bool) (h : Constraints p) : clause p c6684 = true :=
  Snake9.LocalRup.prove_clause [c4849, c3858] c6684 (by decide) p (sat_cons (step4849 p h) (sat_cons (step3858 p h) (sat_nil p)))
def c6685 : List Lit := [(1789, true), (88, false)]
theorem step6685 (p : Nat → Bool) (h : Constraints p) : clause p c6685 = true :=
  Snake9.LocalRup.prove_clause [c4849, c4551] c6685 (by decide) p (sat_cons (step4849 p h) (sat_cons (step4551 p h) (sat_nil p)))
def c6686 : List Lit := [(1804, true), (117, false), (1807, true), (106, false), (1781, true)]
theorem step6686 (p : Nat → Bool) (h : Constraints p) : clause p c6686 = true :=
  Snake9.LocalRup.prove_clause [c6298, c3812] c6686 (by decide) p (sat_cons (step6298 p h) (sat_cons (step3812 p h) (sat_nil p)))
def c6687 : List Lit := [(113, true), (1742, true), (105, false)]
theorem step6687 (p : Nat → Bool) (h : Constraints p) : clause p c6687 = true :=
  Snake9.LocalRup.prove_clause [c6298, c3906] c6687 (by decide) p (sat_cons (step6298 p h) (sat_cons (step3906 p h) (sat_nil p)))
def c6688 : List Lit := [(119, true), (93, false)]
theorem step6688 (p : Nat → Bool) (h : Constraints p) : clause p c6688 = true :=
  Snake9.LocalRup.prove_clause [c6298, c3533] c6688 (by decide) p (sat_cons (step6298 p h) (sat_cons (step3533 p h) (sat_nil p)))
def c6689 : List Lit := [(118, false), (117, false), (115, false)]
theorem step6689 (p : Nat → Bool) (h : Constraints p) : clause p c6689 = true :=
  Snake9.LocalRup.prove_clause [c6298, c3810] c6689 (by decide) p (sat_cons (step6298 p h) (sat_cons (step3810 p h) (sat_nil p)))
def c6690 : List Lit := [(94, false), (1741, true)]
theorem step6690 (p : Nat → Bool) (h : Constraints p) : clause p c6690 = true :=
  Snake9.LocalRup.prove_clause [c6298, c4484] c6690 (by decide) p (sat_cons (step6298 p h) (sat_cons (step4484 p h) (sat_nil p)))
def c6691 : List Lit := [(115, false), (1817, true), (1727, true), (1830, false), (1807, true), (73, true), (106, false), (95, false)]
theorem step6691 (p : Nat → Bool) (h : Constraints p) : clause p c6691 = true :=
  Snake9.LocalRup.prove_clause [c4849, c4711] c6691 (by decide) p (sat_cons (step4849 p h) (sat_cons (step4711 p h) (sat_nil p)))
def c6692 : List Lit := [(1741, true), (1792, true), (1772, false), (103, true), (106, true)]
theorem step6692 (p : Nat → Bool) (h : Constraints p) : clause p c6692 = true :=
  Snake9.LocalRup.prove_clause [c4849, c3897] c6692 (by decide) p (sat_cons (step4849 p h) (sat_cons (step3897 p h) (sat_nil p)))
def c6693 : List Lit := [(117, false), (118, false), (112, false), (1798, true)]
theorem step6693 (p : Nat → Bool) (h : Constraints p) : clause p c6693 = true :=
  Snake9.LocalRup.prove_clause [c6298, c3809] c6693 (by decide) p (sat_cons (step6298 p h) (sat_cons (step3809 p h) (sat_nil p)))
def c6694 : List Lit := [(1726, false), (1779, false), (1852, true), (1817, false)]
theorem step6694 (p : Nat → Bool) (h : Constraints p) : clause p c6694 = true :=
  Snake9.LocalRup.prove_clause [c5659, c4486] c6694 (by decide) p (sat_cons (step5659 p h) (sat_cons (step4486 p h) (sat_nil p)))
def c6695 : List Lit := [(1742, false), (1817, false), (1852, true), (1807, true), (105, false), (95, true), (1789, false)]
theorem step6695 (p : Nat → Bool) (h : Constraints p) : clause p c6695 = true :=
  Snake9.LocalRup.prove_clause [c4850, c6298, c3545] c6695 (by decide) p (sat_cons (step4850 p h) (sat_cons (step6298 p h) (sat_cons (step3545 p h) (sat_nil p))))
def c6696 : List Lit := [(50, false), (64, true), (73, true), (1761, true), (1749, false)]
theorem step6696 (p : Nat → Bool) (h : Constraints p) : clause p c6696 = true :=
  Snake9.LocalRup.prove_clause [c5660, c3801] c6696 (by decide) p (sat_cons (step5660 p h) (sat_cons (step3801 p h) (sat_nil p)))
def c6697 : List Lit := [(1817, false), (1830, true), (37, false), (1725, false), (1781, false)]
theorem step6697 (p : Nat → Bool) (h : Constraints p) : clause p c6697 = true :=
  Snake9.LocalRup.prove_clause [c5661, c5659, c4709] c6697 (by decide) p (sat_cons (step5661 p h) (sat_cons (step5659 p h) (sat_cons (step4709 p h) (sat_nil p))))
def c6698 : List Lit := [(1780, false), (1744, true), (88, false), (1791, true)]
theorem step6698 (p : Nat → Bool) (h : Constraints p) : clause p c6698 = true :=
  Snake9.LocalRup.prove_clause [c5659, c4866] c6698 (by decide) p (sat_cons (step5659 p h) (sat_cons (step4866 p h) (sat_nil p)))
def c6699 : List Lit := [(1830, true), (1807, true), (1790, false)]
theorem step6699 (p : Nat → Bool) (h : Constraints p) : clause p c6699 = true :=
  Snake9.LocalRup.prove_clause [c5662, c4878] c6699 (by decide) p (sat_cons (step5662 p h) (sat_cons (step4878 p h) (sat_nil p)))
def c6700 : List Lit := [(121, true), (126, false), (112, false), (89, false), (1760, true), (125, false), (124, false), (1712, true), (1739, false)]
theorem step6700 (p : Nat → Bool) (h : Constraints p) : clause p c6700 = true :=
  Snake9.LocalRup.prove_clause [c6298, c4881] c6700 (by decide) p (sat_cons (step6298 p h) (sat_cons (step4881 p h) (sat_nil p)))
end B112E036
