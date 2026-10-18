import B112E153Part0048
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4683 : List Lit := [(1074, false), (1076, false), (1049, false), (1051, false), (1057, false), (119, false), (118, false), (1101, true)]
theorem step4683 (p : Nat → Bool) (h : Constraints p) : clause p c4683 = true :=
  Snake9.LocalRup.prove_clause [c2065, c1324, c1233, c1224, c1218, c1231, c1312, c2067, c4672, c1261, c4682, c1317, c1232, c1221, c4681, c1213, c4560] c4683 (by decide) p (sat_cons (step2065 p h) (sat_cons (step1324 p h) (sat_cons (step1233 p h) (sat_cons (step1224 p h) (sat_cons (step1218 p h) (sat_cons (step1231 p h) (sat_cons (step1312 p h) (sat_cons (step2067 p h) (sat_cons (step4672 p h) (sat_cons (step1261 p h) (sat_cons (step4682 p h) (sat_cons (step1317 p h) (sat_cons (step1232 p h) (sat_cons (step1221 p h) (sat_cons (step4681 p h) (sat_cons (step1213 p h) (sat_cons (step4560 p h) (sat_nil p))))))))))))))))))
def c4684 : List Lit := [(108, false), (113, false), (1051, false), (1057, false), (1073, false), (1101, true)]
theorem step4684 (p : Nat → Bool) (h : Constraints p) : clause p c4684 = true :=
  Snake9.LocalRup.prove_clause [c4657, c3674] c4684 (by decide) p (sat_cons (step4657 p h) (sat_cons (step3674 p h) (sat_nil p)))
def c4685 : List Lit := [(1076, false), (1049, false), (1051, false), (1057, false), (115, true), (118, false), (1101, true)]
theorem step4685 (p : Nat → Bool) (h : Constraints p) : clause p c4685 = true :=
  Snake9.LocalRup.prove_clause [c4680, c1805, c1251, c4672, c2065, c1324, c1233, c4683, c1253, c4684, c4681, c1232, c1237, c1317, c1207, c1286, c1198, c3670, c595, c1212, c1217, c1222] c4685 (by decide) p (sat_cons (step4680 p h) (sat_cons (step1805 p h) (sat_cons (step1251 p h) (sat_cons (step4672 p h) (sat_cons (step2065 p h) (sat_cons (step1324 p h) (sat_cons (step1233 p h) (sat_cons (step4683 p h) (sat_cons (step1253 p h) (sat_cons (step4684 p h) (sat_cons (step4681 p h) (sat_cons (step1232 p h) (sat_cons (step1237 p h) (sat_cons (step1317 p h) (sat_cons (step1207 p h) (sat_cons (step1286 p h) (sat_cons (step1198 p h) (sat_cons (step3670 p h) (sat_cons (step595 p h) (sat_cons (step1212 p h) (sat_cons (step1217 p h) (sat_cons (step1222 p h) (sat_nil p)))))))))))))))))))))))
def c4686 : List Lit := [(1059, true), (86, false)]
theorem step4686 (p : Nat → Bool) (h : Constraints p) : clause p c4686 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1636] c4686 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1636 p h) (sat_nil p)))
def c4687 : List Lit := [(1071, true), (86, false)]
theorem step4687 (p : Nat → Bool) (h : Constraints p) : clause p c4687 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1988] c4687 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1988 p h) (sat_nil p)))
def c4688 : List Lit := [(1067, false), (1101, true)]
theorem step4688 (p : Nat → Bool) (h : Constraints p) : clause p c4688 = true :=
  Snake9.LocalRup.prove_clause [c3634, c1330] c4688 (by decide) p (sat_cons (step3634 p h) (sat_cons (step1330 p h) (sat_nil p)))
def c4689 : List Lit := [(86, false), (1002, true), (1057, false), (1060, true)]
theorem step4689 (p : Nat → Bool) (h : Constraints p) : clause p c4689 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1872] c4689 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1872 p h) (sat_nil p)))
def c4690 : List Lit := [(86, false), (107, true), (1060, true)]
theorem step4690 (p : Nat → Bool) (h : Constraints p) : clause p c4690 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1658] c4690 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1658 p h) (sat_nil p)))
def c4691 : List Lit := [(1099, true), (1065, false)]
theorem step4691 (p : Nat → Bool) (h : Constraints p) : clause p c4691 = true :=
  Snake9.LocalRup.prove_clause [c3634, c1315] c4691 (by decide) p (sat_cons (step3634 p h) (sat_cons (step1315 p h) (sat_nil p)))
def c4692 : List Lit := [(1100, true), (1066, false)]
theorem step4692 (p : Nat → Bool) (h : Constraints p) : clause p c4692 = true :=
  Snake9.LocalRup.prove_clause [c3634, c1323] c4692 (by decide) p (sat_cons (step3634 p h) (sat_cons (step1323 p h) (sat_nil p)))
def c4693 : List Lit := [(86, false), (105, true), (1060, true)]
theorem step4693 (p : Nat → Bool) (h : Constraints p) : clause p c4693 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1666] c4693 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1666 p h) (sat_nil p)))
def c4694 : List Lit := [(97, false), (89, false), (86, false)]
theorem step4694 (p : Nat → Bool) (h : Constraints p) : clause p c4694 = true :=
  Snake9.LocalRup.prove_clause [c3961, c286] c4694 (by decide) p (sat_cons (step3961 p h) (sat_cons (step286 p h) (sat_nil p)))
def c4695 : List Lit := [(70, false), (120, false), (108, false)]
theorem step4695 (p : Nat → Bool) (h : Constraints p) : clause p c4695 = true :=
  Snake9.LocalRup.prove_clause [c3961, c470] c4695 (by decide) p (sat_cons (step3961 p h) (sat_cons (step470 p h) (sat_nil p)))
def c4696 : List Lit := [(34, false), (120, false), (108, false)]
theorem step4696 (p : Nat → Bool) (h : Constraints p) : clause p c4696 = true :=
  Snake9.LocalRup.prove_clause [c3961, c466] c4696 (by decide) p (sat_cons (step3961 p h) (sat_cons (step466 p h) (sat_nil p)))
def c4697 : List Lit := [(1098, true), (1064, false)]
theorem step4697 (p : Nat → Bool) (h : Constraints p) : clause p c4697 = true :=
  Snake9.LocalRup.prove_clause [c3634, c1309] c4697 (by decide) p (sat_cons (step3634 p h) (sat_cons (step1309 p h) (sat_nil p)))
def c4698 : List Lit := [(86, false), (103, false), (1072, true)]
theorem step4698 (p : Nat → Bool) (h : Constraints p) : clause p c4698 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1880] c4698 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1880 p h) (sat_nil p)))
def c4699 : List Lit := [(86, false), (108, false), (1072, true)]
theorem step4699 (p : Nat → Bool) (h : Constraints p) : clause p c4699 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1625] c4699 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1625 p h) (sat_nil p)))
def c4700 : List Lit := [(86, false), (71, false), (1072, true)]
theorem step4700 (p : Nat → Bool) (h : Constraints p) : clause p c4700 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1877] c4700 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1877 p h) (sat_nil p)))
def c4701 : List Lit := [(35, false), (86, false), (1072, true)]
theorem step4701 (p : Nat → Bool) (h : Constraints p) : clause p c4701 = true :=
  Snake9.LocalRup.prove_clause [c3961, c2008] c4701 (by decide) p (sat_cons (step3961 p h) (sat_cons (step2008 p h) (sat_nil p)))
def c4702 : List Lit := [(86, false), (71, false), (1060, true)]
theorem step4702 (p : Nat → Bool) (h : Constraints p) : clause p c4702 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1661] c4702 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1661 p h) (sat_nil p)))
def c4703 : List Lit := [(35, false), (86, false), (1060, true)]
theorem step4703 (p : Nat → Bool) (h : Constraints p) : clause p c4703 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1656] c4703 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1656 p h) (sat_nil p)))
def c4704 : List Lit := [(1068, false), (1102, true)]
theorem step4704 (p : Nat → Bool) (h : Constraints p) : clause p c4704 = true :=
  Snake9.LocalRup.prove_clause [c3634, c1336] c4704 (by decide) p (sat_cons (step3634 p h) (sat_cons (step1336 p h) (sat_nil p)))
def c4705 : List Lit := [(71, false), (1090, true), (1060, true), (1057, false)]
theorem step4705 (p : Nat → Bool) (h : Constraints p) : clause p c4705 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1881] c4705 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1881 p h) (sat_nil p)))
def c4706 : List Lit := [(71, false), (103, false), (1072, true)]
theorem step4706 (p : Nat → Bool) (h : Constraints p) : clause p c4706 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1882] c4706 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1882 p h) (sat_nil p)))
def c4707 : List Lit := [(86, false), (71, false), (108, false)]
theorem step4707 (p : Nat → Bool) (h : Constraints p) : clause p c4707 = true :=
  Snake9.LocalRup.prove_clause [c3961, c488] c4707 (by decide) p (sat_cons (step3961 p h) (sat_cons (step488 p h) (sat_nil p)))
def c4708 : List Lit := [(111, false), (71, false), (108, false)]
theorem step4708 (p : Nat → Bool) (h : Constraints p) : clause p c4708 = true :=
  Snake9.LocalRup.prove_clause [c3961, c494] c4708 (by decide) p (sat_cons (step3961 p h) (sat_cons (step494 p h) (sat_nil p)))
def c4709 : List Lit := [(112, false), (71, false), (108, false)]
theorem step4709 (p : Nat → Bool) (h : Constraints p) : clause p c4709 = true :=
  Snake9.LocalRup.prove_clause [c3961, c495] c4709 (by decide) p (sat_cons (step3961 p h) (sat_cons (step495 p h) (sat_nil p)))
def c4710 : List Lit := [(35, false), (71, false), (1074, false), (1051, false), (1102, true)]
theorem step4710 (p : Nat → Bool) (h : Constraints p) : clause p c4710 = true :=
  Snake9.LocalRup.prove_clause [c3961, c2167] c4710 (by decide) p (sat_cons (step3961 p h) (sat_cons (step2167 p h) (sat_nil p)))
def c4711 : List Lit := [(112, false), (86, false), (71, false)]
theorem step4711 (p : Nat → Bool) (h : Constraints p) : clause p c4711 = true :=
  Snake9.LocalRup.prove_clause [c3961, c490] c4711 (by decide) p (sat_cons (step3961 p h) (sat_cons (step490 p h) (sat_nil p)))
def c4712 : List Lit := [(112, false), (35, false), (71, false)]
theorem step4712 (p : Nat → Bool) (h : Constraints p) : clause p c4712 = true :=
  Snake9.LocalRup.prove_clause [c3961, c476] c4712 (by decide) p (sat_cons (step3961 p h) (sat_cons (step476 p h) (sat_nil p)))
def c4713 : List Lit := [(35, false), (71, false), (108, false)]
theorem step4713 (p : Nat → Bool) (h : Constraints p) : clause p c4713 = true :=
  Snake9.LocalRup.prove_clause [c3961, c474] c4713 (by decide) p (sat_cons (step3961 p h) (sat_cons (step474 p h) (sat_nil p)))
def c4714 : List Lit := [(71, false), (108, false), (103, false)]
theorem step4714 (p : Nat → Bool) (h : Constraints p) : clause p c4714 = true :=
  Snake9.LocalRup.prove_clause [c3961, c491] c4714 (by decide) p (sat_cons (step3961 p h) (sat_cons (step491 p h) (sat_nil p)))
def c4715 : List Lit := [(86, false), (71, false), (103, false)]
theorem step4715 (p : Nat → Bool) (h : Constraints p) : clause p c4715 = true :=
  Snake9.LocalRup.prove_clause [c3961, c487] c4715 (by decide) p (sat_cons (step3961 p h) (sat_cons (step487 p h) (sat_nil p)))
def c4716 : List Lit := [(35, false), (86, false), (71, false)]
theorem step4716 (p : Nat → Bool) (h : Constraints p) : clause p c4716 = true :=
  Snake9.LocalRup.prove_clause [c3961, c472] c4716 (by decide) p (sat_cons (step3961 p h) (sat_cons (step472 p h) (sat_nil p)))
def c4717 : List Lit := [(35, false), (86, false), (108, false)]
theorem step4717 (p : Nat → Bool) (h : Constraints p) : clause p c4717 = true :=
  Snake9.LocalRup.prove_clause [c3961, c478] c4717 (by decide) p (sat_cons (step3961 p h) (sat_cons (step478 p h) (sat_nil p)))
def c4718 : List Lit := [(35, false), (86, false), (103, false)]
theorem step4718 (p : Nat → Bool) (h : Constraints p) : clause p c4718 = true :=
  Snake9.LocalRup.prove_clause [c3961, c477] c4718 (by decide) p (sat_cons (step3961 p h) (sat_cons (step477 p h) (sat_nil p)))
def c4719 : List Lit := [(111, false), (35, false), (108, false)]
theorem step4719 (p : Nat → Bool) (h : Constraints p) : clause p c4719 = true :=
  Snake9.LocalRup.prove_clause [c3961, c484] c4719 (by decide) p (sat_cons (step3961 p h) (sat_cons (step484 p h) (sat_nil p)))
def c4720 : List Lit := [(35, false), (1071, true)]
theorem step4720 (p : Nat → Bool) (h : Constraints p) : clause p c4720 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1597] c4720 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1597 p h) (sat_nil p)))
def c4721 : List Lit := [(112, false), (35, false), (108, false)]
theorem step4721 (p : Nat → Bool) (h : Constraints p) : clause p c4721 = true :=
  Snake9.LocalRup.prove_clause [c3961, c485] c4721 (by decide) p (sat_cons (step3961 p h) (sat_cons (step485 p h) (sat_nil p)))
def c4722 : List Lit := [(35, false), (108, false), (103, false)]
theorem step4722 (p : Nat → Bool) (h : Constraints p) : clause p c4722 = true :=
  Snake9.LocalRup.prove_clause [c3961, c481] c4722 (by decide) p (sat_cons (step3961 p h) (sat_cons (step481 p h) (sat_nil p)))
def c4723 : List Lit := [(112, false), (35, false), (103, false)]
theorem step4723 (p : Nat → Bool) (h : Constraints p) : clause p c4723 = true :=
  Snake9.LocalRup.prove_clause [c3961, c483] c4723 (by decide) p (sat_cons (step3961 p h) (sat_cons (step483 p h) (sat_nil p)))
def c4724 : List Lit := [(34, false), (35, false), (108, false)]
theorem step4724 (p : Nat → Bool) (h : Constraints p) : clause p c4724 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1506] c4724 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1506 p h) (sat_nil p)))
def c4725 : List Lit := [(112, false), (35, false), (86, false)]
theorem step4725 (p : Nat → Bool) (h : Constraints p) : clause p c4725 = true :=
  Snake9.LocalRup.prove_clause [c3961, c480] c4725 (by decide) p (sat_cons (step3961 p h) (sat_cons (step480 p h) (sat_nil p)))
def c4726 : List Lit := [(35, false), (71, false), (103, false)]
theorem step4726 (p : Nat → Bool) (h : Constraints p) : clause p c4726 = true :=
  Snake9.LocalRup.prove_clause [c3961, c473] c4726 (by decide) p (sat_cons (step3961 p h) (sat_cons (step473 p h) (sat_nil p)))
def c4727 : List Lit := [(111, false), (35, false), (103, false)]
theorem step4727 (p : Nat → Bool) (h : Constraints p) : clause p c4727 = true :=
  Snake9.LocalRup.prove_clause [c3961, c482] c4727 (by decide) p (sat_cons (step3961 p h) (sat_cons (step482 p h) (sat_nil p)))
def c4728 : List Lit := [(112, false), (71, false), (103, false)]
theorem step4728 (p : Nat → Bool) (h : Constraints p) : clause p c4728 = true :=
  Snake9.LocalRup.prove_clause [c3961, c493] c4728 (by decide) p (sat_cons (step3961 p h) (sat_cons (step493 p h) (sat_nil p)))
def c4729 : List Lit := [(103, false), (86, false), (108, false)]
theorem step4729 (p : Nat → Bool) (h : Constraints p) : clause p c4729 = true :=
  Snake9.LocalRup.prove_clause [c3961, c497] c4729 (by decide) p (sat_cons (step3961 p h) (sat_cons (step497 p h) (sat_nil p)))
def c4730 : List Lit := [(1071, true), (108, false)]
theorem step4730 (p : Nat → Bool) (h : Constraints p) : clause p c4730 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1943] c4730 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1943 p h) (sat_nil p)))
def c4731 : List Lit := [(70, false), (71, false), (108, false)]
theorem step4731 (p : Nat → Bool) (h : Constraints p) : clause p c4731 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1516] c4731 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1516 p h) (sat_nil p)))
def c4732 : List Lit := [(102, false), (108, false), (103, false)]
theorem step4732 (p : Nat → Bool) (h : Constraints p) : clause p c4732 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1536] c4732 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1536 p h) (sat_nil p)))
def c4733 : List Lit := [(111, false), (114, false), (112, false)]
theorem step4733 (p : Nat → Bool) (h : Constraints p) : clause p c4733 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1542] c4733 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1542 p h) (sat_nil p)))
def c4734 : List Lit := [(114, false), (89, false), (112, false)]
theorem step4734 (p : Nat → Bool) (h : Constraints p) : clause p c4734 = true :=
  Snake9.LocalRup.prove_clause [c3961, c525] c4734 (by decide) p (sat_cons (step3961 p h) (sat_cons (step525 p h) (sat_nil p)))
def c4735 : List Lit := [(112, false), (86, false), (89, false)]
theorem step4735 (p : Nat → Bool) (h : Constraints p) : clause p c4735 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1526] c4735 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1526 p h) (sat_nil p)))
def c4736 : List Lit := [(102, false), (110, false), (108, false)]
theorem step4736 (p : Nat → Bool) (h : Constraints p) : clause p c4736 = true :=
  Snake9.LocalRup.prove_clause [c3961, c471] c4736 (by decide) p (sat_cons (step3961 p h) (sat_cons (step471 p h) (sat_nil p)))
def c4737 : List Lit := [(102, false), (70, false), (108, false)]
theorem step4737 (p : Nat → Bool) (h : Constraints p) : clause p c4737 = true :=
  Snake9.LocalRup.prove_clause [c3961, c467] c4737 (by decide) p (sat_cons (step3961 p h) (sat_cons (step467 p h) (sat_nil p)))
def c4738 : List Lit := [(106, false), (103, false), (112, false)]
theorem step4738 (p : Nat → Bool) (h : Constraints p) : clause p c4738 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1540] c4738 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1540 p h) (sat_nil p)))
def c4739 : List Lit := [(111, false), (103, false), (112, false)]
theorem step4739 (p : Nat → Bool) (h : Constraints p) : clause p c4739 = true :=
  Snake9.LocalRup.prove_clause [c3961, c505] c4739 (by decide) p (sat_cons (step3961 p h) (sat_cons (step505 p h) (sat_nil p)))
def c4740 : List Lit := [(104, false), (111, false), (103, false)]
theorem step4740 (p : Nat → Bool) (h : Constraints p) : clause p c4740 = true :=
  Snake9.LocalRup.prove_clause [c3961, c1539] c4740 (by decide) p (sat_cons (step3961 p h) (sat_cons (step1539 p h) (sat_nil p)))
def c4741 : List Lit := [(78, false), (70, false), (71, false)]
theorem step4741 (p : Nat → Bool) (h : Constraints p) : clause p c4741 = true :=
  Snake9.LocalRup.prove_clause [c3961, c223] c4741 (by decide) p (sat_cons (step3961 p h) (sat_cons (step223 p h) (sat_nil p)))
def c4742 : List Lit := [(34, false), (70, false), (108, false)]
theorem step4742 (p : Nat → Bool) (h : Constraints p) : clause p c4742 = true :=
  Snake9.LocalRup.prove_clause [c3961, c464] c4742 (by decide) p (sat_cons (step3961 p h) (sat_cons (step464 p h) (sat_nil p)))
def c4743 : List Lit := [(110, false), (70, false), (108, false)]
theorem step4743 (p : Nat → Bool) (h : Constraints p) : clause p c4743 = true :=
  Snake9.LocalRup.prove_clause [c3961, c469] c4743 (by decide) p (sat_cons (step3961 p h) (sat_cons (step469 p h) (sat_nil p)))
def c4744 : List Lit := [(110, false), (122, false), (111, false)]
theorem step4744 (p : Nat → Bool) (h : Constraints p) : clause p c4744 = true :=
  Snake9.LocalRup.prove_clause [c3961, c521] c4744 (by decide) p (sat_cons (step3961 p h) (sat_cons (step521 p h) (sat_nil p)))
def c4745 : List Lit := [(100, false), (1001, true), (86, false)]
theorem step4745 (p : Nat → Bool) (h : Constraints p) : clause p c4745 = true :=
  Snake9.LocalRup.prove_clause [c3961, c2163] c4745 (by decide) p (sat_cons (step3961 p h) (sat_cons (step2163 p h) (sat_nil p)))
def c4746 : List Lit := [(1079, true), (86, false)]
theorem step4746 (p : Nat → Bool) (h : Constraints p) : clause p c4746 = true :=
  Snake9.LocalRup.prove_clause [c3961, c2138] c4746 (by decide) p (sat_cons (step3961 p h) (sat_cons (step2138 p h) (sat_nil p)))
end B112E153
