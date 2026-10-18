import B112E256Part0167
namespace B112E256
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c12596 : List Lit := [(886, false), (897, true)]
theorem step12596 (p : Nat → Bool) (h : Constraints p) : clause p c12596 = true :=
  Snake9.LocalRup.prove_clause [c12542, c1210] c12596 (by decide) p (sat_cons (step12542 p h) (sat_cons (step1210 p h) (sat_nil p)))
def c12597 : List Lit := [(850, false), (853, true)]
theorem step12597 (p : Nat → Bool) (h : Constraints p) : clause p c12597 = true :=
  Snake9.LocalRup.prove_clause [c12569, c1105] c12597 (by decide) p (sat_cons (step12569 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c12598 : List Lit := [(17, false), (15, false), (18, false)]
theorem step12598 (p : Nat → Bool) (h : Constraints p) : clause p c12598 = true :=
  Snake9.LocalRup.prove_clause [c11996, c114] c12598 (by decide) p (sat_cons (step11996 p h) (sat_cons (step114 p h) (sat_nil p)))
def c12599 : List Lit := [(24, true), (150, true)]
theorem step12599 (p : Nat → Bool) (h : Constraints p) : clause p c12599 = true :=
  Snake9.LocalRup.prove_clause [c12541, c152] c12599 (by decide) p (sat_cons (step12541 p h) (sat_cons (step152 p h) (sat_nil p)))
def c12600 : List Lit := [(989, false), (1003, true), (189, true), (60, false)]
theorem step12600 (p : Nat → Bool) (h : Constraints p) : clause p c12600 = true :=
  Snake9.LocalRup.prove_clause [c11996, c3584] c12600 (by decide) p (sat_cons (step11996 p h) (sat_cons (step3584 p h) (sat_nil p)))
def c12601 : List Lit := [(70, false), (869, true), (142, true)]
theorem step12601 (p : Nat → Bool) (h : Constraints p) : clause p c12601 = true :=
  Snake9.LocalRup.prove_clause [c11996, c4442] c12601 (by decide) p (sat_cons (step11996 p h) (sat_cons (step4442 p h) (sat_nil p)))
def c12602 : List Lit := [(70, false), (62, false), (189, true), (60, false)]
theorem step12602 (p : Nat → Bool) (h : Constraints p) : clause p c12602 = true :=
  Snake9.LocalRup.prove_clause [c11996, c4438] c12602 (by decide) p (sat_cons (step11996 p h) (sat_cons (step4438 p h) (sat_nil p)))
def c12603 : List Lit := [(185, true), (293, true), (65, false), (21, false)]
theorem step12603 (p : Nat → Bool) (h : Constraints p) : clause p c12603 = true :=
  Snake9.LocalRup.prove_clause [c12541, c4309] c12603 (by decide) p (sat_cons (step12541 p h) (sat_cons (step4309 p h) (sat_nil p)))
def c12604 : List Lit := [(850, false), (866, true), (855, false)]
theorem step12604 (p : Nat → Bool) (h : Constraints p) : clause p c12604 = true :=
  Snake9.LocalRup.prove_clause [c12541, c12570, c4317] c12604 (by decide) p (sat_cons (step12541 p h) (sat_cons (step12570 p h) (sat_cons (step4317 p h) (sat_nil p))))
def c12605 : List Lit := [(78, false), (2, true), (866, true), (854, false)]
theorem step12605 (p : Nat → Bool) (h : Constraints p) : clause p c12605 = true :=
  Snake9.LocalRup.prove_clause [c12541, c11462, c4314] c12605 (by decide) p (sat_cons (step12541 p h) (sat_cons (step11462 p h) (sat_cons (step4314 p h) (sat_nil p))))
def c12606 : List Lit := [(941, true), (377, true)]
theorem step12606 (p : Nat → Bool) (h : Constraints p) : clause p c12606 = true :=
  Snake9.LocalRup.prove_clause [c12570, c4477] c12606 (by decide) p (sat_cons (step12570 p h) (sat_cons (step4477 p h) (sat_nil p)))
def c12607 : List Lit := [(15, false), (45, false), (42, false), (142, true)]
theorem step12607 (p : Nat → Bool) (h : Constraints p) : clause p c12607 = true :=
  Snake9.LocalRup.prove_clause [c11996, c4632] c12607 (by decide) p (sat_cons (step11996 p h) (sat_cons (step4632 p h) (sat_nil p)))
def c12608 : List Lit := [(7, false), (150, true)]
theorem step12608 (p : Nat → Bool) (h : Constraints p) : clause p c12608 = true :=
  Snake9.LocalRup.prove_clause [c12541, c4008] c12608 (by decide) p (sat_cons (step12541 p h) (sat_cons (step4008 p h) (sat_nil p)))
def c12609 : List Lit := [(941, true), (343, false)]
theorem step12609 (p : Nat → Bool) (h : Constraints p) : clause p c12609 = true :=
  Snake9.LocalRup.prove_clause [c12570, c4481] c12609 (by decide) p (sat_cons (step12570 p h) (sat_cons (step4481 p h) (sat_nil p)))
def c12610 : List Lit := [(58, false), (343, false)]
theorem step12610 (p : Nat → Bool) (h : Constraints p) : clause p c12610 = true :=
  Snake9.LocalRup.prove_clause [c12570, c4529] c12610 (by decide) p (sat_cons (step12570 p h) (sat_cons (step4529 p h) (sat_nil p)))
def c12611 : List Lit := [(373, false), (44, false)]
theorem step12611 (p : Nat → Bool) (h : Constraints p) : clause p c12611 = true :=
  Snake9.LocalRup.prove_clause [c12541, c4423] c12611 (by decide) p (sat_cons (step12541 p h) (sat_cons (step4423 p h) (sat_nil p)))
def c12612 : List Lit := [(2, false), (977, true)]
theorem step12612 (p : Nat → Bool) (h : Constraints p) : clause p c12612 = true :=
  Snake9.LocalRup.prove_clause [c12196, c4998] c12612 (by decide) p (sat_cons (step12196 p h) (sat_cons (step4998 p h) (sat_nil p)))
def c12613 : List Lit := [(941, true), (913, false)]
theorem step12613 (p : Nat → Bool) (h : Constraints p) : clause p c12613 = true :=
  Snake9.LocalRup.prove_clause [c12570, c11462, c5670] c12613 (by decide) p (sat_cons (step12570 p h) (sat_cons (step11462 p h) (sat_cons (step5670 p h) (sat_nil p))))
def c12614 : List Lit := [(10, true), (78, false), (866, true)]
theorem step12614 (p : Nat → Bool) (h : Constraints p) : clause p c12614 = true :=
  Snake9.LocalRup.prove_clause [c11462, c12541, c5052] c12614 (by decide) p (sat_cons (step11462 p h) (sat_cons (step12541 p h) (sat_cons (step5052 p h) (sat_nil p))))
def c12615 : List Lit := [(955, true), (913, false)]
theorem step12615 (p : Nat → Bool) (h : Constraints p) : clause p c12615 = true :=
  Snake9.LocalRup.prove_clause [c12570, c5331] c12615 (by decide) p (sat_cons (step12570 p h) (sat_cons (step5331 p h) (sat_nil p)))
def c12616 : List Lit := [(855, false), (865, true)]
theorem step12616 (p : Nat → Bool) (h : Constraints p) : clause p c12616 = true :=
  Snake9.LocalRup.prove_clause [c12541, c12569, c11462, c4846] c12616 (by decide) p (sat_cons (step12541 p h) (sat_cons (step12569 p h) (sat_cons (step11462 p h) (sat_cons (step4846 p h) (sat_nil p)))))
def c12617 : List Lit := [(977, true), (869, true), (854, false), (918, false), (377, true)]
theorem step12617 (p : Nat → Bool) (h : Constraints p) : clause p c12617 = true :=
  Snake9.LocalRup.prove_clause [c12569, c4800] c12617 (by decide) p (sat_cons (step12569 p h) (sat_cons (step4800 p h) (sat_nil p)))
def c12618 : List Lit := [(860, false), (887, false), (953, false), (977, true), (5, true)]
theorem step12618 (p : Nat → Bool) (h : Constraints p) : clause p c12618 = true :=
  Snake9.LocalRup.prove_clause [c12196, c12569, c5124] c12618 (by decide) p (sat_cons (step12196 p h) (sat_cons (step12569 p h) (sat_cons (step5124 p h) (sat_nil p))))
def c12619 : List Lit := [(66, false), (1004, true), (189, true), (60, false), (57, false), (47, false)]
theorem step12619 (p : Nat → Bool) (h : Constraints p) : clause p c12619 = true :=
  Snake9.LocalRup.prove_clause [c11996, c5695] c12619 (by decide) p (sat_cons (step11996 p h) (sat_cons (step5695 p h) (sat_nil p)))
def c12620 : List Lit := [(928, false), (936, false), (917, false), (955, true)]
theorem step12620 (p : Nat → Bool) (h : Constraints p) : clause p c12620 = true :=
  Snake9.LocalRup.prove_clause [c12571, c5138] c12620 (by decide) p (sat_cons (step12571 p h) (sat_cons (step5138 p h) (sat_nil p)))
def c12621 : List Lit := [(90, true), (87, true), (78, false), (1036, true), (10, true)]
theorem step12621 (p : Nat → Bool) (h : Constraints p) : clause p c12621 = true :=
  Snake9.LocalRup.prove_clause [c12542, c4753] c12621 (by decide) p (sat_cons (step12542 p h) (sat_cons (step4753 p h) (sat_nil p)))
def c12622 : List Lit := [(11, true), (2, true), (867, true), (150, true), (10, true)]
theorem step12622 (p : Nat → Bool) (h : Constraints p) : clause p c12622 = true :=
  Snake9.LocalRup.prove_clause [c12569, c12541, c5368] c12622 (by decide) p (sat_cons (step12569 p h) (sat_cons (step12541 p h) (sat_cons (step5368 p h) (sat_nil p))))
def c12623 : List Lit := [(57, true), (942, true), (61, true), (65, false)]
theorem step12623 (p : Nat → Bool) (h : Constraints p) : clause p c12623 = true :=
  Snake9.LocalRup.prove_clause [c12570, c5740] c12623 (by decide) p (sat_cons (step12570 p h) (sat_cons (step5740 p h) (sat_nil p)))
def c12624 : List Lit := [(30, false), (879, true), (25, false), (65, true), (19, false), (869, true), (313, true)]
theorem step12624 (p : Nat → Bool) (h : Constraints p) : clause p c12624 = true :=
  Snake9.LocalRup.prove_clause [c11996, c5087] c12624 (by decide) p (sat_cons (step11996 p h) (sat_cons (step5087 p h) (sat_nil p)))
def c12625 : List Lit := [(25, true), (873, false), (899, true), (10, true), (78, false)]
theorem step12625 (p : Nat → Bool) (h : Constraints p) : clause p c12625 = true :=
  Snake9.LocalRup.prove_clause [c11462, c5107] c12625 (by decide) p (sat_cons (step11462 p h) (sat_cons (step5107 p h) (sat_nil p)))
def c12626 : List Lit := [(30, false), (908, false), (78, false), (27, true), (10, true), (1120, true), (65, true)]
theorem step12626 (p : Nat → Bool) (h : Constraints p) : clause p c12626 = true :=
  Snake9.LocalRup.prove_clause [c11996, c11462, c5112] c12626 (by decide) p (sat_cons (step11996 p h) (sat_cons (step11462 p h) (sat_cons (step5112 p h) (sat_nil p))))
def c12627 : List Lit := [(1026, true), (993, false), (60, false), (189, true), (405, true), (1120, true), (65, true)]
theorem step12627 (p : Nat → Bool) (h : Constraints p) : clause p c12627 = true :=
  Snake9.LocalRup.prove_clause [c11996, c5098] c12627 (by decide) p (sat_cons (step11996 p h) (sat_cons (step5098 p h) (sat_nil p)))
def c12628 : List Lit := [(993, false), (869, true), (10, false), (65, true), (78, true), (1121, true)]
theorem step12628 (p : Nat → Bool) (h : Constraints p) : clause p c12628 = true :=
  Snake9.LocalRup.prove_clause [c11996, c6704] c12628 (by decide) p (sat_cons (step11996 p h) (sat_cons (step6704 p h) (sat_nil p)))
def c12629 : List Lit := [(954, true), (910, false)]
theorem step12629 (p : Nat → Bool) (h : Constraints p) : clause p c12629 = true :=
  Snake9.LocalRup.prove_clause [c12570, c5933] c12629 (by decide) p (sat_cons (step12570 p h) (sat_cons (step5933 p h) (sat_nil p)))
def c12630 : List Lit := [(25, false), (1038, true), (993, false), (988, false), (78, true), (189, true), (10, false)]
theorem step12630 (p : Nat → Bool) (h : Constraints p) : clause p c12630 = true :=
  Snake9.LocalRup.prove_clause [c11996, c6700] c12630 (by decide) p (sat_cons (step11996 p h) (sat_cons (step6700 p h) (sat_nil p)))
def c12631 : List Lit := [(5, false), (855, false), (866, true), (849, false)]
theorem step12631 (p : Nat → Bool) (h : Constraints p) : clause p c12631 = true :=
  Snake9.LocalRup.prove_clause [c11462, c12541, c6327] c12631 (by decide) p (sat_cons (step11462 p h) (sat_cons (step12541 p h) (sat_cons (step6327 p h) (sat_nil p))))
def c12632 : List Lit := [(377, true), (65, false), (21, false)]
theorem step12632 (p : Nat → Bool) (h : Constraints p) : clause p c12632 = true :=
  Snake9.LocalRup.prove_clause [c12541, c6785] c12632 (by decide) p (sat_cons (step12541 p h) (sat_cons (step6785 p h) (sat_nil p)))
def c12633 : List Lit := [(25, false), (1122, true), (78, true), (993, false), (501, true), (65, true), (10, false)]
theorem step12633 (p : Nat → Bool) (h : Constraints p) : clause p c12633 = true :=
  Snake9.LocalRup.prove_clause [c11996, c6839] c12633 (by decide) p (sat_cons (step11996 p h) (sat_cons (step6839 p h) (sat_nil p)))
def c12634 : List Lit := [(309, false), (65, false), (21, false)]
theorem step12634 (p : Nat → Bool) (h : Constraints p) : clause p c12634 = true :=
  Snake9.LocalRup.prove_clause [c12541, c6651] c12634 (by decide) p (sat_cons (step12541 p h) (sat_cons (step6651 p h) (sat_nil p)))
def c12635 : List Lit := [(910, false), (957, true), (913, false), (915, false), (932, false)]
theorem step12635 (p : Nat → Bool) (h : Constraints p) : clause p c12635 = true :=
  Snake9.LocalRup.prove_clause [c12570, c11462, c8729] c12635 (by decide) p (sat_cons (step12570 p h) (sat_cons (step11462 p h) (sat_cons (step8729 p h) (sat_nil p))))
def c12636 : List Lit := [(941, true), (993, true)]
theorem step12636 (p : Nat → Bool) (h : Constraints p) : clause p c12636 = true :=
  Snake9.LocalRup.prove_clause [c12570, c11996, c9769] c12636 (by decide) p (sat_cons (step12570 p h) (sat_cons (step11996 p h) (sat_cons (step9769 p h) (sat_nil p))))
def c12637 : List Lit := [(28, true), (19, false), (880, true), (993, true), (10, false)]
theorem step12637 (p : Nat → Bool) (h : Constraints p) : clause p c12637 = true :=
  Snake9.LocalRup.prove_clause [c11996, c9725] c12637 (by decide) p (sat_cons (step11996 p h) (sat_cons (step9725 p h) (sat_nil p)))
def c12638 : List Lit := [(879, true), (993, true), (155, true), (1004, true), (65, true)]
theorem step12638 (p : Nat → Bool) (h : Constraints p) : clause p c12638 = true :=
  Snake9.LocalRup.prove_clause [c11996, c8125] c12638 (by decide) p (sat_cons (step11996 p h) (sat_cons (step8125 p h) (sat_nil p)))
def c12639 : List Lit := [(887, false), (977, true), (955, false), (10, true)]
theorem step12639 (p : Nat → Bool) (h : Constraints p) : clause p c12639 = true :=
  Snake9.LocalRup.prove_clause [c12569, c11462, c8245] c12639 (by decide) p (sat_cons (step12569 p h) (sat_cons (step11462 p h) (sat_cons (step8245 p h) (sat_nil p))))
def c12640 : List Lit := [(879, true), (19, false), (41, true), (171, true), (36, false), (941, false), (1120, true), (899, false), (65, true)]
theorem step12640 (p : Nat → Bool) (h : Constraints p) : clause p c12640 = true :=
  Snake9.LocalRup.prove_clause [c11996, c8192] c12640 (by decide) p (sat_cons (step11996 p h) (sat_cons (step8192 p h) (sat_nil p)))
def c12641 : List Lit := [(993, true), (879, true), (10, false)]
theorem step12641 (p : Nat → Bool) (h : Constraints p) : clause p c12641 = true :=
  Snake9.LocalRup.prove_clause [c11996, c9748] c12641 (by decide) p (sat_cons (step11996 p h) (sat_cons (step9748 p h) (sat_nil p)))
def c12642 : List Lit := [(993, true), (899, false), (65, true), (922, false), (405, true)]
theorem step12642 (p : Nat → Bool) (h : Constraints p) : clause p c12642 = true :=
  Snake9.LocalRup.prove_clause [c11996, c8240] c12642 (by decide) p (sat_cons (step11996 p h) (sat_cons (step8240 p h) (sat_nil p)))
def c12643 : List Lit := [(70, true), (957, false), (990, false), (78, true), (897, false)]
theorem step12643 (p : Nat → Bool) (h : Constraints p) : clause p c12643 = true :=
  Snake9.LocalRup.prove_clause [c12196, c8784] c12643 (by decide) p (sat_cons (step12196 p h) (sat_cons (step8784 p h) (sat_nil p)))
def c12644 : List Lit := [(887, false), (954, false), (860, false), (977, true), (5, true)]
theorem step12644 (p : Nat → Bool) (h : Constraints p) : clause p c12644 = true :=
  Snake9.LocalRup.prove_clause [c12196, c8225] c12644 (by decide) p (sat_cons (step12196 p h) (sat_cons (step8225 p h) (sat_nil p)))
def c12645 : List Lit := [(33, false), (1120, true), (65, true), (942, true), (36, false), (78, true)]
theorem step12645 (p : Nat → Bool) (h : Constraints p) : clause p c12645 = true :=
  Snake9.LocalRup.prove_clause [c11996, c8734] c12645 (by decide) p (sat_cons (step11996 p h) (sat_cons (step8734 p h) (sat_nil p)))
def c12646 : List Lit := [(25, false), (1002, true), (152, true), (142, true), (869, true)]
theorem step12646 (p : Nat → Bool) (h : Constraints p) : clause p c12646 = true :=
  Snake9.LocalRup.prove_clause [c11996, c10285] c12646 (by decide) p (sat_cons (step11996 p h) (sat_cons (step10285 p h) (sat_nil p)))
def c12647 : List Lit := [(25, false), (74, true), (1003, true), (869, true), (152, true), (142, true)]
theorem step12647 (p : Nat → Bool) (h : Constraints p) : clause p c12647 = true :=
  Snake9.LocalRup.prove_clause [c11996, c10360] c12647 (by decide) p (sat_cons (step11996 p h) (sat_cons (step10360 p h) (sat_nil p)))
def c12648 : List Lit := [(25, false), (74, true), (195, true), (1003, true)]
theorem step12648 (p : Nat → Bool) (h : Constraints p) : clause p c12648 = true :=
  Snake9.LocalRup.prove_clause [c11996, c10397] c12648 (by decide) p (sat_cons (step11996 p h) (sat_cons (step10397 p h) (sat_nil p)))
def c12649 : List Lit := [(877, false), (869, false), (888, true), (311, true), (65, false)]
theorem step12649 (p : Nat → Bool) (h : Constraints p) : clause p c12649 = true :=
  Snake9.LocalRup.prove_clause [c12570, c11435] c12649 (by decide) p (sat_cons (step12570 p h) (sat_cons (step11435 p h) (sat_nil p)))
def c12650 : List Lit := [(185, true), (78, false), (900, true), (869, false), (65, false), (10, true), (311, true)]
theorem step12650 (p : Nat → Bool) (h : Constraints p) : clause p c12650 = true :=
  Snake9.LocalRup.prove_clause [c12570, c11818] c12650 (by decide) p (sat_cons (step12570 p h) (sat_cons (step11818 p h) (sat_nil p)))
def c12651 : List Lit := [(899, true), (311, true), (869, false), (10, true), (65, false)]
theorem step12651 (p : Nat → Bool) (h : Constraints p) : clause p c12651 = true :=
  Snake9.LocalRup.prove_clause [c12569, c11828] c12651 (by decide) p (sat_cons (step12569 p h) (sat_cons (step11828 p h) (sat_nil p)))
def c12652 : List Lit := [(899, true), (78, false), (65, false), (10, true), (869, false)]
theorem step12652 (p : Nat → Bool) (h : Constraints p) : clause p c12652 = true :=
  Snake9.LocalRup.prove_clause [c12570, c11844] c12652 (by decide) p (sat_cons (step12570 p h) (sat_cons (step11844 p h) (sat_nil p)))
def c12653 : List Lit := [(899, true), (41, false), (21, true), (155, true), (65, false), (10, true)]
theorem step12653 (p : Nat → Bool) (h : Constraints p) : clause p c12653 = true :=
  Snake9.LocalRup.prove_clause [c12569, c11855] c12653 (by decide) p (sat_cons (step12569 p h) (sat_cons (step11855 p h) (sat_nil p)))
def c12654 : List Lit := [(956, false), (78, false), (869, false), (65, true), (10, true), (375, false)]
theorem step12654 (p : Nat → Bool) (h : Constraints p) : clause p c12654 = true :=
  Snake9.LocalRup.prove_clause [c12570, c11885] c12654 (by decide) p (sat_cons (step12570 p h) (sat_cons (step11885 p h) (sat_nil p)))
def c12655 : List Lit := [(41, false), (2, true), (866, true)]
theorem step12655 (p : Nat → Bool) (h : Constraints p) : clause p c12655 = true :=
  Snake9.LocalRup.prove_clause [c12541, c12569, c11899] c12655 (by decide) p (sat_cons (step12541 p h) (sat_cons (step12569 p h) (sat_cons (step11899 p h) (sat_nil p))))
def c12656 : List Lit := [(877, false), (887, true), (869, false), (65, false)]
theorem step12656 (p : Nat → Bool) (h : Constraints p) : clause p c12656 = true :=
  Snake9.LocalRup.prove_clause [c12570, c11906] c12656 (by decide) p (sat_cons (step12570 p h) (sat_cons (step11906 p h) (sat_nil p)))
def c12657 : List Lit := [(869, false), (886, true)]
theorem step12657 (p : Nat → Bool) (h : Constraints p) : clause p c12657 = true :=
  Snake9.LocalRup.prove_clause [c12570, c11956] c12657 (by decide) p (sat_cons (step12570 p h) (sat_cons (step11956 p h) (sat_nil p)))
def c12658 : List Lit := [(78, false), (865, true)]
theorem step12658 (p : Nat → Bool) (h : Constraints p) : clause p c12658 = true :=
  Snake9.LocalRup.prove_clause [c12541, c11969] c12658 (by decide) p (sat_cons (step12541 p h) (sat_cons (step11969 p h) (sat_nil p)))
def c12659 : List Lit := [(977, true), (955, false), (78, false), (886, false)]
theorem step12659 (p : Nat → Bool) (h : Constraints p) : clause p c12659 = true :=
  Snake9.LocalRup.prove_clause [c12196, c12541, c11973] c12659 (by decide) p (sat_cons (step12196 p h) (sat_cons (step12541 p h) (sat_cons (step11973 p h) (sat_nil p))))
end B112E256
