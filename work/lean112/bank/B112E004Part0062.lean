import B112E004Part0061
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5702 : List Lit := [(1505, true), (1549, true), (1569, true), (51, false), (56, false)]
theorem step5702 (p : Nat → Bool) (h : Constraints p) : clause p c5702 = true :=
  Snake9.LocalRup.prove_clause [c5583, c2261] c5702 (by decide) p (sat_cons (step5583 p h) (sat_cons (step2261 p h) (sat_nil p)))
def c5703 : List Lit := [(15, false), (73, false), (1525, true)]
theorem step5703 (p : Nat → Bool) (h : Constraints p) : clause p c5703 = true :=
  Snake9.LocalRup.prove_clause [c5583, c2317] c5703 (by decide) p (sat_cons (step5583 p h) (sat_cons (step2317 p h) (sat_nil p)))
def c5704 : List Lit := [(53, false), (48, false), (103, false)]
theorem step5704 (p : Nat → Bool) (h : Constraints p) : clause p c5704 = true :=
  Snake9.LocalRup.prove_clause [c5583, c432] c5704 (by decide) p (sat_cons (step5583 p h) (sat_cons (step432 p h) (sat_nil p)))
def c5705 : List Lit := [(56, false), (48, false), (103, false)]
theorem step5705 (p : Nat → Bool) (h : Constraints p) : clause p c5705 = true :=
  Snake9.LocalRup.prove_clause [c5583, c434] c5705 (by decide) p (sat_cons (step5583 p h) (sat_cons (step434 p h) (sat_nil p)))
def c5706 : List Lit := [(15, false), (56, false), (103, false)]
theorem step5706 (p : Nat → Bool) (h : Constraints p) : clause p c5706 = true :=
  Snake9.LocalRup.prove_clause [c5583, c424] c5706 (by decide) p (sat_cons (step5583 p h) (sat_cons (step424 p h) (sat_nil p)))
def c5707 : List Lit := [(1530, false), (46, true), (103, false), (1541, true), (51, true)]
theorem step5707 (p : Nat → Bool) (h : Constraints p) : clause p c5707 = true :=
  Snake9.LocalRup.prove_clause [c5583, c2161] c5707 (by decide) p (sat_cons (step5583 p h) (sat_cons (step2161 p h) (sat_nil p)))
def c5708 : List Lit := [(73, true), (1580, false), (51, false), (1488, false), (1585, false), (1692, false), (1630, true), (1618, false)]
theorem step5708 (p : Nat → Bool) (h : Constraints p) : clause p c5708 = true :=
  Snake9.LocalRup.prove_clause [c5584, c2259] c5708 (by decide) p (sat_cons (step5584 p h) (sat_cons (step2259 p h) (sat_nil p)))
def c5709 : List Lit := [(16, false), (54, false), (56, false)]
theorem step5709 (p : Nat → Bool) (h : Constraints p) : clause p c5709 = true :=
  Snake9.LocalRup.prove_clause [c5583, c455] c5709 (by decide) p (sat_cons (step5583 p h) (sat_cons (step455 p h) (sat_nil p)))
def c5710 : List Lit := [(16, false), (49, false), (56, false)]
theorem step5710 (p : Nat → Bool) (h : Constraints p) : clause p c5710 = true :=
  Snake9.LocalRup.prove_clause [c5583, c453] c5710 (by decide) p (sat_cons (step5583 p h) (sat_cons (step453 p h) (sat_nil p)))
def c5711 : List Lit := [(74, false), (56, false), (73, false)]
theorem step5711 (p : Nat → Bool) (h : Constraints p) : clause p c5711 = true :=
  Snake9.LocalRup.prove_clause [c5583, c1718] c5711 (by decide) p (sat_cons (step5583 p h) (sat_cons (step1718 p h) (sat_nil p)))
def c5712 : List Lit := [(48, false), (15, false), (103, false)]
theorem step5712 (p : Nat → Bool) (h : Constraints p) : clause p c5712 = true :=
  Snake9.LocalRup.prove_clause [c5583, c415] c5712 (by decide) p (sat_cons (step5583 p h) (sat_cons (step415 p h) (sat_nil p)))
def c5713 : List Lit := [(48, false), (15, false), (73, false)]
theorem step5713 (p : Nat → Bool) (h : Constraints p) : clause p c5713 = true :=
  Snake9.LocalRup.prove_clause [c5583, c414] c5713 (by decide) p (sat_cons (step5583 p h) (sat_cons (step414 p h) (sat_nil p)))
def c5714 : List Lit := [(48, false), (15, false), (1529, true)]
theorem step5714 (p : Nat → Bool) (h : Constraints p) : clause p c5714 = true :=
  Snake9.LocalRup.prove_clause [c5583, c2175] c5714 (by decide) p (sat_cons (step5583 p h) (sat_cons (step2175 p h) (sat_nil p)))
def c5715 : List Lit := [(52, false), (48, false), (15, false)]
theorem step5715 (p : Nat → Bool) (h : Constraints p) : clause p c5715 = true :=
  Snake9.LocalRup.prove_clause [c5583, c411] c5715 (by decide) p (sat_cons (step5583 p h) (sat_cons (step411 p h) (sat_nil p)))
def c5716 : List Lit := [(47, false), (53, false), (48, false)]
theorem step5716 (p : Nat → Bool) (h : Constraints p) : clause p c5716 = true :=
  Snake9.LocalRup.prove_clause [c5583, c1710] c5716 (by decide) p (sat_cons (step5583 p h) (sat_cons (step1710 p h) (sat_nil p)))
def c5717 : List Lit := [(74, false), (43, false), (56, false)]
theorem step5717 (p : Nat → Bool) (h : Constraints p) : clause p c5717 = true :=
  Snake9.LocalRup.prove_clause [c5583, c457] c5717 (by decide) p (sat_cons (step5583 p h) (sat_cons (step457 p h) (sat_nil p)))
def c5718 : List Lit := [(52, false), (73, false), (1529, true)]
theorem step5718 (p : Nat → Bool) (h : Constraints p) : clause p c5718 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3213] c5718 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3213 p h) (sat_nil p)))
def c5719 : List Lit := [(1528, true), (73, false)]
theorem step5719 (p : Nat → Bool) (h : Constraints p) : clause p c5719 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3233] c5719 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3233 p h) (sat_nil p)))
def c5720 : List Lit := [(1694, false), (39, true), (103, false), (1617, false), (51, false), (1488, false), (1514, false)]
theorem step5720 (p : Nat → Bool) (h : Constraints p) : clause p c5720 = true :=
  Snake9.LocalRup.prove_clause [c5583, c2922] c5720 (by decide) p (sat_cons (step5583 p h) (sat_cons (step2922 p h) (sat_nil p)))
def c5721 : List Lit := [(1620, false), (61, true), (1515, false), (1488, false), (103, false)]
theorem step5721 (p : Nat → Bool) (h : Constraints p) : clause p c5721 = true :=
  Snake9.LocalRup.prove_clause [c5583, c4385] c5721 (by decide) p (sat_cons (step5583 p h) (sat_cons (step4385 p h) (sat_nil p)))
def c5722 : List Lit := [(1538, true), (1530, false)]
theorem step5722 (p : Nat → Bool) (h : Constraints p) : clause p c5722 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3520] c5722 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3520 p h) (sat_nil p)))
def c5723 : List Lit := [(103, false), (1528, true)]
theorem step5723 (p : Nat → Bool) (h : Constraints p) : clause p c5723 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3347] c5723 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3347 p h) (sat_nil p)))
def c5724 : List Lit := [(51, true), (1539, true), (103, false)]
theorem step5724 (p : Nat → Bool) (h : Constraints p) : clause p c5724 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3667] c5724 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3667 p h) (sat_nil p)))
def c5725 : List Lit := [(1538, true), (51, true)]
theorem step5725 (p : Nat → Bool) (h : Constraints p) : clause p c5725 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3666] c5725 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3666 p h) (sat_nil p)))
def c5726 : List Lit := [(39, true), (1488, false), (1514, false), (1618, false), (1530, true), (103, false), (51, true), (73, false)]
theorem step5726 (p : Nat → Bool) (h : Constraints p) : clause p c5726 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3954] c5726 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3954 p h) (sat_nil p)))
def c5727 : List Lit := [(52, false), (1488, false), (1522, false), (1691, false), (1618, false), (1514, false), (1530, true), (38, true), (39, true)]
theorem step5727 (p : Nat → Bool) (h : Constraints p) : clause p c5727 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3366] c5727 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3366 p h) (sat_nil p)))
def c5728 : List Lit := [(10, false), (21, false), (131, true), (49, true), (12, false), (16, true), (1, false)]
theorem step5728 (p : Nat → Bool) (h : Constraints p) : clause p c5728 = true :=
  Snake9.LocalRup.prove_clause [c5583, c4187] c5728 (by decide) p (sat_cons (step5583 p h) (sat_cons (step4187 p h) (sat_nil p)))
def c5729 : List Lit := [(1605, false), (1595, false), (1515, false), (1691, false), (51, true), (1488, false)]
theorem step5729 (p : Nat → Bool) (h : Constraints p) : clause p c5729 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3764] c5729 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3764 p h) (sat_nil p)))
def c5730 : List Lit := [(52, false), (1528, true)]
theorem step5730 (p : Nat → Bool) (h : Constraints p) : clause p c5730 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3252] c5730 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3252 p h) (sat_nil p)))
def c5731 : List Lit := [(1595, true), (61, true), (103, false), (51, true), (73, false), (1541, true)]
theorem step5731 (p : Nat → Bool) (h : Constraints p) : clause p c5731 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3790] c5731 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3790 p h) (sat_nil p)))
def c5732 : List Lit := [(39, true), (38, false), (1530, false), (1523, false), (1540, true), (1550, true), (48, true)]
theorem step5732 (p : Nat → Bool) (h : Constraints p) : clause p c5732 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3321] c5732 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3321 p h) (sat_nil p)))
def c5733 : List Lit := [(46, true), (1541, true), (103, false), (1530, false), (73, false)]
theorem step5733 (p : Nat → Bool) (h : Constraints p) : clause p c5733 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3934] c5733 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3934 p h) (sat_nil p)))
def c5734 : List Lit := [(1530, false), (46, true), (51, true), (1541, true), (73, false)]
theorem step5734 (p : Nat → Bool) (h : Constraints p) : clause p c5734 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3915] c5734 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3915 p h) (sat_nil p)))
def c5735 : List Lit := [(1530, false), (1541, true), (103, false), (73, false), (51, true)]
theorem step5735 (p : Nat → Bool) (h : Constraints p) : clause p c5735 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3565] c5735 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3565 p h) (sat_nil p)))
def c5736 : List Lit := [(46, false), (39, true), (1528, true), (1515, true), (38, false)]
theorem step5736 (p : Nat → Bool) (h : Constraints p) : clause p c5736 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3656] c5736 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3656 p h) (sat_nil p)))
def c5737 : List Lit := [(1530, false), (1540, true), (51, true), (46, true)]
theorem step5737 (p : Nat → Bool) (h : Constraints p) : clause p c5737 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3571] c5737 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3571 p h) (sat_nil p)))
def c5738 : List Lit := [(1540, true), (46, true), (73, false), (51, true)]
theorem step5738 (p : Nat → Bool) (h : Constraints p) : clause p c5738 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3646] c5738 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3646 p h) (sat_nil p)))
def c5739 : List Lit := [(73, false), (1540, true), (103, false), (51, true)]
theorem step5739 (p : Nat → Bool) (h : Constraints p) : clause p c5739 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3651] c5739 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3651 p h) (sat_nil p)))
def c5740 : List Lit := [(1530, false), (1540, true), (51, true), (103, false)]
theorem step5740 (p : Nat → Bool) (h : Constraints p) : clause p c5740 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3572] c5740 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3572 p h) (sat_nil p)))
def c5741 : List Lit := [(1540, true), (1530, false), (51, true), (73, false)]
theorem step5741 (p : Nat → Bool) (h : Constraints p) : clause p c5741 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3713] c5741 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3713 p h) (sat_nil p)))
def c5742 : List Lit := [(39, true), (38, true), (1550, true), (1526, false), (1530, false), (1540, true)]
theorem step5742 (p : Nat → Bool) (h : Constraints p) : clause p c5742 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3311] c5742 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3311 p h) (sat_nil p)))
def c5743 : List Lit := [(1523, false), (1540, true), (46, true), (103, false)]
theorem step5743 (p : Nat → Bool) (h : Constraints p) : clause p c5743 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3643] c5743 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3643 p h) (sat_nil p)))
def c5744 : List Lit := [(1523, false), (1540, true), (51, true), (103, false), (1530, false)]
theorem step5744 (p : Nat → Bool) (h : Constraints p) : clause p c5744 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3457] c5744 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3457 p h) (sat_nil p)))
def c5745 : List Lit := [(1529, true), (73, false), (103, false)]
theorem step5745 (p : Nat → Bool) (h : Constraints p) : clause p c5745 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3258] c5745 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3258 p h) (sat_nil p)))
def c5746 : List Lit := [(1594, true), (1541, true), (103, false), (73, false), (51, true)]
theorem step5746 (p : Nat → Bool) (h : Constraints p) : clause p c5746 = true :=
  Snake9.LocalRup.prove_clause [c5583, c4061] c5746 (by decide) p (sat_cons (step5583 p h) (sat_cons (step4061 p h) (sat_nil p)))
def c5747 : List Lit := [(1530, false), (1539, true), (51, true)]
theorem step5747 (p : Nat → Bool) (h : Constraints p) : clause p c5747 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3551] c5747 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3551 p h) (sat_nil p)))
def c5748 : List Lit := [(46, true), (1542, true), (103, false), (73, false), (51, true), (1530, false)]
theorem step5748 (p : Nat → Bool) (h : Constraints p) : clause p c5748 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3951] c5748 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3951 p h) (sat_nil p)))
def c5749 : List Lit := [(35, true), (46, false), (5, false), (73, false), (1691, false), (1530, false), (1593, false), (1605, false), (1510, true), (51, true), (1515, true), (103, false), (49, true), (1451, true)]
theorem step5749 (p : Nat → Bool) (h : Constraints p) : clause p c5749 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3617] c5749 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3617 p h) (sat_nil p)))
def c5750 : List Lit := [(1530, false), (1539, true), (73, false)]
theorem step5750 (p : Nat → Bool) (h : Constraints p) : clause p c5750 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3509] c5750 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3509 p h) (sat_nil p)))
def c5751 : List Lit := [(73, false), (1539, true), (51, true)]
theorem step5751 (p : Nat → Bool) (h : Constraints p) : clause p c5751 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3650] c5751 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3650 p h) (sat_nil p)))
def c5752 : List Lit := [(1539, true), (51, true), (46, true)]
theorem step5752 (p : Nat → Bool) (h : Constraints p) : clause p c5752 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3695] c5752 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3695 p h) (sat_nil p)))
def c5753 : List Lit := [(74, false), (42, false), (56, false), (39, true)]
theorem step5753 (p : Nat → Bool) (h : Constraints p) : clause p c5753 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3553] c5753 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3553 p h) (sat_nil p)))
def c5754 : List Lit := [(1516, false), (61, true), (1617, false), (1488, false), (1691, false), (1587, false), (1595, false)]
theorem step5754 (p : Nat → Bool) (h : Constraints p) : clause p c5754 = true :=
  Snake9.LocalRup.prove_clause [c5583, c4079] c5754 (by decide) p (sat_cons (step5583 p h) (sat_cons (step4079 p h) (sat_nil p)))
def c5755 : List Lit := [(46, true), (1541, true), (103, false), (73, false), (51, true)]
theorem step5755 (p : Nat → Bool) (h : Constraints p) : clause p c5755 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3974] c5755 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3974 p h) (sat_nil p)))
def c5756 : List Lit := [(1489, false), (1514, false), (1691, false), (73, false), (1617, false), (1593, false), (46, true), (51, true)]
theorem step5756 (p : Nat → Bool) (h : Constraints p) : clause p c5756 = true :=
  Snake9.LocalRup.prove_clause [c5583, c4167] c5756 (by decide) p (sat_cons (step5583 p h) (sat_cons (step4167 p h) (sat_nil p)))
def c5757 : List Lit := [(15, false), (73, false), (51, true), (1541, true), (46, true)]
theorem step5757 (p : Nat → Bool) (h : Constraints p) : clause p c5757 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3634] c5757 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3634 p h) (sat_nil p)))
def c5758 : List Lit := [(1530, false), (15, false), (1541, true), (51, true), (73, false)]
theorem step5758 (p : Nat → Bool) (h : Constraints p) : clause p c5758 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3754] c5758 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3754 p h) (sat_nil p)))
def c5759 : List Lit := [(46, true), (15, false), (73, false), (51, true), (1542, true), (1530, false)]
theorem step5759 (p : Nat → Bool) (h : Constraints p) : clause p c5759 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3598] c5759 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3598 p h) (sat_nil p)))
def c5760 : List Lit := [(15, false), (46, true), (51, true), (1540, true)]
theorem step5760 (p : Nat → Bool) (h : Constraints p) : clause p c5760 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3641] c5760 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3641 p h) (sat_nil p)))
def c5761 : List Lit := [(1490, false), (39, true), (1617, false), (1691, false), (1515, false), (1530, false)]
theorem step5761 (p : Nat → Bool) (h : Constraints p) : clause p c5761 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3541] c5761 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3541 p h) (sat_nil p)))
def c5762 : List Lit := [(73, false), (1538, true)]
theorem step5762 (p : Nat → Bool) (h : Constraints p) : clause p c5762 = true :=
  Snake9.LocalRup.prove_clause [c5583, c3868] c5762 (by decide) p (sat_cons (step5583 p h) (sat_cons (step3868 p h) (sat_nil p)))
def c5763 : List Lit := [(1515, false), (1488, false), (1691, false), (46, true), (51, true), (73, false), (1593, false), (1617, false)]
theorem step5763 (p : Nat → Bool) (h : Constraints p) : clause p c5763 = true :=
  Snake9.LocalRup.prove_clause [c5583, c4162] c5763 (by decide) p (sat_cons (step5583 p h) (sat_cons (step4162 p h) (sat_nil p)))
def c5764 : List Lit := [(38, true), (1569, true), (103, false), (51, true), (1530, false), (1594, true)]
theorem step5764 (p : Nat → Bool) (h : Constraints p) : clause p c5764 = true :=
  Snake9.LocalRup.prove_clause [c5583, c4386] c5764 (by decide) p (sat_cons (step5583 p h) (sat_cons (step4386 p h) (sat_nil p)))
def c5765 : List Lit := [(51, true), (1692, false), (103, false), (38, true), (1614, false)]
theorem step5765 (p : Nat → Bool) (h : Constraints p) : clause p c5765 = true :=
  Snake9.LocalRup.prove_clause [c5583, c4389] c5765 (by decide) p (sat_cons (step5583 p h) (sat_cons (step4389 p h) (sat_nil p)))
end B112E004
