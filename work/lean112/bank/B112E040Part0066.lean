import B112E040Part0065
namespace B112E040
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5749 : List Lit := [(38, false), (73, false), (111, false)]
theorem step5749 (p : Nat → Bool) (h : Constraints p) : clause p c5749 = true :=
  Snake9.LocalRup.prove_clause [c5234, c348] c5749 (by decide) p (sat_cons (step5234 p h) (sat_cons (step348 p h) (sat_nil p)))
def c5750 : List Lit := [(38, false), (73, false), (18, false)]
theorem step5750 (p : Nat → Bool) (h : Constraints p) : clause p c5750 = true :=
  Snake9.LocalRup.prove_clause [c5234, c325] c5750 (by decide) p (sat_cons (step5234 p h) (sat_cons (step325 p h) (sat_nil p)))
def c5751 : List Lit := [(42, false), (38, false), (34, false)]
theorem step5751 (p : Nat → Bool) (h : Constraints p) : clause p c5751 = true :=
  Snake9.LocalRup.prove_clause [c5234, c334] c5751 (by decide) p (sat_cons (step5234 p h) (sat_cons (step334 p h) (sat_nil p)))
def c5752 : List Lit := [(42, false), (73, false), (18, false)]
theorem step5752 (p : Nat → Bool) (h : Constraints p) : clause p c5752 = true :=
  Snake9.LocalRup.prove_clause [c5234, c330] c5752 (by decide) p (sat_cons (step5234 p h) (sat_cons (step330 p h) (sat_nil p)))
def c5753 : List Lit := [(42, false), (73, false), (111, false)]
theorem step5753 (p : Nat → Bool) (h : Constraints p) : clause p c5753 = true :=
  Snake9.LocalRup.prove_clause [c5234, c352] c5753 (by decide) p (sat_cons (step5234 p h) (sat_cons (step352 p h) (sat_nil p)))
def c5754 : List Lit := [(39, false), (73, false), (111, false)]
theorem step5754 (p : Nat → Bool) (h : Constraints p) : clause p c5754 = true :=
  Snake9.LocalRup.prove_clause [c5234, c351] c5754 (by decide) p (sat_cons (step5234 p h) (sat_cons (step351 p h) (sat_nil p)))
def c5755 : List Lit := [(39, false), (42, false), (34, false)]
theorem step5755 (p : Nat → Bool) (h : Constraints p) : clause p c5755 = true :=
  Snake9.LocalRup.prove_clause [c5234, c337] c5755 (by decide) p (sat_cons (step5234 p h) (sat_cons (step337 p h) (sat_nil p)))
def c5756 : List Lit := [(73, false), (18, false), (111, false)]
theorem step5756 (p : Nat → Bool) (h : Constraints p) : clause p c5756 = true :=
  Snake9.LocalRup.prove_clause [c5234, c332] c5756 (by decide) p (sat_cons (step5234 p h) (sat_cons (step332 p h) (sat_nil p)))
def c5757 : List Lit := [(34, false), (73, false), (111, false)]
theorem step5757 (p : Nat → Bool) (h : Constraints p) : clause p c5757 = true :=
  Snake9.LocalRup.prove_clause [c5234, c342] c5757 (by decide) p (sat_cons (step5234 p h) (sat_cons (step342 p h) (sat_nil p)))
def c5758 : List Lit := [(34, false), (73, false), (18, false)]
theorem step5758 (p : Nat → Bool) (h : Constraints p) : clause p c5758 = true :=
  Snake9.LocalRup.prove_clause [c5234, c321] c5758 (by decide) p (sat_cons (step5234 p h) (sat_cons (step321 p h) (sat_nil p)))
def c5759 : List Lit := [(1491, false), (80, true), (1647, false), (115, true), (37, true)]
theorem step5759 (p : Nat → Bool) (h : Constraints p) : clause p c5759 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2703] c5759 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2703 p h) (sat_nil p)))
def c5760 : List Lit := [(80, true), (1491, false), (1647, false), (1570, true), (115, true), (1594, false)]
theorem step5760 (p : Nat → Bool) (h : Constraints p) : clause p c5760 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3027] c5760 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3027 p h) (sat_nil p)))
def c5761 : List Lit := [(1490, false), (47, true), (80, true), (25, true)]
theorem step5761 (p : Nat → Bool) (h : Constraints p) : clause p c5761 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2628] c5761 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2628 p h) (sat_nil p)))
def c5762 : List Lit := [(1490, false), (47, true), (80, true), (1647, false), (25, true)]
theorem step5762 (p : Nat → Bool) (h : Constraints p) : clause p c5762 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2604] c5762 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2604 p h) (sat_nil p)))
def c5763 : List Lit := [(1490, false), (1520, false), (80, true), (1647, false), (37, true)]
theorem step5763 (p : Nat → Bool) (h : Constraints p) : clause p c5763 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2683] c5763 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2683 p h) (sat_nil p)))
def c5764 : List Lit := [(1515, true), (37, true)]
theorem step5764 (p : Nat → Bool) (h : Constraints p) : clause p c5764 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2673] c5764 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2673 p h) (sat_nil p)))
def c5765 : List Lit := [(1516, true), (37, true), (111, false)]
theorem step5765 (p : Nat → Bool) (h : Constraints p) : clause p c5765 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2463] c5765 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2463 p h) (sat_nil p)))
def c5766 : List Lit := [(18, false), (1517, true), (111, false), (37, true)]
theorem step5766 (p : Nat → Bool) (h : Constraints p) : clause p c5766 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2607] c5766 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2607 p h) (sat_nil p)))
def c5767 : List Lit := [(1570, true), (1538, false), (1594, false), (37, true), (1647, false), (1549, false), (80, true), (115, true), (1489, false)]
theorem step5767 (p : Nat → Bool) (h : Constraints p) : clause p c5767 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2499] c5767 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2499 p h) (sat_nil p)))
def c5768 : List Lit := [(1549, true), (1520, false), (37, true)]
theorem step5768 (p : Nat → Bool) (h : Constraints p) : clause p c5768 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2509] c5768 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2509 p h) (sat_nil p)))
def c5769 : List Lit := [(1505, true), (34, false)]
theorem step5769 (p : Nat → Bool) (h : Constraints p) : clause p c5769 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2542] c5769 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2542 p h) (sat_nil p)))
def c5770 : List Lit := [(80, true), (1490, false), (1594, false), (1647, false), (1549, false), (1539, false)]
theorem step5770 (p : Nat → Bool) (h : Constraints p) : clause p c5770 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2534] c5770 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2534 p h) (sat_nil p)))
def c5771 : List Lit := [(1665, false), (1520, false), (1647, false), (1490, false), (1594, true), (115, false), (80, true), (1711, true)]
theorem step5771 (p : Nat → Bool) (h : Constraints p) : clause p c5771 = true :=
  Snake9.LocalRup.prove_clause [c5236, c2491] c5771 (by decide) p (sat_cons (step5236 p h) (sat_cons (step2491 p h) (sat_nil p)))
def c5772 : List Lit := [(1505, true), (18, false)]
theorem step5772 (p : Nat → Bool) (h : Constraints p) : clause p c5772 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2665] c5772 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2665 p h) (sat_nil p)))
def c5773 : List Lit := [(1492, false), (80, true), (115, true), (1647, true), (37, true)]
theorem step5773 (p : Nat → Bool) (h : Constraints p) : clause p c5773 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3208] c5773 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3208 p h) (sat_nil p)))
def c5774 : List Lit := [(1570, true), (1456, false), (1463, false), (1538, false), (111, false), (37, true)]
theorem step5774 (p : Nat → Bool) (h : Constraints p) : clause p c5774 = true :=
  Snake9.LocalRup.prove_clause [c5234, c2630] c5774 (by decide) p (sat_cons (step5234 p h) (sat_cons (step2630 p h) (sat_nil p)))
def c5775 : List Lit := [(3, false), (25, true)]
theorem step5775 (p : Nat → Bool) (h : Constraints p) : clause p c5775 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4341] c5775 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4341 p h) (sat_nil p)))
def c5776 : List Lit := [(1456, false), (1680, false), (1647, false), (18, false), (24, false), (21, true), (39, true), (30, false), (1628, false), (29, true), (1465, false), (26, false), (37, true), (1569, true)]
theorem step5776 (p : Nat → Bool) (h : Constraints p) : clause p c5776 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3544] c5776 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3544 p h) (sat_nil p)))
def c5777 : List Lit := [(1628, false), (1618, false), (1647, false), (1456, false), (21, true), (1680, false), (1582, false), (18, false), (26, false), (37, true), (29, true), (1569, true)]
theorem step5777 (p : Nat → Bool) (h : Constraints p) : clause p c5777 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3552] c5777 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3552 p h) (sat_nil p)))
def c5778 : List Lit := [(1463, false), (1455, false), (1569, true), (1474, false), (37, true)]
theorem step5778 (p : Nat → Bool) (h : Constraints p) : clause p c5778 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4261] c5778 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4261 p h) (sat_nil p)))
def c5779 : List Lit := [(1491, false), (111, true), (80, false), (1594, false), (1647, false), (115, true)]
theorem step5779 (p : Nat → Bool) (h : Constraints p) : clause p c5779 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3799] c5779 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3799 p h) (sat_nil p)))
def c5780 : List Lit := [(1491, false), (111, true), (80, false), (1647, false), (1594, false), (115, true)]
theorem step5780 (p : Nat → Bool) (h : Constraints p) : clause p c5780 = true :=
  Snake9.LocalRup.prove_clause [c5236, c4013] c5780 (by decide) p (sat_cons (step5236 p h) (sat_cons (step4013 p h) (sat_nil p)))
def c5781 : List Lit := [(1491, false), (1690, false), (1627, false), (37, true), (80, false), (1711, true), (1663, false), (111, true), (1675, false)]
theorem step5781 (p : Nat → Bool) (h : Constraints p) : clause p c5781 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4349] c5781 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4349 p h) (sat_nil p)))
def c5782 : List Lit := [(80, true), (1594, false), (1647, false), (115, true), (37, true), (1490, false)]
theorem step5782 (p : Nat → Bool) (h : Constraints p) : clause p c5782 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3547] c5782 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3547 p h) (sat_nil p)))
def c5783 : List Lit := [(1490, false), (111, true), (16, false), (1647, false), (55, false), (115, true), (80, false), (1594, false), (50, true)]
theorem step5783 (p : Nat → Bool) (h : Constraints p) : clause p c5783 = true :=
  Snake9.LocalRup.prove_clause [c5236, c3898] c5783 (by decide) p (sat_cons (step5236 p h) (sat_cons (step3898 p h) (sat_nil p)))
def c5784 : List Lit := [(3, false), (1570, true), (115, true), (111, true), (37, true), (26, true), (16, false)]
theorem step5784 (p : Nat → Bool) (h : Constraints p) : clause p c5784 = true :=
  Snake9.LocalRup.prove_clause [c5234, c4358] c5784 (by decide) p (sat_cons (step5234 p h) (sat_cons (step4358 p h) (sat_nil p)))
def c5785 : List Lit := [(1570, true), (1455, false), (111, false), (1463, false), (37, true), (1473, false), (16, true)]
theorem step5785 (p : Nat → Bool) (h : Constraints p) : clause p c5785 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3942] c5785 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3942 p h) (sat_nil p)))
def c5786 : List Lit := [(1570, true), (1474, false), (16, true), (1455, false), (37, true), (1481, true), (1463, false)]
theorem step5786 (p : Nat → Bool) (h : Constraints p) : clause p c5786 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3934] c5786 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3934 p h) (sat_nil p)))
def c5787 : List Lit := [(1570, true), (1455, false), (1520, false), (37, true), (16, true), (1473, false), (1463, false)]
theorem step5787 (p : Nat → Bool) (h : Constraints p) : clause p c5787 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3937] c5787 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3937 p h) (sat_nil p)))
def c5788 : List Lit := [(1570, true), (1475, false), (37, true), (1456, false), (1480, true)]
theorem step5788 (p : Nat → Bool) (h : Constraints p) : clause p c5788 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3523] c5788 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3523 p h) (sat_nil p)))
def c5789 : List Lit := [(1627, false), (1480, true), (1455, false), (1656, false), (1463, false), (115, false), (16, true), (1594, true), (1473, false), (37, true)]
theorem step5789 (p : Nat → Bool) (h : Constraints p) : clause p c5789 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3573] c5789 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3573 p h) (sat_nil p)))
def c5790 : List Lit := [(1456, false), (80, true), (1594, false), (25, false), (21, true), (115, true), (16, false), (37, true), (5, true), (1647, false), (26, false)]
theorem step5790 (p : Nat → Bool) (h : Constraints p) : clause p c5790 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3553] c5790 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3553 p h) (sat_nil p)))
def c5791 : List Lit := [(12, true), (80, false), (16, false), (1647, false), (30, false), (1594, false), (18, false), (21, true), (37, false), (24, false), (6, true), (1473, false), (1448, false), (115, true), (111, true)]
theorem step5791 (p : Nat → Bool) (h : Constraints p) : clause p c5791 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3783] c5791 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3783 p h) (sat_nil p)))
def c5792 : List Lit := [(80, false), (1490, false), (1594, false), (1516, false), (37, true), (1571, true), (115, true), (1647, false)]
theorem step5792 (p : Nat → Bool) (h : Constraints p) : clause p c5792 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3761] c5792 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3761 p h) (sat_nil p)))
def c5793 : List Lit := [(6, false), (80, false), (1594, false), (1455, false), (30, true), (25, false), (115, true), (37, false), (111, true), (1647, false), (1469, false)]
theorem step5793 (p : Nat → Bool) (h : Constraints p) : clause p c5793 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3800] c5793 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3800 p h) (sat_nil p)))
def c5794 : List Lit := [(1570, true), (1480, true), (30, true), (1469, false), (1456, false), (25, false), (37, true), (1549, false), (63, false)]
theorem step5794 (p : Nat → Bool) (h : Constraints p) : clause p c5794 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3744] c5794 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3744 p h) (sat_nil p)))
def c5795 : List Lit := [(32, true), (1517, true), (111, false), (37, true)]
theorem step5795 (p : Nat → Bool) (h : Constraints p) : clause p c5795 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3500] c5795 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3500 p h) (sat_nil p)))
def c5796 : List Lit := [(32, true), (18, false), (1517, true), (37, true)]
theorem step5796 (p : Nat → Bool) (h : Constraints p) : clause p c5796 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3485] c5796 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3485 p h) (sat_nil p)))
def c5797 : List Lit := [(32, true), (1515, true)]
theorem step5797 (p : Nat → Bool) (h : Constraints p) : clause p c5797 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3641] c5797 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3641 p h) (sat_nil p)))
def c5798 : List Lit := [(28, false), (1516, true), (24, false), (37, true), (25, true), (32, true)]
theorem step5798 (p : Nat → Bool) (h : Constraints p) : clause p c5798 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3487] c5798 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3487 p h) (sat_nil p)))
def c5799 : List Lit := [(42, false), (32, false), (28, false), (23, false), (70, false), (25, true), (15, false)]
theorem step5799 (p : Nat → Bool) (h : Constraints p) : clause p c5799 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3437] c5799 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3437 p h) (sat_nil p)))
def c5800 : List Lit := [(1515, true), (18, false)]
theorem step5800 (p : Nat → Bool) (h : Constraints p) : clause p c5800 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3421] c5800 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3421 p h) (sat_nil p)))
def c5801 : List Lit := [(1573, true), (1455, false), (1473, false), (1463, false), (115, false), (37, true), (16, true), (111, false), (1594, true)]
theorem step5801 (p : Nat → Bool) (h : Constraints p) : clause p c5801 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3975] c5801 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3975 p h) (sat_nil p)))
def c5802 : List Lit := [(80, false), (1647, false), (1463, false), (115, false), (16, true), (1473, false), (37, true), (1455, false)]
theorem step5802 (p : Nat → Bool) (h : Constraints p) : clause p c5802 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3976] c5802 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3976 p h) (sat_nil p)))
def c5803 : List Lit := [(1539, false), (1490, false), (1647, false), (80, true), (115, true)]
theorem step5803 (p : Nat → Bool) (h : Constraints p) : clause p c5803 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3589] c5803 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3589 p h) (sat_nil p)))
def c5804 : List Lit := [(1570, true), (1539, false), (1455, false), (1473, false), (1463, false), (16, true)]
theorem step5804 (p : Nat → Bool) (h : Constraints p) : clause p c5804 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3977] c5804 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3977 p h) (sat_nil p)))
def c5805 : List Lit := [(1570, true), (1539, false), (1473, false), (1455, false), (37, true)]
theorem step5805 (p : Nat → Bool) (h : Constraints p) : clause p c5805 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3557] c5805 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3557 p h) (sat_nil p)))
def c5806 : List Lit := [(1570, true), (1539, false), (25, false), (1469, false), (1455, false), (16, true)]
theorem step5806 (p : Nat → Bool) (h : Constraints p) : clause p c5806 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3981] c5806 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3981 p h) (sat_nil p)))
def c5807 : List Lit := [(17, true), (1548, true), (28, true), (1469, false), (1481, true), (1463, false), (5, true), (37, false), (16, false)]
theorem step5807 (p : Nat → Bool) (h : Constraints p) : clause p c5807 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3425] c5807 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3425 p h) (sat_nil p)))
def c5808 : List Lit := [(1456, false), (80, true), (16, false), (1594, true), (5, true), (115, true), (26, false), (37, true), (6, true), (25, true), (1647, false)]
theorem step5808 (p : Nat → Bool) (h : Constraints p) : clause p c5808 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3543] c5808 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3543 p h) (sat_nil p)))
def c5809 : List Lit := [(80, true), (1594, false), (1474, false), (1647, false), (1455, false), (1463, false), (16, true)]
theorem step5809 (p : Nat → Bool) (h : Constraints p) : clause p c5809 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3424] c5809 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3424 p h) (sat_nil p)))
def c5810 : List Lit := [(80, true), (1474, false), (1455, false), (1463, false), (16, true), (1647, false), (37, true)]
theorem step5810 (p : Nat → Bool) (h : Constraints p) : clause p c5810 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3432] c5810 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3432 p h) (sat_nil p)))
def c5811 : List Lit := [(80, true), (1594, false), (1647, false), (16, true), (115, true), (1456, false), (1463, false), (1473, false)]
theorem step5811 (p : Nat → Bool) (h : Constraints p) : clause p c5811 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3651] c5811 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3651 p h) (sat_nil p)))
def c5812 : List Lit := [(80, true), (1594, true), (1647, false), (1456, false), (115, true), (37, false)]
theorem step5812 (p : Nat → Bool) (h : Constraints p) : clause p c5812 = true :=
  Snake9.LocalRup.prove_clause [c5234, c3592] c5812 (by decide) p (sat_cons (step5234 p h) (sat_cons (step3592 p h) (sat_nil p)))
end B112E040
