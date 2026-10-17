import B112E089Part0245
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c17756 : List Lit := [(1615, true), (75, true), (32, true), (158, true)]
theorem step17756 (p : Nat → Bool) (h : Constraints p) : clause p c17756 = true :=
  Snake9.LocalRup.prove_clause [c16983, c5796] c17756 (by decide) p (sat_cons (step16983 p h) (sat_cons (step5796 p h) (sat_nil p)))
def c17757 : List Lit := [(1569, false), (1588, false), (169, true), (1593, false), (50, true), (1617, true)]
theorem step17757 (p : Nat → Bool) (h : Constraints p) : clause p c17757 = true :=
  Snake9.LocalRup.prove_clause [c16983, c2787] c17757 (by decide) p (sat_cons (step16983 p h) (sat_cons (step2787 p h) (sat_nil p)))
def c17758 : List Lit := [(1577, false), (75, true), (158, true), (32, true), (1617, true)]
theorem step17758 (p : Nat → Bool) (h : Constraints p) : clause p c17758 = true :=
  Snake9.LocalRup.prove_clause [c16983, c3356] c17758 (by decide) p (sat_cons (step16983 p h) (sat_cons (step3356 p h) (sat_nil p)))
def c17759 : List Lit := [(1582, false), (51, true), (1761, false), (1553, false), (1751, false), (1699, false), (455, true)]
theorem step17759 (p : Nat → Bool) (h : Constraints p) : clause p c17759 = true :=
  Snake9.LocalRup.prove_clause [c16983, c3533] c17759 (by decide) p (sat_cons (step16983 p h) (sat_cons (step3533 p h) (sat_nil p)))
def c17760 : List Lit := [(1576, false), (51, true), (158, true), (32, true), (75, true), (1617, true)]
theorem step17760 (p : Nat → Bool) (h : Constraints p) : clause p c17760 = true :=
  Snake9.LocalRup.prove_clause [c16983, c3320] c17760 (by decide) p (sat_cons (step16983 p h) (sat_cons (step3320 p h) (sat_nil p)))
def c17761 : List Lit := [(51, true), (56, true), (45, false), (1608, true), (55, false), (1588, false)]
theorem step17761 (p : Nat → Bool) (h : Constraints p) : clause p c17761 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13355] c17761 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13355 p h) (sat_nil p)))
def c17762 : List Lit := [(1578, false), (75, false), (1617, true), (158, true)]
theorem step17762 (p : Nat → Bool) (h : Constraints p) : clause p c17762 = true :=
  Snake9.LocalRup.prove_clause [c16983, c2982] c17762 (by decide) p (sat_cons (step16983 p h) (sat_cons (step2982 p h) (sat_nil p)))
def c17763 : List Lit := [(75, false), (73, false), (49, false), (333, true), (103, false), (1617, true)]
theorem step17763 (p : Nat → Bool) (h : Constraints p) : clause p c17763 = true :=
  Snake9.LocalRup.prove_clause [c16983, c3398] c17763 (by decide) p (sat_cons (step16983 p h) (sat_cons (step3398 p h) (sat_nil p)))
def c17764 : List Lit := [(43, false), (64, false), (1574, false), (96, false), (1617, true)]
theorem step17764 (p : Nat → Bool) (h : Constraints p) : clause p c17764 = true :=
  Snake9.LocalRup.prove_clause [c16982, c3258] c17764 (by decide) p (sat_cons (step16982 p h) (sat_cons (step3258 p h) (sat_nil p)))
def c17765 : List Lit := [(51, true), (1614, true)]
theorem step17765 (p : Nat → Bool) (h : Constraints p) : clause p c17765 = true :=
  Snake9.LocalRup.prove_clause [c16983, c4720] c17765 (by decide) p (sat_cons (step16983 p h) (sat_cons (step4720 p h) (sat_nil p)))
def c17766 : List Lit := [(1574, false), (75, true), (1617, true), (158, true), (32, true)]
theorem step17766 (p : Nat → Bool) (h : Constraints p) : clause p c17766 = true :=
  Snake9.LocalRup.prove_clause [c16982, c4499] c17766 (by decide) p (sat_cons (step16982 p h) (sat_cons (step4499 p h) (sat_nil p)))
def c17767 : List Lit := [(32, true), (158, true), (1616, true), (51, true), (75, true)]
theorem step17767 (p : Nat → Bool) (h : Constraints p) : clause p c17767 = true :=
  Snake9.LocalRup.prove_clause [c16983, c5841] c17767 (by decide) p (sat_cons (step16983 p h) (sat_cons (step5841 p h) (sat_nil p)))
def c17768 : List Lit := [(51, true), (1577, false), (1616, true)]
theorem step17768 (p : Nat → Bool) (h : Constraints p) : clause p c17768 = true :=
  Snake9.LocalRup.prove_clause [c16983, c3972] c17768 (by decide) p (sat_cons (step16983 p h) (sat_cons (step3972 p h) (sat_nil p)))
def c17769 : List Lit := [(1615, true), (51, true), (1576, false)]
theorem step17769 (p : Nat → Bool) (h : Constraints p) : clause p c17769 = true :=
  Snake9.LocalRup.prove_clause [c16983, c4725] c17769 (by decide) p (sat_cons (step16983 p h) (sat_cons (step4725 p h) (sat_nil p)))
def c17770 : List Lit := [(1614, true), (1580, false), (115, false), (51, false)]
theorem step17770 (p : Nat → Bool) (h : Constraints p) : clause p c17770 = true :=
  Snake9.LocalRup.prove_clause [c16983, c13823] c17770 (by decide) p (sat_cons (step16983 p h) (sat_cons (step13823 p h) (sat_nil p)))
def c17771 : List Lit := [(1569, false), (175, true), (45, true), (1616, true)]
theorem step17771 (p : Nat → Bool) (h : Constraints p) : clause p c17771 = true :=
  Snake9.LocalRup.prove_clause [c16982, c4426] c17771 (by decide) p (sat_cons (step16982 p h) (sat_cons (step4426 p h) (sat_nil p)))
def c17772 : List Lit := [(1615, true), (45, true)]
theorem step17772 (p : Nat → Bool) (h : Constraints p) : clause p c17772 = true :=
  Snake9.LocalRup.prove_clause [c16982, c16983, c5132] c17772 (by decide) p (sat_cons (step16982 p h) (sat_cons (step16983 p h) (sat_cons (step5132 p h) (sat_nil p))))
def c17773 : List Lit := [(1615, true), (1568, false), (103, false), (1592, false)]
theorem step17773 (p : Nat → Bool) (h : Constraints p) : clause p c17773 = true :=
  Snake9.LocalRup.prove_clause [c16982, c4791] c17773 (by decide) p (sat_cons (step16982 p h) (sat_cons (step4791 p h) (sat_nil p)))
def c17774 : List Lit := [(1564, false), (51, true), (1616, true), (1576, false)]
theorem step17774 (p : Nat → Bool) (h : Constraints p) : clause p c17774 = true :=
  Snake9.LocalRup.prove_clause [c16983, c5696] c17774 (by decide) p (sat_cons (step16983 p h) (sat_cons (step5696 p h) (sat_nil p)))
def c17775 : List Lit := [(1564, false), (1577, false), (1616, true)]
theorem step17775 (p : Nat → Bool) (h : Constraints p) : clause p c17775 = true :=
  Snake9.LocalRup.prove_clause [c16983, c5669] c17775 (by decide) p (sat_cons (step16983 p h) (sat_cons (step5669 p h) (sat_nil p)))
def c17776 : List Lit := [(1578, false), (1616, true)]
theorem step17776 (p : Nat → Bool) (h : Constraints p) : clause p c17776 = true :=
  Snake9.LocalRup.prove_clause [c16983, c7824] c17776 (by decide) p (sat_cons (step16983 p h) (sat_cons (step7824 p h) (sat_nil p)))
def c17777 : List Lit := [(56, true), (1568, false), (1617, true), (1581, false), (51, false), (1592, false), (45, true), (1606, false)]
theorem step17777 (p : Nat → Bool) (h : Constraints p) : clause p c17777 = true :=
  Snake9.LocalRup.prove_clause [c16982, c7291] c17777 (by decide) p (sat_cons (step16982 p h) (sat_cons (step7291 p h) (sat_nil p)))
def c17778 : List Lit := [(60, true), (51, true), (57, false), (103, false), (1617, true), (197, true), (1657, true), (1576, false)]
theorem step17778 (p : Nat → Bool) (h : Constraints p) : clause p c17778 = true :=
  Snake9.LocalRup.prove_clause [c16983, c6740] c17778 (by decide) p (sat_cons (step16983 p h) (sat_cons (step6740 p h) (sat_nil p)))
def c17779 : List Lit := [(45, true), (54, false), (1616, true), (175, true), (1572, false), (1578, true), (74, true)]
theorem step17779 (p : Nat → Bool) (h : Constraints p) : clause p c17779 = true :=
  Snake9.LocalRup.prove_clause [c16983, c7783] c17779 (by decide) p (sat_cons (step16983 p h) (sat_cons (step7783 p h) (sat_nil p)))
def c17780 : List Lit := [(64, false), (1574, false), (1578, true), (58, true), (63, true), (51, true), (188, true), (1617, true)]
theorem step17780 (p : Nat → Bool) (h : Constraints p) : clause p c17780 = true :=
  Snake9.LocalRup.prove_clause [c16982, c7402] c17780 (by decide) p (sat_cons (step16982 p h) (sat_cons (step7402 p h) (sat_nil p)))
def c17781 : List Lit := [(1601, true), (64, false), (63, true), (1578, true), (188, true)]
theorem step17781 (p : Nat → Bool) (h : Constraints p) : clause p c17781 = true :=
  Snake9.LocalRup.prove_clause [c16982, c7387] c17781 (by decide) p (sat_cons (step16982 p h) (sat_cons (step7387 p h) (sat_nil p)))
def c17782 : List Lit := [(1576, false), (51, true), (49, false), (103, false), (1619, true), (158, true), (75, true), (73, false), (32, true)]
theorem step17782 (p : Nat → Bool) (h : Constraints p) : clause p c17782 = true :=
  Snake9.LocalRup.prove_clause [c16983, c10699] c17782 (by decide) p (sat_cons (step16983 p h) (sat_cons (step10699 p h) (sat_nil p)))
def c17783 : List Lit := [(75, false), (51, true), (1577, false), (74, true), (1617, true)]
theorem step17783 (p : Nat → Bool) (h : Constraints p) : clause p c17783 = true :=
  Snake9.LocalRup.prove_clause [c16983, c8834] c17783 (by decide) p (sat_cons (step16983 p h) (sat_cons (step8834 p h) (sat_nil p)))
def c17784 : List Lit := [(75, false), (1577, false), (1616, true), (74, true)]
theorem step17784 (p : Nat → Bool) (h : Constraints p) : clause p c17784 = true :=
  Snake9.LocalRup.prove_clause [c16983, c9951] c17784 (by decide) p (sat_cons (step16983 p h) (sat_cons (step9951 p h) (sat_nil p)))
def c17785 : List Lit := [(75, false), (45, true), (1617, true), (365, true), (51, true)]
theorem step17785 (p : Nat → Bool) (h : Constraints p) : clause p c17785 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13009] c17785 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13009 p h) (sat_nil p)))
def c17786 : List Lit := [(45, true), (1568, false), (1593, false), (1617, true), (51, false)]
theorem step17786 (p : Nat → Bool) (h : Constraints p) : clause p c17786 = true :=
  Snake9.LocalRup.prove_clause [c16982, c16983, c12959] c17786 (by decide) p (sat_cons (step16982 p h) (sat_cons (step16983 p h) (sat_cons (step12959 p h) (sat_nil p))))
def c17787 : List Lit := [(1606, true), (1577, true), (1572, true), (103, false)]
theorem step17787 (p : Nat → Bool) (h : Constraints p) : clause p c17787 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13192] c17787 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13192 p h) (sat_nil p)))
def c17788 : List Lit := [(14, false), (1577, false), (103, false), (49, false), (1617, true)]
theorem step17788 (p : Nat → Bool) (h : Constraints p) : clause p c17788 = true :=
  Snake9.LocalRup.prove_clause [c16983, c13667] c17788 (by decide) p (sat_cons (step16983 p h) (sat_cons (step13667 p h) (sat_nil p)))
def c17789 : List Lit := [(75, false), (46, true), (49, false), (72, false), (1665, false), (74, true), (1601, false), (427, false), (73, false)]
theorem step17789 (p : Nat → Bool) (h : Constraints p) : clause p c17789 = true :=
  Snake9.LocalRup.prove_clause [c16983, c16643] c17789 (by decide) p (sat_cons (step16983 p h) (sat_cons (step16643 p h) (sat_nil p)))
def c17790 : List Lit := [(75, false), (73, false), (1576, false), (74, true), (1616, true), (49, false)]
theorem step17790 (p : Nat → Bool) (h : Constraints p) : clause p c17790 = true :=
  Snake9.LocalRup.prove_clause [c16983, c12736] c17790 (by decide) p (sat_cons (step16983 p h) (sat_cons (step12736 p h) (sat_nil p)))
def c17791 : List Lit := [(45, true), (46, true), (1616, true), (51, true), (347, true), (1607, true)]
theorem step17791 (p : Nat → Bool) (h : Constraints p) : clause p c17791 = true :=
  Snake9.LocalRup.prove_clause [c16983, c13337] c17791 (by decide) p (sat_cons (step16983 p h) (sat_cons (step13337 p h) (sat_nil p)))
def c17792 : List Lit := [(1576, false), (44, false), (1616, true), (347, true), (51, true), (1594, true), (1595, true), (46, true)]
theorem step17792 (p : Nat → Bool) (h : Constraints p) : clause p c17792 = true :=
  Snake9.LocalRup.prove_clause [c16983, c12028] c17792 (by decide) p (sat_cons (step16983 p h) (sat_cons (step12028 p h) (sat_nil p)))
def c17793 : List Lit := [(1666, true), (1650, true), (487, false), (74, false), (62, true), (1638, true)]
theorem step17793 (p : Nat → Bool) (h : Constraints p) : clause p c17793 = true :=
  Snake9.LocalRup.prove_clause [c16983, c12984] c17793 (by decide) p (sat_cons (step16983 p h) (sat_cons (step12984 p h) (sat_nil p)))
def c17794 : List Lit := [(1617, true), (197, true), (75, false), (333, true), (103, false), (1657, true), (71, true), (32, true), (74, false), (1570, true)]
theorem step17794 (p : Nat → Bool) (h : Constraints p) : clause p c17794 = true :=
  Snake9.LocalRup.prove_clause [c16983, c12929] c17794 (by decide) p (sat_cons (step16983 p h) (sat_cons (step12929 p h) (sat_nil p)))
def c17795 : List Lit := [(1614, true), (175, true), (74, true)]
theorem step17795 (p : Nat → Bool) (h : Constraints p) : clause p c17795 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13532] c17795 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13532 p h) (sat_nil p)))
def c17796 : List Lit := [(46, true), (1601, true), (51, true), (1616, true), (45, false), (39, false), (1568, false)]
theorem step17796 (p : Nat → Bool) (h : Constraints p) : clause p c17796 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13692] c17796 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13692 p h) (sat_nil p)))
def c17797 : List Lit := [(1574, false), (1601, true), (27, true), (74, true), (1554, true), (367, true), (75, true), (113, false), (1617, true)]
theorem step17797 (p : Nat → Bool) (h : Constraints p) : clause p c17797 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13444] c17797 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13444 p h) (sat_nil p)))
def c17798 : List Lit := [(1615, true), (75, false), (74, false), (1576, false)]
theorem step17798 (p : Nat → Bool) (h : Constraints p) : clause p c17798 = true :=
  Snake9.LocalRup.prove_clause [c16983, c12927] c17798 (by decide) p (sat_cons (step16983 p h) (sat_cons (step12927 p h) (sat_nil p)))
def c17799 : List Lit := [(1554, true), (1576, false), (27, true), (74, true), (1616, true), (367, true), (75, true)]
theorem step17799 (p : Nat → Bool) (h : Constraints p) : clause p c17799 = true :=
  Snake9.LocalRup.prove_clause [c16983, c13419] c17799 (by decide) p (sat_cons (step16983 p h) (sat_cons (step13419 p h) (sat_nil p)))
def c17800 : List Lit := [(1615, true), (1577, false)]
theorem step17800 (p : Nat → Bool) (h : Constraints p) : clause p c17800 = true :=
  Snake9.LocalRup.prove_clause [c16983, c12819] c17800 (by decide) p (sat_cons (step16983 p h) (sat_cons (step12819 p h) (sat_nil p)))
def c17801 : List Lit := [(44, true), (75, false), (103, false), (365, true), (74, true), (1617, true)]
theorem step17801 (p : Nat → Bool) (h : Constraints p) : clause p c17801 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13183] c17801 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13183 p h) (sat_nil p)))
def c17802 : List Lit := [(44, true), (75, false), (51, false), (74, true), (103, false), (1617, true)]
theorem step17802 (p : Nat → Bool) (h : Constraints p) : clause p c17802 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13187] c17802 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13187 p h) (sat_nil p)))
def c17803 : List Lit := [(75, false), (44, false), (103, false), (365, true), (1572, true), (74, true), (1577, true), (1616, true), (45, false), (1606, false)]
theorem step17803 (p : Nat → Bool) (h : Constraints p) : clause p c17803 = true :=
  Snake9.LocalRup.prove_clause [c16983, c13193] c17803 (by decide) p (sat_cons (step16983 p h) (sat_cons (step13193 p h) (sat_nil p)))
def c17804 : List Lit := [(75, false), (395, false), (1726, true), (1572, true), (1691, true), (1617, true), (73, false), (91, true)]
theorem step17804 (p : Nat → Bool) (h : Constraints p) : clause p c17804 = true :=
  Snake9.LocalRup.prove_clause [c16983, c12922] c17804 (by decide) p (sat_cons (step16983 p h) (sat_cons (step12922 p h) (sat_nil p)))
def c17805 : List Lit := [(1601, false), (1607, true), (73, false), (74, true), (56, true), (175, true), (40, true)]
theorem step17805 (p : Nat → Bool) (h : Constraints p) : clause p c17805 = true :=
  Snake9.LocalRup.prove_clause [c16982, c12466] c17805 (by decide) p (sat_cons (step16982 p h) (sat_cons (step12466 p h) (sat_nil p)))
def c17806 : List Lit := [(1657, true), (1576, false), (61, true), (75, false), (1617, true), (74, false), (103, false), (32, true), (1593, false)]
theorem step17806 (p : Nat → Bool) (h : Constraints p) : clause p c17806 = true :=
  Snake9.LocalRup.prove_clause [c16983, c12907] c17806 (by decide) p (sat_cons (step16983 p h) (sat_cons (step12907 p h) (sat_nil p)))
def c17807 : List Lit := [(1576, false), (32, true), (103, false), (1616, true), (75, true)]
theorem step17807 (p : Nat → Bool) (h : Constraints p) : clause p c17807 = true :=
  Snake9.LocalRup.prove_clause [c16983, c13073] c17807 (by decide) p (sat_cons (step16983 p h) (sat_cons (step13073 p h) (sat_nil p)))
def c17808 : List Lit := [(1574, false), (51, true), (1617, true), (1568, false), (1726, true), (73, false), (1691, true), (439, true), (227, true), (415, true), (91, true)]
theorem step17808 (p : Nat → Bool) (h : Constraints p) : clause p c17808 = true :=
  Snake9.LocalRup.prove_clause [c16983, c12914] c17808 (by decide) p (sat_cons (step16983 p h) (sat_cons (step12914 p h) (sat_nil p)))
def c17809 : List Lit := [(1576, false), (46, true), (1639, true), (367, true), (32, true), (56, true), (72, false), (1554, true)]
theorem step17809 (p : Nat → Bool) (h : Constraints p) : clause p c17809 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13290] c17809 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13290 p h) (sat_nil p)))
def c17810 : List Lit := [(46, true), (1580, true), (73, false), (49, false), (1577, true), (1608, true)]
theorem step17810 (p : Nat → Bool) (h : Constraints p) : clause p c17810 = true :=
  Snake9.LocalRup.prove_clause [c16982, c16136] c17810 (by decide) p (sat_cons (step16982 p h) (sat_cons (step16136 p h) (sat_nil p)))
def c17811 : List Lit := [(73, false), (45, true), (103, false), (1568, false), (1617, true), (49, false)]
theorem step17811 (p : Nat → Bool) (h : Constraints p) : clause p c17811 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13882] c17811 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13882 p h) (sat_nil p)))
def c17812 : List Lit := [(73, false), (45, true), (1617, true), (103, false), (49, false)]
theorem step17812 (p : Nat → Bool) (h : Constraints p) : clause p c17812 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13960] c17812 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13960 p h) (sat_nil p)))
def c17813 : List Lit := [(75, false), (1577, false), (74, true), (73, false), (175, true), (49, false), (1619, true), (103, false)]
theorem step17813 (p : Nat → Bool) (h : Constraints p) : clause p c17813 = true :=
  Snake9.LocalRup.prove_clause [c16982, c15365] c17813 (by decide) p (sat_cons (step16982 p h) (sat_cons (step15365 p h) (sat_nil p)))
def c17814 : List Lit := [(57, false), (60, true), (1605, false), (1574, false), (1594, true), (163, true), (168, true), (103, false), (1616, true), (44, false), (65, true), (1577, true), (73, false)]
theorem step17814 (p : Nat → Bool) (h : Constraints p) : clause p c17814 = true :=
  Snake9.LocalRup.prove_clause [c16982, c15855] c17814 (by decide) p (sat_cons (step16982 p h) (sat_cons (step15855 p h) (sat_nil p)))
def c17815 : List Lit := [(46, true), (73, false), (1617, true), (49, false), (45, true)]
theorem step17815 (p : Nat → Bool) (h : Constraints p) : clause p c17815 = true :=
  Snake9.LocalRup.prove_clause [c16982, c16983, c16115] c17815 (by decide) p (sat_cons (step16982 p h) (sat_cons (step16983 p h) (sat_cons (step16115 p h) (sat_nil p))))
def c17816 : List Lit := [(1568, false), (1574, false), (1616, true), (103, false), (1605, false)]
theorem step17816 (p : Nat → Bool) (h : Constraints p) : clause p c17816 = true :=
  Snake9.LocalRup.prove_clause [c16982, c13884] c17816 (by decide) p (sat_cons (step16982 p h) (sat_cons (step13884 p h) (sat_nil p)))
def c17817 : List Lit := [(1615, true), (1576, false), (175, true), (74, true)]
theorem step17817 (p : Nat → Bool) (h : Constraints p) : clause p c17817 = true :=
  Snake9.LocalRup.prove_clause [c16982, c14658] c17817 (by decide) p (sat_cons (step16982 p h) (sat_cons (step14658 p h) (sat_nil p)))
def c17818 : List Lit := [(1576, false), (51, true), (46, true), (1616, true), (347, true)]
theorem step17818 (p : Nat → Bool) (h : Constraints p) : clause p c17818 = true :=
  Snake9.LocalRup.prove_clause [c16982, c15743] c17818 (by decide) p (sat_cons (step16982 p h) (sat_cons (step15743 p h) (sat_nil p)))
def c17819 : List Lit := [(1637, true), (1574, false), (27, true), (367, true), (1615, false), (75, true)]
theorem step17819 (p : Nat → Bool) (h : Constraints p) : clause p c17819 = true :=
  Snake9.LocalRup.prove_clause [c16982, c16983, c13967] c17819 (by decide) p (sat_cons (step16982 p h) (sat_cons (step16983 p h) (sat_cons (step13967 p h) (sat_nil p))))
end B112E089
