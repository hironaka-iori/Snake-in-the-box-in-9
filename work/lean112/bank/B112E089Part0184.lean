import B112E089Part0183
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c13788 : List Lit := [(55, false), (43, false), (45, false)]
theorem step13788 (p : Nat → Bool) (h : Constraints p) : clause p c13788 = true :=
  Snake9.LocalRup.prove_clause [c12893, c298] c13788 (by decide) p (sat_cons (step12893 p h) (sat_cons (step298 p h) (sat_nil p)))
def c13789 : List Lit := [(35, false), (26, false), (27, false)]
theorem step13789 (p : Nat → Bool) (h : Constraints p) : clause p c13789 = true :=
  Snake9.LocalRup.prove_clause [c12893, c160] c13789 (by decide) p (sat_cons (step12893 p h) (sat_cons (step160 p h) (sat_nil p)))
def c13790 : List Lit := [(115, true), (27, true), (45, true), (66, true), (64, true), (67, true)]
theorem step13790 (p : Nat → Bool) (h : Constraints p) : clause p c13790 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2244] c13790 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2244 p h) (sat_nil p)))
def c13791 : List Lit := [(78, false), (26, false), (67, false)]
theorem step13791 (p : Nat → Bool) (h : Constraints p) : clause p c13791 = true :=
  Snake9.LocalRup.prove_clause [c12893, c581] c13791 (by decide) p (sat_cons (step12893 p h) (sat_cons (step581 p h) (sat_nil p)))
def c13792 : List Lit := [(114, false), (65, false), (67, false)]
theorem step13792 (p : Nat → Bool) (h : Constraints p) : clause p c13792 = true :=
  Snake9.LocalRup.prove_clause [c12893, c589] c13792 (by decide) p (sat_cons (step12893 p h) (sat_cons (step589 p h) (sat_nil p)))
def c13793 : List Lit := [(65, false), (78, false), (67, false)]
theorem step13793 (p : Nat → Bool) (h : Constraints p) : clause p c13793 = true :=
  Snake9.LocalRup.prove_clause [c12893, c588] c13793 (by decide) p (sat_cons (step12893 p h) (sat_cons (step588 p h) (sat_nil p)))
def c13794 : List Lit := [(66, false), (67, false), (61, false)]
theorem step13794 (p : Nat → Bool) (h : Constraints p) : clause p c13794 = true :=
  Snake9.LocalRup.prove_clause [c12893, c621] c13794 (by decide) p (sat_cons (step12893 p h) (sat_cons (step621 p h) (sat_nil p)))
def c13795 : List Lit := [(64, false), (66, false), (27, false)]
theorem step13795 (p : Nat → Bool) (h : Constraints p) : clause p c13795 = true :=
  Snake9.LocalRup.prove_clause [c12893, c602] c13795 (by decide) p (sat_cons (step12893 p h) (sat_cons (step602 p h) (sat_nil p)))
def c13796 : List Lit := [(66, false), (27, false), (61, false)]
theorem step13796 (p : Nat → Bool) (h : Constraints p) : clause p c13796 = true :=
  Snake9.LocalRup.prove_clause [c12893, c599] c13796 (by decide) p (sat_cons (step12893 p h) (sat_cons (step599 p h) (sat_nil p)))
def c13797 : List Lit := [(66, false), (61, false), (45, false)]
theorem step13797 (p : Nat → Bool) (h : Constraints p) : clause p c13797 = true :=
  Snake9.LocalRup.prove_clause [c12893, c609] c13797 (by decide) p (sat_cons (step12893 p h) (sat_cons (step609 p h) (sat_nil p)))
def c13798 : List Lit := [(66, false), (64, false), (45, false)]
theorem step13798 (p : Nat → Bool) (h : Constraints p) : clause p c13798 = true :=
  Snake9.LocalRup.prove_clause [c12893, c612] c13798 (by decide) p (sat_cons (step12893 p h) (sat_cons (step612 p h) (sat_nil p)))
def c13799 : List Lit := [(59, false), (77, false), (66, false)]
theorem step13799 (p : Nat → Bool) (h : Constraints p) : clause p c13799 = true :=
  Snake9.LocalRup.prove_clause [c12893, c568] c13799 (by decide) p (sat_cons (step12893 p h) (sat_cons (step568 p h) (sat_nil p)))
def c13800 : List Lit := [(58, false), (64, false), (61, false)]
theorem step13800 (p : Nat → Bool) (h : Constraints p) : clause p c13800 = true :=
  Snake9.LocalRup.prove_clause [c12893, c1988] c13800 (by decide) p (sat_cons (step12893 p h) (sat_cons (step1988 p h) (sat_nil p)))
def c13801 : List Lit := [(59, false), (66, false), (61, false)]
theorem step13801 (p : Nat → Bool) (h : Constraints p) : clause p c13801 = true :=
  Snake9.LocalRup.prove_clause [c12893, c1989] c13801 (by decide) p (sat_cons (step12893 p h) (sat_cons (step1989 p h) (sat_nil p)))
def c13802 : List Lit := [(114, false), (78, false), (67, false)]
theorem step13802 (p : Nat → Bool) (h : Constraints p) : clause p c13802 = true :=
  Snake9.LocalRup.prove_clause [c12893, c591] c13802 (by decide) p (sat_cons (step12893 p h) (sat_cons (step591 p h) (sat_nil p)))
def c13803 : List Lit := [(1651, true), (27, false), (61, false)]
theorem step13803 (p : Nat → Bool) (h : Constraints p) : clause p c13803 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2566] c13803 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2566 p h) (sat_nil p)))
def c13804 : List Lit := [(115, false), (27, false), (1657, false), (1667, true), (69, true)]
theorem step13804 (p : Nat → Bool) (h : Constraints p) : clause p c13804 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2653] c13804 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2653 p h) (sat_nil p)))
def c13805 : List Lit := [(27, false), (1650, true)]
theorem step13805 (p : Nat → Bool) (h : Constraints p) : clause p c13805 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2620] c13805 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2620 p h) (sat_nil p)))
def c13806 : List Lit := [(67, false), (27, false), (1670, true), (1575, true), (74, true), (200, true)]
theorem step13806 (p : Nat → Bool) (h : Constraints p) : clause p c13806 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2845] c13806 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2845 p h) (sat_nil p)))
def c13807 : List Lit := [(67, false), (1651, true), (61, false)]
theorem step13807 (p : Nat → Bool) (h : Constraints p) : clause p c13807 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3433] c13807 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3433 p h) (sat_nil p)))
def c13808 : List Lit := [(67, false), (1651, true), (45, false)]
theorem step13808 (p : Nat → Bool) (h : Constraints p) : clause p c13808 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3420] c13808 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3420 p h) (sat_nil p)))
def c13809 : List Lit := [(115, false), (67, false), (1651, true)]
theorem step13809 (p : Nat → Bool) (h : Constraints p) : clause p c13809 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3406] c13809 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3406 p h) (sat_nil p)))
def c13810 : List Lit := [(1650, true), (115, false)]
theorem step13810 (p : Nat → Bool) (h : Constraints p) : clause p c13810 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3360] c13810 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3360 p h) (sat_nil p)))
def c13811 : List Lit := [(1667, true), (62, true), (64, true), (1657, false), (45, false), (27, false)]
theorem step13811 (p : Nat → Bool) (h : Constraints p) : clause p c13811 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2873] c13811 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2873 p h) (sat_nil p)))
def c13812 : List Lit := [(27, false), (1651, true), (45, false)]
theorem step13812 (p : Nat → Bool) (h : Constraints p) : clause p c13812 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3488] c13812 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3488 p h) (sat_nil p)))
def c13813 : List Lit := [(115, false), (1651, true), (45, false)]
theorem step13813 (p : Nat → Bool) (h : Constraints p) : clause p c13813 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3318] c13813 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3318 p h) (sat_nil p)))
def c13814 : List Lit := [(115, false), (1651, true), (27, false)]
theorem step13814 (p : Nat → Bool) (h : Constraints p) : clause p c13814 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3471] c13814 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3471 p h) (sat_nil p)))
def c13815 : List Lit := [(115, false), (44, true), (1593, false), (1617, true), (1572, false), (1596, false)]
theorem step13815 (p : Nat → Bool) (h : Constraints p) : clause p c13815 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2972] c13815 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2972 p h) (sat_nil p)))
def c13816 : List Lit := [(115, false), (44, true), (1572, false), (1568, false), (1593, false), (1617, true)]
theorem step13816 (p : Nat → Bool) (h : Constraints p) : clause p c13816 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3005] c13816 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3005 p h) (sat_nil p)))
def c13817 : List Lit := [(115, false), (32, true), (51, true), (158, true), (1651, true), (75, true), (1617, true)]
theorem step13817 (p : Nat → Bool) (h : Constraints p) : clause p c13817 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3348] c13817 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3348 p h) (sat_nil p)))
def c13818 : List Lit := [(1580, true), (51, false), (1606, true), (115, false)]
theorem step13818 (p : Nat → Bool) (h : Constraints p) : clause p c13818 = true :=
  Snake9.LocalRup.prove_clause [c12893, c4555] c13818 (by decide) p (sat_cons (step12893 p h) (sat_cons (step4555 p h) (sat_nil p)))
def c13819 : List Lit := [(67, false), (49, true), (45, false), (1599, true), (163, true), (42, false), (39, false)]
theorem step13819 (p : Nat → Bool) (h : Constraints p) : clause p c13819 = true :=
  Snake9.LocalRup.prove_clause [c12893, c4529] c13819 (by decide) p (sat_cons (step12893 p h) (sat_cons (step4529 p h) (sat_nil p)))
def c13820 : List Lit := [(169, false), (52, true), (54, false), (43, true)]
theorem step13820 (p : Nat → Bool) (h : Constraints p) : clause p c13820 = true :=
  Snake9.LocalRup.prove_clause [c12893, c4623] c13820 (by decide) p (sat_cons (step12893 p h) (sat_cons (step4623 p h) (sat_nil p)))
def c13821 : List Lit := [(55, false), (43, false), (54, true)]
theorem step13821 (p : Nat → Bool) (h : Constraints p) : clause p c13821 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3954] c13821 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3954 p h) (sat_nil p)))
def c13822 : List Lit := [(67, false), (1650, true)]
theorem step13822 (p : Nat → Bool) (h : Constraints p) : clause p c13822 = true :=
  Snake9.LocalRup.prove_clause [c12893, c4051] c13822 (by decide) p (sat_cons (step12893 p h) (sat_cons (step4051 p h) (sat_nil p)))
def c13823 : List Lit := [(115, false), (1614, true), (1580, false), (1600, false), (51, false)]
theorem step13823 (p : Nat → Bool) (h : Constraints p) : clause p c13823 = true :=
  Snake9.LocalRup.prove_clause [c12893, c4556] c13823 (by decide) p (sat_cons (step12893 p h) (sat_cons (step4556 p h) (sat_nil p)))
def c13824 : List Lit := [(1666, true), (61, false), (45, false), (56, false), (74, true)]
theorem step13824 (p : Nat → Bool) (h : Constraints p) : clause p c13824 = true :=
  Snake9.LocalRup.prove_clause [c12893, c4459] c13824 (by decide) p (sat_cons (step12893 p h) (sat_cons (step4459 p h) (sat_nil p)))
def c13825 : List Lit := [(1666, true), (61, false), (74, true), (193, true), (45, false)]
theorem step13825 (p : Nat → Bool) (h : Constraints p) : clause p c13825 = true :=
  Snake9.LocalRup.prove_clause [c12893, c4025] c13825 (by decide) p (sat_cons (step12893 p h) (sat_cons (step4025 p h) (sat_nil p)))
def c13826 : List Lit := [(72, false), (1701, false), (1762, false), (75, true), (115, false)]
theorem step13826 (p : Nat → Bool) (h : Constraints p) : clause p c13826 = true :=
  Snake9.LocalRup.prove_clause [c12893, c4577] c13826 (by decide) p (sat_cons (step12893 p h) (sat_cons (step4577 p h) (sat_nil p)))
def c13827 : List Lit := [(39, true), (1554, true), (155, true), (1569, true), (305, true), (67, false)]
theorem step13827 (p : Nat → Bool) (h : Constraints p) : clause p c13827 = true :=
  Snake9.LocalRup.prove_clause [c12893, c6371] c13827 (by decide) p (sat_cons (step12893 p h) (sat_cons (step6371 p h) (sat_nil p)))
def c13828 : List Lit := [(1650, true), (1572, true), (51, true), (54, false), (44, false), (1595, true), (1578, true), (39, false), (1594, true), (1601, true)]
theorem step13828 (p : Nat → Bool) (h : Constraints p) : clause p c13828 = true :=
  Snake9.LocalRup.prove_clause [c12893, c5700] c13828 (by decide) p (sat_cons (step12893 p h) (sat_cons (step5700 p h) (sat_nil p)))
def c13829 : List Lit := [(1592, true), (1564, false), (1583, true), (51, false), (54, false)]
theorem step13829 (p : Nat → Bool) (h : Constraints p) : clause p c13829 = true :=
  Snake9.LocalRup.prove_clause [c12893, c6075] c13829 (by decide) p (sat_cons (step12893 p h) (sat_cons (step6075 p h) (sat_nil p)))
def c13830 : List Lit := [(54, false), (43, true), (45, false), (1590, false), (41, false), (1593, true), (42, false), (1577, true)]
theorem step13830 (p : Nat → Bool) (h : Constraints p) : clause p c13830 = true :=
  Snake9.LocalRup.prove_clause [c12893, c5608] c13830 (by decide) p (sat_cons (step12893 p h) (sat_cons (step5608 p h) (sat_nil p)))
def c13831 : List Lit := [(67, false), (27, false), (1568, true), (151, true)]
theorem step13831 (p : Nat → Bool) (h : Constraints p) : clause p c13831 = true :=
  Snake9.LocalRup.prove_clause [c12893, c5358] c13831 (by decide) p (sat_cons (step12893 p h) (sat_cons (step5358 p h) (sat_nil p)))
def c13832 : List Lit := [(120, true), (1651, true), (1761, true), (185, true), (1577, true), (188, true), (1578, true), (1600, true), (1601, true)]
theorem step13832 (p : Nat → Bool) (h : Constraints p) : clause p c13832 = true :=
  Snake9.LocalRup.prove_clause [c12893, c6112] c13832 (by decide) p (sat_cons (step12893 p h) (sat_cons (step6112 p h) (sat_nil p)))
def c13833 : List Lit := [(1651, true), (61, false), (45, false)]
theorem step13833 (p : Nat → Bool) (h : Constraints p) : clause p c13833 = true :=
  Snake9.LocalRup.prove_clause [c12893, c6459] c13833 (by decide) p (sat_cons (step12893 p h) (sat_cons (step6459 p h) (sat_nil p)))
def c13834 : List Lit := [(34, false), (67, false), (1569, true), (305, true), (1554, true), (1519, false), (155, true), (32, true)]
theorem step13834 (p : Nat → Bool) (h : Constraints p) : clause p c13834 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7172] c13834 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7172 p h) (sat_nil p)))
def c13835 : List Lit := [(1666, true), (62, true), (1657, false), (69, true)]
theorem step13835 (p : Nat → Bool) (h : Constraints p) : clause p c13835 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7633] c13835 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7633 p h) (sat_nil p)))
def c13836 : List Lit := [(1688, false), (1727, false), (61, false), (62, true), (45, false), (1785, true), (1660, false)]
theorem step13836 (p : Nat → Bool) (h : Constraints p) : clause p c13836 = true :=
  Snake9.LocalRup.prove_clause [c12893, c6621] c13836 (by decide) p (sat_cons (step12893 p h) (sat_cons (step6621 p h) (sat_nil p)))
def c13837 : List Lit := [(67, false), (27, false), (1651, true)]
theorem step13837 (p : Nat → Bool) (h : Constraints p) : clause p c13837 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7344] c13837 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7344 p h) (sat_nil p)))
def c13838 : List Lit := [(115, false), (32, true), (1651, true), (75, true), (158, true), (1617, true)]
theorem step13838 (p : Nat → Bool) (h : Constraints p) : clause p c13838 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7435] c13838 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7435 p h) (sat_nil p)))
def c13839 : List Lit := [(32, true), (67, false), (1617, true), (75, true), (158, true), (1651, true)]
theorem step13839 (p : Nat → Bool) (h : Constraints p) : clause p c13839 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7175] c13839 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7175 p h) (sat_nil p)))
def c13840 : List Lit := [(1607, false), (51, true), (1601, false), (32, true), (1639, true), (67, false), (1576, false), (1553, false), (75, true)]
theorem step13840 (p : Nat → Bool) (h : Constraints p) : clause p c13840 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7275] c13840 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7275 p h) (sat_nil p)))
def c13841 : List Lit := [(67, false), (73, false), (1569, true), (1554, true), (1582, true), (27, true), (367, true)]
theorem step13841 (p : Nat → Bool) (h : Constraints p) : clause p c13841 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7485] c13841 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7485 p h) (sat_nil p)))
def c13842 : List Lit := [(103, false), (71, true), (197, true), (1660, true), (51, true), (67, true), (1607, true), (193, true)]
theorem step13842 (p : Nat → Bool) (h : Constraints p) : clause p c13842 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7461] c13842 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7461 p h) (sat_nil p)))
def c13843 : List Lit := [(1660, true), (67, false), (69, true), (1617, true), (103, false), (75, true), (51, true), (32, true), (76, false)]
theorem step13843 (p : Nat → Bool) (h : Constraints p) : clause p c13843 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7550] c13843 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7550 p h) (sat_nil p)))
def c13844 : List Lit := [(1750, true), (122, false), (74, false), (69, true), (67, false), (91, false)]
theorem step13844 (p : Nat → Bool) (h : Constraints p) : clause p c13844 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7654] c13844 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7654 p h) (sat_nil p)))
def c13845 : List Lit := [(1746, false), (1617, false), (1688, false), (91, true), (1553, false), (115, false), (1568, false), (1639, true), (487, true), (120, true), (1659, false), (1760, false), (62, true), (1593, false)]
theorem step13845 (p : Nat → Bool) (h : Constraints p) : clause p c13845 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7477] c13845 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7477 p h) (sat_nil p)))
def c13846 : List Lit := [(69, false), (1651, true), (115, false), (73, false), (1617, true), (51, true), (1564, false), (1593, false)]
theorem step13846 (p : Nat → Bool) (h : Constraints p) : clause p c13846 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7466] c13846 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7466 p h) (sat_nil p)))
def c13847 : List Lit := [(67, false), (1600, true), (51, false), (1577, true)]
theorem step13847 (p : Nat → Bool) (h : Constraints p) : clause p c13847 = true :=
  Snake9.LocalRup.prove_clause [c12893, c7142] c13847 (by decide) p (sat_cons (step12893 p h) (sat_cons (step7142 p h) (sat_nil p)))
def c13848 : List Lit := [(61, false), (1650, true)]
theorem step13848 (p : Nat → Bool) (h : Constraints p) : clause p c13848 = true :=
  Snake9.LocalRup.prove_clause [c12893, c12661] c13848 (by decide) p (sat_cons (step12893 p h) (sat_cons (step12661 p h) (sat_nil p)))
def c13849 : List Lit := [(43, false), (67, true), (1653, true), (185, true), (115, true), (27, true), (61, false), (60, true), (188, true), (1569, false), (58, true), (45, true), (1617, true), (1592, false)]
theorem step13849 (p : Nat → Bool) (h : Constraints p) : clause p c13849 = true :=
  Snake9.LocalRup.prove_clause [c12893, c12673] c13849 (by decide) p (sat_cons (step12893 p h) (sat_cons (step12673 p h) (sat_nil p)))
def c13850 : List Lit := [(107, true), (103, false), (485, true), (75, false), (1598, true), (439, true), (1753, true), (1651, true), (1784, true), (1666, false), (1616, false), (91, true), (1762, true), (62, false), (74, true), (49, true)]
theorem step13850 (p : Nat → Bool) (h : Constraints p) : clause p c13850 = true :=
  Snake9.LocalRup.prove_clause [c12893, c12676] c13850 (by decide) p (sat_cons (step12893 p h) (sat_cons (step12676 p h) (sat_nil p)))
def c13851 : List Lit := [(72, false), (1554, true), (60, true), (1555, true), (45, true), (67, true), (57, false), (27, true), (305, true), (61, false), (185, true), (115, true)]
theorem step13851 (p : Nat → Bool) (h : Constraints p) : clause p c13851 = true :=
  Snake9.LocalRup.prove_clause [c12893, c12681] c13851 (by decide) p (sat_cons (step12893 p h) (sat_cons (step12681 p h) (sat_nil p)))
end B112E089
