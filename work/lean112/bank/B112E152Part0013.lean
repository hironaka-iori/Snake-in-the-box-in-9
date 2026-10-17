import B112E152Part0012
namespace B112E152
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1779 : List Lit := [(1558, false), (1637, false), (101, true), (99, false)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c1777, c793, c987, c1778, c874, c1760, c1736, c1032, c1269, c1283, c903, c881, c1761, c995, c324, c794] c1779 (by decide) p (sat_cons (step1777 p h) (sat_cons (step793 p h) (sat_cons (step987 p h) (sat_cons (step1778 p h) (sat_cons (step874 p h) (sat_cons (step1760 p h) (sat_cons (step1736 p h) (sat_cons (step1032 p h) (sat_cons (step1269 p h) (sat_cons (step1283 p h) (sat_cons (step903 p h) (sat_cons (step881 p h) (sat_cons (step1761 p h) (sat_cons (step995 p h) (sat_cons (step324 p h) (sat_cons (step794 p h) (sat_nil p)))))))))))))))))
def c1780 : List Lit := [(1637, false), (101, true), (99, false)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1778, c1777, c1032, c1771, c776, c716, c1760, c1736, c1779, c1416, c314, c307, c794, c995, c881, c903, c1283, c1272, c1013, c1351, c578, c559, c561, c1337, c557, c553, c703, c18, c708, c709, c719, c704, c1027, c1199, c1186] c1780 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1778 p h) (sat_cons (step1777 p h) (sat_cons (step1032 p h) (sat_cons (step1771 p h) (sat_cons (step776 p h) (sat_cons (step716 p h) (sat_cons (step1760 p h) (sat_cons (step1736 p h) (sat_cons (step1779 p h) (sat_cons (step1416 p h) (sat_cons (step314 p h) (sat_cons (step307 p h) (sat_cons (step794 p h) (sat_cons (step995 p h) (sat_cons (step881 p h) (sat_cons (step903 p h) (sat_cons (step1283 p h) (sat_cons (step1272 p h) (sat_cons (step1013 p h) (sat_cons (step1351 p h) (sat_cons (step578 p h) (sat_cons (step559 p h) (sat_cons (step561 p h) (sat_cons (step1337 p h) (sat_cons (step557 p h) (sat_cons (step553 p h) (sat_cons (step703 p h) (sat_cons (step18 p h) (sat_cons (step708 p h) (sat_cons (step709 p h) (sat_cons (step719 p h) (sat_cons (step704 p h) (sat_cons (step1027 p h) (sat_cons (step1199 p h) (sat_cons (step1186 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1781 : List Lit := [(1591, false), (101, true), (99, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c1693, c1695, c1096, c767, c1736, c1760, c1764, c816, c1777, c793, c987, c1778, c1780, c1432, c772, c1754, c324, c307, c715, c830, c1416, c1626, c896, c1502, c1284, c702, c686, c706, c707, c1013, c1351, c718, c704, c578, c561, c1027, c553, c1199, c21, c1186] c1781 (by decide) p (sat_cons (step1693 p h) (sat_cons (step1695 p h) (sat_cons (step1096 p h) (sat_cons (step767 p h) (sat_cons (step1736 p h) (sat_cons (step1760 p h) (sat_cons (step1764 p h) (sat_cons (step816 p h) (sat_cons (step1777 p h) (sat_cons (step793 p h) (sat_cons (step987 p h) (sat_cons (step1778 p h) (sat_cons (step1780 p h) (sat_cons (step1432 p h) (sat_cons (step772 p h) (sat_cons (step1754 p h) (sat_cons (step324 p h) (sat_cons (step307 p h) (sat_cons (step715 p h) (sat_cons (step830 p h) (sat_cons (step1416 p h) (sat_cons (step1626 p h) (sat_cons (step896 p h) (sat_cons (step1502 p h) (sat_cons (step1284 p h) (sat_cons (step702 p h) (sat_cons (step686 p h) (sat_cons (step706 p h) (sat_cons (step707 p h) (sat_cons (step1013 p h) (sat_cons (step1351 p h) (sat_cons (step718 p h) (sat_cons (step704 p h) (sat_cons (step578 p h) (sat_cons (step561 p h) (sat_cons (step1027 p h) (sat_cons (step553 p h) (sat_cons (step1199 p h) (sat_cons (step21 p h) (sat_cons (step1186 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c1782 : List Lit := [(101, true), (99, false)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c1032, c1781] c1782 (by decide) p (sat_cons (step1032 p h) (sat_cons (step1781 p h) (sat_nil p)))
def c1783 : List Lit := [(1558, false), (108, false), (1604, true), (100, true), (1687, false), (1698, false), (99, false)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c1693, c1695, c1535, c1534, c1782, c1269, c1506, c1449, c1502, c1283, c1188, c324, c307, c326, c702, c903, c794, c1501, c816, c1364, c1060, c768, c995, c824, c767, c250, c258, c882, c896, c1037, c728, c853, c1284, c627, c730, c841, c1127, c1270, c686, c674, c756, c1259, c1336, c979, c831, c1756] c1783 (by decide) p (sat_cons (step1693 p h) (sat_cons (step1695 p h) (sat_cons (step1535 p h) (sat_cons (step1534 p h) (sat_cons (step1782 p h) (sat_cons (step1269 p h) (sat_cons (step1506 p h) (sat_cons (step1449 p h) (sat_cons (step1502 p h) (sat_cons (step1283 p h) (sat_cons (step1188 p h) (sat_cons (step324 p h) (sat_cons (step307 p h) (sat_cons (step326 p h) (sat_cons (step702 p h) (sat_cons (step903 p h) (sat_cons (step794 p h) (sat_cons (step1501 p h) (sat_cons (step816 p h) (sat_cons (step1364 p h) (sat_cons (step1060 p h) (sat_cons (step768 p h) (sat_cons (step995 p h) (sat_cons (step824 p h) (sat_cons (step767 p h) (sat_cons (step250 p h) (sat_cons (step258 p h) (sat_cons (step882 p h) (sat_cons (step896 p h) (sat_cons (step1037 p h) (sat_cons (step728 p h) (sat_cons (step853 p h) (sat_cons (step1284 p h) (sat_cons (step627 p h) (sat_cons (step730 p h) (sat_cons (step841 p h) (sat_cons (step1127 p h) (sat_cons (step1270 p h) (sat_cons (step686 p h) (sat_cons (step674 p h) (sat_cons (step756 p h) (sat_cons (step1259 p h) (sat_cons (step1336 p h) (sat_cons (step979 p h) (sat_cons (step831 p h) (sat_cons (step1756 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c1784 : List Lit := [(67, true), (1595, true), (1698, false)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c1693, c1432, c703, c903, c1337, c1283, c1351, c1272] c1784 (by decide) p (sat_cons (step1693 p h) (sat_cons (step1432 p h) (sat_cons (step703 p h) (sat_cons (step903 p h) (sat_cons (step1337 p h) (sat_cons (step1283 p h) (sat_cons (step1351 p h) (sat_cons (step1272 p h) (sat_nil p)))))))))
def c1785 : List Lit := [(108, false), (1604, true), (100, true), (1687, false), (1698, false), (99, false)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c1064, c1784, c1188, c1783, c307, c1416] c1785 (by decide) p (sat_cons (step1064 p h) (sat_cons (step1784 p h) (sat_cons (step1188 p h) (sat_cons (step1783 p h) (sat_cons (step307 p h) (sat_cons (step1416 p h) (sat_nil p)))))))
def c1786 : List Lit := [(1558, false), (1669, false), (1604, true), (1662, false), (1698, false), (99, false)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c1693, c1695, c1782, c1269, c1506, c1502, c1283, c876, c702, c903, c1364, c1060, c768, c767, c1606, c262, c258, c896, c827, c728, c1284, c1742, c730, c686, c756, c1259, c1756, c979] c1786 (by decide) p (sat_cons (step1693 p h) (sat_cons (step1695 p h) (sat_cons (step1782 p h) (sat_cons (step1269 p h) (sat_cons (step1506 p h) (sat_cons (step1502 p h) (sat_cons (step1283 p h) (sat_cons (step876 p h) (sat_cons (step702 p h) (sat_cons (step903 p h) (sat_cons (step1364 p h) (sat_cons (step1060 p h) (sat_cons (step768 p h) (sat_cons (step767 p h) (sat_cons (step1606 p h) (sat_cons (step262 p h) (sat_cons (step258 p h) (sat_cons (step896 p h) (sat_cons (step827 p h) (sat_cons (step728 p h) (sat_cons (step1284 p h) (sat_cons (step1742 p h) (sat_cons (step730 p h) (sat_cons (step686 p h) (sat_cons (step756 p h) (sat_cons (step1259 p h) (sat_cons (step1756 p h) (sat_cons (step979 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1787 : List Lit := [(1500, true), (1663, false), (1669, false), (1599, true), (1604, true), (99, false)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1782, c1013, c1351, c576, c1337, c573, c702, c1364, c1060, c707, c767, c1606, c262, c704, c1279, c827, c1194, c883, c1742, c1190, c1201] c1787 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1782 p h) (sat_cons (step1013 p h) (sat_cons (step1351 p h) (sat_cons (step576 p h) (sat_cons (step1337 p h) (sat_cons (step573 p h) (sat_cons (step702 p h) (sat_cons (step1364 p h) (sat_cons (step1060 p h) (sat_cons (step707 p h) (sat_cons (step767 p h) (sat_cons (step1606 p h) (sat_cons (step262 p h) (sat_cons (step704 p h) (sat_cons (step1279 p h) (sat_cons (step827 p h) (sat_cons (step1194 p h) (sat_cons (step883 p h) (sat_cons (step1742 p h) (sat_cons (step1190 p h) (sat_cons (step1201 p h) (sat_nil p)))))))))))))))))))))))
def c1788 : List Lit := [(1594, false), (1718, true), (1663, false), (1669, false), (1604, true), (99, false)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1782, c1364, c1060, c767, c1606, c262, c897, c827, c882, c1559] c1788 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1782 p h) (sat_cons (step1364 p h) (sat_cons (step1060 p h) (sat_cons (step767 p h) (sat_cons (step1606 p h) (sat_cons (step262 p h) (sat_cons (step897 p h) (sat_cons (step827 p h) (sat_cons (step882 p h) (sat_cons (step1559 p h) (sat_nil p))))))))))))
def c1789 : List Lit := [(112, true), (1688, true), (1669, false), (99, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c819, c1559, c827] c1789 (by decide) p (sat_cons (step819 p h) (sat_cons (step1559 p h) (sat_cons (step827 p h) (sat_nil p))))
def c1790 : List Lit := [(1604, true), (100, true), (1687, false), (1698, false), (1591, false), (99, false)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.TreeRup.prove_clause [c1693, c793, c987, c1782, c1064, c715, c1784, c1188, c1758, c1785, c817, c1786, c1416, c306, c794, c995, c1787, c1272, c1283, c1788, c702, c1507, c896, c897, c1284, c882, c1273, c1593, c1260, c1359, c964, c547, c548, c1151, c1148, c1149, c1147, c444, c445, c1253, c453, c1, c459, c1255, c12, c1256, c458, c1155, c473, c457, c472, c456, c468, c15, c466, c1360, c967, c604, c979, c1756, c1789, c262, c265, c1132, c728, c730, c756, c903, c768] c1790 (by decide) p (sat_cons (step1693 p h) (sat_cons (step793 p h) (sat_cons (step987 p h) (sat_cons (step1782 p h) (sat_cons (step1064 p h) (sat_cons (step715 p h) (sat_cons (step1784 p h) (sat_cons (step1188 p h) (sat_cons (step1758 p h) (sat_cons (step1785 p h) (sat_cons (step817 p h) (sat_cons (step1786 p h) (sat_cons (step1416 p h) (sat_cons (step306 p h) (sat_cons (step794 p h) (sat_cons (step995 p h) (sat_cons (step1787 p h) (sat_cons (step1272 p h) (sat_cons (step1283 p h) (sat_cons (step1788 p h) (sat_cons (step702 p h) (sat_cons (step1507 p h) (sat_cons (step896 p h) (sat_cons (step897 p h) (sat_cons (step1284 p h) (sat_cons (step882 p h) (sat_cons (step1273 p h) (sat_cons (step1593 p h) (sat_cons (step1260 p h) (sat_cons (step1359 p h) (sat_cons (step964 p h) (sat_cons (step547 p h) (sat_cons (step548 p h) (sat_cons (step1151 p h) (sat_cons (step1148 p h) (sat_cons (step1149 p h) (sat_cons (step1147 p h) (sat_cons (step444 p h) (sat_cons (step445 p h) (sat_cons (step1253 p h) (sat_cons (step453 p h) (sat_cons (step1 p h) (sat_cons (step459 p h) (sat_cons (step1255 p h) (sat_cons (step12 p h) (sat_cons (step1256 p h) (sat_cons (step458 p h) (sat_cons (step1155 p h) (sat_cons (step473 p h) (sat_cons (step457 p h) (sat_cons (step472 p h) (sat_cons (step456 p h) (sat_cons (step468 p h) (sat_cons (step15 p h) (sat_cons (step466 p h) (sat_cons (step1360 p h) (sat_cons (step967 p h) (sat_cons (step604 p h) (sat_cons (step979 p h) (sat_cons (step1756 p h) (sat_cons (step1789 p h) (sat_cons (step262 p h) (sat_cons (step265 p h) (sat_cons (step1132 p h) (sat_cons (step728 p h) (sat_cons (step730 p h) (sat_cons (step756 p h) (sat_cons (step903 p h) (sat_cons (step768 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1791 : List Lit := [(1604, false), (1698, false), (99, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.TreeRup.prove_clause [c1695, c1696, c1693, c1281, c1782, c772, c773, c903, c1304, c1283, c724, c725, c1269, c1272, c1209, c1268, c1259, c1013, c1143, c1351, c591, c979, c576, c1148, c559, c561, c1337, c588, c583, c584, c573, c574, c1147, c556, c554, c1156, c444, c1155, c26, c445, c582, c453, c1159, c459, c33, c475, c492, c1258, c543, c516, c509, c510, c508, c499, c503, c498, c502, c497, c132, c1190, c1206, c1211, c124, c250, c258, c1037, c728, c630, c730, c1511, c756, c741, c743] c1791 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1696 p h) (sat_cons (step1693 p h) (sat_cons (step1281 p h) (sat_cons (step1782 p h) (sat_cons (step772 p h) (sat_cons (step773 p h) (sat_cons (step903 p h) (sat_cons (step1304 p h) (sat_cons (step1283 p h) (sat_cons (step724 p h) (sat_cons (step725 p h) (sat_cons (step1269 p h) (sat_cons (step1272 p h) (sat_cons (step1209 p h) (sat_cons (step1268 p h) (sat_cons (step1259 p h) (sat_cons (step1013 p h) (sat_cons (step1143 p h) (sat_cons (step1351 p h) (sat_cons (step591 p h) (sat_cons (step979 p h) (sat_cons (step576 p h) (sat_cons (step1148 p h) (sat_cons (step559 p h) (sat_cons (step561 p h) (sat_cons (step1337 p h) (sat_cons (step588 p h) (sat_cons (step583 p h) (sat_cons (step584 p h) (sat_cons (step573 p h) (sat_cons (step574 p h) (sat_cons (step1147 p h) (sat_cons (step556 p h) (sat_cons (step554 p h) (sat_cons (step1156 p h) (sat_cons (step444 p h) (sat_cons (step1155 p h) (sat_cons (step26 p h) (sat_cons (step445 p h) (sat_cons (step582 p h) (sat_cons (step453 p h) (sat_cons (step1159 p h) (sat_cons (step459 p h) (sat_cons (step33 p h) (sat_cons (step475 p h) (sat_cons (step492 p h) (sat_cons (step1258 p h) (sat_cons (step543 p h) (sat_cons (step516 p h) (sat_cons (step509 p h) (sat_cons (step510 p h) (sat_cons (step508 p h) (sat_cons (step499 p h) (sat_cons (step503 p h) (sat_cons (step498 p h) (sat_cons (step502 p h) (sat_cons (step497 p h) (sat_cons (step132 p h) (sat_cons (step1190 p h) (sat_cons (step1206 p h) (sat_cons (step1211 p h) (sat_cons (step124 p h) (sat_cons (step250 p h) (sat_cons (step258 p h) (sat_cons (step1037 p h) (sat_cons (step728 p h) (sat_cons (step630 p h) (sat_cons (step730 p h) (sat_cons (step1511 p h) (sat_cons (step756 p h) (sat_cons (step741 p h) (sat_cons (step743 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1792 : List Lit := [(100, false), (1698, false), (99, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1693, c1791, c1064, c1784, c1188, c1758, c1782, c1000, c1573, c261, c267, c1504, c767, c1060, c702, c1337, c1502, c1351, c1416, c1272, c307, c306, c1283, c817, c792, c897, c827, c987, c876, c1742] c1792 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1693 p h) (sat_cons (step1791 p h) (sat_cons (step1064 p h) (sat_cons (step1784 p h) (sat_cons (step1188 p h) (sat_cons (step1758 p h) (sat_cons (step1782 p h) (sat_cons (step1000 p h) (sat_cons (step1573 p h) (sat_cons (step261 p h) (sat_cons (step267 p h) (sat_cons (step1504 p h) (sat_cons (step767 p h) (sat_cons (step1060 p h) (sat_cons (step702 p h) (sat_cons (step1337 p h) (sat_cons (step1502 p h) (sat_cons (step1351 p h) (sat_cons (step1416 p h) (sat_cons (step1272 p h) (sat_cons (step307 p h) (sat_cons (step306 p h) (sat_cons (step1283 p h) (sat_cons (step817 p h) (sat_cons (step792 p h) (sat_cons (step897 p h) (sat_cons (step827 p h) (sat_cons (step987 p h) (sat_cons (step876 p h) (sat_cons (step1742 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1793 : List Lit := [(1698, false), (1591, false), (99, false)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1340, c1693, c1535, c1782, c1791, c1064, c715, c1784, c1188, c1758, c816, c1792, c1790, c1291, c855, c817, c825, c307, c1416, c1502, c702, c1060, c707, c1606, c262, c704, c824, c820, c852, c1198, c838, c1190, c830, c1201] c1793 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1340 p h) (sat_cons (step1693 p h) (sat_cons (step1535 p h) (sat_cons (step1782 p h) (sat_cons (step1791 p h) (sat_cons (step1064 p h) (sat_cons (step715 p h) (sat_cons (step1784 p h) (sat_cons (step1188 p h) (sat_cons (step1758 p h) (sat_cons (step816 p h) (sat_cons (step1792 p h) (sat_cons (step1790 p h) (sat_cons (step1291 p h) (sat_cons (step855 p h) (sat_cons (step817 p h) (sat_cons (step825 p h) (sat_cons (step307 p h) (sat_cons (step1416 p h) (sat_cons (step1502 p h) (sat_cons (step702 p h) (sat_cons (step1060 p h) (sat_cons (step707 p h) (sat_cons (step1606 p h) (sat_cons (step262 p h) (sat_cons (step704 p h) (sat_cons (step824 p h) (sat_cons (step820 p h) (sat_cons (step852 p h) (sat_cons (step1198 p h) (sat_cons (step838 p h) (sat_cons (step1190 p h) (sat_cons (step830 p h) (sat_cons (step1201 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1794 : List Lit := [(104, true), (67, true), (106, false), (108, true), (107, true), (226, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1693, c339] c1794 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1693 p h) (sat_cons (step339 p h) (sat_nil p))))
def c1795 : List Lit := [(50, true), (226, true), (106, false), (107, true), (67, true), (108, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1693, c340] c1795 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1693 p h) (sat_cons (step340 p h) (sat_nil p))))
def c1796 : List Lit := [(226, true), (104, true), (67, true), (106, false), (108, true), (50, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c1693, c1534, c341] c1796 (by decide) p (sat_cons (step1693 p h) (sat_cons (step1534 p h) (sat_cons (step341 p h) (sat_nil p))))
def c1797 : List Lit := [(119, false), (120, true), (114, true), (239, true)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c1534, c397] c1797 (by decide) p (sat_cons (step1534 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1798 : List Lit := [(88, true), (1620, true)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c1693, c741] c1798 (by decide) p (sat_cons (step1693 p h) (sat_cons (step741 p h) (sat_nil p)))
def c1799 : List Lit := [(1622, true), (1617, false)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c1694, c745] c1799 (by decide) p (sat_cons (step1694 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1800 : List Lit := [(1618, false), (1623, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c1694, c748] c1800 (by decide) p (sat_cons (step1694 p h) (sat_cons (step748 p h) (sat_nil p)))
def c1801 : List Lit := [(1614, false), (1627, true)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c1696, c759] c1801 (by decide) p (sat_cons (step1696 p h) (sat_cons (step759 p h) (sat_nil p)))
def c1802 : List Lit := [(1615, false), (1628, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c1696, c761] c1802 (by decide) p (sat_cons (step1696 p h) (sat_cons (step761 p h) (sat_nil p)))
def c1803 : List Lit := [(1636, true), (1603, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c1695, c767] c1803 (by decide) p (sat_cons (step1695 p h) (sat_cons (step767 p h) (sat_nil p)))
def c1804 : List Lit := [(1637, true), (1604, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c1695, c772] c1804 (by decide) p (sat_cons (step1695 p h) (sat_cons (step772 p h) (sat_nil p)))
def c1805 : List Lit := [(1605, false), (1638, true)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c1695, c776] c1805 (by decide) p (sat_cons (step1695 p h) (sat_cons (step776 p h) (sat_nil p)))
def c1806 : List Lit := [(1606, false), (1639, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c1695, c779] c1806 (by decide) p (sat_cons (step1695 p h) (sat_cons (step779 p h) (sat_nil p)))
def c1807 : List Lit := [(120, true), (1679, true)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c1534, c834] c1807 (by decide) p (sat_cons (step1534 p h) (sat_cons (step834 p h) (sat_nil p)))
def c1808 : List Lit := [(1681, true), (1676, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1535, c838] c1808 (by decide) p (sat_cons (step1535 p h) (sat_cons (step838 p h) (sat_nil p)))
def c1809 : List Lit := [(1677, false), (1682, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c1535, c841] c1809 (by decide) p (sat_cons (step1535 p h) (sat_cons (step841 p h) (sat_nil p)))
def c1810 : List Lit := [(1685, true), (1672, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c1340, c847] c1810 (by decide) p (sat_cons (step1340 p h) (sat_cons (step847 p h) (sat_nil p)))
def c1811 : List Lit := [(1686, true), (1673, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c1340, c851] c1811 (by decide) p (sat_cons (step1340 p h) (sat_cons (step851 p h) (sat_nil p)))
def c1812 : List Lit := [(1674, false), (1687, true)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c1340, c855] c1812 (by decide) p (sat_cons (step1340 p h) (sat_cons (step855 p h) (sat_nil p)))
def c1813 : List Lit := [(1695, true), (1686, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c1342, c866] c1813 (by decide) p (sat_cons (step1342 p h) (sat_cons (step866 p h) (sat_nil p)))
def c1814 : List Lit := [(1687, false), (1696, true)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1342, c867] c1814 (by decide) p (sat_cons (step1342 p h) (sat_cons (step867 p h) (sat_nil p)))
def c1815 : List Lit := [(1688, false), (1697, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c1342, c868] c1815 (by decide) p (sat_cons (step1342 p h) (sat_cons (step868 p h) (sat_nil p)))
def c1816 : List Lit := [(1689, false), (1698, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c1342, c869] c1816 (by decide) p (sat_cons (step1342 p h) (sat_cons (step869 p h) (sat_nil p)))
def c1817 : List Lit := [(1694, true), (1662, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1341, c871] c1817 (by decide) p (sat_cons (step1341 p h) (sat_cons (step871 p h) (sat_nil p)))
def c1818 : List Lit := [(1690, false), (1663, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1698, c884] c1818 (by decide) p (sat_cons (step1698 p h) (sat_cons (step884 p h) (sat_nil p)))
def c1819 : List Lit := [(1716, true), (1698, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1697, c890] c1819 (by decide) p (sat_cons (step1697 p h) (sat_cons (step890 p h) (sat_nil p)))
def c1820 : List Lit := [(1717, true), (1699, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1697, c891] c1820 (by decide) p (sat_cons (step1697 p h) (sat_cons (step891 p h) (sat_nil p)))
def c1821 : List Lit := [(99, true), (36, false), (1637, false), (1604, false), (1548, false), (104, false), (1687, false), (1655, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1693, c1069] c1821 (by decide) p (sat_cons (step1693 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c1822 : List Lit := [(1596, false), (67, true), (1697, false), (1577, true), (1558, false), (1591, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1076] c1822 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c1823 : List Lit := [(1543, true), (1682, true)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1127] c1823 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1127 p h) (sat_nil p)))
def c1824 : List Lit := [(1687, true), (1669, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1534, c1291] c1824 (by decide) p (sat_cons (step1534 p h) (sat_cons (step1291 p h) (sat_nil p)))
def c1825 : List Lit := [(1636, true), (64, true), (114, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1696, c1299] c1825 (by decide) p (sat_cons (step1696 p h) (sat_cons (step1299 p h) (sat_nil p)))
def c1826 : List Lit := [(1609, false), (1627, true)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1693, c1696, c1304] c1826 (by decide) p (sat_cons (step1693 p h) (sat_cons (step1696 p h) (sat_cons (step1304 p h) (sat_nil p))))
def c1827 : List Lit := [(81, false), (113, true), (107, true), (114, false), (104, true), (1676, true), (1655, false), (1697, false), (1558, true), (1604, false), (106, false), (1594, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1323] c1827 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1323 p h) (sat_nil p)))
def c1828 : List Lit := [(1637, true), (67, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1693, c1432] c1828 (by decide) p (sat_cons (step1693 p h) (sat_cons (step1432 p h) (sat_nil p)))
def c1829 : List Lit := [(67, true), (1558, false), (1698, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1449] c1829 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1449 p h) (sat_nil p)))
def c1830 : List Lit := [(1699, false), (1558, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1506] c1830 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1506 p h) (sat_nil p)))
def c1831 : List Lit := [(65, false), (1636, true), (1591, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1693, c1507] c1831 (by decide) p (sat_cons (step1693 p h) (sat_cons (step1507 p h) (sat_nil p)))
def c1832 : List Lit := [(4, true), (67, true), (1697, false), (1501, true), (1558, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1641] c1832 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1641 p h) (sat_nil p)))
def c1833 : List Lit := [(65, true), (1604, true), (1698, true), (99, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1064, c1782, c702, c703, c1060, c1188, c1758, c1606, c261, c262, c816, c824, c793, c987, c875, c1789, c817, c324, c794, c995, c881, c852, c1808, c830, c1661, c1295] c1833 (by decide) p (sat_cons (step1064 p h) (sat_cons (step1782 p h) (sat_cons (step702 p h) (sat_cons (step703 p h) (sat_cons (step1060 p h) (sat_cons (step1188 p h) (sat_cons (step1758 p h) (sat_cons (step1606 p h) (sat_cons (step261 p h) (sat_cons (step262 p h) (sat_cons (step816 p h) (sat_cons (step824 p h) (sat_cons (step793 p h) (sat_cons (step987 p h) (sat_cons (step875 p h) (sat_cons (step1789 p h) (sat_cons (step817 p h) (sat_cons (step324 p h) (sat_cons (step794 p h) (sat_cons (step995 p h) (sat_cons (step881 p h) (sat_cons (step852 p h) (sat_cons (step1808 p h) (sat_cons (step830 p h) (sat_cons (step1661 p h) (sat_cons (step1295 p h) (sat_nil p)))))))))))))))))))))))))))
def c1834 : List Lit := [(1668, false), (1687, true), (62, false), (99, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1812, c1782, c262, c1606, c824, c825, c852, c820, c836, c1808, c1807, c829, c356, c390, c1247] c1834 (by decide) p (sat_cons (step1812 p h) (sat_cons (step1782 p h) (sat_cons (step262 p h) (sat_cons (step1606 p h) (sat_cons (step824 p h) (sat_cons (step825 p h) (sat_cons (step852 p h) (sat_cons (step820 p h) (sat_cons (step836 p h) (sat_cons (step1808 p h) (sat_cons (step1807 p h) (sat_cons (step829 p h) (sat_cons (step356 p h) (sat_cons (step390 p h) (sat_cons (step1247 p h) (sat_nil p))))))))))))))))
def c1835 : List Lit := [(1676, true), (108, false), (107, false), (1687, true), (1550, true), (112, true), (1604, true), (99, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c829, c830, c1708, c1661, c326, c1295, c701] c1835 (by decide) p (sat_cons (step829 p h) (sat_cons (step830 p h) (sat_cons (step1708 p h) (sat_cons (step1661 p h) (sat_cons (step326 p h) (sat_cons (step1295 p h) (sat_cons (step701 p h) (sat_nil p))))))))
def c1836 : List Lit := [(108, false), (107, false), (1687, true), (1550, true), (1613, false), (1525, false), (1672, false), (112, true), (1662, false), (1604, true), (99, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1835, c1808, c1712, c1661, c1709, c1295, c326, c701] c1836 (by decide) p (sat_cons (step1835 p h) (sat_cons (step1808 p h) (sat_cons (step1712 p h) (sat_cons (step1661 p h) (sat_cons (step1709 p h) (sat_cons (step1295 p h) (sat_cons (step326 p h) (sat_cons (step701 p h) (sat_nil p)))))))))
def c1837 : List Lit := [(1687, true), (1550, true), (1662, false), (62, false), (1604, true), (99, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1782, c258, c728, c730, c250, c1037, c627, c1606, c821, c262, c1834, c816, c1836, c815] c1837 (by decide) p (sat_cons (step1782 p h) (sat_cons (step258 p h) (sat_cons (step728 p h) (sat_cons (step730 p h) (sat_cons (step250 p h) (sat_cons (step1037 p h) (sat_cons (step627 p h) (sat_cons (step1606 p h) (sat_cons (step821 p h) (sat_cons (step262 p h) (sat_cons (step1834 p h) (sat_cons (step816 p h) (sat_cons (step1836 p h) (sat_cons (step815 p h) (sat_nil p)))))))))))))))
def c1838 : List Lit := [(106, true), (62, false), (99, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1606, c1514, c1718] c1838 (by decide) p (sat_cons (step1606 p h) (sat_cons (step1514 p h) (sat_cons (step1718 p h) (sat_nil p))))
def c1839 : List Lit := [(107, false), (106, false), (104, false), (1697, false), (1595, true)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1758, c313, c1741, c1416] c1839 (by decide) p (sat_cons (step1758 p h) (sat_cons (step313 p h) (sat_cons (step1741 p h) (sat_cons (step1416 p h) (sat_nil p)))))
def c1840 : List Lit := [(62, false), (1604, true), (1591, false), (99, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1793, c1833, c1337, c1351, c1831, c1064, c1782, c1606, c1700, c1305, c261, c262, c250, c929, c873, c875, c793, c1037, c1179, c894, c1789, c627, c122, c1286, c724, c688, c1826, c675, c1837, c881, c874, c995, c794, c1838, c1049, c1284, c1839, c686, c817, c1416, c314] c1840 (by decide) p (sat_cons (step1793 p h) (sat_cons (step1833 p h) (sat_cons (step1337 p h) (sat_cons (step1351 p h) (sat_cons (step1831 p h) (sat_cons (step1064 p h) (sat_cons (step1782 p h) (sat_cons (step1606 p h) (sat_cons (step1700 p h) (sat_cons (step1305 p h) (sat_cons (step261 p h) (sat_cons (step262 p h) (sat_cons (step250 p h) (sat_cons (step929 p h) (sat_cons (step873 p h) (sat_cons (step875 p h) (sat_cons (step793 p h) (sat_cons (step1037 p h) (sat_cons (step1179 p h) (sat_cons (step894 p h) (sat_cons (step1789 p h) (sat_cons (step627 p h) (sat_cons (step122 p h) (sat_cons (step1286 p h) (sat_cons (step724 p h) (sat_cons (step688 p h) (sat_cons (step1826 p h) (sat_cons (step675 p h) (sat_cons (step1837 p h) (sat_cons (step881 p h) (sat_cons (step874 p h) (sat_cons (step995 p h) (sat_cons (step794 p h) (sat_cons (step1838 p h) (sat_cons (step1049 p h) (sat_cons (step1284 p h) (sat_cons (step1839 p h) (sat_cons (step686 p h) (sat_cons (step817 p h) (sat_cons (step1416 p h) (sat_cons (step314 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c1841 : List Lit := [(104, false), (1670, false), (64, false), (67, false), (1698, true), (99, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1188, c1758, c1816, c324, c817, c827, c1130, c1789, c1742, c875, c1497, c987, c793] c1841 (by decide) p (sat_cons (step1188 p h) (sat_cons (step1758 p h) (sat_cons (step1816 p h) (sat_cons (step324 p h) (sat_cons (step817 p h) (sat_cons (step827 p h) (sat_cons (step1130 p h) (sat_cons (step1789 p h) (sat_cons (step1742 p h) (sat_cons (step875 p h) (sat_cons (step1497 p h) (sat_cons (step987 p h) (sat_cons (step793 p h) (sat_nil p))))))))))))))
def c1842 : List Lit := [(1687, true), (1673, false), (64, false), (107, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1824, c852, c817, c1808, c1661, c830] c1842 (by decide) p (sat_cons (step1824 p h) (sat_cons (step852 p h) (sat_cons (step817 p h) (sat_cons (step1808 p h) (sat_cons (step1661 p h) (sat_cons (step830 p h) (sat_nil p)))))))
end B112E152
