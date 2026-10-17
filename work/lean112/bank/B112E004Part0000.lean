import B112E004Inputs
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1734 : List Lit := [(76, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c534, c533] c1734 (by decide) p (sat_cons (step534 p h) (sat_cons (step533 p h) (sat_nil p)))
def c1735 : List Lit := [(196, false), (78, false)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c534, c535] c1735 (by decide) p (sat_cons (step534 p h) (sat_cons (step535 p h) (sat_nil p)))
def c1736 : List Lit := [(196, true), (78, true)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c1734, c536] c1736 (by decide) p (sat_cons (step1734 p h) (sat_cons (step536 p h) (sat_nil p)))
def c1737 : List Lit := [(78, false), (16, false), (77, false)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c1734, c541] c1737 (by decide) p (sat_cons (step1734 p h) (sat_cons (step541 p h) (sat_nil p)))
def c1738 : List Lit := [(474, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c1057, c1054] c1738 (by decide) p (sat_cons (step1057 p h) (sat_cons (step1054 p h) (sat_nil p)))
def c1739 : List Lit := [(356, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c1057, c1056] c1739 (by decide) p (sat_cons (step1057 p h) (sat_cons (step1056 p h) (sat_nil p)))
def c1740 : List Lit := [(472, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c1738, c1050] c1740 (by decide) p (sat_cons (step1738 p h) (sat_cons (step1050 p h) (sat_nil p)))
def c1741 : List Lit := [(414, false)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c1738, c1053] c1741 (by decide) p (sat_cons (step1738 p h) (sat_cons (step1053 p h) (sat_nil p)))
def c1742 : List Lit := [(354, false)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c1739, c938] c1742 (by decide) p (sat_cons (step1739 p h) (sat_cons (step938 p h) (sat_nil p)))
def c1743 : List Lit := [(296, false)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c1739, c941] c1743 (by decide) p (sat_cons (step1739 p h) (sat_cons (step941 p h) (sat_nil p)))
def c1744 : List Lit := [(470, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1045] c1744 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1045 p h) (sat_nil p)))
def c1745 : List Lit := [(442, false)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1048] c1745 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1048 p h) (sat_nil p)))
def c1746 : List Lit := [(412, false)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c1741, c991] c1746 (by decide) p (sat_cons (step1741 p h) (sat_cons (step991 p h) (sat_nil p)))
def c1747 : List Lit := [(384, false)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c1741, c994] c1747 (by decide) p (sat_cons (step1741 p h) (sat_cons (step994 p h) (sat_nil p)))
def c1748 : List Lit := [(352, false)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c1742, c933] c1748 (by decide) p (sat_cons (step1742 p h) (sat_cons (step933 p h) (sat_nil p)))
def c1749 : List Lit := [(324, false)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c1742, c936] c1749 (by decide) p (sat_cons (step1742 p h) (sat_cons (step936 p h) (sat_nil p)))
def c1750 : List Lit := [(294, false)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c1743, c887] c1750 (by decide) p (sat_cons (step1743 p h) (sat_cons (step887 p h) (sat_nil p)))
def c1751 : List Lit := [(266, false)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c1743, c890] c1751 (by decide) p (sat_cons (step1743 p h) (sat_cons (step890 p h) (sat_nil p)))
def c1752 : List Lit := [(468, false)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c1744, c1040] c1752 (by decide) p (sat_cons (step1744 p h) (sat_cons (step1040 p h) (sat_nil p)))
def c1753 : List Lit := [(454, false)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c1744, c1043] c1753 (by decide) p (sat_cons (step1744 p h) (sat_cons (step1043 p h) (sat_nil p)))
def c1754 : List Lit := [(426, false)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c1745, c1017] c1754 (by decide) p (sat_cons (step1745 p h) (sat_cons (step1017 p h) (sat_nil p)))
def c1755 : List Lit := [(396, false)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c1746, c989] c1755 (by decide) p (sat_cons (step1746 p h) (sat_cons (step989 p h) (sat_nil p)))
def c1756 : List Lit := [(382, false)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c1747, c962] c1756 (by decide) p (sat_cons (step1747 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1757 : List Lit := [(368, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c1747, c965] c1757 (by decide) p (sat_cons (step1747 p h) (sat_cons (step965 p h) (sat_nil p)))
def c1758 : List Lit := [(308, false)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c1749, c912] c1758 (by decide) p (sat_cons (step1749 p h) (sat_cons (step912 p h) (sat_nil p)))
def c1759 : List Lit := [(292, false)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c1750, c883] c1759 (by decide) p (sat_cons (step1750 p h) (sat_cons (step883 p h) (sat_nil p)))
def c1760 : List Lit := [(264, false)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c1751, c859] c1760 (by decide) p (sat_cons (step1751 p h) (sat_cons (step859 p h) (sat_nil p)))
def c1761 : List Lit := [(460, false)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1038] c1761 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1038 p h) (sat_nil p)))
def c1762 : List Lit := [(388, false)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c1755, c977] c1762 (by decide) p (sat_cons (step1755 p h) (sat_cons (step977 p h) (sat_nil p)))
def c1763 : List Lit := [(366, false)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c1757, c949] c1763 (by decide) p (sat_cons (step1757 p h) (sat_cons (step949 p h) (sat_nil p)))
def c1764 : List Lit := [(284, false)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c1759, c881] c1764 (by decide) p (sat_cons (step1759 p h) (sat_cons (step881 p h) (sat_nil p)))
def c1765 : List Lit := [(256, false)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c1760, c857] c1765 (by decide) p (sat_cons (step1760 p h) (sat_cons (step857 p h) (sat_nil p)))
def c1766 : List Lit := [(254, false)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c1765, c847] c1766 (by decide) p (sat_cons (step1765 p h) (sat_cons (step847 p h) (sat_nil p)))
def c1767 : List Lit := [(121, true), (124, true), (127, true), (128, true), (129, true), (130, true), (131, true), (134, true), (136, true), (137, true), (139, true), (143, true), (145, true), (147, true), (149, true), (151, true), (153, true), (154, true), (157, true), (159, true), (161, true), (163, true), (165, true), (167, true), (169, true), (170, true), (174, true), (175, true), (177, true), (178, true), (183, true), (185, true), (186, true), (188, true), (189, true), (192, true), (194, true), (196, true), (197, true), (199, true), (201, true), (205, true), (208, true), (209, true), (212, true), (213, true), (214, true), (215, true), (216, true), (219, true), (220, true), (224, true), (227, true), (230, true), (232, true), (233, true), (235, true), (238, true), (240, true)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.TreeRup.prove_clause [c776, c777, c778, c779, c780, c781, c782, c783, c784, c785, c786, c787, c788, c789, c790, c791, c792, c793, c794, c795, c796, c797, c798, c799, c800, c801, c802, c803, c804, c805, c806, c807, c808, c809, c810, c811, c812, c813, c814, c815, c816, c817, c818, c819, c820, c821, c822, c823, c824, c825, c826, c827, c828, c829, c830, c831, c832, c833, c834, c835, c1058] c1767 (by decide) p (sat_cons (step776 p h) (sat_cons (step777 p h) (sat_cons (step778 p h) (sat_cons (step779 p h) (sat_cons (step780 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step783 p h) (sat_cons (step784 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step787 p h) (sat_cons (step788 p h) (sat_cons (step789 p h) (sat_cons (step790 p h) (sat_cons (step791 p h) (sat_cons (step792 p h) (sat_cons (step793 p h) (sat_cons (step794 p h) (sat_cons (step795 p h) (sat_cons (step796 p h) (sat_cons (step797 p h) (sat_cons (step798 p h) (sat_cons (step799 p h) (sat_cons (step800 p h) (sat_cons (step801 p h) (sat_cons (step802 p h) (sat_cons (step803 p h) (sat_cons (step804 p h) (sat_cons (step805 p h) (sat_cons (step806 p h) (sat_cons (step807 p h) (sat_cons (step808 p h) (sat_cons (step809 p h) (sat_cons (step810 p h) (sat_cons (step811 p h) (sat_cons (step812 p h) (sat_cons (step813 p h) (sat_cons (step814 p h) (sat_cons (step815 p h) (sat_cons (step816 p h) (sat_cons (step817 p h) (sat_cons (step818 p h) (sat_cons (step819 p h) (sat_cons (step820 p h) (sat_cons (step821 p h) (sat_cons (step822 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step825 p h) (sat_cons (step826 p h) (sat_cons (step827 p h) (sat_cons (step828 p h) (sat_cons (step829 p h) (sat_cons (step830 p h) (sat_cons (step831 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step834 p h) (sat_cons (step835 p h) (sat_cons (step1058 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1768 : List Lit := [(1473, true)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c789, c1152, c1154, c1149, c1150, c1146, c104, c93] c1768 (by decide) p (sat_cons (step789 p h) (sat_cons (step1152 p h) (sat_cons (step1154 p h) (sat_cons (step1149 p h) (sat_cons (step1150 p h) (sat_cons (step1146 p h) (sat_cons (step104 p h) (sat_cons (step93 p h) (sat_nil p)))))))))
def c1769 : List Lit := [(1477, true)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1160] c1769 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1160 p h) (sat_nil p)))
def c1770 : List Lit := [(1486, true)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c1769, c1768, c779, c1177, c1181, c1164, c1120, c1124, c1138, c1112, c1114, c1101, c1136, c1109, c1110, c1107, c1098, c1099, c9, c19, c26] c1770 (by decide) p (sat_cons (step1769 p h) (sat_cons (step1768 p h) (sat_cons (step779 p h) (sat_cons (step1177 p h) (sat_cons (step1181 p h) (sat_cons (step1164 p h) (sat_cons (step1120 p h) (sat_cons (step1124 p h) (sat_cons (step1138 p h) (sat_cons (step1112 p h) (sat_cons (step1114 p h) (sat_cons (step1101 p h) (sat_cons (step1136 p h) (sat_cons (step1109 p h) (sat_cons (step1110 p h) (sat_cons (step1107 p h) (sat_cons (step1098 p h) (sat_cons (step1099 p h) (sat_cons (step9 p h) (sat_cons (step19 p h) (sat_cons (step26 p h) (sat_nil p))))))))))))))))))))))
def c1771 : List Lit := [(1536, true)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c799, c1267, c1271, c1261, c1245, c1247, c1253, c1254, c1242, c1239, c1240, c436, c277, c319, c290] c1771 (by decide) p (sat_cons (step799 p h) (sat_cons (step1267 p h) (sat_cons (step1271 p h) (sat_cons (step1261 p h) (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1253 p h) (sat_cons (step1254 p h) (sat_cons (step1242 p h) (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step436 p h) (sat_cons (step277 p h) (sat_cons (step319 p h) (sat_cons (step290 p h) (sat_nil p))))))))))))))))
def c1772 : List Lit := [(1513, true)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c1221, c1225, c1213, c1215, c1202, c1210, c1211, c1207, c1199, c1200, c153, c171, c203, c160] c1772 (by decide) p (sat_cons (step1221 p h) (sat_cons (step1225 p h) (sat_cons (step1213 p h) (sat_cons (step1215 p h) (sat_cons (step1202 p h) (sat_cons (step1210 p h) (sat_cons (step1211 p h) (sat_cons (step1207 p h) (sat_cons (step1199 p h) (sat_cons (step1200 p h) (sat_cons (step153 p h) (sat_cons (step171 p h) (sat_cons (step203 p h) (sat_cons (step160 p h) (sat_nil p)))))))))))))))
def c1773 : List Lit := [(1612, true), (38, false)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c819, c1431, c1433, c1428, c1429, c1425, c581, c569, c580] c1773 (by decide) p (sat_cons (step819 p h) (sat_cons (step1431 p h) (sat_cons (step1433 p h) (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step1425 p h) (sat_cons (step581 p h) (sat_cons (step569 p h) (sat_cons (step580 p h) (sat_nil p))))))))))
def c1774 : List Lit := [(1479, true), (1602, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c815, c1768, c784, c1417, c1418, c557, c543, c1136, c1138, c558, c1167, c1165, c1141, c1157, c1132, c1133, c72, c67, c1146, c1148, c1155, c126, c1149] c1774 (by decide) p (sat_cons (step815 p h) (sat_cons (step1768 p h) (sat_cons (step784 p h) (sat_cons (step1417 p h) (sat_cons (step1418 p h) (sat_cons (step557 p h) (sat_cons (step543 p h) (sat_cons (step1136 p h) (sat_cons (step1138 p h) (sat_cons (step558 p h) (sat_cons (step1167 p h) (sat_cons (step1165 p h) (sat_cons (step1141 p h) (sat_cons (step1157 p h) (sat_cons (step1132 p h) (sat_cons (step1133 p h) (sat_cons (step72 p h) (sat_cons (step67 p h) (sat_cons (step1146 p h) (sat_cons (step1148 p h) (sat_cons (step1155 p h) (sat_cons (step126 p h) (sat_cons (step1149 p h) (sat_nil p))))))))))))))))))))))))
def c1775 : List Lit := [(26, true), (1474, true), (82, false)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c815, c1157, c558, c1146, c1148, c1155, c126, c1149] c1775 (by decide) p (sat_cons (step815 p h) (sat_cons (step1157 p h) (sat_cons (step558 p h) (sat_cons (step1146 p h) (sat_cons (step1148 p h) (sat_cons (step1155 p h) (sat_cons (step126 p h) (sat_cons (step1149 p h) (sat_nil p)))))))))
def c1776 : List Lit := [(24, false), (1474, true), (82, false)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c815, c789, c1775, c1153, c558, c126, c1151, c104, c90] c1776 (by decide) p (sat_cons (step815 p h) (sat_cons (step789 p h) (sat_cons (step1775 p h) (sat_cons (step1153 p h) (sat_cons (step558 p h) (sat_cons (step126 p h) (sat_cons (step1151 p h) (sat_cons (step104 p h) (sat_cons (step90 p h) (sat_nil p))))))))))
def c1777 : List Lit := [(1474, true), (82, false)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c789, c1775, c1776, c1147, c1155, c1149, c1150, c104, c93] c1777 (by decide) p (sat_cons (step789 p h) (sat_cons (step1775 p h) (sat_cons (step1776 p h) (sat_cons (step1147 p h) (sat_cons (step1155 p h) (sat_cons (step1149 p h) (sat_cons (step1150 p h) (sat_cons (step104 p h) (sat_cons (step93 p h) (sat_nil p))))))))))
def c1778 : List Lit := [(28, false), (30, false), (26, false)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c789, c104, c93] c1778 (by decide) p (sat_cons (step789 p h) (sat_cons (step104 p h) (sat_cons (step93 p h) (sat_nil p))))
def c1779 : List Lit := [(1582, true), (1509, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c806, c1215, c1207, c1213, c1211, c1380, c1382, c1378, c485, c213, c480] c1779 (by decide) p (sat_cons (step806 p h) (sat_cons (step1215 p h) (sat_cons (step1207 p h) (sat_cons (step1213 p h) (sat_cons (step1211 p h) (sat_cons (step1380 p h) (sat_cons (step1382 p h) (sat_cons (step1378 p h) (sat_cons (step485 p h) (sat_cons (step213 p h) (sat_cons (step480 p h) (sat_nil p))))))))))))
def c1780 : List Lit := [(61, false), (63, true), (1509, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c806, c1215, c1207, c1213, c1211, c213, c480] c1780 (by decide) p (sat_cons (step806 p h) (sat_cons (step1215 p h) (sat_cons (step1207 p h) (sat_cons (step1213 p h) (sat_cons (step1211 p h) (sat_cons (step213 p h) (sat_cons (step480 p h) (sat_nil p))))))))
def c1781 : List Lit := [(41, false), (1535, true), (60, true), (65, false), (64, false), (56, true), (42, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c804, c235, c490, c1255, c473, c1266, c1258] c1781 (by decide) p (sat_cons (step804 p h) (sat_cons (step235 p h) (sat_cons (step490 p h) (sat_cons (step1255 p h) (sat_cons (step473 p h) (sat_cons (step1266 p h) (sat_cons (step1258 p h) (sat_nil p))))))))
def c1782 : List Lit := [(1456, true), (13, true), (40, false), (12, true)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c779, c1106, c1110, c1115, c1122, c1126, c1118, c1116, c1101, c1108, c1111, c1098, c1099, c21, c18, c26] c1782 (by decide) p (sat_cons (step779 p h) (sat_cons (step1106 p h) (sat_cons (step1110 p h) (sat_cons (step1115 p h) (sat_cons (step1122 p h) (sat_cons (step1126 p h) (sat_cons (step1118 p h) (sat_cons (step1116 p h) (sat_cons (step1101 p h) (sat_cons (step1108 p h) (sat_cons (step1111 p h) (sat_cons (step1098 p h) (sat_cons (step1099 p h) (sat_cons (step21 p h) (sat_cons (step18 p h) (sat_cons (step26 p h) (sat_nil p)))))))))))))))))
def c1783 : List Lit := [(108, false), (1611, true), (88, false), (38, false)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c585, c583, c1430] c1783 (by decide) p (sat_cons (step585 p h) (sat_cons (step583 p h) (sat_cons (step1430 p h) (sat_nil p))))
def c1784 : List Lit := [(36, true), (37, true), (32, true), (1515, true), (40, false)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c792, c1235, c1206, c1199, c1201, c1205, c161, c1231, c203, c1213, c1211] c1784 (by decide) p (sat_cons (step792 p h) (sat_cons (step1235 p h) (sat_cons (step1206 p h) (sat_cons (step1199 p h) (sat_cons (step1201 p h) (sat_cons (step1205 p h) (sat_cons (step161 p h) (sat_cons (step1231 p h) (sat_cons (step203 p h) (sat_cons (step1213 p h) (sat_cons (step1211 p h) (sat_nil p))))))))))))
def c1785 : List Lit := [(3, false), (15, false), (6, false)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c777, c5, c26] c1785 (by decide) p (sat_cons (step777 p h) (sat_cons (step5 p h) (sat_cons (step26 p h) (sat_nil p))))
def c1786 : List Lit := [(3, true), (1444, true), (12, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c776, c1751, c1099, c1104, c3, c4, c38, c1, c850, c836, c853, c842, c854, c861] c1786 (by decide) p (sat_cons (step776 p h) (sat_cons (step1751 p h) (sat_cons (step1099 p h) (sat_cons (step1104 p h) (sat_cons (step3 p h) (sat_cons (step4 p h) (sat_cons (step38 p h) (sat_cons (step1 p h) (sat_cons (step850 p h) (sat_cons (step836 p h) (sat_cons (step853 p h) (sat_cons (step842 p h) (sat_cons (step854 p h) (sat_cons (step861 p h) (sat_nil p)))))))))))))))
def c1787 : List Lit := [(48, true), (1538, true), (49, false), (53, true), (38, false)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c1254, c1261, c1277, c1250, c1239, c1241, c1247, c310, c1273, c1255, c1264] c1787 (by decide) p (sat_cons (step1254 p h) (sat_cons (step1261 p h) (sat_cons (step1277 p h) (sat_cons (step1250 p h) (sat_cons (step1239 p h) (sat_cons (step1241 p h) (sat_cons (step1247 p h) (sat_cons (step310 p h) (sat_cons (step1273 p h) (sat_cons (step1255 p h) (sat_cons (step1264 p h) (sat_nil p))))))))))))
def c1788 : List Lit := [(1538, true), (49, false), (38, false), (53, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c1787, c313, c309, c1255, c1240, c1264, c1247, c1273] c1788 (by decide) p (sat_cons (step1787 p h) (sat_cons (step313 p h) (sat_cons (step309 p h) (sat_cons (step1255 p h) (sat_cons (step1240 p h) (sat_cons (step1264 p h) (sat_cons (step1247 p h) (sat_cons (step1273 p h) (sat_nil p)))))))))
def c1789 : List Lit := [(1530, true), (64, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c804, c1256, c1257, c473, c467] c1789 (by decide) p (sat_cons (step804 p h) (sat_cons (step1256 p h) (sat_cons (step1257 p h) (sat_cons (step473 p h) (sat_cons (step467 p h) (sat_nil p))))))
def c1790 : List Lit := [(44, false), (55, true), (51, false), (52, false), (48, false)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c801, c276, c344, c386] c1790 (by decide) p (sat_cons (step801 p h) (sat_cons (step276 p h) (sat_cons (step344 p h) (sat_cons (step386 p h) (sat_nil p)))))
def c1791 : List Lit := [(1582, true), (63, false), (40, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c1380, c1382, c1378, c485] c1791 (by decide) p (sat_cons (step1380 p h) (sat_cons (step1382 p h) (sat_cons (step1378 p h) (sat_cons (step485 p h) (sat_nil p)))))
def c1792 : List Lit := [(1582, true), (39, true), (40, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c806, c1382, c1791, c480] c1792 (by decide) p (sat_cons (step806 p h) (sat_cons (step1382 p h) (sat_cons (step1791 p h) (sat_cons (step480 p h) (sat_nil p)))))
def c1793 : List Lit := [(61, false), (71, false), (67, false), (39, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c806, c479, c525] c1793 (by decide) p (sat_cons (step806 p h) (sat_cons (step479 p h) (sat_cons (step525 p h) (sat_nil p))))
def c1794 : List Lit := [(108, true), (1668, true), (110, true), (232, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c831, c1546, c743, c1555, c739, c1549] c1794 (by decide) p (sat_cons (step831 p h) (sat_cons (step1546 p h) (sat_cons (step743 p h) (sat_cons (step1555 p h) (sat_cons (step739 p h) (sat_cons (step1549 p h) (sat_nil p)))))))
def c1795 : List Lit := [(1644, true), (1648, true), (97, true), (39, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c820, c1501, c1504, c1506, c1502, c1497, c1498, c597, c605, c653, c654, c1513] c1795 (by decide) p (sat_cons (step820 p h) (sat_cons (step1501 p h) (sat_cons (step1504 p h) (sat_cons (step1506 p h) (sat_cons (step1502 p h) (sat_cons (step1497 p h) (sat_cons (step1498 p h) (sat_cons (step597 p h) (sat_cons (step605 p h) (sat_cons (step653 p h) (sat_cons (step654 p h) (sat_cons (step1513 p h) (sat_nil p)))))))))))))
def c1796 : List Lit := [(1478, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c1768, c784, c783, c1161, c1164, c1157, c1138, c1140, c1136, c1132, c1133, c72, c66, c67, c62, c1148] c1796 (by decide) p (sat_cons (step1768 p h) (sat_cons (step784 p h) (sat_cons (step783 p h) (sat_cons (step1161 p h) (sat_cons (step1164 p h) (sat_cons (step1157 p h) (sat_cons (step1138 p h) (sat_cons (step1140 p h) (sat_cons (step1136 p h) (sat_cons (step1132 p h) (sat_cons (step1133 p h) (sat_cons (step72 p h) (sat_cons (step66 p h) (sat_cons (step67 p h) (sat_cons (step62 p h) (sat_cons (step1148 p h) (sat_nil p)))))))))))))))))
def c1797 : List Lit := [(12, true), (3, false), (1451, true)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c1117, c1106, c1108, c1115, c1785, c1109] c1797 (by decide) p (sat_cons (step1117 p h) (sat_cons (step1106 p h) (sat_cons (step1108 p h) (sat_cons (step1115 p h) (sat_cons (step1785 p h) (sat_cons (step1109 p h) (sat_nil p)))))))
end B112E004
