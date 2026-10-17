import B112E213Part0008
namespace B112E213
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1780 : List Lit := [(833, true), (16, false), (15, true), (825, false), (21, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c758, c767, c773, c777, c770, c752, c759, c750, c82, c1450] c1780 (by decide) p (sat_cons (step758 p h) (sat_cons (step767 p h) (sat_cons (step773 p h) (sat_cons (step777 p h) (sat_cons (step770 p h) (sat_cons (step752 p h) (sat_cons (step759 p h) (sat_cons (step750 p h) (sat_cons (step82 p h) (sat_cons (step1450 p h) (sat_nil p)))))))))))
def c1781 : List Lit := [(94, true), (457, true), (942, false), (1038, true), (1055, true)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c1074, c1389, c1779, c1247] c1781 (by decide) p (sat_cons (step1074 p h) (sat_cons (step1389 p h) (sat_cons (step1779 p h) (sat_cons (step1247 p h) (sat_nil p)))))
def c1782 : List Lit := [(930, false), (944, true), (42, false)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c1016, c989, c992, c1014, c1777, c1001] c1782 (by decide) p (sat_cons (step1016 p h) (sat_cons (step989 p h) (sat_cons (step992 p h) (sat_cons (step1014 p h) (sat_cons (step1777 p h) (sat_cons (step1001 p h) (sat_nil p)))))))
def c1783 : List Lit := [(936, true), (62, false), (14, false), (44, false)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c996, c1686, c347] c1783 (by decide) p (sat_cons (step996 p h) (sat_cons (step1686 p h) (sat_cons (step347 p h) (sat_nil p))))
def c1784 : List Lit := [(944, true), (14, false), (64, true), (871, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c985, c988, c853, c852, c1011, c1782, c987, c1783, c999, c1002, c1014, c1777, c991] c1784 (by decide) p (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step853 p h) (sat_cons (step852 p h) (sat_cons (step1011 p h) (sat_cons (step1782 p h) (sat_cons (step987 p h) (sat_cons (step1783 p h) (sat_cons (step999 p h) (sat_cons (step1002 p h) (sat_cons (step1014 p h) (sat_cons (step1777 p h) (sat_cons (step991 p h) (sat_nil p))))))))))))))
def c1785 : List Lit := [(842, true), (15, false), (833, false), (828, false), (74, false)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c1552, c799, c782, c1592, c42, c38, c750, c755] c1785 (by decide) p (sat_cons (step1552 p h) (sat_cons (step799 p h) (sat_cons (step782 p h) (sat_cons (step1592 p h) (sat_cons (step42 p h) (sat_cons (step38 p h) (sat_cons (step750 p h) (sat_cons (step755 p h) (sat_nil p)))))))))
def c1786 : List Lit := [(944, false), (988, false), (965, false), (1055, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c1067, c1732] c1786 (by decide) p (sat_cons (step1067 p h) (sat_cons (step1732 p h) (sat_nil p)))
def c1787 : List Lit := [(819, true), (74, false)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c752, c754, c749, c750, c81, c52, c1450] c1787 (by decide) p (sat_cons (step752 p h) (sat_cons (step754 p h) (sat_cons (step749 p h) (sat_cons (step750 p h) (sat_cons (step81 p h) (sat_cons (step52 p h) (sat_cons (step1450 p h) (sat_nil p))))))))
def c1788 : List Lit := [(824, true), (23, false), (35, false)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c760, c761, c129] c1788 (by decide) p (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step129 p h) (sat_nil p))))
def c1789 : List Lit := [(17, false), (16, false), (15, true), (22, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c1450, c82] c1789 (by decide) p (sat_cons (step1450 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1790 : List Lit := [(14, true), (807, true)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c725, c1696] c1790 (by decide) p (sat_cons (step725 p h) (sat_cons (step1696 p h) (sat_nil p)))
def c1791 : List Lit := [(812, true), (1, true), (6, true)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c714, c720, c747, c721, c745, c716, c730, c1436, c722, c723, c23] c1791 (by decide) p (sat_cons (step714 p h) (sat_cons (step720 p h) (sat_cons (step747 p h) (sat_cons (step721 p h) (sat_cons (step745 p h) (sat_cons (step716 p h) (sat_cons (step730 p h) (sat_cons (step1436 p h) (sat_cons (step722 p h) (sat_cons (step723 p h) (sat_cons (step23 p h) (sat_nil p))))))))))))
def c1792 : List Lit := [(943, true), (929, false), (42, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c988, c1013, c1010, c991, c1001, c1777] c1792 (by decide) p (sat_cons (step988 p h) (sat_cons (step1013 p h) (sat_cons (step1010 p h) (sat_cons (step991 p h) (sat_cons (step1001 p h) (sat_cons (step1777 p h) (sat_nil p)))))))
def c1793 : List Lit := [(953, false), (64, true), (1054, true), (871, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c853, c985, c1792, c852, c1045, c1378, c1782, c987, c1739, c1075, c1528, c288] c1793 (by decide) p (sat_cons (step853 p h) (sat_cons (step985 p h) (sat_cons (step1792 p h) (sat_cons (step852 p h) (sat_cons (step1045 p h) (sat_cons (step1378 p h) (sat_cons (step1782 p h) (sat_cons (step987 p h) (sat_cons (step1739 p h) (sat_cons (step1075 p h) (sat_cons (step1528 p h) (sat_cons (step288 p h) (sat_nil p)))))))))))))
def c1794 : List Lit := [(951, true), (16, false), (74, false)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c1020, c1021, c1424] c1794 (by decide) p (sat_cons (step1020 p h) (sat_cons (step1021 p h) (sat_cons (step1424 p h) (sat_nil p))))
def c1795 : List Lit := [(866, true), (858, false), (27, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c826, c817, c840, c844, c829, c818, c1709] c1795 (by decide) p (sat_cons (step826 p h) (sat_cons (step817 p h) (sat_cons (step840 p h) (sat_cons (step844 p h) (sat_cons (step829 p h) (sat_cons (step818 p h) (sat_cons (step1709 p h) (sat_nil p))))))))
def c1796 : List Lit := [(901, true), (856, false), (885, false), (866, false), (39, true), (94, false), (42, false), (853, false)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c882, c925, c919, c841, c886, c830, c858, c825, c855, c1274, c1470, c279] c1796 (by decide) p (sat_cons (step882 p h) (sat_cons (step925 p h) (sat_cons (step919 p h) (sat_cons (step841 p h) (sat_cons (step886 p h) (sat_cons (step830 p h) (sat_cons (step858 p h) (sat_cons (step825 p h) (sat_cons (step855 p h) (sat_cons (step1274 p h) (sat_cons (step1470 p h) (sat_cons (step279 p h) (sat_nil p)))))))))))))
def c1797 : List Lit := [(851, true), (1054, true), (943, false), (953, false)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c1349, c812, c813, c1681, c197] c1797 (by decide) p (sat_cons (step1349 p h) (sat_cons (step812 p h) (sat_cons (step813 p h) (sat_cons (step1681 p h) (sat_cons (step197 p h) (sat_nil p))))))
def c1798 : List Lit := [(884, false), (856, false), (901, true), (854, false), (39, true), (94, false), (42, false)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c824, c829, c845, c925, c881, c885, c932, c858, c846, c855, c1274, c830, c1479, c825, c279] c1798 (by decide) p (sat_cons (step824 p h) (sat_cons (step829 p h) (sat_cons (step845 p h) (sat_cons (step925 p h) (sat_cons (step881 p h) (sat_cons (step885 p h) (sat_cons (step932 p h) (sat_cons (step858 p h) (sat_cons (step846 p h) (sat_cons (step855 p h) (sat_cons (step1274 p h) (sat_cons (step830 p h) (sat_cons (step1479 p h) (sat_cons (step825 p h) (sat_cons (step279 p h) (sat_nil p))))))))))))))))
def c1799 : List Lit := [(884, true), (988, true), (56, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c869, c873, c875, c871, c1275] c1799 (by decide) p (sat_cons (step869 p h) (sat_cons (step873 p h) (sat_cons (step875 p h) (sat_cons (step871 p h) (sat_cons (step1275 p h) (sat_nil p))))))
def c1800 : List Lit := [(943, true), (885, true), (871, true), (56, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c853, c852, c1776, c1792, c996, c986, c1366, c1686, c871, c354, c876, c866] c1800 (by decide) p (sat_cons (step853 p h) (sat_cons (step852 p h) (sat_cons (step1776 p h) (sat_cons (step1792 p h) (sat_cons (step996 p h) (sat_cons (step986 p h) (sat_cons (step1366 p h) (sat_cons (step1686 p h) (sat_cons (step871 p h) (sat_cons (step354 p h) (sat_cons (step876 p h) (sat_cons (step866 p h) (sat_nil p)))))))))))))
def c1801 : List Lit := [(1053, true), (988, false), (871, true), (953, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c1077, c853, c852, c1045, c1053, c1133, c1369, c1253, c1776, c1792, c996, c986, c1686, c358, c1233, c1236, c1096, c1099, c1252, c1080, c1137, c1391, c1054] c1801 (by decide) p (sat_cons (step1077 p h) (sat_cons (step853 p h) (sat_cons (step852 p h) (sat_cons (step1045 p h) (sat_cons (step1053 p h) (sat_cons (step1133 p h) (sat_cons (step1369 p h) (sat_cons (step1253 p h) (sat_cons (step1776 p h) (sat_cons (step1792 p h) (sat_cons (step996 p h) (sat_cons (step986 p h) (sat_cons (step1686 p h) (sat_cons (step358 p h) (sat_cons (step1233 p h) (sat_cons (step1236 p h) (sat_cons (step1096 p h) (sat_cons (step1099 p h) (sat_cons (step1252 p h) (sat_cons (step1080 p h) (sat_cons (step1137 p h) (sat_cons (step1391 p h) (sat_cons (step1054 p h) (sat_nil p))))))))))))))))))))))))
def c1802 : List Lit := [(884, true), (871, true), (56, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c852, c869, c873, c875, c871, c866, c1356, c353, c1473] c1802 (by decide) p (sat_cons (step852 p h) (sat_cons (step869 p h) (sat_cons (step873 p h) (sat_cons (step875 p h) (sat_cons (step871 p h) (sat_cons (step866 p h) (sat_cons (step1356 p h) (sat_cons (step353 p h) (sat_cons (step1473 p h) (sat_nil p))))))))))
def c1803 : List Lit := [(841, true), (822, false), (17, true), (1, true), (819, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c1592, c1556, c798, c1791, c1704, c776, c766, c760, c761, c109] c1803 (by decide) p (sat_cons (step1592 p h) (sat_cons (step1556 p h) (sat_cons (step798 p h) (sat_cons (step1791 p h) (sat_cons (step1704 p h) (sat_cons (step776 p h) (sat_cons (step766 p h) (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step109 p h) (sat_nil p)))))))))))
def c1804 : List Lit := [(832, true), (25, false), (64, false), (822, false), (17, true), (819, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c1704, c776, c130, c766, c761] c1804 (by decide) p (sat_cons (step1704 p h) (sat_cons (step776 p h) (sat_cons (step130 p h) (sat_cons (step766 p h) (sat_cons (step761 p h) (sat_nil p))))))
def c1805 : List Lit := [(1053, true), (871, true), (42, false), (953, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c852, c1369, c1801, c1792, c1075, c986, c1528, c288] c1805 (by decide) p (sat_cons (step852 p h) (sat_cons (step1369 p h) (sat_cons (step1801 p h) (sat_cons (step1792 p h) (sat_cons (step1075 p h) (sat_cons (step986 p h) (sat_cons (step1528 p h) (sat_cons (step288 p h) (sat_nil p)))))))))
def c1806 : List Lit := [(65, true), (56, false), (64, false), (23, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c1498, c1499, c1200] c1806 (by decide) p (sat_cons (step1498 p h) (sat_cons (step1499 p h) (sat_cons (step1200 p h) (sat_nil p))))
def c1807 : List Lit := [(827, true), (23, true), (25, false), (21, true)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c758, c768, c766, c759, c761, c1454, c153] c1807 (by decide) p (sat_cons (step758 p h) (sat_cons (step768 p h) (sat_cons (step766 p h) (sat_cons (step759 p h) (sat_cons (step761 p h) (sat_cons (step1454 p h) (sat_cons (step153 p h) (sat_nil p))))))))
def c1808 : List Lit := [(834, false), (29, true), (866, false), (94, false), (921, true), (799, false), (843, true)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1552, c800, c967, c740, c918, c730, c1763, c723, c1756, c1440] c1808 (by decide) p (sat_cons (step1552 p h) (sat_cons (step800 p h) (sat_cons (step967 p h) (sat_cons (step740 p h) (sat_cons (step918 p h) (sat_cons (step730 p h) (sat_cons (step1763 p h) (sat_cons (step723 p h) (sat_cons (step1756 p h) (sat_cons (step1440 p h) (sat_nil p)))))))))))
def c1809 : List Lit := [(23, true), (827, true), (811, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c1331, c740, c730, c722, c1442, c723, c23, c1736, c758, c1807, c766, c760] c1809 (by decide) p (sat_cons (step1331 p h) (sat_cons (step740 p h) (sat_cons (step730 p h) (sat_cons (step722 p h) (sat_cons (step1442 p h) (sat_cons (step723 p h) (sat_cons (step23 p h) (sat_cons (step1736 p h) (sat_cons (step758 p h) (sat_cons (step1807 p h) (sat_cons (step766 p h) (sat_cons (step760 p h) (sat_nil p)))))))))))))
def c1810 : List Lit := [(824, true), (23, false), (6, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c760, c761, c109] c1810 (by decide) p (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step109 p h) (sat_nil p))))
def c1811 : List Lit := [(842, true), (821, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1552, c799, c785, c1770, c764, c1809, c1810, c766, c758, c104, c105, c762] c1811 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1552 p h) (sat_cons (step799 p h) (sat_cons (step785 p h) (sat_cons (step1770 p h) (sat_cons (step764 p h) (sat_cons (step1809 p h) (sat_cons (step1810 p h) (sat_cons (step766 p h) (sat_cons (step758 p h) (sat_cons (step104 p h) (sat_cons (step105 p h) (sat_cons (step762 p h) (sat_nil p))))))))))))))
def c1812 : List Lit := [(27, true), (854, true), (858, false), (94, false), (900, true), (35, true), (22, false), (24, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c817, c818, c1684, c812, c813, c822, c229, c154, c1469] c1812 (by decide) p (sat_cons (step817 p h) (sat_cons (step818 p h) (sat_cons (step1684 p h) (sat_cons (step812 p h) (sat_cons (step813 p h) (sat_cons (step822 p h) (sat_cons (step229 p h) (sat_cons (step154 p h) (sat_cons (step1469 p h) (sat_nil p))))))))))
def c1813 : List Lit := [(37, false), (22, false), (852, true), (24, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c154, c1469, c230, c233, c814] c1813 (by decide) p (sat_cons (step154 p h) (sat_cons (step1469 p h) (sat_cons (step230 p h) (sat_cons (step233 p h) (sat_cons (step814 p h) (sat_nil p))))))
def c1814 : List Lit := [(8, false), (33, false), (874, true), (94, false), (27, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1756, c171, c1440] c1814 (by decide) p (sat_cons (step1756 p h) (sat_cons (step171 p h) (sat_cons (step1440 p h) (sat_nil p))))
def c1815 : List Lit := [(17, true), (822, false), (799, true), (833, true), (22, false)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c717, c715, c714, c1437, c17, c1331, c781, c753, c750, c751, c752, c755, c777, c767, c762, c147, c93, c1455] c1815 (by decide) p (sat_cons (step717 p h) (sat_cons (step715 p h) (sat_cons (step714 p h) (sat_cons (step1437 p h) (sat_cons (step17 p h) (sat_cons (step1331 p h) (sat_cons (step781 p h) (sat_cons (step753 p h) (sat_cons (step750 p h) (sat_cons (step751 p h) (sat_cons (step752 p h) (sat_cons (step755 p h) (sat_cons (step777 p h) (sat_cons (step767 p h) (sat_cons (step762 p h) (sat_cons (step147 p h) (sat_cons (step93 p h) (sat_cons (step1455 p h) (sat_nil p)))))))))))))))))))
def c1816 : List Lit := [(17, false), (1, false), (18, true), (27, false)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c40, c1450] c1816 (by decide) p (sat_cons (step40 p h) (sat_cons (step1450 p h) (sat_nil p)))
def c1817 : List Lit := [(27, false), (30, false), (931, false), (954, false), (856, false), (20, false), (16, false), (832, false), (22, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c84, c1705, c164, c1708, c191, c192, c1462, c1703, c994, c1031, c215, c232, c231, c726, c1033, c997, c1662, c1039, c1002, c798, c1051, c1011, c957, c1070, c1562, c1262] c1817 (by decide) p (sat_cons (step84 p h) (sat_cons (step1705 p h) (sat_cons (step164 p h) (sat_cons (step1708 p h) (sat_cons (step191 p h) (sat_cons (step192 p h) (sat_cons (step1462 p h) (sat_cons (step1703 p h) (sat_cons (step994 p h) (sat_cons (step1031 p h) (sat_cons (step215 p h) (sat_cons (step232 p h) (sat_cons (step231 p h) (sat_cons (step726 p h) (sat_cons (step1033 p h) (sat_cons (step997 p h) (sat_cons (step1662 p h) (sat_cons (step1039 p h) (sat_cons (step1002 p h) (sat_cons (step798 p h) (sat_cons (step1051 p h) (sat_cons (step1011 p h) (sat_cons (step957 p h) (sat_cons (step1070 p h) (sat_cons (step1562 p h) (sat_cons (step1262 p h) (sat_nil p)))))))))))))))))))))))))))
def c1818 : List Lit := [(34, false), (27, true), (30, false), (931, false), (954, false), (856, false), (953, false), (832, false), (22, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1049, c215, c229, c232, c231, c726, c812, c1033, c997, c1662, c818, c1036, c999, c798, c1394, c1050, c1010, c1563, c1064, c1637, c1259, c1011, c1564, c1382, c959] c1818 (by decide) p (sat_cons (step1049 p h) (sat_cons (step215 p h) (sat_cons (step229 p h) (sat_cons (step232 p h) (sat_cons (step231 p h) (sat_cons (step726 p h) (sat_cons (step812 p h) (sat_cons (step1033 p h) (sat_cons (step997 p h) (sat_cons (step1662 p h) (sat_cons (step818 p h) (sat_cons (step1036 p h) (sat_cons (step999 p h) (sat_cons (step798 p h) (sat_cons (step1394 p h) (sat_cons (step1050 p h) (sat_cons (step1010 p h) (sat_cons (step1563 p h) (sat_cons (step1064 p h) (sat_cons (step1637 p h) (sat_cons (step1259 p h) (sat_cons (step1011 p h) (sat_cons (step1564 p h) (sat_cons (step1382 p h) (sat_cons (step959 p h) (sat_nil p))))))))))))))))))))))))))
def c1819 : List Lit := [(854, false), (900, true), (944, false), (1056, true), (811, false), (861, false), (856, false), (832, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c845, c1394, c1380, c924, c1563, c1687, c1368, c1768, c852, c1236, c357, c1233] c1819 (by decide) p (sat_cons (step845 p h) (sat_cons (step1394 p h) (sat_cons (step1380 p h) (sat_cons (step924 p h) (sat_cons (step1563 p h) (sat_cons (step1687 p h) (sat_cons (step1368 p h) (sat_cons (step1768 p h) (sat_cons (step852 p h) (sat_cons (step1236 p h) (sat_cons (step357 p h) (sat_cons (step1233 p h) (sat_nil p)))))))))))))
def c1820 : List Lit := [(944, false), (811, false), (29, false), (27, true), (30, false), (861, false), (954, false), (856, false), (953, false), (832, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c817, c1703, c798, c957, c1562, c1262, c1049, c1070, c1378, c1068, c1051, c1564, c1153, c959, c1252, c1241, c1819, c818, c812, c1623, c197, c1563, c1569, c958, c1080, c1679, c1074] c1820 (by decide) p (sat_cons (step817 p h) (sat_cons (step1703 p h) (sat_cons (step798 p h) (sat_cons (step957 p h) (sat_cons (step1562 p h) (sat_cons (step1262 p h) (sat_cons (step1049 p h) (sat_cons (step1070 p h) (sat_cons (step1378 p h) (sat_cons (step1068 p h) (sat_cons (step1051 p h) (sat_cons (step1564 p h) (sat_cons (step1153 p h) (sat_cons (step959 p h) (sat_cons (step1252 p h) (sat_cons (step1241 p h) (sat_cons (step1819 p h) (sat_cons (step818 p h) (sat_cons (step812 p h) (sat_cons (step1623 p h) (sat_cons (step197 p h) (sat_cons (step1563 p h) (sat_cons (step1569 p h) (sat_cons (step958 p h) (sat_cons (step1080 p h) (sat_cons (step1679 p h) (sat_cons (step1074 p h) (sat_nil p))))))))))))))))))))))))))))
def c1821 : List Lit := [(934, false), (944, true), (34, true), (64, true), (22, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c985, c988, c1011, c1001, c1002, c1014, c996, c997, c989, c987, c402, c426, c1509] c1821 (by decide) p (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step1011 p h) (sat_cons (step1001 p h) (sat_cons (step1002 p h) (sat_cons (step1014 p h) (sat_cons (step996 p h) (sat_cons (step997 p h) (sat_cons (step989 p h) (sat_cons (step987 p h) (sat_cons (step402 p h) (sat_cons (step426 p h) (sat_cons (step1509 p h) (sat_nil p))))))))))))))
def c1822 : List Lit := [(811, false), (29, false), (27, true), (30, false), (861, false), (954, false), (856, false), (64, true), (953, false), (832, false), (22, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c985, c988, c1818, c1009, c798, c1820, c1011, c1821, c994, c196, c198, c812, c1031, c818, c1038, c1382, c1050, c959, c1059, c1564, c1259, c1147, c1060, c1251, c1051, c1240, c1569, c1079] c1822 (by decide) p (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step1818 p h) (sat_cons (step1009 p h) (sat_cons (step798 p h) (sat_cons (step1820 p h) (sat_cons (step1011 p h) (sat_cons (step1821 p h) (sat_cons (step994 p h) (sat_cons (step196 p h) (sat_cons (step198 p h) (sat_cons (step812 p h) (sat_cons (step1031 p h) (sat_cons (step818 p h) (sat_cons (step1038 p h) (sat_cons (step1382 p h) (sat_cons (step1050 p h) (sat_cons (step959 p h) (sat_cons (step1059 p h) (sat_cons (step1564 p h) (sat_cons (step1259 p h) (sat_cons (step1147 p h) (sat_cons (step1060 p h) (sat_cons (step1251 p h) (sat_cons (step1051 p h) (sat_cons (step1240 p h) (sat_cons (step1569 p h) (sat_cons (step1079 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1823 : List Lit := [(1054, true), (83, true), (942, false), (954, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1031, c1038, c1050, c1059, c1259, c1147, c1060, c1251, c1051, c1240, c1569, c1079] c1823 (by decide) p (sat_cons (step1031 p h) (sat_cons (step1038 p h) (sat_cons (step1050 p h) (sat_cons (step1059 p h) (sat_cons (step1259 p h) (sat_cons (step1147 p h) (sat_cons (step1060 p h) (sat_cons (step1251 p h) (sat_cons (step1051 p h) (sat_cons (step1240 p h) (sat_cons (step1569 p h) (sat_cons (step1079 p h) (sat_nil p)))))))))))))
def c1824 : List Lit := [(943, true), (53, true), (64, true)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c985, c988, c1013, c1010, c989, c999, c987, c1686] c1824 (by decide) p (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step1013 p h) (sat_cons (step1010 p h) (sat_cons (step989 p h) (sat_cons (step999 p h) (sat_cons (step987 p h) (sat_cons (step1686 p h) (sat_nil p)))))))))
def c1825 : List Lit := [(66, false), (939, true), (807, true), (29, false), (34, true), (27, true), (30, false), (954, false), (856, false), (64, true), (840, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c196, c175, c198, c812, c1264, c1031, c818, c1038, c1382, c1050, c951, c1563, c1260, c1824, c1064, c1065, c1152, c1051, c1251, c1569, c1240, c1079] c1825 (by decide) p (sat_cons (step196 p h) (sat_cons (step175 p h) (sat_cons (step198 p h) (sat_cons (step812 p h) (sat_cons (step1264 p h) (sat_cons (step1031 p h) (sat_cons (step818 p h) (sat_cons (step1038 p h) (sat_cons (step1382 p h) (sat_cons (step1050 p h) (sat_cons (step951 p h) (sat_cons (step1563 p h) (sat_cons (step1260 p h) (sat_cons (step1824 p h) (sat_cons (step1064 p h) (sat_cons (step1065 p h) (sat_cons (step1152 p h) (sat_cons (step1051 p h) (sat_cons (step1251 p h) (sat_cons (step1569 p h) (sat_cons (step1240 p h) (sat_cons (step1079 p h) (sat_nil p)))))))))))))))))))))))
def c1826 : List Lit := [(91, true), (991, true), (978, false), (840, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1079, c1080, c1240, c1074, c1251, c1679, c1155, c950, c1562] c1826 (by decide) p (sat_cons (step1079 p h) (sat_cons (step1080 p h) (sat_cons (step1240 p h) (sat_cons (step1074 p h) (sat_cons (step1251 p h) (sat_cons (step1679 p h) (sat_cons (step1155 p h) (sat_cons (step950 p h) (sat_cons (step1562 p h) (sat_nil p))))))))))
def c1827 : List Lit := [(967, true), (74, true), (954, false), (951, false), (20, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1052, c1050, c1029, c1036, c1038, c1019, c1034, c1031, c469, c448, c1514] c1827 (by decide) p (sat_cons (step1052 p h) (sat_cons (step1050 p h) (sat_cons (step1029 p h) (sat_cons (step1036 p h) (sat_cons (step1038 p h) (sat_cons (step1019 p h) (sat_cons (step1034 p h) (sat_cons (step1031 p h) (sat_cons (step469 p h) (sat_cons (step448 p h) (sat_cons (step1514 p h) (sat_nil p))))))))))))
def c1828 : List Lit := [(83, false), (967, false), (807, true), (29, false), (34, true), (27, true), (30, false), (861, false), (856, false), (64, true), (840, false), (22, false)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c176, c197, c198, c1264, c812, c994, c818, c1821, c845, c1069, c1260, c1563, c951, c1380, c924, c1687] c1828 (by decide) p (sat_cons (step176 p h) (sat_cons (step197 p h) (sat_cons (step198 p h) (sat_cons (step1264 p h) (sat_cons (step812 p h) (sat_cons (step994 p h) (sat_cons (step818 p h) (sat_cons (step1821 p h) (sat_cons (step845 p h) (sat_cons (step1069 p h) (sat_cons (step1260 p h) (sat_cons (step1563 p h) (sat_cons (step951 p h) (sat_cons (step1380 p h) (sat_cons (step924 p h) (sat_cons (step1687 p h) (sat_nil p)))))))))))))))))
def c1829 : List Lit := [(979, false), (1057, true), (840, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1159, c1562, c1251, c950, c1240, c1679, c1077, c1074] c1829 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1159 p h) (sat_cons (step1562 p h) (sat_cons (step1251 p h) (sat_cons (step950 p h) (sat_cons (step1240 p h) (sat_cons (step1679 p h) (sat_cons (step1077 p h) (sat_cons (step1074 p h) (sat_nil p))))))))))
def c1830 : List Lit := [(944, true), (807, true), (29, false), (34, true), (27, true), (30, false), (954, false), (856, false), (64, true), (840, false), (22, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c985, c988, c1011, c1821, c1825, c994] c1830 (by decide) p (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step1011 p h) (sat_cons (step1821 p h) (sat_cons (step1825 p h) (sat_cons (step994 p h) (sat_nil p)))))))
def c1831 : List Lit := [(30, false), (861, false), (954, false), (951, false), (856, false), (64, true), (953, false), (2, false), (15, true), (20, false), (16, false), (832, false), (22, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c985, c988, c84, c1550, c1817, c817, c1703, c949, c1561, c1818, c1461, c1462, c74, c1512, c1822, c737, c1827, c1828, c1829, c1830, c1069, c1070, c1156, c1051, c1252, c1569, c1241, c1826] c1831 (by decide) p (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step84 p h) (sat_cons (step1550 p h) (sat_cons (step1817 p h) (sat_cons (step817 p h) (sat_cons (step1703 p h) (sat_cons (step949 p h) (sat_cons (step1561 p h) (sat_cons (step1818 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step74 p h) (sat_cons (step1512 p h) (sat_cons (step1822 p h) (sat_cons (step737 p h) (sat_cons (step1827 p h) (sat_cons (step1828 p h) (sat_cons (step1829 p h) (sat_cons (step1830 p h) (sat_cons (step1069 p h) (sat_cons (step1070 p h) (sat_cons (step1156 p h) (sat_cons (step1051 p h) (sat_cons (step1252 p h) (sat_cons (step1569 p h) (sat_cons (step1241 p h) (sat_cons (step1826 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1832 : List Lit := [(900, true), (867, false), (854, false), (14, false), (856, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1380, c924, c1687, c1322] c1832 (by decide) p (sat_cons (step1380 p h) (sat_cons (step924 p h) (sat_cons (step1687 p h) (sat_cons (step1322 p h) (sat_nil p)))))
def c1833 : List Lit := [(1055, true), (944, false), (954, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1049, c1068, c1260, c1152, c1069, c1251, c1050, c1240, c1036, c1038, c1079, c1034, c1030, c1377] c1833 (by decide) p (sat_cons (step1049 p h) (sat_cons (step1068 p h) (sat_cons (step1260 p h) (sat_cons (step1152 p h) (sat_cons (step1069 p h) (sat_cons (step1251 p h) (sat_cons (step1050 p h) (sat_cons (step1240 p h) (sat_cons (step1036 p h) (sat_cons (step1038 p h) (sat_cons (step1079 p h) (sat_cons (step1034 p h) (sat_cons (step1030 p h) (sat_cons (step1377 p h) (sat_nil p)))))))))))))))
def c1834 : List Lit := [(967, true), (954, false), (81, true), (15, true), (20, false), (21, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1020, c1052, c1050, c1827, c1036, c1038, c1511, c1034, c1030, c1031, c449, c471, c1022, c1524, c1027, c448, c1017] c1834 (by decide) p (sat_cons (step1020 p h) (sat_cons (step1052 p h) (sat_cons (step1050 p h) (sat_cons (step1827 p h) (sat_cons (step1036 p h) (sat_cons (step1038 p h) (sat_cons (step1511 p h) (sat_cons (step1034 p h) (sat_cons (step1030 p h) (sat_cons (step1031 p h) (sat_cons (step449 p h) (sat_cons (step471 p h) (sat_cons (step1022 p h) (sat_cons (step1524 p h) (sat_cons (step1027 p h) (sat_cons (step448 p h) (sat_cons (step1017 p h) (sat_nil p))))))))))))))))))
def c1835 : List Lit := [(854, false), (14, false), (900, true), (861, false), (856, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c845, c1832] c1835 (by decide) p (sat_cons (step845 p h) (sat_cons (step1832 p h) (sat_nil p)))
def c1836 : List Lit := [(29, false), (854, true), (83, false), (851, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c818, c1429, c194] c1836 (by decide) p (sat_cons (step818 p h) (sat_cons (step1429 p h) (sat_cons (step194 p h) (sat_nil p))))
def c1837 : List Lit := [(854, true), (90, false), (83, false), (30, true)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c813, c816, c1836, c1408, c814] c1837 (by decide) p (sat_cons (step813 p h) (sat_cons (step816 p h) (sat_cons (step1836 p h) (sat_cons (step1408 p h) (sat_cons (step814 p h) (sat_nil p))))))
def c1838 : List Lit := [(944, false), (967, false), (30, true), (861, false), (954, false), (856, false), (832, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1550, c813, c815, c1703, c949, c1561, c1829, c1070, c1051, c1833, c1563, c951, c1069, c1156, c1252, c1241, c1826, c1569, c1390, c1837, c1394, c1835, c1662, c725] c1838 (by decide) p (sat_cons (step1550 p h) (sat_cons (step813 p h) (sat_cons (step815 p h) (sat_cons (step1703 p h) (sat_cons (step949 p h) (sat_cons (step1561 p h) (sat_cons (step1829 p h) (sat_cons (step1070 p h) (sat_cons (step1051 p h) (sat_cons (step1833 p h) (sat_cons (step1563 p h) (sat_cons (step951 p h) (sat_cons (step1069 p h) (sat_cons (step1156 p h) (sat_cons (step1252 p h) (sat_cons (step1241 p h) (sat_cons (step1826 p h) (sat_cons (step1569 p h) (sat_cons (step1390 p h) (sat_cons (step1837 p h) (sat_cons (step1394 p h) (sat_cons (step1835 p h) (sat_cons (step1662 p h) (sat_cons (step725 p h) (sat_nil p)))))))))))))))))))))))))
def c1839 : List Lit := [(841, false), (900, false), (867, false), (967, false), (64, true), (953, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c985, c988, c1009, c1059, c1258, c1565, c960, c959, c925, c1564, c1259, c1793, c1147, c1064, c860, c1251, c1010, c1824, c885, c1240, c999, c1077, c996, c1074, c1302, c1293] c1839 (by decide) p (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step1009 p h) (sat_cons (step1059 p h) (sat_cons (step1258 p h) (sat_cons (step1565 p h) (sat_cons (step960 p h) (sat_cons (step959 p h) (sat_cons (step925 p h) (sat_cons (step1564 p h) (sat_cons (step1259 p h) (sat_cons (step1793 p h) (sat_cons (step1147 p h) (sat_cons (step1064 p h) (sat_cons (step860 p h) (sat_cons (step1251 p h) (sat_cons (step1010 p h) (sat_cons (step1824 p h) (sat_cons (step885 p h) (sat_cons (step1240 p h) (sat_cons (step999 p h) (sat_cons (step1077 p h) (sat_cons (step996 p h) (sat_cons (step1074 p h) (sat_cons (step1302 p h) (sat_cons (step1293 p h) (sat_nil p)))))))))))))))))))))))))))
def c1840 : List Lit := [(943, true), (100, false), (14, false), (64, true)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c985, c988, c1010, c1824, c999, c352, c996] c1840 (by decide) p (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step1010 p h) (sat_cons (step1824 p h) (sat_cons (step999 p h) (sat_cons (step352 p h) (sat_cons (step996 p h) (sat_nil p))))))))
def c1841 : List Lit := [(889, true), (988, true), (871, false), (38, false), (1, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c860, c885, c1799, c264, c856, c1764, c861] c1841 (by decide) p (sat_cons (step860 p h) (sat_cons (step885 p h) (sat_cons (step1799 p h) (sat_cons (step264 p h) (sat_cons (step856 p h) (sat_cons (step1764 p h) (sat_cons (step861 p h) (sat_nil p))))))))
def c1842 : List Lit := [(37, false), (13, false), (20, false), (22, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c149, c217, c1469] c1842 (by decide) p (sat_cons (step149 p h) (sat_cons (step217 p h) (sat_cons (step1469 p h) (sat_nil p))))
def c1843 : List Lit := [(854, false), (944, true), (967, false), (858, false), (64, true), (35, true), (953, false), (38, false), (20, false), (799, true), (819, false), (22, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c1331, c776, c1550, c985, c988, c1009, c1059, c1258, c1565, c953, c1011, c821, c829, c719, c845, c1382, c951, c1563, c1148, c1252, c1839, c1385, c798, c1790, c1662, c1784, c726, c1842, c822, c832, c846, c933, c1841, c1077, c1240, c1096, c1251, c1236, c1152, c1233, c1064, c1840] c1843 (by decide) p (sat_cons (step1331 p h) (sat_cons (step776 p h) (sat_cons (step1550 p h) (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step1009 p h) (sat_cons (step1059 p h) (sat_cons (step1258 p h) (sat_cons (step1565 p h) (sat_cons (step953 p h) (sat_cons (step1011 p h) (sat_cons (step821 p h) (sat_cons (step829 p h) (sat_cons (step719 p h) (sat_cons (step845 p h) (sat_cons (step1382 p h) (sat_cons (step951 p h) (sat_cons (step1563 p h) (sat_cons (step1148 p h) (sat_cons (step1252 p h) (sat_cons (step1839 p h) (sat_cons (step1385 p h) (sat_cons (step798 p h) (sat_cons (step1790 p h) (sat_cons (step1662 p h) (sat_cons (step1784 p h) (sat_cons (step726 p h) (sat_cons (step1842 p h) (sat_cons (step822 p h) (sat_cons (step832 p h) (sat_cons (step846 p h) (sat_cons (step933 p h) (sat_cons (step1841 p h) (sat_cons (step1077 p h) (sat_cons (step1240 p h) (sat_cons (step1096 p h) (sat_cons (step1251 p h) (sat_cons (step1236 p h) (sat_cons (step1152 p h) (sat_cons (step1233 p h) (sat_cons (step1064 p h) (sat_cons (step1840 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
end B112E213
