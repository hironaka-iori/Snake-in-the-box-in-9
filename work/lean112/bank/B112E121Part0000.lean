import B112E121Inputs
namespace B112E121
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1724 : List Lit := [(64, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c502, c501] c1724 (by decide) p (sat_cons (step502 p h) (sat_cons (step501 p h) (sat_nil p)))
def c1725 : List Lit := [(190, true), (68, true)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c1724, c503] c1725 (by decide) p (sat_cons (step1724 p h) (sat_cons (step503 p h) (sat_nil p)))
def c1726 : List Lit := [(68, false), (61, false), (67, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c1724, c512] c1726 (by decide) p (sat_cons (step1724 p h) (sat_cons (step512 p h) (sat_nil p)))
def c1727 : List Lit := [(32, false)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c893, c380] c1727 (by decide) p (sat_cons (step893 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1728 : List Lit := [(34, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c894, c383] c1728 (by decide) p (sat_cons (step894 p h) (sat_cons (step383 p h) (sat_nil p)))
def c1729 : List Lit := [(38, false)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c897, c390] c1729 (by decide) p (sat_cons (step897 p h) (sat_cons (step390 p h) (sat_nil p)))
def c1730 : List Lit := [(498, false)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c1085, c1082] c1730 (by decide) p (sat_cons (step1085 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c1731 : List Lit := [(374, false)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c1085, c1084] c1731 (by decide) p (sat_cons (step1085 p h) (sat_cons (step1084 p h) (sat_nil p)))
def c1732 : List Lit := [(496, false)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c1730, c1078] c1732 (by decide) p (sat_cons (step1730 p h) (sat_cons (step1078 p h) (sat_nil p)))
def c1733 : List Lit := [(434, false)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c1730, c1081] c1733 (by decide) p (sat_cons (step1730 p h) (sat_cons (step1081 p h) (sat_nil p)))
def c1734 : List Lit := [(372, false)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c1731, c1022] c1734 (by decide) p (sat_cons (step1731 p h) (sat_cons (step1022 p h) (sat_nil p)))
def c1735 : List Lit := [(312, false)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c1731, c1025] c1735 (by decide) p (sat_cons (step1731 p h) (sat_cons (step1025 p h) (sat_nil p)))
def c1736 : List Lit := [(494, false)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c1732, c1075] c1736 (by decide) p (sat_cons (step1732 p h) (sat_cons (step1075 p h) (sat_nil p)))
def c1737 : List Lit := [(402, false)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c1733, c1057] c1737 (by decide) p (sat_cons (step1733 p h) (sat_cons (step1057 p h) (sat_nil p)))
def c1738 : List Lit := [(370, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c1734, c1017] c1738 (by decide) p (sat_cons (step1734 p h) (sat_cons (step1017 p h) (sat_nil p)))
def c1739 : List Lit := [(340, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c1734, c1020] c1739 (by decide) p (sat_cons (step1734 p h) (sat_cons (step1020 p h) (sat_nil p)))
def c1740 : List Lit := [(310, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c1735, c973] c1740 (by decide) p (sat_cons (step1735 p h) (sat_cons (step973 p h) (sat_nil p)))
def c1741 : List Lit := [(280, false)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c1735, c976] c1741 (by decide) p (sat_cons (step1735 p h) (sat_cons (step976 p h) (sat_nil p)))
def c1742 : List Lit := [(386, false)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c1737, c1045] c1742 (by decide) p (sat_cons (step1737 p h) (sat_cons (step1045 p h) (sat_nil p)))
def c1743 : List Lit := [(368, false)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c1738, c1013] c1743 (by decide) p (sat_cons (step1738 p h) (sat_cons (step1013 p h) (sat_nil p)))
def c1744 : List Lit := [(338, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c1739, c992] c1744 (by decide) p (sat_cons (step1739 p h) (sat_cons (step992 p h) (sat_nil p)))
def c1745 : List Lit := [(294, false)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c1740, c971] c1745 (by decide) p (sat_cons (step1740 p h) (sat_cons (step971 p h) (sat_nil p)))
def c1746 : List Lit := [(264, false)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c1741, c955] c1746 (by decide) p (sat_cons (step1741 p h) (sat_cons (step955 p h) (sat_nil p)))
def c1747 : List Lit := [(378, false)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c1742, c1037] c1747 (by decide) p (sat_cons (step1742 p h) (sat_cons (step1037 p h) (sat_nil p)))
def c1748 : List Lit := [(360, false)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c1743, c1011] c1748 (by decide) p (sat_cons (step1743 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c1749 : List Lit := [(330, false)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c1744, c990] c1749 (by decide) p (sat_cons (step1744 p h) (sat_cons (step990 p h) (sat_nil p)))
def c1750 : List Lit := [(286, false)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c1745, c962] c1750 (by decide) p (sat_cons (step1745 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1751 : List Lit := [(262, false)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c1746, c943] c1751 (by decide) p (sat_cons (step1746 p h) (sat_cons (step943 p h) (sat_nil p)))
def c1752 : List Lit := [(356, false)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1009] c1752 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1009 p h) (sat_nil p)))
def c1753 : List Lit := [(260, false)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c1751, c941] c1753 (by decide) p (sat_cons (step1751 p h) (sat_cons (step941 p h) (sat_nil p)))
def c1754 : List Lit := [(927, true)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1237] c1754 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1237 p h) (sat_nil p)))
def c1755 : List Lit := [(928, true)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c1727, c1728, c1238] c1755 (by decide) p (sat_cons (step1727 p h) (sat_cons (step1728 p h) (sat_cons (step1238 p h) (sat_nil p))))
def c1756 : List Lit := [(931, true)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c1754, c1242] c1756 (by decide) p (sat_cons (step1754 p h) (sat_cons (step1242 p h) (sat_nil p)))
def c1757 : List Lit := [(932, true)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c1755, c1243] c1757 (by decide) p (sat_cons (step1755 p h) (sat_cons (step1243 p h) (sat_nil p)))
def c1758 : List Lit := [(929, false), (933, true)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c1755, c1244] c1758 (by decide) p (sat_cons (step1755 p h) (sat_cons (step1244 p h) (sat_nil p)))
def c1759 : List Lit := [(930, false), (934, true)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c1755, c1245] c1759 (by decide) p (sat_cons (step1755 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c1760 : List Lit := [(935, true)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c1729, c1246] c1760 (by decide) p (sat_cons (step1729 p h) (sat_cons (step1246 p h) (sat_nil p)))
def c1761 : List Lit := [(42, true), (936, true)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c1729, c1247] c1761 (by decide) p (sat_cons (step1729 p h) (sat_cons (step1247 p h) (sat_nil p)))
def c1762 : List Lit := [(939, true)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c1760, c1251] c1762 (by decide) p (sat_cons (step1760 p h) (sat_cons (step1251 p h) (sat_nil p)))
def c1763 : List Lit := [(937, false), (940, true)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c1760, c1252] c1763 (by decide) p (sat_cons (step1760 p h) (sat_cons (step1252 p h) (sat_nil p)))
def c1764 : List Lit := [(938, false), (941, true)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c1760, c1253] c1764 (by decide) p (sat_cons (step1760 p h) (sat_cons (step1253 p h) (sat_nil p)))
def c1765 : List Lit := [(943, true)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c1762, c1257] c1765 (by decide) p (sat_cons (step1762 p h) (sat_cons (step1257 p h) (sat_nil p)))
def c1766 : List Lit := [(944, true)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c1756, c1762, c1258] c1766 (by decide) p (sat_cons (step1756 p h) (sat_cons (step1762 p h) (sat_cons (step1258 p h) (sat_nil p))))
def c1767 : List Lit := [(945, true)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c1757, c1762, c1259] c1767 (by decide) p (sat_cons (step1757 p h) (sat_cons (step1762 p h) (sat_cons (step1259 p h) (sat_nil p))))
def c1768 : List Lit := [(940, false), (946, true)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c1757, c1260] c1768 (by decide) p (sat_cons (step1757 p h) (sat_cons (step1260 p h) (sat_nil p)))
def c1769 : List Lit := [(941, false), (947, true)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c1757, c1261] c1769 (by decide) p (sat_cons (step1757 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c1770 : List Lit := [(933, false), (946, true)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c1762, c1262] c1770 (by decide) p (sat_cons (step1762 p h) (sat_cons (step1262 p h) (sat_nil p)))
def c1771 : List Lit := [(934, false), (947, true)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c1762, c1266] c1771 (by decide) p (sat_cons (step1762 p h) (sat_cons (step1266 p h) (sat_nil p)))
def c1772 : List Lit := [(971, false), (980, true)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c1765, c1311] c1772 (by decide) p (sat_cons (step1765 p h) (sat_cons (step1311 p h) (sat_nil p)))
def c1773 : List Lit := [(969, false), (979, true)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c1766, c1312] c1773 (by decide) p (sat_cons (step1766 p h) (sat_cons (step1312 p h) (sat_nil p)))
def c1774 : List Lit := [(970, false), (980, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c1766, c1313] c1774 (by decide) p (sat_cons (step1766 p h) (sat_cons (step1313 p h) (sat_nil p)))
def c1775 : List Lit := [(977, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c1767, c1314] c1775 (by decide) p (sat_cons (step1767 p h) (sat_cons (step1314 p h) (sat_nil p)))
def c1776 : List Lit := [(967, false), (978, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c1767, c1315] c1776 (by decide) p (sat_cons (step1767 p h) (sat_cons (step1315 p h) (sat_nil p)))
def c1777 : List Lit := [(968, false), (979, true)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c1767, c1316] c1777 (by decide) p (sat_cons (step1767 p h) (sat_cons (step1316 p h) (sat_nil p)))
def c1778 : List Lit := [(969, false), (980, true)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c1767, c1317] c1778 (by decide) p (sat_cons (step1767 p h) (sat_cons (step1317 p h) (sat_nil p)))
def c1779 : List Lit := [(970, false), (981, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c1767, c1318] c1779 (by decide) p (sat_cons (step1767 p h) (sat_cons (step1318 p h) (sat_nil p)))
def c1780 : List Lit := [(971, false), (982, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c1767, c1319] c1780 (by decide) p (sat_cons (step1767 p h) (sat_cons (step1319 p h) (sat_nil p)))
def c1781 : List Lit := [(972, false), (983, true)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c1767, c1320] c1781 (by decide) p (sat_cons (step1767 p h) (sat_cons (step1320 p h) (sat_nil p)))
def c1782 : List Lit := [(919, false), (1002, true)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c1775, c1368] c1782 (by decide) p (sat_cons (step1775 p h) (sat_cons (step1368 p h) (sat_nil p)))
def c1783 : List Lit := [(62, false), (67, false), (65, false)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c1742, c506, c504, c511, c1026, c1030, c1027, c1033, c1036] c1783 (by decide) p (sat_cons (step1742 p h) (sat_cons (step506 p h) (sat_cons (step504 p h) (sat_cons (step511 p h) (sat_cons (step1026 p h) (sat_cons (step1030 p h) (sat_cons (step1027 p h) (sat_cons (step1033 p h) (sat_cons (step1036 p h) (sat_nil p))))))))))
def c1784 : List Lit := [(1051, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c920, c1443, c1445, c1440, c1441, c1437, c1438, c685, c615, c642] c1784 (by decide) p (sat_cons (step920 p h) (sat_cons (step1443 p h) (sat_cons (step1445 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1437 p h) (sat_cons (step1438 p h) (sat_cons (step685 p h) (sat_cons (step615 p h) (sat_cons (step642 p h) (sat_nil p)))))))))))
def c1785 : List Lit := [(1055, true)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c1784, c1451] c1785 (by decide) p (sat_cons (step1784 p h) (sat_cons (step1451 p h) (sat_nil p)))
def c1786 : List Lit := [(1063, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c1785, c1465] c1786 (by decide) p (sat_cons (step1785 p h) (sat_cons (step1465 p h) (sat_nil p)))
def c1787 : List Lit := [(1028, true), (71, true), (85, false)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c917, c1397, c592, c1407, c1405, c1398, c1400, c554] c1787 (by decide) p (sat_cons (step917 p h) (sat_cons (step1397 p h) (sat_cons (step592 p h) (sat_cons (step1407 p h) (sat_cons (step1405 p h) (sat_cons (step1398 p h) (sat_cons (step1400 p h) (sat_cons (step554 p h) (sat_nil p)))))))))
end B112E121
