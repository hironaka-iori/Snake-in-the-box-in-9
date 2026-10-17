import B112E027Part0003
namespace B112E027
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1706 : List Lit := [(361, false), (373, false)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c1460, c819] c1706 (by decide) p (sat_cons (step1460 p h) (sat_cons (step819 p h) (sat_nil p)))
def c1707 : List Lit := [(379, false), (385, false)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c1470, c830] c1707 (by decide) p (sat_cons (step1470 p h) (sat_cons (step830 p h) (sat_nil p)))
def c1708 : List Lit := [(199, false), (200, false)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c1494, c834] c1708 (by decide) p (sat_cons (step1494 p h) (sat_cons (step834 p h) (sat_nil p)))
def c1709 : List Lit := [(393, false), (399, false)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c1469, c841] c1709 (by decide) p (sat_cons (step1469 p h) (sat_cons (step841 p h) (sat_nil p)))
def c1710 : List Lit := [(387, false), (401, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c1459, c846] c1710 (by decide) p (sat_cons (step1459 p h) (sat_cons (step846 p h) (sat_nil p)))
def c1711 : List Lit := [(375, false), (403, false)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c1454, c851] c1711 (by decide) p (sat_cons (step1454 p h) (sat_cons (step851 p h) (sat_nil p)))
def c1712 : List Lit := [(409, false), (415, false)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c1468, c862] c1712 (by decide) p (sat_cons (step1468 p h) (sat_cons (step862 p h) (sat_nil p)))
def c1713 : List Lit := [(214, false), (215, false)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c1493, c865] c1713 (by decide) p (sat_cons (step1493 p h) (sat_cons (step865 p h) (sat_nil p)))
def c1714 : List Lit := [(419, false), (421, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c1482, c869] c1714 (by decide) p (sat_cons (step1482 p h) (sat_cons (step869 p h) (sat_nil p)))
def c1715 : List Lit := [(423, false), (429, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c1467, c875] c1715 (by decide) p (sat_cons (step1467 p h) (sat_cons (step875 p h) (sat_nil p)))
def c1716 : List Lit := [(417, false), (431, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c1458, c880] c1716 (by decide) p (sat_cons (step1458 p h) (sat_cons (step880 p h) (sat_nil p)))
def c1717 : List Lit := [(437, false), (443, false)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c1466, c890] c1717 (by decide) p (sat_cons (step1466 p h) (sat_cons (step890 p h) (sat_nil p)))
def c1718 : List Lit := [(453, false), (455, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c1480, c900] c1718 (by decide) p (sat_cons (step1480 p h) (sat_cons (step900 p h) (sat_nil p)))
def c1719 : List Lit := [(451, false), (457, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c1465, c904] c1719 (by decide) p (sat_cons (step1465 p h) (sat_cons (step904 p h) (sat_nil p)))
def c1720 : List Lit := [(445, false), (459, false)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c1457, c909] c1720 (by decide) p (sat_cons (step1457 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1721 : List Lit := [(433, false), (461, false)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c1453, c914] c1721 (by decide) p (sat_cons (step1453 p h) (sat_cons (step914 p h) (sat_nil p)))
def c1722 : List Lit := [(405, false), (463, false)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c1451, c919] c1722 (by decide) p (sat_cons (step1451 p h) (sat_cons (step919 p h) (sat_nil p)))
def c1723 : List Lit := [(349, false), (465, false)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c924, c922] c1723 (by decide) p (sat_cons (step924 p h) (sat_cons (step922 p h) (sat_nil p)))
def c1724 : List Lit := [(1479, true), (1471, false)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1004] c1724 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1004 p h) (sat_nil p)))
def c1725 : List Lit := [(1472, false), (1480, true)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1005] c1725 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1005 p h) (sat_nil p)))
def c1726 : List Lit := [(1481, true), (1473, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1006] c1726 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1006 p h) (sat_nil p)))
def c1727 : List Lit := [(1474, false), (1482, true)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1007] c1727 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1007 p h) (sat_nil p)))
def c1728 : List Lit := [(1475, false), (1483, true)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1008] c1728 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1008 p h) (sat_nil p)))
def c1729 : List Lit := [(1451, false), (1479, true)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1009] c1729 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1009 p h) (sat_nil p)))
def c1730 : List Lit := [(1452, false), (1480, true)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1015] c1730 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c1731 : List Lit := [(1453, false), (1481, true)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1020] c1731 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1020 p h) (sat_nil p)))
def c1732 : List Lit := [(1454, false), (1482, true)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1024] c1732 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1024 p h) (sat_nil p)))
def c1733 : List Lit := [(1532, true), (1504, false)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1100] c1733 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1100 p h) (sat_nil p)))
def c1734 : List Lit := [(1505, false), (1533, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1105] c1734 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c1735 : List Lit := [(1506, false), (1534, true)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1110] c1735 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1110 p h) (sat_nil p)))
def c1736 : List Lit := [(1507, false), (1535, true)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1114] c1736 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1114 p h) (sat_nil p)))
def c1737 : List Lit := [(1535, false), (1550, true)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c1514, c1117] c1737 (by decide) p (sat_cons (step1514 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c1738 : List Lit := [(1548, true), (1532, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1118] c1738 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1118 p h) (sat_nil p)))
def c1739 : List Lit := [(1549, true), (1533, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1119] c1739 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1119 p h) (sat_nil p)))
def c1740 : List Lit := [(1550, true), (1534, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1120] c1740 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1120 p h) (sat_nil p)))
def c1741 : List Lit := [(1535, false), (1551, true)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1121] c1741 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1121 p h) (sat_nil p)))
def c1742 : List Lit := [(1536, false), (1552, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1122] c1742 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1122 p h) (sat_nil p)))
def c1743 : List Lit := [(1537, false), (1553, true)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1123] c1743 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1123 p h) (sat_nil p)))
def c1744 : List Lit := [(1549, true), (1480, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1130] c1744 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1130 p h) (sat_nil p)))
def c1745 : List Lit := [(1481, false), (1550, true)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1136] c1745 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1136 p h) (sat_nil p)))
def c1746 : List Lit := [(1591, false), (1596, true)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1207] c1746 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1207 p h) (sat_nil p)))
def c1747 : List Lit := [(1592, false), (1597, true)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1208] c1747 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1208 p h) (sat_nil p)))
def c1748 : List Lit := [(1593, false), (1598, true)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1209] c1748 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1209 p h) (sat_nil p)))
def c1749 : List Lit := [(1594, false), (1599, true)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1210] c1749 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1210 p h) (sat_nil p)))
def c1750 : List Lit := [(1575, false), (1603, true)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1229] c1750 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c1751 : List Lit := [(1576, false), (1604, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1237] c1751 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1237 p h) (sat_nil p)))
def c1752 : List Lit := [(1577, false), (1605, true)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1244] c1752 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1244 p h) (sat_nil p)))
def c1753 : List Lit := [(1578, false), (1606, true)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1249] c1753 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1249 p h) (sat_nil p)))
def c1754 : List Lit := [(1579, false), (1607, true)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1253] c1754 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1253 p h) (sat_nil p)))
def c1755 : List Lit := [(1663, false), (1679, true)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1358] c1755 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1358 p h) (sat_nil p)))
def c1756 : List Lit := [(1664, false), (1680, true)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1359] c1756 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1359 p h) (sat_nil p)))
def c1757 : List Lit := [(1665, false), (1681, true)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1360] c1757 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1360 p h) (sat_nil p)))
def c1758 : List Lit := [(1666, false), (1682, true)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1361] c1758 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1361 p h) (sat_nil p)))
def c1759 : List Lit := [(1667, false), (1683, true)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1362] c1759 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1362 p h) (sat_nil p)))
def c1760 : List Lit := [(1548, false), (1687, false)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1402] c1760 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1402 p h) (sat_nil p)))
def c1761 : List Lit := [(1549, false), (1686, false)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1403] c1761 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1403 p h) (sat_nil p)))
def c1762 : List Lit := [(1550, false), (1685, false)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1404] c1762 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1404 p h) (sat_nil p)))
def c1763 : List Lit := [(1551, false), (1684, false)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1405] c1763 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1405 p h) (sat_nil p)))
def c1764 : List Lit := [(1552, false), (1683, false)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1406] c1764 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1406 p h) (sat_nil p)))
def c1765 : List Lit := [(1553, false), (1682, false)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1407] c1765 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1407 p h) (sat_nil p)))
def c1766 : List Lit := [(1554, false), (1681, false)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1408] c1766 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1408 p h) (sat_nil p)))
def c1767 : List Lit := [(1555, false), (1680, false)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1409] c1767 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1409 p h) (sat_nil p)))
def c1768 : List Lit := [(1556, false), (1679, false)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1410] c1768 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1410 p h) (sat_nil p)))
def c1769 : List Lit := [(36, false), (104, false), (1506, true), (41, false), (163, true)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c174, c175, c1624, c1030, c202, c1032, c1038, c1053, c1040] c1769 (by decide) p (sat_cons (step174 p h) (sat_cons (step175 p h) (sat_cons (step1624 p h) (sat_cons (step1030 p h) (sat_cons (step202 p h) (sat_cons (step1032 p h) (sat_cons (step1038 p h) (sat_cons (step1053 p h) (sat_cons (step1040 p h) (sat_nil p))))))))))
end B112E027
