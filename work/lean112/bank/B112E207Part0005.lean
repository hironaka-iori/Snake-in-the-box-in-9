import B112E207Part0004
namespace B112E207
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1667 : List Lit := [(373, false), (401, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c1355, c839] c1667 (by decide) p (sat_cons (step1355 p h) (sat_cons (step839 p h) (sat_nil p)))
def c1668 : List Lit := [(409, false), (411, false)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c1380, c848] c1668 (by decide) p (sat_cons (step1380 p h) (sat_cons (step848 p h) (sat_nil p)))
def c1669 : List Lit := [(407, false), (413, false)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c1366, c852] c1669 (by decide) p (sat_cons (step1366 p h) (sat_cons (step852 p h) (sat_nil p)))
def c1670 : List Lit := [(215, false), (216, false)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c1389, c856] c1670 (by decide) p (sat_cons (step1389 p h) (sat_cons (step856 p h) (sat_nil p)))
def c1671 : List Lit := [(421, false), (423, false)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c1379, c860] c1671 (by decide) p (sat_cons (step1379 p h) (sat_cons (step860 p h) (sat_nil p)))
def c1672 : List Lit := [(419, false), (425, false)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c1365, c865] c1672 (by decide) p (sat_cons (step1365 p h) (sat_cons (step865 p h) (sat_nil p)))
def c1673 : List Lit := [(415, false), (427, false)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c1358, c869] c1673 (by decide) p (sat_cons (step1358 p h) (sat_cons (step869 p h) (sat_nil p)))
def c1674 : List Lit := [(429, false), (457, false)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c1354, c891] c1674 (by decide) p (sat_cons (step1354 p h) (sat_cons (step891 p h) (sat_nil p)))
def c1675 : List Lit := [(403, false), (459, false)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c1352, c896] c1675 (by decide) p (sat_cons (step1352 p h) (sat_cons (step896 p h) (sat_nil p)))
def c1676 : List Lit := [(347, false), (461, false)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c901, c899] c1676 (by decide) p (sat_cons (step901 p h) (sat_cons (step899 p h) (sat_nil p)))
def c1677 : List Lit := [(1503, false), (1512, true)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1090] c1677 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1090 p h) (sat_nil p)))
def c1678 : List Lit := [(1504, false), (1513, true)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1091] c1678 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1091 p h) (sat_nil p)))
def c1679 : List Lit := [(1505, false), (1514, true)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1092] c1679 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c1680 : List Lit := [(1479, false), (1512, true)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1093] c1680 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1093 p h) (sat_nil p)))
def c1681 : List Lit := [(1480, false), (1513, true)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1099] c1681 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1099 p h) (sat_nil p)))
def c1682 : List Lit := [(1481, false), (1514, true)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1104] c1682 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1104 p h) (sat_nil p)))
def c1683 : List Lit := [(1531, true), (1455, false)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1121] c1683 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1121 p h) (sat_nil p)))
def c1684 : List Lit := [(1532, true), (1456, false)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1127] c1684 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1127 p h) (sat_nil p)))
def c1685 : List Lit := [(1533, true), (1457, false)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1132] c1685 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1132 p h) (sat_nil p)))
def c1686 : List Lit := [(1534, true), (1458, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1136] c1686 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1136 p h) (sat_nil p)))
def c1687 : List Lit := [(1535, true), (1459, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1139] c1687 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1139 p h) (sat_nil p)))
def c1688 : List Lit := [(1536, true), (1460, false)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1140] c1688 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1140 p h) (sat_nil p)))
def c1689 : List Lit := [(1584, true), (1556, false)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1213] c1689 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1213 p h) (sat_nil p)))
def c1690 : List Lit := [(1585, true), (1557, false)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1216] c1690 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1216 p h) (sat_nil p)))
def c1691 : List Lit := [(1586, true), (1558, false)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1219] c1691 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1219 p h) (sat_nil p)))
def c1692 : List Lit := [(1559, false), (1587, true)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1222] c1692 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1222 p h) (sat_nil p)))
def c1693 : List Lit := [(1560, false), (1588, true)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1224] c1693 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1224 p h) (sat_nil p)))
def c1694 : List Lit := [(1620, false), (1633, true)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1267] c1694 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1267 p h) (sat_nil p)))
def c1695 : List Lit := [(1642, true), (1610, false)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1272] c1695 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1272 p h) (sat_nil p)))
def c1696 : List Lit := [(1643, true), (1611, false)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1274] c1696 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1274 p h) (sat_nil p)))
def c1697 : List Lit := [(1612, false), (1644, true)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1276] c1697 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1276 p h) (sat_nil p)))
def c1698 : List Lit := [(1613, false), (1645, true)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1278] c1698 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1278 p h) (sat_nil p)))
def c1699 : List Lit := [(1642, false), (1659, true)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c1399, c1279] c1699 (by decide) p (sat_cons (step1399 p h) (sat_cons (step1279 p h) (sat_nil p)))
def c1700 : List Lit := [(1643, false), (1660, true)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c1399, c1280] c1700 (by decide) p (sat_cons (step1399 p h) (sat_cons (step1280 p h) (sat_nil p)))
def c1701 : List Lit := [(1644, false), (1661, true)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c1399, c1281] c1701 (by decide) p (sat_cons (step1399 p h) (sat_cons (step1281 p h) (sat_nil p)))
def c1702 : List Lit := [(1645, false), (1662, true)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c1399, c1282] c1702 (by decide) p (sat_cons (step1399 p h) (sat_cons (step1282 p h) (sat_nil p)))
def c1703 : List Lit := [(1659, true), (1584, false)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1283] c1703 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1283 p h) (sat_nil p)))
def c1704 : List Lit := [(1585, false), (1659, true)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c1414, c1288] c1704 (by decide) p (sat_cons (step1414 p h) (sat_cons (step1288 p h) (sat_nil p)))
def c1705 : List Lit := [(1660, true), (1585, false)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1289] c1705 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1289 p h) (sat_nil p)))
def c1706 : List Lit := [(1661, true), (1586, false)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1295] c1706 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1295 p h) (sat_nil p)))
def c1707 : List Lit := [(1587, false), (1661, true)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c1414, c1299] c1707 (by decide) p (sat_cons (step1414 p h) (sat_cons (step1299 p h) (sat_nil p)))
def c1708 : List Lit := [(1587, false), (1662, true)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1300] c1708 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1300 p h) (sat_nil p)))
def c1709 : List Lit := [(1588, false), (1663, true)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1303] c1709 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1303 p h) (sat_nil p)))
def c1710 : List Lit := [(1530, false), (1665, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1306] c1710 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1306 p h) (sat_nil p)))
def c1711 : List Lit := [(1531, false), (1664, false)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1307] c1711 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1307 p h) (sat_nil p)))
def c1712 : List Lit := [(1532, false), (1663, false)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1308] c1712 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1308 p h) (sat_nil p)))
def c1713 : List Lit := [(1533, false), (1662, false)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1309] c1713 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1309 p h) (sat_nil p)))
def c1714 : List Lit := [(1534, false), (1661, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1310] c1714 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1310 p h) (sat_nil p)))
def c1715 : List Lit := [(1535, false), (1660, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1311] c1715 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1311 p h) (sat_nil p)))
def c1716 : List Lit := [(1536, false), (1659, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1312] c1716 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1312 p h) (sat_nil p)))
def c1717 : List Lit := [(29, true), (85, false), (273, true), (20, true), (22, false), (18, true)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c706, c705, c110, c109, c1562, c1569, c59, c115] c1717 (by decide) p (sat_cons (step706 p h) (sat_cons (step705 p h) (sat_cons (step110 p h) (sat_cons (step109 p h) (sat_cons (step1562 p h) (sat_cons (step1569 p h) (sat_cons (step59 p h) (sat_cons (step115 p h) (sat_nil p)))))))))
def c1718 : List Lit := [(1505, true), (1491, false), (1486, false), (58, true), (52, false), (177, true), (90, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c1058, c1060, c1086, c1082, c1053, c1061, c1063, c1059, c1055, c407, c304, c237, c1045] c1718 (by decide) p (sat_cons (step1058 p h) (sat_cons (step1060 p h) (sat_cons (step1086 p h) (sat_cons (step1082 p h) (sat_cons (step1053 p h) (sat_cons (step1061 p h) (sat_cons (step1063 p h) (sat_cons (step1059 p h) (sat_cons (step1055 p h) (sat_cons (step407 p h) (sat_cons (step304 p h) (sat_cons (step237 p h) (sat_cons (step1045 p h) (sat_nil p))))))))))))))
def c1719 : List Lit := [(1542, true), (59, false), (54, false), (180, true)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1142, c437, c436, c421] c1719 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1142 p h) (sat_cons (step437 p h) (sat_cons (step436 p h) (sat_cons (step421 p h) (sat_nil p))))))
def c1720 : List Lit := [(1576, true), (1569, false)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c1192, c1200, c1203, c1195, c1182, c1400] c1720 (by decide) p (sat_cons (step1192 p h) (sat_cons (step1200 p h) (sat_cons (step1203 p h) (sat_cons (step1195 p h) (sat_cons (step1182 p h) (sat_cons (step1400 p h) (sat_nil p)))))))
def c1721 : List Lit := [(1544, false), (1585, true), (1569, false)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c1720, c1214, c1166, c1167, c1211, c1397, c1445] c1721 (by decide) p (sat_cons (step1720 p h) (sat_cons (step1214 p h) (sat_cons (step1166 p h) (sat_cons (step1167 p h) (sat_cons (step1211 p h) (sat_cons (step1397 p h) (sat_cons (step1445 p h) (sat_nil p))))))))
def c1722 : List Lit := [(1585, true), (1569, false), (52, false), (90, false), (57, false)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c1720, c1214, c1164, c1156, c1721, c1144, c1141, c1142, c311, c1153, c1154, c1155, c1158, c1163, c1149, c1150, c1211, c478, c1445, c465, c342, c471] c1722 (by decide) p (sat_cons (step1720 p h) (sat_cons (step1214 p h) (sat_cons (step1164 p h) (sat_cons (step1156 p h) (sat_cons (step1721 p h) (sat_cons (step1144 p h) (sat_cons (step1141 p h) (sat_cons (step1142 p h) (sat_cons (step311 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1155 p h) (sat_cons (step1158 p h) (sat_cons (step1163 p h) (sat_cons (step1149 p h) (sat_cons (step1150 p h) (sat_cons (step1211 p h) (sat_cons (step478 p h) (sat_cons (step1445 p h) (sat_cons (step465 p h) (sat_cons (step342 p h) (sat_cons (step471 p h) (sat_nil p)))))))))))))))))))))))
def c1723 : List Lit := [(1504, true), (177, true), (52, false), (45, true), (90, false), (58, true)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c1058, c1534, c1043, c1044, c304, c1055, c1063, c1476] c1723 (by decide) p (sat_cons (step1058 p h) (sat_cons (step1534 p h) (sat_cons (step1043 p h) (sat_cons (step1044 p h) (sat_cons (step304 p h) (sat_cons (step1055 p h) (sat_cons (step1063 p h) (sat_cons (step1476 p h) (sat_nil p)))))))))
def c1724 : List Lit := [(1545, false), (1586, true), (72, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c1691, c1153, c1155, c1172, c1171, c1156, c1158, c1217, c1154, c1149, c1150, c1398, c481, c465, c477, c472, c1665] c1724 (by decide) p (sat_cons (step1691 p h) (sat_cons (step1153 p h) (sat_cons (step1155 p h) (sat_cons (step1172 p h) (sat_cons (step1171 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1217 p h) (sat_cons (step1154 p h) (sat_cons (step1149 p h) (sat_cons (step1150 p h) (sat_cons (step1398 p h) (sat_cons (step481 p h) (sat_cons (step465 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step1665 p h) (sat_nil p))))))))))))))))))
def c1725 : List Lit := [(1596, true), (89, false), (66, false), (53, false), (90, false)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c1225, c1226, c1471, c562, c340, c552] c1725 (by decide) p (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step1471 p h) (sat_cons (step562 p h) (sat_cons (step340 p h) (sat_cons (step552 p h) (sat_nil p)))))))
def c1726 : List Lit := [(1576, true), (66, false), (1661, true), (1544, false), (72, true), (53, false), (90, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1398, c1720, c1189, c1725, c1228, c1454, c1290, c1690, c1168, c1156, c1158, c1154, c1149, c1150, c339, c481, c465, c471] c1726 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1398 p h) (sat_cons (step1720 p h) (sat_cons (step1189 p h) (sat_cons (step1725 p h) (sat_cons (step1228 p h) (sat_cons (step1454 p h) (sat_cons (step1290 p h) (sat_cons (step1690 p h) (sat_cons (step1168 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1154 p h) (sat_cons (step1149 p h) (sat_cons (step1150 p h) (sat_cons (step339 p h) (sat_cons (step481 p h) (sat_cons (step465 p h) (sat_cons (step471 p h) (sat_nil p))))))))))))))))))))
def c1727 : List Lit := [(1661, true), (72, true), (63, true), (53, false), (90, false)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c1142, c1144, c1153, c1155, c1167, c1706, c1215, c1724, c1145, c1143, c1726, c1214, c1217, c1290, c1168, c1454, c1156, c1158, c1228, c1154, c1149, c1150, c1725, c339, c1189, c1445, c481, c465, c471] c1727 (by decide) p (sat_cons (step1142 p h) (sat_cons (step1144 p h) (sat_cons (step1153 p h) (sat_cons (step1155 p h) (sat_cons (step1167 p h) (sat_cons (step1706 p h) (sat_cons (step1215 p h) (sat_cons (step1724 p h) (sat_cons (step1145 p h) (sat_cons (step1143 p h) (sat_cons (step1726 p h) (sat_cons (step1214 p h) (sat_cons (step1217 p h) (sat_cons (step1290 p h) (sat_cons (step1168 p h) (sat_cons (step1454 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1228 p h) (sat_cons (step1154 p h) (sat_cons (step1149 p h) (sat_cons (step1150 p h) (sat_cons (step1725 p h) (sat_cons (step339 p h) (sat_cons (step1189 p h) (sat_cons (step1445 p h) (sat_cons (step481 p h) (sat_cons (step465 p h) (sat_cons (step471 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1728 : List Lit := [(1569, false), (1586, true), (191, true), (54, true), (1544, false), (72, true)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c1691, c1169, c1449, c1153, c1155, c1167, c1215, c1720, c1445, c1217, c1411, c1168, c1154, c1156] c1728 (by decide) p (sat_cons (step1691 p h) (sat_cons (step1169 p h) (sat_cons (step1449 p h) (sat_cons (step1153 p h) (sat_cons (step1155 p h) (sat_cons (step1167 p h) (sat_cons (step1215 p h) (sat_cons (step1720 p h) (sat_cons (step1445 p h) (sat_cons (step1217 p h) (sat_cons (step1411 p h) (sat_cons (step1168 p h) (sat_cons (step1154 p h) (sat_cons (step1156 p h) (sat_nil p)))))))))))))))
def c1729 : List Lit := [(1494, false), (1505, true), (50, false), (177, true), (45, true), (58, true)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c1041, c1048, c1074, c1058, c1066, c1067, c1078, c1059, c1051, c1469, c1042] c1729 (by decide) p (sat_cons (step1041 p h) (sat_cons (step1048 p h) (sat_cons (step1074 p h) (sat_cons (step1058 p h) (sat_cons (step1066 p h) (sat_cons (step1067 p h) (sat_cons (step1078 p h) (sat_cons (step1059 p h) (sat_cons (step1051 p h) (sat_cons (step1469 p h) (sat_cons (step1042 p h) (sat_nil p))))))))))))
def c1730 : List Lit := [(1420, false), (1445, false), (50, false), (72, true), (63, true), (55, true), (4, true), (53, false), (1514, false), (90, false), (177, true), (45, true), (58, true), (1479, false)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c903, c905, c1727, c1714, c1124, c998, c930, c921, c1606, c1142, c929, c991, c1118, c1713, c1119, c1096, c934, c906, c904, c1729, c1056, c1478, c1473, c326, c1228, c674, c24, c1454, c679, c30, c1296, c682, c912, c1724, c696, c1145, c1147, c724, c1143, c779, c442, c392, c1676, c440, c895, c793, c838, c804, c805] c1730 (by decide) p (sat_cons (step903 p h) (sat_cons (step905 p h) (sat_cons (step1727 p h) (sat_cons (step1714 p h) (sat_cons (step1124 p h) (sat_cons (step998 p h) (sat_cons (step930 p h) (sat_cons (step921 p h) (sat_cons (step1606 p h) (sat_cons (step1142 p h) (sat_cons (step929 p h) (sat_cons (step991 p h) (sat_cons (step1118 p h) (sat_cons (step1713 p h) (sat_cons (step1119 p h) (sat_cons (step1096 p h) (sat_cons (step934 p h) (sat_cons (step906 p h) (sat_cons (step904 p h) (sat_cons (step1729 p h) (sat_cons (step1056 p h) (sat_cons (step1478 p h) (sat_cons (step1473 p h) (sat_cons (step326 p h) (sat_cons (step1228 p h) (sat_cons (step674 p h) (sat_cons (step24 p h) (sat_cons (step1454 p h) (sat_cons (step679 p h) (sat_cons (step30 p h) (sat_cons (step1296 p h) (sat_cons (step682 p h) (sat_cons (step912 p h) (sat_cons (step1724 p h) (sat_cons (step696 p h) (sat_cons (step1145 p h) (sat_cons (step1147 p h) (sat_cons (step724 p h) (sat_cons (step1143 p h) (sat_cons (step779 p h) (sat_cons (step442 p h) (sat_cons (step392 p h) (sat_cons (step1676 p h) (sat_cons (step440 p h) (sat_cons (step895 p h) (sat_cons (step793 p h) (sat_cons (step838 p h) (sat_cons (step804 p h) (sat_cons (step805 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))
end B112E207
