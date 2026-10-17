import B112E254Part0003
namespace B112E254
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1671 : List Lit := [(1646, true), (98, false), (1752, true)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c1469, c1655, c1666, c1656, c1651, c1332, c1187, c1168, c1160, c1648, c1223, c1641, c1235, c1602, c1128, c1667, c1670, c1225, c1664, c1662, c1231, c1167, c1172, c1240, c1186, c1148, c1329, c1145, c1319, c1256, c1229, c1669, c1156, c1158, c1643, c511] c1671 (by decide) p (sat_cons (step1469 p h) (sat_cons (step1655 p h) (sat_cons (step1666 p h) (sat_cons (step1656 p h) (sat_cons (step1651 p h) (sat_cons (step1332 p h) (sat_cons (step1187 p h) (sat_cons (step1168 p h) (sat_cons (step1160 p h) (sat_cons (step1648 p h) (sat_cons (step1223 p h) (sat_cons (step1641 p h) (sat_cons (step1235 p h) (sat_cons (step1602 p h) (sat_cons (step1128 p h) (sat_cons (step1667 p h) (sat_cons (step1670 p h) (sat_cons (step1225 p h) (sat_cons (step1664 p h) (sat_cons (step1662 p h) (sat_cons (step1231 p h) (sat_cons (step1167 p h) (sat_cons (step1172 p h) (sat_cons (step1240 p h) (sat_cons (step1186 p h) (sat_cons (step1148 p h) (sat_cons (step1329 p h) (sat_cons (step1145 p h) (sat_cons (step1319 p h) (sat_cons (step1256 p h) (sat_cons (step1229 p h) (sat_cons (step1669 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1643 p h) (sat_cons (step511 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1672 : List Lit := [(98, false), (1752, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c1655, c1641, c1235, c1648, c1651, c1332, c1199, c1656, c1671, c1192, c1193, c1329, c1167, c1661, c1319, c1660, c1256, c1231, c1240] c1672 (by decide) p (sat_cons (step1655 p h) (sat_cons (step1641 p h) (sat_cons (step1235 p h) (sat_cons (step1648 p h) (sat_cons (step1651 p h) (sat_cons (step1332 p h) (sat_cons (step1199 p h) (sat_cons (step1656 p h) (sat_cons (step1671 p h) (sat_cons (step1192 p h) (sat_cons (step1193 p h) (sat_cons (step1329 p h) (sat_cons (step1167 p h) (sat_cons (step1661 p h) (sat_cons (step1319 p h) (sat_cons (step1660 p h) (sat_cons (step1256 p h) (sat_cons (step1231 p h) (sat_cons (step1240 p h) (sat_nil p))))))))))))))))))))
def c1673 : List Lit := [(1731, true)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c1655, c1300] c1673 (by decide) p (sat_cons (step1655 p h) (sat_cons (step1300 p h) (sat_nil p)))
def c1674 : List Lit := [(1661, true), (98, true)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c1159, c1161, c1157, c1153, c1154, c1605] c1674 (by decide) p (sat_cons (step1159 p h) (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1605 p h) (sat_nil p)))))))
def c1675 : List Lit := [(86, false), (1659, true), (1646, false), (1752, true)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.TreeRup.prove_clause [c649, c652, c1655, c650, c643, c886, c1672, c1157, c445, c1156, c1641, c1235, c1237, c1674, c1167, c1193, c1332, c1313, c1255, c1227, c456, c1605, c1223, c1225, c1226, c1229, c473, c1250, c1251, c498, c1307, c1240, c1335, c1232, c1194, c490, c1172, c478, c477, c1148, c1396, c1650, c485, c396, c831, c832, c839, c850, c875, c878, c884, c774, c776, c771, c722, c750, c719, c734, c698, c728, c697, c727, c696, c180, c119, c195] c1675 (by decide) p (sat_cons (step649 p h) (sat_cons (step652 p h) (sat_cons (step1655 p h) (sat_cons (step650 p h) (sat_cons (step643 p h) (sat_cons (step886 p h) (sat_cons (step1672 p h) (sat_cons (step1157 p h) (sat_cons (step445 p h) (sat_cons (step1156 p h) (sat_cons (step1641 p h) (sat_cons (step1235 p h) (sat_cons (step1237 p h) (sat_cons (step1674 p h) (sat_cons (step1167 p h) (sat_cons (step1193 p h) (sat_cons (step1332 p h) (sat_cons (step1313 p h) (sat_cons (step1255 p h) (sat_cons (step1227 p h) (sat_cons (step456 p h) (sat_cons (step1605 p h) (sat_cons (step1223 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step1229 p h) (sat_cons (step473 p h) (sat_cons (step1250 p h) (sat_cons (step1251 p h) (sat_cons (step498 p h) (sat_cons (step1307 p h) (sat_cons (step1240 p h) (sat_cons (step1335 p h) (sat_cons (step1232 p h) (sat_cons (step1194 p h) (sat_cons (step490 p h) (sat_cons (step1172 p h) (sat_cons (step478 p h) (sat_cons (step477 p h) (sat_cons (step1148 p h) (sat_cons (step1396 p h) (sat_cons (step1650 p h) (sat_cons (step485 p h) (sat_cons (step396 p h) (sat_cons (step831 p h) (sat_cons (step832 p h) (sat_cons (step839 p h) (sat_cons (step850 p h) (sat_cons (step875 p h) (sat_cons (step878 p h) (sat_cons (step884 p h) (sat_cons (step774 p h) (sat_cons (step776 p h) (sat_cons (step771 p h) (sat_cons (step722 p h) (sat_cons (step750 p h) (sat_cons (step719 p h) (sat_cons (step734 p h) (sat_cons (step698 p h) (sat_cons (step728 p h) (sat_cons (step697 p h) (sat_cons (step727 p h) (sat_cons (step696 p h) (sat_cons (step180 p h) (sat_cons (step119 p h) (sat_cons (step195 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1676 : List Lit := [(1662, false), (1659, true), (1646, false), (1752, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.TreeRup.prove_clause [c1655, c653, c652, c650, c654, c886, c646, c643, c642, c1675, c1156, c1641, c1235, c1237, c1672, c1674, c1167, c1193, c1332, c1313, c1255, c1245, c1303, c1339, c1195, c1168, c1173, c1201, c1194, c1148, c1150, c1335, c1145, c1146, c1307, c1572, c1246, c1250, c1240, c1226, c1228, c1232, c1223, c1224, c1574, c490, c413, c531, c498, c1132, c478, c535, c481, c1120, c461, c813, c818, c819, c823, c826, c880, c884, c774, c776, c771, c722, c750, c719, c734, c698, c728, c697, c727, c696, c180, c195, c171, c119, c425, c424, c396, c1406, c1116, c1118, c1105, c1119, c1122, c392, c1136, c1113, c1404, c1111] c1676 (by decide) p (sat_cons (step1655 p h) (sat_cons (step653 p h) (sat_cons (step652 p h) (sat_cons (step650 p h) (sat_cons (step654 p h) (sat_cons (step886 p h) (sat_cons (step646 p h) (sat_cons (step643 p h) (sat_cons (step642 p h) (sat_cons (step1675 p h) (sat_cons (step1156 p h) (sat_cons (step1641 p h) (sat_cons (step1235 p h) (sat_cons (step1237 p h) (sat_cons (step1672 p h) (sat_cons (step1674 p h) (sat_cons (step1167 p h) (sat_cons (step1193 p h) (sat_cons (step1332 p h) (sat_cons (step1313 p h) (sat_cons (step1255 p h) (sat_cons (step1245 p h) (sat_cons (step1303 p h) (sat_cons (step1339 p h) (sat_cons (step1195 p h) (sat_cons (step1168 p h) (sat_cons (step1173 p h) (sat_cons (step1201 p h) (sat_cons (step1194 p h) (sat_cons (step1148 p h) (sat_cons (step1150 p h) (sat_cons (step1335 p h) (sat_cons (step1145 p h) (sat_cons (step1146 p h) (sat_cons (step1307 p h) (sat_cons (step1572 p h) (sat_cons (step1246 p h) (sat_cons (step1250 p h) (sat_cons (step1240 p h) (sat_cons (step1226 p h) (sat_cons (step1228 p h) (sat_cons (step1232 p h) (sat_cons (step1223 p h) (sat_cons (step1224 p h) (sat_cons (step1574 p h) (sat_cons (step490 p h) (sat_cons (step413 p h) (sat_cons (step531 p h) (sat_cons (step498 p h) (sat_cons (step1132 p h) (sat_cons (step478 p h) (sat_cons (step535 p h) (sat_cons (step481 p h) (sat_cons (step1120 p h) (sat_cons (step461 p h) (sat_cons (step813 p h) (sat_cons (step818 p h) (sat_cons (step819 p h) (sat_cons (step823 p h) (sat_cons (step826 p h) (sat_cons (step880 p h) (sat_cons (step884 p h) (sat_cons (step774 p h) (sat_cons (step776 p h) (sat_cons (step771 p h) (sat_cons (step722 p h) (sat_cons (step750 p h) (sat_cons (step719 p h) (sat_cons (step734 p h) (sat_cons (step698 p h) (sat_cons (step728 p h) (sat_cons (step697 p h) (sat_cons (step727 p h) (sat_cons (step696 p h) (sat_cons (step180 p h) (sat_cons (step195 p h) (sat_cons (step171 p h) (sat_cons (step119 p h) (sat_cons (step425 p h) (sat_cons (step424 p h) (sat_cons (step396 p h) (sat_cons (step1406 p h) (sat_cons (step1116 p h) (sat_cons (step1118 p h) (sat_cons (step1105 p h) (sat_cons (step1119 p h) (sat_cons (step1122 p h) (sat_cons (step392 p h) (sat_cons (step1136 p h) (sat_cons (step1113 p h) (sat_cons (step1404 p h) (sat_cons (step1111 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1677 : List Lit := [(1659, true), (1646, false), (1752, true)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.TreeRup.prove_clause [c652, c1655, c650, c654, c886, c646, c643, c642, c1641, c1235, c1237, c1672, c1674, c1167, c1193, c1332, c1313, c1255, c1227, c1156, c1675, c1676, c1636, c1223, c1225, c1226, c1229, c473, c498, c1250, c1251, c1307, c1240, c1335, c1232, c1194, c1200, c490, c1172, c478, c477, c1148, c1150, c1396, c1145, c1146, c1574, c413, c1132, c535, c1120, c461, c813, c818, c819, c823, c826, c880, c884, c774, c776, c771, c722, c750, c719, c734, c698, c728, c697, c727, c696, c180, c195, c171, c119, c425, c424, c396, c1406, c1116, c1118, c1105, c1119, c1122, c392, c1136, c1113, c1404, c1111] c1677 (by decide) p (sat_cons (step652 p h) (sat_cons (step1655 p h) (sat_cons (step650 p h) (sat_cons (step654 p h) (sat_cons (step886 p h) (sat_cons (step646 p h) (sat_cons (step643 p h) (sat_cons (step642 p h) (sat_cons (step1641 p h) (sat_cons (step1235 p h) (sat_cons (step1237 p h) (sat_cons (step1672 p h) (sat_cons (step1674 p h) (sat_cons (step1167 p h) (sat_cons (step1193 p h) (sat_cons (step1332 p h) (sat_cons (step1313 p h) (sat_cons (step1255 p h) (sat_cons (step1227 p h) (sat_cons (step1156 p h) (sat_cons (step1675 p h) (sat_cons (step1676 p h) (sat_cons (step1636 p h) (sat_cons (step1223 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step1229 p h) (sat_cons (step473 p h) (sat_cons (step498 p h) (sat_cons (step1250 p h) (sat_cons (step1251 p h) (sat_cons (step1307 p h) (sat_cons (step1240 p h) (sat_cons (step1335 p h) (sat_cons (step1232 p h) (sat_cons (step1194 p h) (sat_cons (step1200 p h) (sat_cons (step490 p h) (sat_cons (step1172 p h) (sat_cons (step478 p h) (sat_cons (step477 p h) (sat_cons (step1148 p h) (sat_cons (step1150 p h) (sat_cons (step1396 p h) (sat_cons (step1145 p h) (sat_cons (step1146 p h) (sat_cons (step1574 p h) (sat_cons (step413 p h) (sat_cons (step1132 p h) (sat_cons (step535 p h) (sat_cons (step1120 p h) (sat_cons (step461 p h) (sat_cons (step813 p h) (sat_cons (step818 p h) (sat_cons (step819 p h) (sat_cons (step823 p h) (sat_cons (step826 p h) (sat_cons (step880 p h) (sat_cons (step884 p h) (sat_cons (step774 p h) (sat_cons (step776 p h) (sat_cons (step771 p h) (sat_cons (step722 p h) (sat_cons (step750 p h) (sat_cons (step719 p h) (sat_cons (step734 p h) (sat_cons (step698 p h) (sat_cons (step728 p h) (sat_cons (step697 p h) (sat_cons (step727 p h) (sat_cons (step696 p h) (sat_cons (step180 p h) (sat_cons (step195 p h) (sat_cons (step171 p h) (sat_cons (step119 p h) (sat_cons (step425 p h) (sat_cons (step424 p h) (sat_cons (step396 p h) (sat_cons (step1406 p h) (sat_cons (step1116 p h) (sat_cons (step1118 p h) (sat_cons (step1105 p h) (sat_cons (step1119 p h) (sat_cons (step1122 p h) (sat_cons (step392 p h) (sat_cons (step1136 p h) (sat_cons (step1113 p h) (sat_cons (step1404 p h) (sat_cons (step1111 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1678 : List Lit := [(86, true), (1646, false), (1752, true)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c1655, c653, c1641, c1235, c1237, c1245, c1303, c1339, c1195, c1169, c1677, c1165, c1672, c1153, c1155, c1162, c1168, c1194, c1335, c1307, c1250, c1226, c1223, c531, c532, c1411] c1678 (by decide) p (sat_cons (step1655 p h) (sat_cons (step653 p h) (sat_cons (step1641 p h) (sat_cons (step1235 p h) (sat_cons (step1237 p h) (sat_cons (step1245 p h) (sat_cons (step1303 p h) (sat_cons (step1339 p h) (sat_cons (step1195 p h) (sat_cons (step1169 p h) (sat_cons (step1677 p h) (sat_cons (step1165 p h) (sat_cons (step1672 p h) (sat_cons (step1153 p h) (sat_cons (step1155 p h) (sat_cons (step1162 p h) (sat_cons (step1168 p h) (sat_cons (step1194 p h) (sat_cons (step1335 p h) (sat_cons (step1307 p h) (sat_cons (step1250 p h) (sat_cons (step1226 p h) (sat_cons (step1223 p h) (sat_cons (step531 p h) (sat_cons (step532 p h) (sat_cons (step1411 p h) (sat_nil p)))))))))))))))))))))))))))
def c1679 : List Lit := [(64, false), (1633, true), (70, false), (82, false)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c299, c296, c1107] c1679 (by decide) p (sat_cons (step299 p h) (sat_cons (step296 p h) (sat_cons (step1107 p h) (sat_nil p))))
def c1680 : List Lit := [(99, false), (1646, false), (1752, true)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.TreeRup.prove_clause [c653, c1655, c654, c642, c637, c1678, c1641, c1235, c1237, c1672, c1674, c1167, c1193, c1332, c1313, c1255, c1245, c1303, c1339, c1195, c1169, c532, c1624, c1636, c456, c1163, c1168, c1173, c1158, c1201, c1194, c1148, c1150, c1335, c1145, c1146, c1307, c1572, c1246, c1250, c1240, c1228, c1232, c1574, c413, c490, c1132, c535, c440, c392, c1117, c1119, c1122, c1136, c1113, c1109, c1679, c305, c1493, c1111, c1105] c1680 (by decide) p (sat_cons (step653 p h) (sat_cons (step1655 p h) (sat_cons (step654 p h) (sat_cons (step642 p h) (sat_cons (step637 p h) (sat_cons (step1678 p h) (sat_cons (step1641 p h) (sat_cons (step1235 p h) (sat_cons (step1237 p h) (sat_cons (step1672 p h) (sat_cons (step1674 p h) (sat_cons (step1167 p h) (sat_cons (step1193 p h) (sat_cons (step1332 p h) (sat_cons (step1313 p h) (sat_cons (step1255 p h) (sat_cons (step1245 p h) (sat_cons (step1303 p h) (sat_cons (step1339 p h) (sat_cons (step1195 p h) (sat_cons (step1169 p h) (sat_cons (step532 p h) (sat_cons (step1624 p h) (sat_cons (step1636 p h) (sat_cons (step456 p h) (sat_cons (step1163 p h) (sat_cons (step1168 p h) (sat_cons (step1173 p h) (sat_cons (step1158 p h) (sat_cons (step1201 p h) (sat_cons (step1194 p h) (sat_cons (step1148 p h) (sat_cons (step1150 p h) (sat_cons (step1335 p h) (sat_cons (step1145 p h) (sat_cons (step1146 p h) (sat_cons (step1307 p h) (sat_cons (step1572 p h) (sat_cons (step1246 p h) (sat_cons (step1250 p h) (sat_cons (step1240 p h) (sat_cons (step1228 p h) (sat_cons (step1232 p h) (sat_cons (step1574 p h) (sat_cons (step413 p h) (sat_cons (step490 p h) (sat_cons (step1132 p h) (sat_cons (step535 p h) (sat_cons (step440 p h) (sat_cons (step392 p h) (sat_cons (step1117 p h) (sat_cons (step1119 p h) (sat_cons (step1122 p h) (sat_cons (step1136 p h) (sat_cons (step1113 p h) (sat_cons (step1109 p h) (sat_cons (step1679 p h) (sat_cons (step305 p h) (sat_cons (step1493 p h) (sat_cons (step1111 p h) (sat_cons (step1105 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1681 : List Lit := [(1635, true), (67, true), (1642, true), (82, false), (86, false)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c637, c1105, c1109, c1111, c1107, c285, c305, c360, c359, c1117, c1113, c1122] c1681 (by decide) p (sat_cons (step637 p h) (sat_cons (step1105 p h) (sat_cons (step1109 p h) (sat_cons (step1111 p h) (sat_cons (step1107 p h) (sat_cons (step285 p h) (sat_cons (step305 p h) (sat_cons (step360 p h) (sat_cons (step359 p h) (sat_cons (step1117 p h) (sat_cons (step1113 p h) (sat_cons (step1122 p h) (sat_nil p)))))))))))))
def c1682 : List Lit := [(1641, true), (80, true), (86, false)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c642, c1119, c1121, c1117, c1113, c392, c361] c1682 (by decide) p (sat_cons (step642 p h) (sat_cons (step1119 p h) (sat_cons (step1121 p h) (sat_cons (step1117 p h) (sat_cons (step1113 p h) (sat_cons (step392 p h) (sat_cons (step361 p h) (sat_nil p))))))))
def c1683 : List Lit := [(1646, false), (1752, true)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c1655, c1672, c1674, c1167, c1641, c1235, c1237, c1193, c1332, c1313, c1255, c1227, c1677, c1678, c1680, c1223, c1225, c1226, c1229, c1250, c1251, c1307, c1240, c1335, c1232, c1194, c1200, c1168, c1172, c1160, c1162, c1148, c1150, c1154, c1145, c1146, c1605, c471, c413, c1158, c1574, c1132, c1682, c1136, c1681, c1493, c294, c288, c1106, c1111] c1683 (by decide) p (sat_cons (step1655 p h) (sat_cons (step1672 p h) (sat_cons (step1674 p h) (sat_cons (step1167 p h) (sat_cons (step1641 p h) (sat_cons (step1235 p h) (sat_cons (step1237 p h) (sat_cons (step1193 p h) (sat_cons (step1332 p h) (sat_cons (step1313 p h) (sat_cons (step1255 p h) (sat_cons (step1227 p h) (sat_cons (step1677 p h) (sat_cons (step1678 p h) (sat_cons (step1680 p h) (sat_cons (step1223 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step1229 p h) (sat_cons (step1250 p h) (sat_cons (step1251 p h) (sat_cons (step1307 p h) (sat_cons (step1240 p h) (sat_cons (step1335 p h) (sat_cons (step1232 p h) (sat_cons (step1194 p h) (sat_cons (step1200 p h) (sat_cons (step1168 p h) (sat_cons (step1172 p h) (sat_cons (step1160 p h) (sat_cons (step1162 p h) (sat_cons (step1148 p h) (sat_cons (step1150 p h) (sat_cons (step1154 p h) (sat_cons (step1145 p h) (sat_cons (step1146 p h) (sat_cons (step1605 p h) (sat_cons (step471 p h) (sat_cons (step413 p h) (sat_cons (step1158 p h) (sat_cons (step1574 p h) (sat_cons (step1132 p h) (sat_cons (step1682 p h) (sat_cons (step1136 p h) (sat_cons (step1681 p h) (sat_cons (step1493 p h) (sat_cons (step294 p h) (sat_cons (step288 p h) (sat_cons (step1106 p h) (sat_cons (step1111 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c1684 : List Lit := [(2, false), (4, true)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c609, c3] c1684 (by decide) p (sat_cons (step609 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1685 : List Lit := [(2, false), (1, true)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c609, c4] c1685 (by decide) p (sat_cons (step609 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1686 : List Lit := [(4, false), (2, true)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c1415, c6] c1686 (by decide) p (sat_cons (step1415 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1687 : List Lit := [(4, false), (126, true)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c1415, c7] c1687 (by decide) p (sat_cons (step1415 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1688 : List Lit := [(26, true), (10, true), (8, false)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c611, c19] c1688 (by decide) p (sat_cons (step611 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1689 : List Lit := [(6, true), (8, false), (26, true)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c611, c20] c1689 (by decide) p (sat_cons (step611 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1690 : List Lit := [(6, true), (8, false), (10, true)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c611, c21] c1690 (by decide) p (sat_cons (step611 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1691 : List Lit := [(9, false), (10, true), (68, true)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c612, c23] c1691 (by decide) p (sat_cons (step612 p h) (sat_cons (step23 p h) (sat_nil p)))
def c1692 : List Lit := [(9, false), (10, true), (7, true)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c612, c25] c1692 (by decide) p (sat_cons (step612 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1693 : List Lit := [(14, false), (72, true), (30, true)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c614, c88] c1693 (by decide) p (sat_cons (step614 p h) (sat_cons (step88 p h) (sat_nil p)))
def c1694 : List Lit := [(11, true), (14, false), (72, true)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c614, c89] c1694 (by decide) p (sat_cons (step614 p h) (sat_cons (step89 p h) (sat_nil p)))
def c1695 : List Lit := [(11, true), (14, false), (30, true)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c614, c90] c1695 (by decide) p (sat_cons (step614 p h) (sat_cons (step90 p h) (sat_nil p)))
def c1696 : List Lit := [(73, true), (15, false), (23, true), (13, true)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c615, c93] c1696 (by decide) p (sat_cons (step615 p h) (sat_cons (step93 p h) (sat_nil p)))
def c1697 : List Lit := [(73, true), (15, false), (10, true), (23, true)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c615, c94] c1697 (by decide) p (sat_cons (step615 p h) (sat_cons (step94 p h) (sat_nil p)))
def c1698 : List Lit := [(13, true), (73, true), (10, true), (15, false)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c615, c95] c1698 (by decide) p (sat_cons (step615 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1699 : List Lit := [(13, true), (10, true), (15, false), (23, true)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c615, c96] c1699 (by decide) p (sat_cons (step615 p h) (sat_cons (step96 p h) (sat_nil p)))
def c1700 : List Lit := [(18, false), (35, true), (75, true)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c616, c102] c1700 (by decide) p (sat_cons (step616 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1701 : List Lit := [(16, true), (18, false), (75, true)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c616, c103] c1701 (by decide) p (sat_cons (step616 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1702 : List Lit := [(16, true), (18, false), (35, true)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c616, c104] c1702 (by decide) p (sat_cons (step616 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1703 : List Lit := [(76, true), (19, false), (23, true), (17, true)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c617, c108] c1703 (by decide) p (sat_cons (step617 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1704 : List Lit := [(76, true), (10, true), (19, false), (23, true)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c617, c109] c1704 (by decide) p (sat_cons (step617 p h) (sat_cons (step109 p h) (sat_nil p)))
def c1705 : List Lit := [(76, true), (19, false), (10, true), (17, true)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c617, c110] c1705 (by decide) p (sat_cons (step617 p h) (sat_cons (step110 p h) (sat_nil p)))
def c1706 : List Lit := [(10, true), (19, false), (17, true), (23, true)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c617, c111] c1706 (by decide) p (sat_cons (step617 p h) (sat_cons (step111 p h) (sat_nil p)))
def c1707 : List Lit := [(39, true), (22, false), (80, true), (23, true)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c618, c121] c1707 (by decide) p (sat_cons (step618 p h) (sat_cons (step121 p h) (sat_nil p)))
def c1708 : List Lit := [(20, true), (39, true), (80, true), (22, false)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c618, c122] c1708 (by decide) p (sat_cons (step618 p h) (sat_cons (step122 p h) (sat_nil p)))
def c1709 : List Lit := [(20, true), (22, false), (23, true), (80, true)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c618, c123] c1709 (by decide) p (sat_cons (step618 p h) (sat_cons (step123 p h) (sat_nil p)))
def c1710 : List Lit := [(39, true), (20, true), (23, true), (22, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c618, c124] c1710 (by decide) p (sat_cons (step618 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1711 : List Lit := [(25, false), (24, true)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c619, c143] c1711 (by decide) p (sat_cons (step619 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1712 : List Lit := [(25, false), (7, true)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c619, c144] c1712 (by decide) p (sat_cons (step619 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1713 : List Lit := [(26, true), (27, false), (85, true)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c620, c149] c1713 (by decide) p (sat_cons (step620 p h) (sat_cons (step149 p h) (sat_nil p)))
def c1714 : List Lit := [(10, true), (27, false), (85, true)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c620, c150] c1714 (by decide) p (sat_cons (step620 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1715 : List Lit := [(26, true), (10, true), (27, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c620, c151] c1715 (by decide) p (sat_cons (step620 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1716 : List Lit := [(28, true), (29, false), (88, true)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c621, c157] c1716 (by decide) p (sat_cons (step621 p h) (sat_cons (step157 p h) (sat_nil p)))
def c1717 : List Lit := [(29, false), (13, true), (88, true)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c621, c158] c1717 (by decide) p (sat_cons (step621 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1718 : List Lit := [(28, true), (13, true), (29, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c621, c159] c1718 (by decide) p (sat_cons (step621 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1719 : List Lit := [(40, true), (31, false), (90, true)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c622, c164] c1719 (by decide) p (sat_cons (step622 p h) (sat_cons (step164 p h) (sat_nil p)))
def c1720 : List Lit := [(30, true), (31, false), (90, true)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c622, c165] c1720 (by decide) p (sat_cons (step622 p h) (sat_cons (step165 p h) (sat_nil p)))
def c1721 : List Lit := [(40, true), (30, true), (31, false)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c622, c166] c1721 (by decide) p (sat_cons (step622 p h) (sat_cons (step166 p h) (sat_nil p)))
def c1722 : List Lit := [(93, true), (33, true), (34, false)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c624, c181] c1722 (by decide) p (sat_cons (step624 p h) (sat_cons (step181 p h) (sat_nil p)))
def c1723 : List Lit := [(93, true), (34, false), (17, true)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c624, c182] c1723 (by decide) p (sat_cons (step624 p h) (sat_cons (step182 p h) (sat_nil p)))
def c1724 : List Lit := [(34, false), (33, true), (17, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c624, c183] c1724 (by decide) p (sat_cons (step624 p h) (sat_cons (step183 p h) (sat_nil p)))
def c1725 : List Lit := [(40, true), (36, false), (96, true)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c625, c191] c1725 (by decide) p (sat_cons (step625 p h) (sat_cons (step191 p h) (sat_nil p)))
def c1726 : List Lit := [(36, false), (96, true), (35, true)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c625, c192] c1726 (by decide) p (sat_cons (step625 p h) (sat_cons (step192 p h) (sat_nil p)))
def c1727 : List Lit := [(40, true), (36, false), (35, true)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c625, c193] c1727 (by decide) p (sat_cons (step625 p h) (sat_cons (step193 p h) (sat_nil p)))
def c1728 : List Lit := [(61, true), (40, true), (98, true), (38, false), (37, true)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c626, c200] c1728 (by decide) p (sat_cons (step626 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1729 : List Lit := [(40, true), (61, true), (38, false), (21, true), (98, true)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c626, c201] c1729 (by decide) p (sat_cons (step626 p h) (sat_cons (step201 p h) (sat_nil p)))
def c1730 : List Lit := [(21, true), (40, true), (37, true), (98, true), (38, false)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c626, c202] c1730 (by decide) p (sat_cons (step626 p h) (sat_cons (step202 p h) (sat_nil p)))
def c1731 : List Lit := [(40, true), (61, true), (37, true), (21, true), (38, false)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c626, c203] c1731 (by decide) p (sat_cons (step626 p h) (sat_cons (step203 p h) (sat_nil p)))
def c1732 : List Lit := [(40, true), (41, false), (39, true)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c627, c218] c1732 (by decide) p (sat_cons (step627 p h) (sat_cons (step218 p h) (sat_nil p)))
def c1733 : List Lit := [(40, true), (41, false), (23, true)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c627, c219] c1733 (by decide) p (sat_cons (step627 p h) (sat_cons (step219 p h) (sat_nil p)))
def c1734 : List Lit := [(41, false), (23, true), (39, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c627, c220] c1734 (by decide) p (sat_cons (step627 p h) (sat_cons (step220 p h) (sat_nil p)))
end B112E254
