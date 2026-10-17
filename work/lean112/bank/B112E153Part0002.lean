import B112E153Part0001
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1675 : List Lit := [(1091, true), (113, true), (1072, false), (1079, false), (103, false), (105, false)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1260, c1270, c1294, c1290, c1261, c1271, c1253, c1638] c1675 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1260 p h) (sat_cons (step1270 p h) (sat_cons (step1294 p h) (sat_cons (step1290 p h) (sat_cons (step1261 p h) (sat_cons (step1271 p h) (sat_cons (step1253 p h) (sat_cons (step1638 p h) (sat_nil p))))))))))
def c1676 : List Lit := [(890, true), (891, true), (20, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c1653, c896, c898, c918, c927, c931, c1618, c1576, c875, c879, c878, c877, c1617, c1548] c1676 (by decide) p (sat_cons (step1653 p h) (sat_cons (step896 p h) (sat_cons (step898 p h) (sat_cons (step918 p h) (sat_cons (step927 p h) (sat_cons (step931 p h) (sat_cons (step1618 p h) (sat_cons (step1576 p h) (sat_cons (step875 p h) (sat_cons (step879 p h) (sat_cons (step878 p h) (sat_cons (step877 p h) (sat_cons (step1617 p h) (sat_cons (step1548 p h) (sat_nil p)))))))))))))))
def c1677 : List Lit := [(2, false), (126, true)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c1550, c2] c1677 (by decide) p (sat_cons (step1550 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1678 : List Lit := [(15, false), (3, false), (49, false)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c1547, c3] c1678 (by decide) p (sat_cons (step1547 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1679 : List Lit := [(6, true), (50, true), (4, false), (16, true)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c651, c4] c1679 (by decide) p (sat_cons (step651 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1680 : List Lit := [(50, true), (4, false), (16, true), (2, true)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c651, c5] c1680 (by decide) p (sat_cons (step651 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1681 : List Lit := [(6, true), (4, false), (16, true), (2, true)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c651, c6] c1681 (by decide) p (sat_cons (step651 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1682 : List Lit := [(11, false), (10, true)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c652, c18] c1682 (by decide) p (sat_cons (step652 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1683 : List Lit := [(12, false), (15, true)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c653, c19] c1683 (by decide) p (sat_cons (step653 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1684 : List Lit := [(12, false), (13, true)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c653, c20] c1684 (by decide) p (sat_cons (step653 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1685 : List Lit := [(28, true), (13, true), (18, false)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c654, c41] c1685 (by decide) p (sat_cons (step654 p h) (sat_cons (step41 p h) (sat_nil p)))
def c1686 : List Lit := [(17, true), (13, true), (18, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c654, c42] c1686 (by decide) p (sat_cons (step654 p h) (sat_cons (step42 p h) (sat_nil p)))
def c1687 : List Lit := [(19, true), (20, false), (89, true)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c655, c48] c1687 (by decide) p (sat_cons (step655 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1688 : List Lit := [(15, true), (20, false), (89, true)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c655, c49] c1688 (by decide) p (sat_cons (step655 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1689 : List Lit := [(19, true), (15, true), (20, false)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c655, c50] c1689 (by decide) p (sat_cons (step655 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1690 : List Lit := [(26, true), (92, true), (21, false)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c656, c52] c1690 (by decide) p (sat_cons (step656 p h) (sat_cons (step52 p h) (sat_nil p)))
def c1691 : List Lit := [(22, true), (92, true), (21, false)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c656, c53] c1691 (by decide) p (sat_cons (step656 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1692 : List Lit := [(22, true), (25, true), (24, false)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c657, c60] c1692 (by decide) p (sat_cons (step657 p h) (sat_cons (step60 p h) (sat_nil p)))
def c1693 : List Lit := [(16, true), (25, true), (24, false)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c657, c61] c1693 (by decide) p (sat_cons (step657 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1694 : List Lit := [(22, true), (16, true), (24, false)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c657, c62] c1694 (by decide) p (sat_cons (step657 p h) (sat_cons (step62 p h) (sat_nil p)))
def c1695 : List Lit := [(28, true), (26, true), (27, false)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c658, c70] c1695 (by decide) p (sat_cons (step658 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1696 : List Lit := [(28, true), (17, true), (27, false)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c658, c71] c1696 (by decide) p (sat_cons (step658 p h) (sat_cons (step71 p h) (sat_nil p)))
def c1697 : List Lit := [(17, true), (26, true), (27, false)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c658, c72] c1697 (by decide) p (sat_cons (step658 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1698 : List Lit := [(31, true), (34, true), (29, false), (102, true)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c659, c76] c1698 (by decide) p (sat_cons (step659 p h) (sat_cons (step76 p h) (sat_nil p)))
def c1699 : List Lit := [(30, true), (34, true), (29, false), (102, true)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c659, c77] c1699 (by decide) p (sat_cons (step659 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1700 : List Lit := [(30, true), (31, true), (29, false), (102, true)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c659, c78] c1700 (by decide) p (sat_cons (step659 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1701 : List Lit := [(30, true), (31, true), (32, false), (36, true), (33, true)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c660, c84] c1701 (by decide) p (sat_cons (step660 p h) (sat_cons (step84 p h) (sat_nil p)))
def c1702 : List Lit := [(30, true), (16, true), (36, true), (32, false), (31, true)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c660, c85] c1702 (by decide) p (sat_cons (step660 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1703 : List Lit := [(42, true), (109, true), (35, false)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c661, c93] c1703 (by decide) p (sat_cons (step661 p h) (sat_cons (step93 p h) (sat_nil p)))
def c1704 : List Lit := [(34, true), (109, true), (35, false)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c661, c94] c1704 (by decide) p (sat_cons (step661 p h) (sat_cons (step94 p h) (sat_nil p)))
def c1705 : List Lit := [(42, true), (34, true), (35, false)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c661, c95] c1705 (by decide) p (sat_cons (step661 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1706 : List Lit := [(36, true), (114, true), (37, false)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c662, c102] c1706 (by decide) p (sat_cons (step662 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1707 : List Lit := [(33, true), (114, true), (37, false)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c662, c103] c1707 (by decide) p (sat_cons (step662 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1708 : List Lit := [(36, true), (33, true), (37, false)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c662, c104] c1708 (by decide) p (sat_cons (step662 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1709 : List Lit := [(42, true), (41, true), (38, false)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c663, c105] c1709 (by decide) p (sat_cons (step663 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1710 : List Lit := [(40, true), (41, true), (38, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c663, c106] c1710 (by decide) p (sat_cons (step663 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1711 : List Lit := [(39, false), (40, true)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c664, c107] c1711 (by decide) p (sat_cons (step664 p h) (sat_cons (step107 p h) (sat_nil p)))
def c1712 : List Lit := [(39, false), (30, true)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c664, c108] c1712 (by decide) p (sat_cons (step664 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1713 : List Lit := [(40, true), (43, false), (42, true), (122, true)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c665, c121] c1713 (by decide) p (sat_cons (step665 p h) (sat_cons (step121 p h) (sat_nil p)))
def c1714 : List Lit := [(28, true), (43, false), (42, true), (122, true)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c665, c122] c1714 (by decide) p (sat_cons (step665 p h) (sat_cons (step122 p h) (sat_nil p)))
def c1715 : List Lit := [(42, true), (44, true), (45, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c666, c125] c1715 (by decide) p (sat_cons (step666 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1716 : List Lit := [(42, true), (41, true), (45, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c666, c126] c1716 (by decide) p (sat_cons (step666 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1717 : List Lit := [(44, true), (46, false), (124, true)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c667, c128] c1717 (by decide) p (sat_cons (step667 p h) (sat_cons (step128 p h) (sat_nil p)))
def c1718 : List Lit := [(36, true), (46, false), (124, true)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c667, c129] c1718 (by decide) p (sat_cons (step667 p h) (sat_cons (step129 p h) (sat_nil p)))
def c1719 : List Lit := [(36, true), (44, true), (46, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c667, c130] c1719 (by decide) p (sat_cons (step667 p h) (sat_cons (step130 p h) (sat_nil p)))
def c1720 : List Lit := [(47, false), (49, true)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c668, c131] c1720 (by decide) p (sat_cons (step668 p h) (sat_cons (step131 p h) (sat_nil p)))
def c1721 : List Lit := [(51, false), (85, true), (50, true), (49, true), (56, true), (69, true)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c669, c145] c1721 (by decide) p (sat_cons (step669 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1722 : List Lit := [(70, true), (62, true), (52, false)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c670, c147] c1722 (by decide) p (sat_cons (step670 p h) (sat_cons (step147 p h) (sat_nil p)))
def c1723 : List Lit := [(54, true), (70, true), (52, false)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c670, c148] c1723 (by decide) p (sat_cons (step670 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1724 : List Lit := [(54, true), (62, true), (52, false)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c670, c149] c1724 (by decide) p (sat_cons (step670 p h) (sat_cons (step149 p h) (sat_nil p)))
def c1725 : List Lit := [(64, true), (56, true), (53, false)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c671, c150] c1725 (by decide) p (sat_cons (step671 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1726 : List Lit := [(64, true), (48, true), (53, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c671, c151] c1726 (by decide) p (sat_cons (step671 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1727 : List Lit := [(48, true), (56, true), (53, false)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c671, c152] c1727 (by decide) p (sat_cons (step671 p h) (sat_cons (step152 p h) (sat_nil p)))
def c1728 : List Lit := [(54, true), (56, true), (89, true), (55, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c672, c158] c1728 (by decide) p (sat_cons (step672 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1729 : List Lit := [(49, true), (55, false), (56, true), (89, true)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c672, c159] c1729 (by decide) p (sat_cons (step672 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1730 : List Lit := [(49, true), (54, true), (55, false), (89, true)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c672, c160] c1730 (by decide) p (sat_cons (step672 p h) (sat_cons (step160 p h) (sat_nil p)))
def c1731 : List Lit := [(54, true), (56, true), (55, false), (49, true)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c672, c161] c1731 (by decide) p (sat_cons (step672 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1732 : List Lit := [(62, true), (92, true), (59, true), (57, false)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c673, c171] c1732 (by decide) p (sat_cons (step673 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1733 : List Lit := [(58, true), (59, true), (92, true), (57, false)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c673, c172] c1733 (by decide) p (sat_cons (step673 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1734 : List Lit := [(77, true), (59, true), (60, false)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c674, c185] c1734 (by decide) p (sat_cons (step674 p h) (sat_cons (step185 p h) (sat_nil p)))
def c1735 : List Lit := [(49, true), (77, true), (60, false)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c674, c186] c1735 (by decide) p (sat_cons (step674 p h) (sat_cons (step186 p h) (sat_nil p)))
def c1736 : List Lit := [(49, true), (59, true), (60, false)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c674, c187] c1736 (by decide) p (sat_cons (step674 p h) (sat_cons (step187 p h) (sat_nil p)))
def c1737 : List Lit := [(58, true), (59, true), (61, false)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c675, c188] c1737 (by decide) p (sat_cons (step675 p h) (sat_cons (step188 p h) (sat_nil p)))
def c1738 : List Lit := [(50, true), (59, true), (61, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c675, c189] c1738 (by decide) p (sat_cons (step675 p h) (sat_cons (step189 p h) (sat_nil p)))
end B112E153
