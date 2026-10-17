import B112E064Part0003
namespace B112E064
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1675 : List Lit := [(23, false), (19, true), (140, true)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c1421, c94] c1675 (by decide) p (sat_cons (step1421 p h) (sat_cons (step94 p h) (sat_nil p)))
def c1676 : List Lit := [(21, true), (25, false), (45, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c653, c97] c1676 (by decide) p (sat_cons (step653 p h) (sat_cons (step97 p h) (sat_nil p)))
def c1677 : List Lit := [(28, false), (145, true), (25, true)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1423, c100] c1677 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step100 p h) (sat_nil p))))
def c1678 : List Lit := [(38, true), (32, true), (29, false)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c656, c102] c1678 (by decide) p (sat_cons (step656 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1679 : List Lit := [(31, true), (32, true), (29, false)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c656, c104] c1679 (by decide) p (sat_cons (step656 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1680 : List Lit := [(101, true), (31, true), (39, true), (30, false)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c657, c108] c1680 (by decide) p (sat_cons (step657 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1681 : List Lit := [(36, true), (33, false), (32, true)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c658, c132] c1681 (by decide) p (sat_cons (step658 p h) (sat_cons (step132 p h) (sat_nil p)))
def c1682 : List Lit := [(32, true), (31, true), (33, false)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c658, c134] c1682 (by decide) p (sat_cons (step658 p h) (sat_cons (step134 p h) (sat_nil p)))
def c1683 : List Lit := [(36, true), (35, false), (32, true)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c659, c138] c1683 (by decide) p (sat_cons (step659 p h) (sat_cons (step138 p h) (sat_nil p)))
def c1684 : List Lit := [(34, true), (35, false), (32, true)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c659, c139] c1684 (by decide) p (sat_cons (step659 p h) (sat_cons (step139 p h) (sat_nil p)))
def c1685 : List Lit := [(40, true), (41, false), (45, true)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c661, c171] c1685 (by decide) p (sat_cons (step661 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1686 : List Lit := [(39, true), (41, false), (45, true)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c661, c172] c1686 (by decide) p (sat_cons (step661 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1687 : List Lit := [(40, true), (39, true), (41, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c661, c173] c1687 (by decide) p (sat_cons (step661 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1688 : List Lit := [(42, true), (43, false), (45, true)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c662, c186] c1688 (by decide) p (sat_cons (step662 p h) (sat_cons (step186 p h) (sat_nil p)))
def c1689 : List Lit := [(43, false), (39, true), (45, true)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c662, c187] c1689 (by decide) p (sat_cons (step662 p h) (sat_cons (step187 p h) (sat_nil p)))
def c1690 : List Lit := [(43, false), (39, true), (42, true)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c662, c188] c1690 (by decide) p (sat_cons (step662 p h) (sat_cons (step188 p h) (sat_nil p)))
def c1691 : List Lit := [(40, true), (42, true), (44, false), (45, true)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c663, c191] c1691 (by decide) p (sat_cons (step663 p h) (sat_cons (step191 p h) (sat_nil p)))
def c1692 : List Lit := [(34, true), (42, true), (44, false), (45, true)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c663, c192] c1692 (by decide) p (sat_cons (step663 p h) (sat_cons (step192 p h) (sat_nil p)))
def c1693 : List Lit := [(40, true), (34, true), (44, false), (45, true)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c663, c193] c1693 (by decide) p (sat_cons (step663 p h) (sat_cons (step193 p h) (sat_nil p)))
def c1694 : List Lit := [(45, true), (117, true), (46, false)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c664, c228] c1694 (by decide) p (sat_cons (step664 p h) (sat_cons (step228 p h) (sat_nil p)))
def c1695 : List Lit := [(45, true), (36, true), (46, false)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c664, c229] c1695 (by decide) p (sat_cons (step664 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1696 : List Lit := [(49, false), (58, true)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c665, c236] c1696 (by decide) p (sat_cons (step665 p h) (sat_cons (step236 p h) (sat_nil p)))
def c1697 : List Lit := [(49, false), (48, true)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c665, c237] c1697 (by decide) p (sat_cons (step665 p h) (sat_cons (step237 p h) (sat_nil p)))
def c1698 : List Lit := [(48, true), (54, true), (50, false)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c666, c238] c1698 (by decide) p (sat_cons (step666 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1699 : List Lit := [(47, true), (54, true), (50, false)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c666, c239] c1699 (by decide) p (sat_cons (step666 p h) (sat_cons (step239 p h) (sat_nil p)))
def c1700 : List Lit := [(50, false), (47, true), (48, true)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c666, c240] c1700 (by decide) p (sat_cons (step666 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1701 : List Lit := [(69, true), (61, true), (51, false)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c667, c242] c1701 (by decide) p (sat_cons (step667 p h) (sat_cons (step242 p h) (sat_nil p)))
def c1702 : List Lit := [(53, true), (69, true), (51, false)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c667, c243] c1702 (by decide) p (sat_cons (step667 p h) (sat_cons (step243 p h) (sat_nil p)))
def c1703 : List Lit := [(54, true), (52, false), (53, true)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c668, c245] c1703 (by decide) p (sat_cons (step668 p h) (sat_cons (step245 p h) (sat_nil p)))
def c1704 : List Lit := [(47, true), (54, true), (52, false)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c668, c246] c1704 (by decide) p (sat_cons (step668 p h) (sat_cons (step246 p h) (sat_nil p)))
def c1705 : List Lit := [(47, true), (52, false), (53, true)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c668, c247] c1705 (by decide) p (sat_cons (step668 p h) (sat_cons (step247 p h) (sat_nil p)))
def c1706 : List Lit := [(55, true), (57, true), (61, true), (56, false)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c669, c262] c1706 (by decide) p (sat_cons (step669 p h) (sat_cons (step262 p h) (sat_nil p)))
def c1707 : List Lit := [(63, true), (58, true), (59, false), (79, true)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c670, c268] c1707 (by decide) p (sat_cons (step670 p h) (sat_cons (step268 p h) (sat_nil p)))
def c1708 : List Lit := [(57, true), (63, true), (59, false), (79, true)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c670, c269] c1708 (by decide) p (sat_cons (step670 p h) (sat_cons (step269 p h) (sat_nil p)))
def c1709 : List Lit := [(80, true), (60, false), (61, true)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c671, c270] c1709 (by decide) p (sat_cons (step671 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1710 : List Lit := [(55, true), (80, true), (60, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c671, c271] c1710 (by decide) p (sat_cons (step671 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1711 : List Lit := [(55, true), (60, false), (61, true)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c671, c272] c1711 (by decide) p (sat_cons (step671 p h) (sat_cons (step272 p h) (sat_nil p)))
def c1712 : List Lit := [(63, true), (62, false), (85, true)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c672, c281] c1712 (by decide) p (sat_cons (step672 p h) (sat_cons (step281 p h) (sat_nil p)))
def c1713 : List Lit := [(54, true), (62, false), (85, true)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c672, c282] c1713 (by decide) p (sat_cons (step672 p h) (sat_cons (step282 p h) (sat_nil p)))
def c1714 : List Lit := [(63, true), (54, true), (62, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c672, c283] c1714 (by decide) p (sat_cons (step672 p h) (sat_cons (step283 p h) (sat_nil p)))
def c1715 : List Lit := [(65, false), (67, true), (69, true)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c673, c291] c1715 (by decide) p (sat_cons (step673 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1716 : List Lit := [(64, true), (65, false), (69, true)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c673, c292] c1716 (by decide) p (sat_cons (step673 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1717 : List Lit := [(64, true), (67, true), (65, false)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c673, c293] c1717 (by decide) p (sat_cons (step673 p h) (sat_cons (step293 p h) (sat_nil p)))
def c1718 : List Lit := [(64, true), (75, true), (66, false), (67, true), (47, true)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c674, c295] c1718 (by decide) p (sat_cons (step674 p h) (sat_cons (step295 p h) (sat_nil p)))
def c1719 : List Lit := [(73, true), (79, true), (68, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c675, c305] c1719 (by decide) p (sat_cons (step675 p h) (sat_cons (step305 p h) (sat_nil p)))
def c1720 : List Lit := [(67, true), (79, true), (68, false)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c675, c306] c1720 (by decide) p (sat_cons (step675 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1721 : List Lit := [(73, true), (67, true), (68, false)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c675, c307] c1721 (by decide) p (sat_cons (step675 p h) (sat_cons (step307 p h) (sat_nil p)))
def c1722 : List Lit := [(73, true), (84, true), (71, true), (72, false)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c677, c358] c1722 (by decide) p (sat_cons (step677 p h) (sat_cons (step358 p h) (sat_nil p)))
def c1723 : List Lit := [(73, true), (69, true), (84, true), (72, false)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c677, c359] c1723 (by decide) p (sat_cons (step677 p h) (sat_cons (step359 p h) (sat_nil p)))
def c1724 : List Lit := [(71, true), (69, true), (72, false), (84, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c677, c360] c1724 (by decide) p (sat_cons (step677 p h) (sat_cons (step360 p h) (sat_nil p)))
def c1725 : List Lit := [(71, true), (73, true), (72, false), (69, true)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c677, c361] c1725 (by decide) p (sat_cons (step677 p h) (sat_cons (step361 p h) (sat_nil p)))
def c1726 : List Lit := [(77, true), (79, true), (85, true), (78, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c680, c402] c1726 (by decide) p (sat_cons (step680 p h) (sat_cons (step402 p h) (sat_nil p)))
def c1727 : List Lit := [(79, true), (75, true), (85, true), (78, false)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c680, c403] c1727 (by decide) p (sat_cons (step680 p h) (sat_cons (step403 p h) (sat_nil p)))
def c1728 : List Lit := [(77, true), (75, true), (85, true), (78, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c680, c404] c1728 (by decide) p (sat_cons (step680 p h) (sat_cons (step404 p h) (sat_nil p)))
def c1729 : List Lit := [(77, true), (75, true), (78, false), (79, true)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c680, c405] c1729 (by decide) p (sat_cons (step680 p h) (sat_cons (step405 p h) (sat_nil p)))
def c1730 : List Lit := [(82, false), (80, true), (85, true)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c682, c482] c1730 (by decide) p (sat_cons (step682 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1731 : List Lit := [(82, false), (75, true), (85, true)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c682, c483] c1731 (by decide) p (sat_cons (step682 p h) (sat_cons (step483 p h) (sat_nil p)))
def c1732 : List Lit := [(80, true), (82, false), (75, true)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c682, c484] c1732 (by decide) p (sat_cons (step682 p h) (sat_cons (step484 p h) (sat_nil p)))
def c1733 : List Lit := [(77, true), (80, true), (84, true), (83, false), (85, true)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c683, c488] c1733 (by decide) p (sat_cons (step683 p h) (sat_cons (step488 p h) (sat_nil p)))
def c1734 : List Lit := [(71, true), (80, true), (84, true), (83, false), (85, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c683, c489] c1734 (by decide) p (sat_cons (step683 p h) (sat_cons (step489 p h) (sat_nil p)))
def c1735 : List Lit := [(77, true), (84, true), (83, false), (71, true), (85, true)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c683, c490] c1735 (by decide) p (sat_cons (step683 p h) (sat_cons (step490 p h) (sat_nil p)))
def c1736 : List Lit := [(71, true), (77, true), (83, false), (80, true), (85, true)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c683, c491] c1736 (by decide) p (sat_cons (step683 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1737 : List Lit := [(71, true), (77, true), (83, false), (84, true), (80, true)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c683, c492] c1737 (by decide) p (sat_cons (step683 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1738 : List Lit := [(89, false), (95, true)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c685, c551] c1738 (by decide) p (sat_cons (step685 p h) (sat_cons (step551 p h) (sat_nil p)))
end B112E064
