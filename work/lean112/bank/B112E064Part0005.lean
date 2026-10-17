import B112E064Part0004
namespace B112E064
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1739 : List Lit := [(90, false), (94, true), (88, true)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c686, c553] c1739 (by decide) p (sat_cons (step686 p h) (sat_cons (step553 p h) (sat_nil p)))
def c1740 : List Lit := [(90, false), (87, true), (88, true)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c686, c554] c1740 (by decide) p (sat_cons (step686 p h) (sat_cons (step554 p h) (sat_nil p)))
def c1741 : List Lit := [(91, false), (93, true)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c687, c555] c1741 (by decide) p (sat_cons (step687 p h) (sat_cons (step555 p h) (sat_nil p)))
def c1742 : List Lit := [(96, false), (100, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c689, c561] c1742 (by decide) p (sat_cons (step689 p h) (sat_cons (step561 p h) (sat_nil p)))
def c1743 : List Lit := [(103, false), (102, true), (112, true)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c691, c576] c1743 (by decide) p (sat_cons (step691 p h) (sat_cons (step576 p h) (sat_nil p)))
def c1744 : List Lit := [(32, true), (112, true), (103, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c691, c577] c1744 (by decide) p (sat_cons (step691 p h) (sat_cons (step577 p h) (sat_nil p)))
def c1745 : List Lit := [(103, false), (102, true), (32, true)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c691, c578] c1745 (by decide) p (sat_cons (step691 p h) (sat_cons (step578 p h) (sat_nil p)))
def c1746 : List Lit := [(102, true), (104, false), (108, true)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c692, c580] c1746 (by decide) p (sat_cons (step692 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1747 : List Lit := [(104, false), (101, true), (108, true)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c692, c581] c1747 (by decide) p (sat_cons (step692 p h) (sat_cons (step581 p h) (sat_nil p)))
def c1748 : List Lit := [(102, true), (101, true), (104, false)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c692, c582] c1748 (by decide) p (sat_cons (step692 p h) (sat_cons (step582 p h) (sat_nil p)))
def c1749 : List Lit := [(105, false), (107, true), (115, true)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c693, c584] c1749 (by decide) p (sat_cons (step693 p h) (sat_cons (step584 p h) (sat_nil p)))
def c1750 : List Lit := [(115, true), (105, false), (69, true)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c693, c585] c1750 (by decide) p (sat_cons (step693 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1751 : List Lit := [(107, true), (105, false), (69, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c693, c586] c1751 (by decide) p (sat_cons (step693 p h) (sat_cons (step586 p h) (sat_nil p)))
def c1752 : List Lit := [(107, true), (106, false), (108, true)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c694, c588] c1752 (by decide) p (sat_cons (step694 p h) (sat_cons (step588 p h) (sat_nil p)))
def c1753 : List Lit := [(101, true), (106, false), (108, true)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c694, c589] c1753 (by decide) p (sat_cons (step694 p h) (sat_cons (step589 p h) (sat_nil p)))
def c1754 : List Lit := [(101, true), (106, false), (107, true)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c694, c590] c1754 (by decide) p (sat_cons (step694 p h) (sat_cons (step590 p h) (sat_nil p)))
def c1755 : List Lit := [(109, true), (111, true), (112, true), (110, false), (115, true)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c695, c609] c1755 (by decide) p (sat_cons (step695 p h) (sat_cons (step609 p h) (sat_nil p)))
def c1756 : List Lit := [(38, true), (112, true), (110, false), (115, true), (109, true)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c695, c610] c1756 (by decide) p (sat_cons (step695 p h) (sat_cons (step610 p h) (sat_nil p)))
def c1757 : List Lit := [(38, true), (111, true), (110, false), (109, true), (115, true)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c695, c611] c1757 (by decide) p (sat_cons (step695 p h) (sat_cons (step611 p h) (sat_nil p)))
def c1758 : List Lit := [(112, true), (117, true), (79, true), (113, false)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c696, c616] c1758 (by decide) p (sat_cons (step696 p h) (sat_cons (step616 p h) (sat_nil p)))
def c1759 : List Lit := [(111, true), (117, true), (79, true), (113, false)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c696, c617] c1759 (by decide) p (sat_cons (step696 p h) (sat_cons (step617 p h) (sat_nil p)))
def c1760 : List Lit := [(111, true), (112, true), (79, true), (113, false)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c696, c618] c1760 (by decide) p (sat_cons (step696 p h) (sat_cons (step618 p h) (sat_nil p)))
def c1761 : List Lit := [(109, true), (80, true), (115, true), (114, false)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c697, c620] c1761 (by decide) p (sat_cons (step697 p h) (sat_cons (step620 p h) (sat_nil p)))
def c1762 : List Lit := [(109, true), (42, true), (114, false), (115, true)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c697, c621] c1762 (by decide) p (sat_cons (step697 p h) (sat_cons (step621 p h) (sat_nil p)))
def c1763 : List Lit := [(42, true), (80, true), (114, false), (115, true)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c697, c622] c1763 (by decide) p (sat_cons (step697 p h) (sat_cons (step622 p h) (sat_nil p)))
def c1764 : List Lit := [(109, true), (42, true), (114, false), (80, true)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c697, c623] c1764 (by decide) p (sat_cons (step697 p h) (sat_cons (step623 p h) (sat_nil p)))
def c1765 : List Lit := [(117, true), (108, true), (116, false), (85, true)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c698, c631] c1765 (by decide) p (sat_cons (step698 p h) (sat_cons (step631 p h) (sat_nil p)))
def c1766 : List Lit := [(45, true), (117, true), (116, false), (108, true)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c698, c632] c1766 (by decide) p (sat_cons (step698 p h) (sat_cons (step632 p h) (sat_nil p)))
def c1767 : List Lit := [(117, true), (45, true), (85, true), (116, false)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c698, c633] c1767 (by decide) p (sat_cons (step698 p h) (sat_cons (step633 p h) (sat_nil p)))
def c1768 : List Lit := [(45, true), (108, true), (85, true), (116, false)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c698, c634] c1768 (by decide) p (sat_cons (step698 p h) (sat_cons (step634 p h) (sat_nil p)))
def c1769 : List Lit := [(239, false), (241, false)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c1448, c704] c1769 (by decide) p (sat_cons (step1448 p h) (sat_cons (step704 p h) (sat_nil p)))
def c1770 : List Lit := [(237, false), (243, false)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c1442, c708] c1770 (by decide) p (sat_cons (step1442 p h) (sat_cons (step708 p h) (sat_nil p)))
def c1771 : List Lit := [(126, false), (127, false)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c1449, c711] c1771 (by decide) p (sat_cons (step1449 p h) (sat_cons (step711 p h) (sat_nil p)))
def c1772 : List Lit := [(125, false), (247, false)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c1447, c715] c1772 (by decide) p (sat_cons (step1447 p h) (sat_cons (step715 p h) (sat_nil p)))
def c1773 : List Lit := [(251, false), (253, false)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c1446, c720] c1773 (by decide) p (sat_cons (step1446 p h) (sat_cons (step720 p h) (sat_nil p)))
def c1774 : List Lit := [(249, false), (255, false)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c1441, c724] c1774 (by decide) p (sat_cons (step1441 p h) (sat_cons (step724 p h) (sat_nil p)))
def c1775 : List Lit := [(245, false), (257, false)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c1435, c729] c1775 (by decide) p (sat_cons (step1435 p h) (sat_cons (step729 p h) (sat_nil p)))
def c1776 : List Lit := [(265, false), (267, false)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c1445, c737] c1776 (by decide) p (sat_cons (step1445 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1777 : List Lit := [(277, false), (283, false)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c1439, c747] c1777 (by decide) p (sat_cons (step1439 p h) (sat_cons (step747 p h) (sat_nil p)))
def c1778 : List Lit := [(271, false), (285, false)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c1434, c751] c1778 (by decide) p (sat_cons (step1434 p h) (sat_cons (step751 p h) (sat_nil p)))
def c1779 : List Lit := [(259, false), (287, false)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c1429, c756] c1779 (by decide) p (sat_cons (step1429 p h) (sat_cons (step756 p h) (sat_nil p)))
def c1780 : List Lit := [(295, false), (297, false)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c1444, c765] c1780 (by decide) p (sat_cons (step1444 p h) (sat_cons (step765 p h) (sat_nil p)))
def c1781 : List Lit := [(301, false), (313, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c1433, c780] c1781 (by decide) p (sat_cons (step1433 p h) (sat_cons (step780 p h) (sat_nil p)))
def c1782 : List Lit := [(333, false), (339, false)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c1437, c799] c1782 (by decide) p (sat_cons (step1437 p h) (sat_cons (step799 p h) (sat_nil p)))
def c1783 : List Lit := [(327, false), (341, false)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c1432, c803] c1783 (by decide) p (sat_cons (step1432 p h) (sat_cons (step803 p h) (sat_nil p)))
def c1784 : List Lit := [(315, false), (343, false)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c1428, c807] c1784 (by decide) p (sat_cons (step1428 p h) (sat_cons (step807 p h) (sat_nil p)))
def c1785 : List Lit := [(289, false), (345, false)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c1425, c812] c1785 (by decide) p (sat_cons (step1425 p h) (sat_cons (step812 p h) (sat_nil p)))
def c1786 : List Lit := [(353, false), (355, false)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c1443, c820] c1786 (by decide) p (sat_cons (step1443 p h) (sat_cons (step820 p h) (sat_nil p)))
def c1787 : List Lit := [(373, false), (401, false)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c1427, c855] c1787 (by decide) p (sat_cons (step1427 p h) (sat_cons (step855 p h) (sat_nil p)))
def c1788 : List Lit := [(441, false), (455, false)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c1430, c893] c1788 (by decide) p (sat_cons (step1430 p h) (sat_cons (step893 p h) (sat_nil p)))
def c1789 : List Lit := [(429, false), (457, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c1426, c897] c1789 (by decide) p (sat_cons (step1426 p h) (sat_cons (step897 p h) (sat_nil p)))
def c1790 : List Lit := [(403, false), (459, false)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c1424, c901] c1790 (by decide) p (sat_cons (step1424 p h) (sat_cons (step901 p h) (sat_nil p)))
def c1791 : List Lit := [(347, false), (461, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c906, c904] c1791 (by decide) p (sat_cons (step906 p h) (sat_cons (step904 p h) (sat_nil p)))
def c1792 : List Lit := [(1503, true), (1493, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1065] c1792 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1065 p h) (sat_nil p)))
def c1793 : List Lit := [(1504, true), (1494, false)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1066] c1793 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1066 p h) (sat_nil p)))
def c1794 : List Lit := [(1495, false), (1505, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1067] c1794 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1067 p h) (sat_nil p)))
def c1795 : List Lit := [(1496, false), (1506, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1068] c1795 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1068 p h) (sat_nil p)))
def c1796 : List Lit := [(1497, false), (1507, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1069] c1796 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c1797 : List Lit := [(1498, false), (1508, true)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1070] c1797 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1070 p h) (sat_nil p)))
def c1798 : List Lit := [(1503, false), (1522, true)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c1485, c1095] c1798 (by decide) p (sat_cons (step1485 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c1799 : List Lit := [(1504, false), (1523, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c1485, c1096] c1799 (by decide) p (sat_cons (step1485 p h) (sat_cons (step1096 p h) (sat_nil p)))
def c1800 : List Lit := [(1505, false), (1524, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c1485, c1097] c1800 (by decide) p (sat_cons (step1485 p h) (sat_cons (step1097 p h) (sat_nil p)))
def c1801 : List Lit := [(1506, false), (1525, true)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c1485, c1098] c1801 (by decide) p (sat_cons (step1485 p h) (sat_cons (step1098 p h) (sat_nil p)))
def c1802 : List Lit := [(1507, false), (1526, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c1485, c1099] c1802 (by decide) p (sat_cons (step1485 p h) (sat_cons (step1099 p h) (sat_nil p)))
end B112E064
