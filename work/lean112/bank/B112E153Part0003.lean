import B112E153Part0002
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1739 : List Lit := [(58, true), (50, true), (61, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c675, c190] c1739 (by decide) p (sat_cons (step675 p h) (sat_cons (step190 p h) (sat_nil p)))
def c1740 : List Lit := [(64, true), (58, true), (63, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c676, c196] c1740 (by decide) p (sat_cons (step676 p h) (sat_cons (step196 p h) (sat_nil p)))
def c1741 : List Lit := [(62, true), (58, true), (63, false)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c676, c197] c1741 (by decide) p (sat_cons (step676 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1742 : List Lit := [(67, true), (70, true), (65, false), (102, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c677, c201] c1742 (by decide) p (sat_cons (step677 p h) (sat_cons (step201 p h) (sat_nil p)))
def c1743 : List Lit := [(70, true), (102, true), (65, false), (66, true)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c677, c202] c1743 (by decide) p (sat_cons (step677 p h) (sat_cons (step202 p h) (sat_nil p)))
def c1744 : List Lit := [(67, true), (102, true), (65, false), (66, true)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c677, c203] c1744 (by decide) p (sat_cons (step677 p h) (sat_cons (step203 p h) (sat_nil p)))
def c1745 : List Lit := [(67, true), (70, true), (66, true), (65, false)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c677, c204] c1745 (by decide) p (sat_cons (step677 p h) (sat_cons (step204 p h) (sat_nil p)))
def c1746 : List Lit := [(78, true), (71, false), (109, true)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c678, c224] c1746 (by decide) p (sat_cons (step678 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1747 : List Lit := [(70, true), (71, false), (109, true)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c678, c225] c1747 (by decide) p (sat_cons (step678 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1748 : List Lit := [(78, true), (70, true), (71, false)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c678, c226] c1748 (by decide) p (sat_cons (step678 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1749 : List Lit := [(114, true), (72, true), (73, false), (69, true)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c679, c234] c1749 (by decide) p (sat_cons (step679 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1750 : List Lit := [(114, true), (56, true), (73, false), (72, true)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c679, c235] c1750 (by decide) p (sat_cons (step679 p h) (sat_cons (step235 p h) (sat_nil p)))
def c1751 : List Lit := [(114, true), (56, true), (73, false), (69, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c679, c236] c1751 (by decide) p (sat_cons (step679 p h) (sat_cons (step236 p h) (sat_nil p)))
def c1752 : List Lit := [(56, true), (72, true), (73, false), (69, true)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c679, c237] c1752 (by decide) p (sat_cons (step679 p h) (sat_cons (step237 p h) (sat_nil p)))
def c1753 : List Lit := [(78, true), (77, true), (74, false)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c680, c239] c1753 (by decide) p (sat_cons (step680 p h) (sat_cons (step239 p h) (sat_nil p)))
def c1754 : List Lit := [(76, true), (78, true), (74, false)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c680, c240] c1754 (by decide) p (sat_cons (step680 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1755 : List Lit := [(76, true), (77, true), (74, false)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c680, c241] c1755 (by decide) p (sat_cons (step680 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1756 : List Lit := [(76, true), (66, true), (75, false)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c681, c242] c1756 (by decide) p (sat_cons (step681 p h) (sat_cons (step242 p h) (sat_nil p)))
def c1757 : List Lit := [(76, true), (58, true), (75, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c681, c243] c1757 (by decide) p (sat_cons (step681 p h) (sat_cons (step243 p h) (sat_nil p)))
def c1758 : List Lit := [(66, true), (58, true), (75, false)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c681, c244] c1758 (by decide) p (sat_cons (step681 p h) (sat_cons (step244 p h) (sat_nil p)))
def c1759 : List Lit := [(78, true), (79, true), (80, false)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c682, c263] c1759 (by decide) p (sat_cons (step682 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1760 : List Lit := [(79, true), (77, true), (80, false)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c682, c264] c1760 (by decide) p (sat_cons (step682 p h) (sat_cons (step264 p h) (sat_nil p)))
def c1761 : List Lit := [(78, true), (77, true), (80, false)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c682, c265] c1761 (by decide) p (sat_cons (step682 p h) (sat_cons (step265 p h) (sat_nil p)))
def c1762 : List Lit := [(79, true), (81, false), (124, true)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c683, c266] c1762 (by decide) p (sat_cons (step683 p h) (sat_cons (step266 p h) (sat_nil p)))
def c1763 : List Lit := [(72, true), (81, false), (124, true)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c683, c267] c1763 (by decide) p (sat_cons (step683 p h) (sat_cons (step267 p h) (sat_nil p)))
def c1764 : List Lit := [(79, true), (72, true), (81, false)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c683, c268] c1764 (by decide) p (sat_cons (step683 p h) (sat_cons (step268 p h) (sat_nil p)))
def c1765 : List Lit := [(84, true), (92, true), (82, false), (102, true)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c684, c270] c1765 (by decide) p (sat_cons (step684 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1766 : List Lit := [(83, true), (92, true), (102, true), (82, false)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c684, c271] c1766 (by decide) p (sat_cons (step684 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1767 : List Lit := [(83, true), (84, true), (102, true), (82, false)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c684, c272] c1767 (by decide) p (sat_cons (step684 p h) (sat_cons (step272 p h) (sat_nil p)))
def c1768 : List Lit := [(84, true), (83, true), (82, false), (92, true)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c684, c273] c1768 (by decide) p (sat_cons (step684 p h) (sat_cons (step273 p h) (sat_nil p)))
def c1769 : List Lit := [(97, true), (109, true), (86, false)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c685, c287] c1769 (by decide) p (sat_cons (step685 p h) (sat_cons (step287 p h) (sat_nil p)))
def c1770 : List Lit := [(89, true), (109, true), (86, false)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c685, c288] c1770 (by decide) p (sat_cons (step685 p h) (sat_cons (step288 p h) (sat_nil p)))
def c1771 : List Lit := [(97, true), (89, true), (86, false)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c685, c289] c1771 (by decide) p (sat_cons (step685 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1772 : List Lit := [(110, true), (83, true), (87, false), (90, true)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c686, c290] c1772 (by decide) p (sat_cons (step686 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1773 : List Lit := [(17, true), (110, true), (87, false), (90, true)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c686, c291] c1773 (by decide) p (sat_cons (step686 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1774 : List Lit := [(17, true), (110, true), (87, false), (83, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c686, c292] c1774 (by decide) p (sat_cons (step686 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1775 : List Lit := [(17, true), (83, true), (90, true), (87, false)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c686, c293] c1775 (by decide) p (sat_cons (step686 p h) (sat_cons (step293 p h) (sat_nil p)))
def c1776 : List Lit := [(85, true), (114, true), (89, true), (91, false), (101, true), (90, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c687, c346] c1776 (by decide) p (sat_cons (step687 p h) (sat_cons (step346 p h) (sat_nil p)))
def c1777 : List Lit := [(114, true), (90, true), (89, true), (91, false), (56, true), (101, true)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c687, c347] c1777 (by decide) p (sat_cons (step687 p h) (sat_cons (step347 p h) (sat_nil p)))
def c1778 : List Lit := [(114, true), (85, true), (90, true), (91, false), (56, true), (101, true)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c687, c348] c1778 (by decide) p (sat_cons (step687 p h) (sat_cons (step348 p h) (sat_nil p)))
def c1779 : List Lit := [(95, true), (93, false), (97, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c688, c370] c1779 (by decide) p (sat_cons (step688 p h) (sat_cons (step370 p h) (sat_nil p)))
def c1780 : List Lit := [(93, false), (92, true), (97, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c688, c371] c1780 (by decide) p (sat_cons (step688 p h) (sat_cons (step371 p h) (sat_nil p)))
def c1781 : List Lit := [(95, true), (92, true), (93, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c688, c372] c1781 (by decide) p (sat_cons (step688 p h) (sat_cons (step372 p h) (sat_nil p)))
def c1782 : List Lit := [(83, true), (92, true), (94, false), (58, true)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c689, c373] c1782 (by decide) p (sat_cons (step689 p h) (sat_cons (step373 p h) (sat_nil p)))
def c1783 : List Lit := [(98, true), (101, true), (99, false), (97, true)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c690, c390] c1783 (by decide) p (sat_cons (step690 p h) (sat_cons (step390 p h) (sat_nil p)))
def c1784 : List Lit := [(98, true), (101, true), (99, false), (89, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c690, c391] c1784 (by decide) p (sat_cons (step690 p h) (sat_cons (step391 p h) (sat_nil p)))
def c1785 : List Lit := [(97, true), (101, true), (89, true), (99, false)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c690, c392] c1785 (by decide) p (sat_cons (step690 p h) (sat_cons (step392 p h) (sat_nil p)))
def c1786 : List Lit := [(101, true), (98, true), (100, false), (124, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c691, c394] c1786 (by decide) p (sat_cons (step691 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1787 : List Lit := [(90, true), (124, true), (101, true), (100, false)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c691, c395] c1787 (by decide) p (sat_cons (step691 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1788 : List Lit := [(90, true), (98, true), (124, true), (100, false)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c691, c396] c1788 (by decide) p (sat_cons (step691 p h) (sat_cons (step396 p h) (sat_nil p)))
def c1789 : List Lit := [(101, true), (90, true), (100, false), (98, true)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c691, c397] c1789 (by decide) p (sat_cons (step691 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1790 : List Lit := [(104, true), (109, true), (103, false), (106, true)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c692, c436] c1790 (by decide) p (sat_cons (step692 p h) (sat_cons (step436 p h) (sat_nil p)))
def c1791 : List Lit := [(102, true), (109, true), (106, true), (103, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c692, c437] c1791 (by decide) p (sat_cons (step692 p h) (sat_cons (step437 p h) (sat_nil p)))
def c1792 : List Lit := [(104, true), (109, true), (102, true), (103, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c692, c438] c1792 (by decide) p (sat_cons (step692 p h) (sat_cons (step438 p h) (sat_nil p)))
def c1793 : List Lit := [(104, true), (102, true), (103, false), (106, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c692, c439] c1793 (by decide) p (sat_cons (step692 p h) (sat_cons (step439 p h) (sat_nil p)))
def c1794 : List Lit := [(114, true), (109, true), (111, false), (110, true), (104, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c693, c523] c1794 (by decide) p (sat_cons (step693 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1795 : List Lit := [(112, false), (114, true), (109, true), (106, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c694, c526] c1795 (by decide) p (sat_cons (step694 p h) (sat_cons (step526 p h) (sat_nil p)))
def c1796 : List Lit := [(112, false), (114, true), (89, true), (109, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c694, c527] c1796 (by decide) p (sat_cons (step694 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1797 : List Lit := [(112, false), (106, true), (89, true), (114, true)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c694, c528] c1797 (by decide) p (sat_cons (step694 p h) (sat_cons (step528 p h) (sat_nil p)))
def c1798 : List Lit := [(112, false), (109, true), (89, true), (106, true)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c694, c529] c1798 (by decide) p (sat_cons (step694 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1799 : List Lit := [(110, true), (72, true), (90, true), (113, false), (114, true), (124, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c695, c539] c1799 (by decide) p (sat_cons (step695 p h) (sat_cons (step539 p h) (sat_nil p)))
def c1800 : List Lit := [(116, true), (120, true), (102, true), (115, false)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c696, c574] c1800 (by decide) p (sat_cons (step696 p h) (sat_cons (step574 p h) (sat_nil p)))
def c1801 : List Lit := [(92, true), (120, true), (116, true), (115, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c696, c575] c1801 (by decide) p (sat_cons (step696 p h) (sat_cons (step575 p h) (sat_nil p)))
def c1802 : List Lit := [(92, true), (120, true), (102, true), (115, false)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c696, c576] c1802 (by decide) p (sat_cons (step696 p h) (sat_cons (step576 p h) (sat_nil p)))
end B112E153
