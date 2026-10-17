import B112E040Part0002
namespace B112E040
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1717 : List Lit := [(27, true), (40, true), (36, true), (39, false), (41, true)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c684, c305] c1717 (by decide) p (sat_cons (step684 p h) (sat_cons (step305 p h) (sat_nil p)))
def c1718 : List Lit := [(27, true), (33, true), (39, false), (36, true), (41, true)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c684, c306] c1718 (by decide) p (sat_cons (step684 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1719 : List Lit := [(27, true), (33, true), (39, false), (36, true), (40, true)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c684, c307] c1719 (by decide) p (sat_cons (step684 p h) (sat_cons (step307 p h) (sat_nil p)))
def c1720 : List Lit := [(74, true), (35, true), (29, true), (42, false), (41, true), (40, true)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c685, c364] c1720 (by decide) p (sat_cons (step685 p h) (sat_cons (step364 p h) (sat_nil p)))
def c1721 : List Lit := [(44, false), (45, true)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c686, c368] c1721 (by decide) p (sat_cons (step686 p h) (sat_cons (step368 p h) (sat_nil p)))
def c1722 : List Lit := [(44, false), (43, true)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c686, c369] c1722 (by decide) p (sat_cons (step686 p h) (sat_cons (step369 p h) (sat_nil p)))
def c1723 : List Lit := [(46, false), (49, true)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c687, c372] c1723 (by decide) p (sat_cons (step687 p h) (sat_cons (step372 p h) (sat_nil p)))
def c1724 : List Lit := [(46, false), (45, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c687, c373] c1724 (by decide) p (sat_cons (step687 p h) (sat_cons (step373 p h) (sat_nil p)))
def c1725 : List Lit := [(112, true), (5, true), (55, true), (47, false)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c688, c377] c1725 (by decide) p (sat_cons (step688 p h) (sat_cons (step377 p h) (sat_nil p)))
def c1726 : List Lit := [(112, true), (5, true), (47, false), (43, true)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c688, c378] c1726 (by decide) p (sat_cons (step688 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1727 : List Lit := [(43, true), (5, true), (55, true), (47, false)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c688, c379] c1727 (by decide) p (sat_cons (step688 p h) (sat_cons (step379 p h) (sat_nil p)))
def c1728 : List Lit := [(48, false), (59, true)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c689, c380] c1728 (by decide) p (sat_cons (step689 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1729 : List Lit := [(13, true), (57, true), (51, true), (52, false), (68, true)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c690, c391] c1729 (by decide) p (sat_cons (step690 p h) (sat_cons (step391 p h) (sat_nil p)))
def c1730 : List Lit := [(54, false), (53, true)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c691, c395] c1730 (by decide) p (sat_cons (step691 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1731 : List Lit := [(57, true), (56, false), (55, true)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c692, c426] c1731 (by decide) p (sat_cons (step692 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1732 : List Lit := [(51, true), (56, false), (55, true)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c692, c427] c1732 (by decide) p (sat_cons (step692 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1733 : List Lit := [(53, true), (58, false), (55, true)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c693, c430] c1733 (by decide) p (sat_cons (step693 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1734 : List Lit := [(61, false), (69, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c694, c434] c1734 (by decide) p (sat_cons (step694 p h) (sat_cons (step434 p h) (sat_nil p)))
def c1735 : List Lit := [(61, false), (60, true)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c694, c435] c1735 (by decide) p (sat_cons (step694 p h) (sat_cons (step435 p h) (sat_nil p)))
def c1736 : List Lit := [(62, false), (66, true)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c695, c436] c1736 (by decide) p (sat_cons (step695 p h) (sat_cons (step436 p h) (sat_nil p)))
def c1737 : List Lit := [(62, false), (60, true)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c695, c437] c1737 (by decide) p (sat_cons (step695 p h) (sat_cons (step437 p h) (sat_nil p)))
def c1738 : List Lit := [(72, true), (25, true), (63, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c696, c439] c1738 (by decide) p (sat_cons (step696 p h) (sat_cons (step439 p h) (sat_nil p)))
def c1739 : List Lit := [(65, true), (25, true), (63, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c696, c440] c1739 (by decide) p (sat_cons (step696 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1740 : List Lit := [(64, false), (66, true)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c697, c441] c1740 (by decide) p (sat_cons (step697 p h) (sat_cons (step441 p h) (sat_nil p)))
def c1741 : List Lit := [(64, false), (65, true)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c697, c442] c1741 (by decide) p (sat_cons (step697 p h) (sat_cons (step442 p h) (sat_nil p)))
def c1742 : List Lit := [(74, true), (69, true), (70, false), (35, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c698, c454] c1742 (by decide) p (sat_cons (step698 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1743 : List Lit := [(74, true), (68, true), (70, false), (35, true)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c698, c455] c1743 (by decide) p (sat_cons (step698 p h) (sat_cons (step455 p h) (sat_nil p)))
def c1744 : List Lit := [(67, true), (55, true), (72, true), (71, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c699, c457] c1744 (by decide) p (sat_cons (step699 p h) (sat_cons (step457 p h) (sat_nil p)))
def c1745 : List Lit := [(72, true), (67, true), (71, false), (36, true)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c699, c458] c1745 (by decide) p (sat_cons (step699 p h) (sat_cons (step458 p h) (sat_nil p)))
def c1746 : List Lit := [(72, true), (55, true), (36, true), (71, false)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c699, c459] c1746 (by decide) p (sat_cons (step699 p h) (sat_cons (step459 p h) (sat_nil p)))
def c1747 : List Lit := [(67, true), (55, true), (36, true), (71, false)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c699, c460] c1747 (by decide) p (sat_cons (step699 p h) (sat_cons (step460 p h) (sat_nil p)))
def c1748 : List Lit := [(66, true), (74, true), (73, false)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c700, c465] c1748 (by decide) p (sat_cons (step700 p h) (sat_cons (step465 p h) (sat_nil p)))
def c1749 : List Lit := [(74, true), (73, false), (41, true)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c700, c466] c1749 (by decide) p (sat_cons (step700 p h) (sat_cons (step466 p h) (sat_nil p)))
def c1750 : List Lit := [(66, true), (73, false), (41, true)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c700, c467] c1750 (by decide) p (sat_cons (step700 p h) (sat_cons (step467 p h) (sat_nil p)))
def c1751 : List Lit := [(76, false), (78, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c701, c477] c1751 (by decide) p (sat_cons (step701 p h) (sat_cons (step477 p h) (sat_nil p)))
def c1752 : List Lit := [(76, false), (75, true)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c701, c478] c1752 (by decide) p (sat_cons (step701 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1753 : List Lit := [(78, true), (79, false), (96, true)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c703, c484] c1753 (by decide) p (sat_cons (step703 p h) (sat_cons (step484 p h) (sat_nil p)))
def c1754 : List Lit := [(81, true), (97, true), (80, false), (5, true), (112, true)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c704, c491] c1754 (by decide) p (sat_cons (step704 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1755 : List Lit := [(81, true), (75, true), (80, false), (97, true), (5, true)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c704, c492] c1755 (by decide) p (sat_cons (step704 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1756 : List Lit := [(91, true), (83, true), (82, false)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c705, c497] c1756 (by decide) p (sat_cons (step705 p h) (sat_cons (step497 p h) (sat_nil p)))
def c1757 : List Lit := [(91, true), (81, true), (82, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c705, c498] c1757 (by decide) p (sat_cons (step705 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1758 : List Lit := [(81, true), (83, true), (82, false)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c705, c499] c1758 (by decide) p (sat_cons (step705 p h) (sat_cons (step499 p h) (sat_nil p)))
def c1759 : List Lit := [(87, false), (86, true)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c706, c506] c1759 (by decide) p (sat_cons (step706 p h) (sat_cons (step506 p h) (sat_nil p)))
def c1760 : List Lit := [(87, false), (84, true)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c706, c507] c1760 (by decide) p (sat_cons (step706 p h) (sat_cons (step507 p h) (sat_nil p)))
def c1761 : List Lit := [(89, true), (88, false), (108, true)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c707, c508] c1761 (by decide) p (sat_cons (step707 p h) (sat_cons (step508 p h) (sat_nil p)))
def c1762 : List Lit := [(84, true), (88, false), (108, true)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c707, c509] c1762 (by decide) p (sat_cons (step707 p h) (sat_cons (step509 p h) (sat_nil p)))
def c1763 : List Lit := [(84, true), (89, true), (88, false)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c707, c510] c1763 (by decide) p (sat_cons (step707 p h) (sat_cons (step510 p h) (sat_nil p)))
def c1764 : List Lit := [(91, true), (81, true), (90, false)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c708, c516] c1764 (by decide) p (sat_cons (step708 p h) (sat_cons (step516 p h) (sat_nil p)))
def c1765 : List Lit := [(102, true), (75, true), (20, true), (92, false), (97, true)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c709, c522] c1765 (by decide) p (sat_cons (step709 p h) (sat_cons (step522 p h) (sat_nil p)))
def c1766 : List Lit := [(94, false), (96, true), (104, true)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c710, c525] c1766 (by decide) p (sat_cons (step710 p h) (sat_cons (step525 p h) (sat_nil p)))
def c1767 : List Lit := [(93, true), (94, false), (104, true)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c710, c526] c1767 (by decide) p (sat_cons (step710 p h) (sat_cons (step526 p h) (sat_nil p)))
def c1768 : List Lit := [(93, true), (96, true), (94, false)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c710, c527] c1768 (by decide) p (sat_cons (step710 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1769 : List Lit := [(96, true), (101, true), (95, false)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c711, c529] c1769 (by decide) p (sat_cons (step711 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1770 : List Lit := [(93, true), (96, true), (95, false)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c711, c530] c1770 (by decide) p (sat_cons (step711 p h) (sat_cons (step530 p h) (sat_nil p)))
def c1771 : List Lit := [(97, true), (98, false), (100, true), (107, true)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c712, c555] c1771 (by decide) p (sat_cons (step712 p h) (sat_cons (step555 p h) (sat_nil p)))
def c1772 : List Lit := [(98, false), (107, true), (25, true), (100, true)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c712, c556] c1772 (by decide) p (sat_cons (step712 p h) (sat_cons (step556 p h) (sat_nil p)))
def c1773 : List Lit := [(97, true), (98, false), (25, true), (107, true)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c712, c557] c1773 (by decide) p (sat_cons (step712 p h) (sat_cons (step557 p h) (sat_nil p)))
def c1774 : List Lit := [(98, false), (97, true), (100, true), (25, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c712, c558] c1774 (by decide) p (sat_cons (step712 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1775 : List Lit := [(101, true), (97, true), (99, false), (108, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c713, c561] c1775 (by decide) p (sat_cons (step713 p h) (sat_cons (step561 p h) (sat_nil p)))
def c1776 : List Lit := [(97, true), (99, false), (108, true), (100, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c713, c562] c1776 (by decide) p (sat_cons (step713 p h) (sat_cons (step562 p h) (sat_nil p)))
def c1777 : List Lit := [(101, true), (97, true), (100, true), (99, false)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c713, c563] c1777 (by decide) p (sat_cons (step713 p h) (sat_cons (step563 p h) (sat_nil p)))
def c1778 : List Lit := [(96, true), (104, true), (35, true), (105, false)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c714, c580] c1778 (by decide) p (sat_cons (step714 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1779 : List Lit := [(96, true), (103, true), (105, false), (35, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c714, c581] c1779 (by decide) p (sat_cons (step714 p h) (sat_cons (step581 p h) (sat_nil p)))
def c1780 : List Lit := [(102, true), (108, true), (107, true), (97, true), (106, false)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c715, c585] c1780 (by decide) p (sat_cons (step715 p h) (sat_cons (step585 p h) (sat_nil p)))
end B112E040
