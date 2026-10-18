import B112E254Part0004
namespace B112E254
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1735 : List Lit := [(44, false), (54, true)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c628, c227] c1735 (by decide) p (sat_cons (step628 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1736 : List Lit := [(44, false), (42, true)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c628, c228] c1736 (by decide) p (sat_cons (step628 p h) (sat_cons (step228 p h) (sat_nil p)))
def c1737 : List Lit := [(104, true), (45, false), (10, true)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c629, c230] c1737 (by decide) p (sat_cons (step629 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1738 : List Lit := [(43, true), (45, false), (10, true)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c629, c231] c1738 (by decide) p (sat_cons (step629 p h) (sat_cons (step231 p h) (sat_nil p)))
def c1739 : List Lit := [(46, false), (12, false), (51, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c236, c232] c1739 (by decide) p (sat_cons (step236 p h) (sat_cons (step232 p h) (sat_nil p)))
def c1740 : List Lit := [(168, false), (51, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c236, c233] c1740 (by decide) p (sat_cons (step236 p h) (sat_cons (step233 p h) (sat_nil p)))
def c1741 : List Lit := [(46, true), (106, true)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c236, c235] c1741 (by decide) p (sat_cons (step236 p h) (sat_cons (step235 p h) (sat_nil p)))
def c1742 : List Lit := [(60, true), (50, true), (51, false), (20, true), (46, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c631, c250] c1742 (by decide) p (sat_cons (step631 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1743 : List Lit := [(60, true), (20, true), (1, true), (46, true), (51, false)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c631, c251] c1743 (by decide) p (sat_cons (step631 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1744 : List Lit := [(50, true), (20, true), (1, true), (46, true), (51, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c631, c252] c1744 (by decide) p (sat_cons (step631 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1745 : List Lit := [(53, false), (52, true)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c632, c255] c1745 (by decide) p (sat_cons (step632 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1746 : List Lit := [(53, false), (43, true)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c632, c256] c1746 (by decide) p (sat_cons (step632 p h) (sat_cons (step256 p h) (sat_nil p)))
def c1747 : List Lit := [(55, false), (113, true)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c633, c262] c1747 (by decide) p (sat_cons (step633 p h) (sat_cons (step262 p h) (sat_nil p)))
def c1748 : List Lit := [(55, false), (54, true)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c633, c263] c1748 (by decide) p (sat_cons (step633 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1749 : List Lit := [(49, true), (58, false), (57, true), (61, true)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c634, c270] c1749 (by decide) p (sat_cons (step634 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1750 : List Lit := [(62, false), (61, true)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c636, c280] c1750 (by decide) p (sat_cons (step636 p h) (sat_cons (step280 p h) (sat_nil p)))
def c1751 : List Lit := [(62, false), (60, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c636, c281] c1751 (by decide) p (sat_cons (step636 p h) (sat_cons (step281 p h) (sat_nil p)))
def c1752 : List Lit := [(64, true), (71, true), (65, false)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c637, c305] c1752 (by decide) p (sat_cons (step637 p h) (sat_cons (step305 p h) (sat_nil p)))
def c1753 : List Lit := [(6, true), (71, true), (65, false)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c637, c306] c1753 (by decide) p (sat_cons (step637 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1754 : List Lit := [(64, true), (6, true), (65, false)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c637, c307] c1754 (by decide) p (sat_cons (step637 p h) (sat_cons (step307 p h) (sat_nil p)))
def c1755 : List Lit := [(74, true), (64, true), (68, true), (66, false)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c638, c311] c1755 (by decide) p (sat_cons (step638 p h) (sat_cons (step311 p h) (sat_nil p)))
def c1756 : List Lit := [(7, true), (68, true), (66, false), (74, true)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c638, c312] c1756 (by decide) p (sat_cons (step638 p h) (sat_cons (step312 p h) (sat_nil p)))
def c1757 : List Lit := [(7, true), (68, true), (64, true), (66, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c638, c313] c1757 (by decide) p (sat_cons (step638 p h) (sat_cons (step313 p h) (sat_nil p)))
def c1758 : List Lit := [(75, true), (68, true), (84, true), (64, true), (67, false)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c639, c316] c1758 (by decide) p (sat_cons (step639 p h) (sat_cons (step316 p h) (sat_nil p)))
def c1759 : List Lit := [(84, true), (72, true), (68, true), (64, true), (67, false)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c639, c317] c1759 (by decide) p (sat_cons (step639 p h) (sat_cons (step317 p h) (sat_nil p)))
def c1760 : List Lit := [(72, true), (68, true), (75, true), (64, true), (67, false)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c639, c318] c1760 (by decide) p (sat_cons (step639 p h) (sat_cons (step318 p h) (sat_nil p)))
def c1761 : List Lit := [(104, true), (68, true), (10, true), (76, true), (69, false), (85, true)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c640, c346] c1761 (by decide) p (sat_cons (step640 p h) (sat_cons (step346 p h) (sat_nil p)))
def c1762 : List Lit := [(72, true), (64, true), (70, false), (71, true)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c641, c349] c1762 (by decide) p (sat_cons (step641 p h) (sat_cons (step349 p h) (sat_nil p)))
def c1763 : List Lit := [(11, true), (72, true), (71, true), (70, false)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c641, c350] c1763 (by decide) p (sat_cons (step641 p h) (sat_cons (step350 p h) (sat_nil p)))
def c1764 : List Lit := [(11, true), (72, true), (64, true), (70, false)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c641, c351] c1764 (by decide) p (sat_cons (step641 p h) (sat_cons (step351 p h) (sat_nil p)))
def c1765 : List Lit := [(11, true), (64, true), (71, true), (70, false)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c641, c352] c1765 (by decide) p (sat_cons (step641 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1766 : List Lit := [(71, true), (77, false), (80, true)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c642, c392] c1766 (by decide) p (sat_cons (step642 p h) (sat_cons (step392 p h) (sat_nil p)))
def c1767 : List Lit := [(20, true), (77, false), (80, true)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c642, c393] c1767 (by decide) p (sat_cons (step642 p h) (sat_cons (step393 p h) (sat_nil p)))
def c1768 : List Lit := [(20, true), (77, false), (71, true)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c642, c394] c1768 (by decide) p (sat_cons (step642 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1769 : List Lit := [(74, true), (78, false), (98, true)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c643, c395] c1769 (by decide) p (sat_cons (step643 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1770 : List Lit := [(21, true), (78, false), (98, true)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c643, c396] c1770 (by decide) p (sat_cons (step643 p h) (sat_cons (step396 p h) (sat_nil p)))
def c1771 : List Lit := [(74, true), (78, false), (21, true)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c643, c397] c1771 (by decide) p (sat_cons (step643 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1772 : List Lit := [(75, true), (109, true), (79, false), (80, true)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c644, c399] c1772 (by decide) p (sat_cons (step644 p h) (sat_cons (step399 p h) (sat_nil p)))
def c1773 : List Lit := [(72, true), (109, true), (80, true), (79, false)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c644, c400] c1773 (by decide) p (sat_cons (step644 p h) (sat_cons (step400 p h) (sat_nil p)))
def c1774 : List Lit := [(72, true), (109, true), (79, false), (75, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c644, c401] c1774 (by decide) p (sat_cons (step644 p h) (sat_cons (step401 p h) (sat_nil p)))
def c1775 : List Lit := [(75, true), (72, true), (79, false), (80, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c644, c402] c1775 (by decide) p (sat_cons (step644 p h) (sat_cons (step402 p h) (sat_nil p)))
def c1776 : List Lit := [(73, true), (76, true), (81, false), (80, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c645, c418] c1776 (by decide) p (sat_cons (step645 p h) (sat_cons (step418 p h) (sat_nil p)))
def c1777 : List Lit := [(76, true), (23, true), (81, false), (80, true)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c645, c419] c1777 (by decide) p (sat_cons (step645 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1778 : List Lit := [(73, true), (23, true), (80, true), (81, false)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c645, c420] c1778 (by decide) p (sat_cons (step645 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1779 : List Lit := [(73, true), (76, true), (23, true), (81, false)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c645, c421] c1779 (by decide) p (sat_cons (step645 p h) (sat_cons (step421 p h) (sat_nil p)))
def c1780 : List Lit := [(84, true), (64, true), (91, true), (82, false)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c646, c423] c1780 (by decide) p (sat_cons (step646 p h) (sat_cons (step423 p h) (sat_nil p)))
def c1781 : List Lit := [(93, true), (88, true), (83, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c647, c427] c1781 (by decide) p (sat_cons (step647 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1782 : List Lit := [(93, true), (85, true), (83, false)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c647, c428] c1782 (by decide) p (sat_cons (step647 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1783 : List Lit := [(85, true), (88, true), (83, false)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c647, c429] c1783 (by decide) p (sat_cons (step647 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1784 : List Lit := [(28, true), (71, true), (88, true), (86, false), (89, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c648, c442] c1784 (by decide) p (sat_cons (step648 p h) (sat_cons (step442 p h) (sat_nil p)))
def c1785 : List Lit := [(90, true), (87, false), (98, true)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c649, c444] c1785 (by decide) p (sat_cons (step649 p h) (sat_cons (step444 p h) (sat_nil p)))
def c1786 : List Lit := [(88, true), (87, false), (98, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c649, c445] c1786 (by decide) p (sat_cons (step649 p h) (sat_cons (step445 p h) (sat_nil p)))
def c1787 : List Lit := [(88, true), (90, true), (87, false)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c649, c446] c1787 (by decide) p (sat_cons (step649 p h) (sat_cons (step446 p h) (sat_nil p)))
def c1788 : List Lit := [(93, true), (95, true), (91, true), (92, false)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c650, c477] c1788 (by decide) p (sat_cons (step650 p h) (sat_cons (step477 p h) (sat_nil p)))
def c1789 : List Lit := [(33, true), (95, true), (91, true), (92, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c650, c478] c1789 (by decide) p (sat_cons (step650 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1790 : List Lit := [(120, true), (91, true), (97, false), (98, true)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c652, c495] c1790 (by decide) p (sat_cons (step652 p h) (sat_cons (step495 p h) (sat_nil p)))
def c1791 : List Lit := [(120, true), (37, true), (97, false), (98, true)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c652, c496] c1791 (by decide) p (sat_cons (step652 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1792 : List Lit := [(37, true), (120, true), (91, true), (97, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c652, c497] c1792 (by decide) p (sat_cons (step652 p h) (sat_cons (step497 p h) (sat_nil p)))
def c1793 : List Lit := [(37, true), (91, true), (97, false), (98, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c652, c498] c1793 (by decide) p (sat_cons (step652 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1794 : List Lit := [(93, true), (99, false), (98, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c653, c531] c1794 (by decide) p (sat_cons (step653 p h) (sat_cons (step531 p h) (sat_nil p)))
def c1795 : List Lit := [(88, true), (99, false), (98, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c653, c532] c1795 (by decide) p (sat_cons (step653 p h) (sat_cons (step532 p h) (sat_nil p)))
def c1796 : List Lit := [(88, true), (93, true), (99, false)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c653, c533] c1796 (by decide) p (sat_cons (step653 p h) (sat_cons (step533 p h) (sat_nil p)))
def c1797 : List Lit := [(89, true), (95, true), (80, true), (100, false)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c654, c535] c1797 (by decide) p (sat_cons (step654 p h) (sat_cons (step535 p h) (sat_nil p)))
def c1798 : List Lit := [(89, true), (39, true), (95, true), (100, false)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c654, c536] c1798 (by decide) p (sat_cons (step654 p h) (sat_cons (step536 p h) (sat_nil p)))
end B112E254
