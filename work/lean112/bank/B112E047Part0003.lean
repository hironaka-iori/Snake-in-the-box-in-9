import B112E047Part0002
namespace B112E047
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1735 : List Lit := [(18, false), (14, true), (82, true)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c687, c94] c1735 (by decide) p (sat_cons (step687 p h) (sat_cons (step94 p h) (sat_nil p)))
def c1736 : List Lit := [(36, true), (19, false), (17, true), (84, true)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c688, c98] c1736 (by decide) p (sat_cons (step688 p h) (sat_cons (step98 p h) (sat_nil p)))
def c1737 : List Lit := [(22, false), (23, true)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c689, c110] c1737 (by decide) p (sat_cons (step689 p h) (sat_cons (step110 p h) (sat_nil p)))
def c1738 : List Lit := [(22, false), (20, true)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c689, c111] c1738 (by decide) p (sat_cons (step689 p h) (sat_cons (step111 p h) (sat_nil p)))
def c1739 : List Lit := [(24, false), (25, true), (28, true), (26, true)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c690, c121] c1739 (by decide) p (sat_cons (step690 p h) (sat_cons (step121 p h) (sat_nil p)))
def c1740 : List Lit := [(24, false), (25, true), (14, true), (26, true)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c690, c122] c1740 (by decide) p (sat_cons (step690 p h) (sat_cons (step122 p h) (sat_nil p)))
def c1741 : List Lit := [(27, false), (25, true), (26, true), (91, true)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c691, c143] c1741 (by decide) p (sat_cons (step691 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1742 : List Lit := [(27, false), (17, true), (91, true), (26, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c691, c144] c1742 (by decide) p (sat_cons (step691 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1743 : List Lit := [(47, true), (31, true), (97, true), (29, false), (26, true)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c692, c160] c1743 (by decide) p (sat_cons (step692 p h) (sat_cons (step160 p h) (sat_nil p)))
def c1744 : List Lit := [(47, true), (31, true), (21, true), (29, false), (26, true)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c692, c161] c1744 (by decide) p (sat_cons (step692 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1745 : List Lit := [(30, false), (31, true)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c693, c162] c1745 (by decide) p (sat_cons (step693 p h) (sat_cons (step162 p h) (sat_nil p)))
def c1746 : List Lit := [(30, false), (28, true)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c693, c163] c1746 (by decide) p (sat_cons (step693 p h) (sat_cons (step163 p h) (sat_nil p)))
def c1747 : List Lit := [(32, false), (31, true)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c694, c169] c1747 (by decide) p (sat_cons (step694 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1748 : List Lit := [(32, false), (23, true)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c694, c170] c1748 (by decide) p (sat_cons (step694 p h) (sat_cons (step170 p h) (sat_nil p)))
def c1749 : List Lit := [(33, false), (37, true), (14, true)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c695, c172] c1749 (by decide) p (sat_cons (step695 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1750 : List Lit := [(35, false), (43, true), (36, true)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c696, c184] c1750 (by decide) p (sat_cons (step696 p h) (sat_cons (step184 p h) (sat_nil p)))
def c1751 : List Lit := [(39, false), (37, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c698, c200] c1751 (by decide) p (sat_cons (step698 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1752 : List Lit := [(12, true), (111, true), (41, false), (26, true), (47, true)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c699, c210] c1752 (by decide) p (sat_cons (step699 p h) (sat_cons (step210 p h) (sat_nil p)))
def c1753 : List Lit := [(48, false), (47, true)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c702, c227] c1753 (by decide) p (sat_cons (step702 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1754 : List Lit := [(49, false), (46, true)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c703, c229] c1754 (by decide) p (sat_cons (step703 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1755 : List Lit := [(49, false), (42, true)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c703, c230] c1755 (by decide) p (sat_cons (step703 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1756 : List Lit := [(64, true), (50, false), (80, true), (52, true)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c704, c235] c1756 (by decide) p (sat_cons (step704 p h) (sat_cons (step235 p h) (sat_nil p)))
def c1757 : List Lit := [(64, true), (50, false), (51, true), (80, true)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c704, c236] c1757 (by decide) p (sat_cons (step704 p h) (sat_cons (step236 p h) (sat_nil p)))
def c1758 : List Lit := [(50, false), (52, true), (51, true), (80, true)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c704, c237] c1758 (by decide) p (sat_cons (step704 p h) (sat_cons (step237 p h) (sat_nil p)))
def c1759 : List Lit := [(50, false), (52, true), (51, true), (64, true)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c704, c238] c1759 (by decide) p (sat_cons (step704 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1760 : List Lit := [(56, true), (58, true), (53, false)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c705, c252] c1760 (by decide) p (sat_cons (step705 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1761 : List Lit := [(53, false), (58, true), (54, true)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c705, c253] c1761 (by decide) p (sat_cons (step705 p h) (sat_cons (step253 p h) (sat_nil p)))
def c1762 : List Lit := [(53, false), (56, true), (54, true)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c705, c254] c1762 (by decide) p (sat_cons (step705 p h) (sat_cons (step254 p h) (sat_nil p)))
def c1763 : List Lit := [(54, true), (91, true), (55, false)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c706, c259] c1763 (by decide) p (sat_cons (step706 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1764 : List Lit := [(55, false), (51, true), (91, true)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c706, c260] c1764 (by decide) p (sat_cons (step706 p h) (sat_cons (step260 p h) (sat_nil p)))
def c1765 : List Lit := [(55, false), (54, true), (51, true)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c706, c261] c1765 (by decide) p (sat_cons (step706 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1766 : List Lit := [(57, false), (56, false), (7, false)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c1543, c266] c1766 (by decide) p (sat_cons (step1543 p h) (sat_cons (step266 p h) (sat_nil p)))
def c1767 : List Lit := [(57, false), (93, false), (7, false)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c1543, c267] c1767 (by decide) p (sat_cons (step1543 p h) (sat_cons (step267 p h) (sat_nil p)))
def c1768 : List Lit := [(56, false), (57, false), (93, false)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c1543, c268] c1768 (by decide) p (sat_cons (step1543 p h) (sat_cons (step268 p h) (sat_nil p)))
def c1769 : List Lit := [(58, false), (56, false), (59, false)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c1543, c274] c1769 (by decide) p (sat_cons (step1543 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1770 : List Lit := [(56, true), (58, true), (59, false)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c708, c275] c1770 (by decide) p (sat_cons (step708 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1771 : List Lit := [(57, false), (59, false)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c1543, c281, c276] c1771 (by decide) p (sat_cons (step1543 p h) (sat_cons (step281 p h) (sat_cons (step276 p h) (sat_nil p))))
def c1772 : List Lit := [(178, false), (57, false)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c281, c277] c1772 (by decide) p (sat_cons (step281 p h) (sat_cons (step277 p h) (sat_nil p)))
def c1773 : List Lit := [(178, false), (59, false)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c281, c278] c1773 (by decide) p (sat_cons (step281 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1774 : List Lit := [(59, true), (57, true), (178, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c1543, c279] c1774 (by decide) p (sat_cons (step1543 p h) (sat_cons (step279 p h) (sat_nil p)))
def c1775 : List Lit := [(62, false), (67, true), (64, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c709, c283] c1775 (by decide) p (sat_cons (step709 p h) (sat_cons (step283 p h) (sat_nil p)))
def c1776 : List Lit := [(62, false), (63, true), (64, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c709, c284] c1776 (by decide) p (sat_cons (step709 p h) (sat_cons (step284 p h) (sat_nil p)))
def c1777 : List Lit := [(65, false), (71, true), (64, true)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c710, c303] c1777 (by decide) p (sat_cons (step710 p h) (sat_cons (step303 p h) (sat_nil p)))
def c1778 : List Lit := [(66, true), (65, false), (64, true)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c710, c304] c1778 (by decide) p (sat_cons (step710 p h) (sat_cons (step304 p h) (sat_nil p)))
def c1779 : List Lit := [(71, true), (76, true), (67, true), (52, true), (69, false), (105, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c712, c339] c1779 (by decide) p (sat_cons (step712 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1780 : List Lit := [(67, true), (64, true), (52, true), (69, false), (76, true), (105, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c712, c340] c1780 (by decide) p (sat_cons (step712 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1781 : List Lit := [(70, false), (71, true)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c713, c341] c1781 (by decide) p (sat_cons (step713 p h) (sat_cons (step341 p h) (sat_nil p)))
def c1782 : List Lit := [(70, false), (67, true)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c713, c342] c1782 (by decide) p (sat_cons (step713 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1783 : List Lit := [(72, false), (76, true), (64, true), (111, true)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c714, c351] c1783 (by decide) p (sat_cons (step714 p h) (sat_cons (step351 p h) (sat_nil p)))
def c1784 : List Lit := [(12, true), (111, true), (64, true), (72, false)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c714, c352] c1784 (by decide) p (sat_cons (step714 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1785 : List Lit := [(74, false), (73, true)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c715, c357] c1785 (by decide) p (sat_cons (step715 p h) (sat_cons (step357 p h) (sat_nil p)))
def c1786 : List Lit := [(74, false), (66, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c715, c358] c1786 (by decide) p (sat_cons (step715 p h) (sat_cons (step358 p h) (sat_nil p)))
def c1787 : List Lit := [(77, false), (76, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c716, c368] c1787 (by decide) p (sat_cons (step716 p h) (sat_cons (step368 p h) (sat_nil p)))
def c1788 : List Lit := [(77, false), (75, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c716, c369] c1788 (by decide) p (sat_cons (step716 p h) (sat_cons (step369 p h) (sat_nil p)))
def c1789 : List Lit := [(78, false), (75, true)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c717, c370] c1789 (by decide) p (sat_cons (step717 p h) (sat_cons (step370 p h) (sat_nil p)))
def c1790 : List Lit := [(78, false), (73, true)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c717, c371] c1790 (by decide) p (sat_cons (step717 p h) (sat_cons (step371 p h) (sat_nil p)))
def c1791 : List Lit := [(79, false), (85, true), (82, true), (80, true)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c718, c375] c1791 (by decide) p (sat_cons (step718 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1792 : List Lit := [(79, false), (82, true), (14, true), (80, true)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c718, c376] c1792 (by decide) p (sat_cons (step718 p h) (sat_cons (step376 p h) (sat_nil p)))
def c1793 : List Lit := [(89, true), (82, true), (93, true), (83, false), (84, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c720, c432] c1793 (by decide) p (sat_cons (step720 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1794 : List Lit := [(89, true), (80, true), (83, false), (84, true), (93, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c720, c433] c1794 (by decide) p (sat_cons (step720 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1795 : List Lit := [(89, true), (80, true), (84, true), (82, true), (83, false)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c720, c434] c1795 (by decide) p (sat_cons (step720 p h) (sat_cons (step434 p h) (sat_nil p)))
def c1796 : List Lit := [(85, true), (104, true), (96, true), (86, false)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c721, c453] c1796 (by decide) p (sat_cons (step721 p h) (sat_cons (step453 p h) (sat_nil p)))
def c1797 : List Lit := [(89, true), (105, true), (87, false), (52, true), (80, true), (85, true), (21, true)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c722, c489] c1797 (by decide) p (sat_cons (step722 p h) (sat_cons (step489 p h) (sat_nil p)))
def c1798 : List Lit := [(85, true), (97, true), (87, false), (52, true), (80, true), (21, true), (89, true)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c722, c490] c1798 (by decide) p (sat_cons (step722 p h) (sat_cons (step490 p h) (sat_nil p)))
end B112E047
