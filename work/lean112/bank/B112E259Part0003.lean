import B112E259Part0002
namespace B112E259
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1732 : List Lit := [(10, false), (28, true)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c593, c53] c1732 (by decide) p (sat_cons (step593 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1733 : List Lit := [(10, false), (12, true)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c593, c54] c1733 (by decide) p (sat_cons (step593 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1734 : List Lit := [(29, true), (11, false), (65, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c594, c56] c1734 (by decide) p (sat_cons (step594 p h) (sat_cons (step56 p h) (sat_nil p)))
def c1735 : List Lit := [(11, false), (65, true), (13, true)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c594, c57] c1735 (by decide) p (sat_cons (step594 p h) (sat_cons (step57 p h) (sat_nil p)))
def c1736 : List Lit := [(29, true), (11, false), (13, true)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c594, c58] c1736 (by decide) p (sat_cons (step594 p h) (sat_cons (step58 p h) (sat_nil p)))
def c1737 : List Lit := [(14, false), (16, true), (70, true)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c595, c68] c1737 (by decide) p (sat_cons (step595 p h) (sat_cons (step68 p h) (sat_nil p)))
def c1738 : List Lit := [(70, true), (5, true), (14, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c595, c69] c1738 (by decide) p (sat_cons (step595 p h) (sat_cons (step69 p h) (sat_nil p)))
def c1739 : List Lit := [(14, false), (16, true), (5, true)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c595, c70] c1739 (by decide) p (sat_cons (step595 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1740 : List Lit := [(71, true), (33, true), (15, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c596, c72] c1740 (by decide) p (sat_cons (step596 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1741 : List Lit := [(71, true), (15, false), (18, true)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c596, c73] c1741 (by decide) p (sat_cons (step596 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1742 : List Lit := [(15, false), (33, true), (18, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c596, c74] c1742 (by decide) p (sat_cons (step596 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1743 : List Lit := [(28, true), (76, true), (19, false)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c597, c98] c1743 (by decide) p (sat_cons (step597 p h) (sat_cons (step98 p h) (sat_nil p)))
def c1744 : List Lit := [(20, true), (76, true), (19, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c597, c99] c1744 (by decide) p (sat_cons (step597 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1745 : List Lit := [(19, false), (28, true), (20, true)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c597, c100] c1745 (by decide) p (sat_cons (step597 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1746 : List Lit := [(21, false), (79, true), (22, true)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c598, c107] c1746 (by decide) p (sat_cons (step598 p h) (sat_cons (step107 p h) (sat_nil p)))
def c1747 : List Lit := [(79, true), (3, true), (21, false)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c598, c108] c1747 (by decide) p (sat_cons (step598 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1748 : List Lit := [(21, false), (3, true), (22, true)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c598, c109] c1748 (by decide) p (sat_cons (step598 p h) (sat_cons (step109 p h) (sat_nil p)))
def c1749 : List Lit := [(23, false), (81, true), (24, true)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c599, c113] c1749 (by decide) p (sat_cons (step599 p h) (sat_cons (step113 p h) (sat_nil p)))
def c1750 : List Lit := [(81, true), (23, false), (5, true)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c599, c114] c1750 (by decide) p (sat_cons (step599 p h) (sat_cons (step114 p h) (sat_nil p)))
def c1751 : List Lit := [(23, false), (24, true), (5, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c599, c115] c1751 (by decide) p (sat_cons (step599 p h) (sat_cons (step115 p h) (sat_nil p)))
def c1752 : List Lit := [(25, false), (26, true)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c600, c120] c1752 (by decide) p (sat_cons (step600 p h) (sat_cons (step120 p h) (sat_nil p)))
def c1753 : List Lit := [(25, false), (8, true)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c600, c121] c1753 (by decide) p (sat_cons (step600 p h) (sat_cons (step121 p h) (sat_nil p)))
def c1754 : List Lit := [(27, false), (86, true), (29, true)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c601, c125] c1754 (by decide) p (sat_cons (step601 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1755 : List Lit := [(27, false), (86, true), (28, true)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c601, c126] c1755 (by decide) p (sat_cons (step601 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1756 : List Lit := [(27, false), (29, true), (28, true)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c601, c127] c1756 (by decide) p (sat_cons (step601 p h) (sat_cons (step127 p h) (sat_nil p)))
def c1757 : List Lit := [(30, false), (31, true), (28, true), (90, true)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c602, c171] c1757 (by decide) p (sat_cons (step602 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1758 : List Lit := [(30, false), (90, true), (12, true), (31, true)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c602, c172] c1758 (by decide) p (sat_cons (step602 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1759 : List Lit := [(90, true), (12, true), (28, true), (30, false)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c602, c173] c1759 (by decide) p (sat_cons (step602 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1760 : List Lit := [(30, false), (31, true), (12, true), (28, true)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c602, c174] c1760 (by decide) p (sat_cons (step602 p h) (sat_cons (step174 p h) (sat_nil p)))
def c1761 : List Lit := [(92, true), (33, true), (32, false)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c603, c180] c1761 (by decide) p (sat_cons (step603 p h) (sat_cons (step180 p h) (sat_nil p)))
def c1762 : List Lit := [(92, true), (32, false), (28, true)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c603, c181] c1762 (by decide) p (sat_cons (step603 p h) (sat_cons (step181 p h) (sat_nil p)))
def c1763 : List Lit := [(33, true), (32, false), (28, true)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c603, c182] c1763 (by decide) p (sat_cons (step603 p h) (sat_cons (step182 p h) (sat_nil p)))
def c1764 : List Lit := [(34, false), (35, true)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c604, c185] c1764 (by decide) p (sat_cons (step604 p h) (sat_cons (step185 p h) (sat_nil p)))
def c1765 : List Lit := [(34, false), (16, true)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c604, c186] c1765 (by decide) p (sat_cons (step604 p h) (sat_cons (step186 p h) (sat_nil p)))
def c1766 : List Lit := [(36, false), (45, true)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c605, c192] c1766 (by decide) p (sat_cons (step605 p h) (sat_cons (step192 p h) (sat_nil p)))
def c1767 : List Lit := [(36, false), (37, true)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c605, c193] c1767 (by decide) p (sat_cons (step605 p h) (sat_cons (step193 p h) (sat_nil p)))
def c1768 : List Lit := [(38, false), (98, true)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c606, c196] c1768 (by decide) p (sat_cons (step606 p h) (sat_cons (step196 p h) (sat_nil p)))
def c1769 : List Lit := [(38, false), (40, true)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c606, c197] c1769 (by decide) p (sat_cons (step606 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1770 : List Lit := [(39, false), (49, true)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c607, c198] c1770 (by decide) p (sat_cons (step607 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1771 : List Lit := [(39, false), (41, true)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c607, c199] c1771 (by decide) p (sat_cons (step607 p h) (sat_cons (step199 p h) (sat_nil p)))
def c1772 : List Lit := [(42, false), (102, true)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c608, c204] c1772 (by decide) p (sat_cons (step608 p h) (sat_cons (step204 p h) (sat_nil p)))
def c1773 : List Lit := [(42, false), (43, true)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c608, c205] c1773 (by decide) p (sat_cons (step608 p h) (sat_cons (step205 p h) (sat_nil p)))
def c1774 : List Lit := [(44, false), (107, true)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c609, c208] c1774 (by decide) p (sat_cons (step609 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1775 : List Lit := [(44, false), (45, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c609, c209] c1775 (by decide) p (sat_cons (step609 p h) (sat_cons (step209 p h) (sat_nil p)))
def c1776 : List Lit := [(48, false), (49, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c610, c216] c1776 (by decide) p (sat_cons (step610 p h) (sat_cons (step216 p h) (sat_nil p)))
def c1777 : List Lit := [(48, false), (28, true)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c610, c217] c1777 (by decide) p (sat_cons (step610 p h) (sat_cons (step217 p h) (sat_nil p)))
def c1778 : List Lit := [(50, false), (51, true)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c611, c220] c1778 (by decide) p (sat_cons (step611 p h) (sat_cons (step220 p h) (sat_nil p)))
def c1779 : List Lit := [(50, false), (40, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c611, c221] c1779 (by decide) p (sat_cons (step611 p h) (sat_cons (step221 p h) (sat_nil p)))
def c1780 : List Lit := [(52, false), (53, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c612, c223] c1780 (by decide) p (sat_cons (step612 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1781 : List Lit := [(52, false), (43, true)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c612, c224] c1781 (by decide) p (sat_cons (step612 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1782 : List Lit := [(55, false), (56, true), (58, true), (61, true), (76, true)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c613, c249] c1782 (by decide) p (sat_cons (step613 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1783 : List Lit := [(55, false), (54, true), (58, true), (61, true), (76, true)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c613, c250] c1783 (by decide) p (sat_cons (step613 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1784 : List Lit := [(55, false), (54, true), (61, true), (56, true), (76, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c613, c251] c1784 (by decide) p (sat_cons (step613 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1785 : List Lit := [(55, false), (56, true), (58, true), (76, true), (54, true)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c613, c252] c1785 (by decide) p (sat_cons (step613 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1786 : List Lit := [(55, false), (54, true), (61, true), (56, true), (58, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c613, c253] c1786 (by decide) p (sat_cons (step613 p h) (sat_cons (step253 p h) (sat_nil p)))
def c1787 : List Lit := [(54, true), (3, true), (67, true), (57, false), (59, true), (58, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c614, c277] c1787 (by decide) p (sat_cons (step614 p h) (sat_cons (step277 p h) (sat_nil p)))
def c1788 : List Lit := [(60, false), (81, true), (61, true), (54, true), (70, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c615, c293] c1788 (by decide) p (sat_cons (step615 p h) (sat_cons (step293 p h) (sat_nil p)))
def c1789 : List Lit := [(54, true), (60, false), (61, true), (5, true), (81, true)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c615, c294] c1789 (by decide) p (sat_cons (step615 p h) (sat_cons (step294 p h) (sat_nil p)))
def c1790 : List Lit := [(60, false), (54, true), (5, true), (61, true), (70, true)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c615, c295] c1790 (by decide) p (sat_cons (step615 p h) (sat_cons (step295 p h) (sat_nil p)))
def c1791 : List Lit := [(62, false), (83, true), (71, true), (61, true)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c616, c308] c1791 (by decide) p (sat_cons (step616 p h) (sat_cons (step308 p h) (sat_nil p)))
def c1792 : List Lit := [(62, false), (83, true), (56, true), (71, true)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c616, c309] c1792 (by decide) p (sat_cons (step616 p h) (sat_cons (step309 p h) (sat_nil p)))
def c1793 : List Lit := [(83, true), (56, true), (62, false), (61, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c616, c310] c1793 (by decide) p (sat_cons (step616 p h) (sat_cons (step310 p h) (sat_nil p)))
def c1794 : List Lit := [(62, false), (56, true), (61, true), (71, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c616, c311] c1794 (by decide) p (sat_cons (step616 p h) (sat_cons (step311 p h) (sat_nil p)))
def c1795 : List Lit := [(72, true), (61, true), (63, false), (58, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c617, c314] c1795 (by decide) p (sat_cons (step617 p h) (sat_cons (step314 p h) (sat_nil p)))
end B112E259
