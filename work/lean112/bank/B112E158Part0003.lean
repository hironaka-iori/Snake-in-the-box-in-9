import B112E158Part0002
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1762 : List Lit := [(15, true), (52, true), (13, false)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c669, c53] c1762 (by decide) p (sat_cons (step669 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1763 : List Lit := [(12, true), (52, true), (13, false)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c669, c54] c1763 (by decide) p (sat_cons (step669 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1764 : List Lit := [(12, true), (15, true), (13, false)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c669, c55] c1764 (by decide) p (sat_cons (step669 p h) (sat_cons (step55 p h) (sat_nil p)))
def c1765 : List Lit := [(26, true), (16, true), (17, false)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c670, c73] c1765 (by decide) p (sat_cons (step670 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1766 : List Lit := [(26, true), (12, true), (17, false)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c670, c74] c1766 (by decide) p (sat_cons (step670 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1767 : List Lit := [(16, true), (12, true), (17, false)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c670, c75] c1767 (by decide) p (sat_cons (step670 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1768 : List Lit := [(18, true), (60, true), (4, true), (19, false)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c671, c82] c1768 (by decide) p (sat_cons (step671 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1769 : List Lit := [(15, true), (60, true), (19, false), (4, true)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c671, c83] c1769 (by decide) p (sat_cons (step671 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1770 : List Lit := [(15, true), (18, true), (19, false), (4, true)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c671, c84] c1770 (by decide) p (sat_cons (step671 p h) (sat_cons (step84 p h) (sat_nil p)))
def c1771 : List Lit := [(20, false), (27, true)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c672, c85] c1771 (by decide) p (sat_cons (step672 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1772 : List Lit := [(20, false), (23, true)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c672, c86] c1772 (by decide) p (sat_cons (step672 p h) (sat_cons (step86 p h) (sat_nil p)))
def c1773 : List Lit := [(23, true), (64, true), (22, true), (21, false)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c673, c89] c1773 (by decide) p (sat_cons (step673 p h) (sat_cons (step89 p h) (sat_nil p)))
def c1774 : List Lit := [(14, true), (64, true), (22, true), (21, false)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c673, c90] c1774 (by decide) p (sat_cons (step673 p h) (sat_cons (step90 p h) (sat_nil p)))
def c1775 : List Lit := [(23, true), (14, true), (21, false), (22, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c673, c91] c1775 (by decide) p (sat_cons (step673 p h) (sat_cons (step91 p h) (sat_nil p)))
def c1776 : List Lit := [(27, true), (26, true), (25, false)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c674, c116] c1776 (by decide) p (sat_cons (step674 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1777 : List Lit := [(27, true), (16, true), (25, false)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c674, c117] c1777 (by decide) p (sat_cons (step674 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1778 : List Lit := [(26, true), (16, true), (25, false)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c674, c118] c1778 (by decide) p (sat_cons (step674 p h) (sat_cons (step118 p h) (sat_nil p)))
def c1779 : List Lit := [(26, true), (69, true), (28, false)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c675, c126] c1779 (by decide) p (sat_cons (step675 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1780 : List Lit := [(69, true), (28, false), (22, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c675, c127] c1780 (by decide) p (sat_cons (step675 p h) (sat_cons (step127 p h) (sat_nil p)))
def c1781 : List Lit := [(26, true), (22, true), (28, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c675, c128] c1781 (by decide) p (sat_cons (step675 p h) (sat_cons (step128 p h) (sat_nil p)))
def c1782 : List Lit := [(33, true), (36, true), (52, true), (30, false)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c676, c139] c1782 (by decide) p (sat_cons (step676 p h) (sat_cons (step139 p h) (sat_nil p)))
def c1783 : List Lit := [(36, true), (30, false), (29, true), (52, true)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c676, c140] c1783 (by decide) p (sat_cons (step676 p h) (sat_cons (step140 p h) (sat_nil p)))
def c1784 : List Lit := [(33, true), (30, false), (29, true), (52, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c676, c141] c1784 (by decide) p (sat_cons (step676 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1785 : List Lit := [(33, true), (36, true), (30, false), (29, true)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c676, c142] c1785 (by decide) p (sat_cons (step676 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1786 : List Lit := [(46, true), (36, true), (37, true), (34, false)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c677, c164] c1786 (by decide) p (sat_cons (step677 p h) (sat_cons (step164 p h) (sat_nil p)))
def c1787 : List Lit := [(46, true), (34, false), (37, true), (29, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c677, c165] c1787 (by decide) p (sat_cons (step677 p h) (sat_cons (step165 p h) (sat_nil p)))
def c1788 : List Lit := [(46, true), (36, true), (34, false), (29, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c677, c166] c1788 (by decide) p (sat_cons (step677 p h) (sat_cons (step166 p h) (sat_nil p)))
def c1789 : List Lit := [(36, true), (34, false), (37, true), (29, true)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c677, c167] c1789 (by decide) p (sat_cons (step677 p h) (sat_cons (step167 p h) (sat_nil p)))
def c1790 : List Lit := [(56, true), (47, true), (36, true), (35, false), (38, true)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c678, c174] c1790 (by decide) p (sat_cons (step678 p h) (sat_cons (step174 p h) (sat_nil p)))
def c1791 : List Lit := [(38, true), (60, true), (39, false), (33, true), (36, true), (37, true)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c679, c221] c1791 (by decide) p (sat_cons (step679 p h) (sat_cons (step221 p h) (sat_nil p)))
def c1792 : List Lit := [(60, true), (38, true), (36, true), (4, true), (37, true), (39, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c679, c222] c1792 (by decide) p (sat_cons (step679 p h) (sat_cons (step222 p h) (sat_nil p)))
def c1793 : List Lit := [(38, true), (60, true), (33, true), (4, true), (37, true), (39, false)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c679, c223] c1793 (by decide) p (sat_cons (step679 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1794 : List Lit := [(38, true), (60, true), (33, true), (4, true), (39, false), (36, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c679, c224] c1794 (by decide) p (sat_cons (step679 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1795 : List Lit := [(60, true), (36, true), (37, true), (39, false), (33, true), (4, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c679, c225] c1795 (by decide) p (sat_cons (step679 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1796 : List Lit := [(38, true), (36, true), (4, true), (37, true), (33, true), (39, false)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c679, c226] c1796 (by decide) p (sat_cons (step679 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1797 : List Lit := [(43, true), (47, true), (41, false)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c680, c237] c1797 (by decide) p (sat_cons (step680 p h) (sat_cons (step237 p h) (sat_nil p)))
def c1798 : List Lit := [(47, true), (40, true), (41, false)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c680, c238] c1798 (by decide) p (sat_cons (step680 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1799 : List Lit := [(43, true), (40, true), (41, false)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c680, c239] c1799 (by decide) p (sat_cons (step680 p h) (sat_cons (step239 p h) (sat_nil p)))
def c1800 : List Lit := [(42, false), (40, true), (64, true), (31, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c681, c241] c1800 (by decide) p (sat_cons (step681 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1801 : List Lit := [(96, true), (43, true), (44, false), (66, true)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c682, c244] c1801 (by decide) p (sat_cons (step682 p h) (sat_cons (step244 p h) (sat_nil p)))
def c1802 : List Lit := [(96, true), (43, true), (44, false), (33, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c682, c245] c1802 (by decide) p (sat_cons (step682 p h) (sat_cons (step245 p h) (sat_nil p)))
def c1803 : List Lit := [(43, true), (66, true), (33, true), (44, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c682, c246] c1803 (by decide) p (sat_cons (step682 p h) (sat_cons (step246 p h) (sat_nil p)))
def c1804 : List Lit := [(47, true), (46, true), (45, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c683, c248] c1804 (by decide) p (sat_cons (step683 p h) (sat_cons (step248 p h) (sat_nil p)))
def c1805 : List Lit := [(47, true), (40, true), (45, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c683, c249] c1805 (by decide) p (sat_cons (step683 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1806 : List Lit := [(46, true), (40, true), (45, false)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c683, c250] c1806 (by decide) p (sat_cons (step683 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1807 : List Lit := [(69, true), (46, true), (48, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c684, c259] c1807 (by decide) p (sat_cons (step684 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1808 : List Lit := [(69, true), (37, true), (48, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c684, c260] c1808 (by decide) p (sat_cons (step684 p h) (sat_cons (step260 p h) (sat_nil p)))
def c1809 : List Lit := [(46, true), (37, true), (48, false)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c684, c261] c1809 (by decide) p (sat_cons (step684 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1810 : List Lit := [(56, true), (51, false), (52, true)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c685, c290] c1810 (by decide) p (sat_cons (step685 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1811 : List Lit := [(49, true), (56, true), (51, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c685, c291] c1811 (by decide) p (sat_cons (step685 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1812 : List Lit := [(49, true), (51, false), (52, true)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c685, c292] c1812 (by decide) p (sat_cons (step685 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1813 : List Lit := [(49, true), (57, true), (103, true), (53, false), (64, true), (31, true)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c686, c338] c1813 (by decide) p (sat_cons (step686 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1814 : List Lit := [(49, true), (16, true), (55, false), (56, true), (57, true)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c687, c352] c1814 (by decide) p (sat_cons (step687 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1815 : List Lit := [(57, true), (69, true), (58, false), (60, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c688, c374] c1815 (by decide) p (sat_cons (step688 p h) (sat_cons (step374 p h) (sat_nil p)))
def c1816 : List Lit := [(69, true), (60, true), (58, false), (37, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c688, c375] c1816 (by decide) p (sat_cons (step688 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1817 : List Lit := [(57, true), (69, true), (58, false), (37, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c688, c376] c1817 (by decide) p (sat_cons (step688 p h) (sat_cons (step376 p h) (sat_nil p)))
def c1818 : List Lit := [(57, true), (60, true), (58, false), (37, true)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c688, c377] c1818 (by decide) p (sat_cons (step688 p h) (sat_cons (step377 p h) (sat_nil p)))
def c1819 : List Lit := [(56, true), (108, true), (60, true), (38, true), (59, false), (18, true), (57, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c689, c386] c1819 (by decide) p (sat_cons (step689 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1820 : List Lit := [(49, true), (61, false), (62, true), (64, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c690, c422] c1820 (by decide) p (sat_cons (step690 p h) (sat_cons (step422 p h) (sat_nil p)))
def c1821 : List Lit := [(61, false), (62, true), (64, true), (40, true)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c690, c423] c1821 (by decide) p (sat_cons (step690 p h) (sat_cons (step423 p h) (sat_nil p)))
def c1822 : List Lit := [(49, true), (61, false), (64, true), (40, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c690, c424] c1822 (by decide) p (sat_cons (step690 p h) (sat_cons (step424 p h) (sat_nil p)))
def c1823 : List Lit := [(49, true), (61, false), (62, true), (40, true)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c690, c425] c1823 (by decide) p (sat_cons (step690 p h) (sat_cons (step425 p h) (sat_nil p)))
def c1824 : List Lit := [(67, true), (66, true), (62, true), (63, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c691, c432] c1824 (by decide) p (sat_cons (step691 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1825 : List Lit := [(67, true), (66, true), (52, true), (63, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c691, c433] c1825 (by decide) p (sat_cons (step691 p h) (sat_cons (step433 p h) (sat_nil p)))
end B112E158
