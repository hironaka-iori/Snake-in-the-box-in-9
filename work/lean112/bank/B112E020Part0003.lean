import B112E020Part0002
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1804 : List Lit := [(12, false), (11, true)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c774, c47] c1804 (by decide) p (sat_cons (step774 p h) (sat_cons (step47 p h) (sat_nil p)))
def c1805 : List Lit := [(12, false), (10, true)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c774, c48] c1805 (by decide) p (sat_cons (step774 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1806 : List Lit := [(17, true), (16, false), (26, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c776, c59] c1806 (by decide) p (sat_cons (step776 p h) (sat_cons (step59 p h) (sat_nil p)))
def c1807 : List Lit := [(14, true), (16, false), (26, true)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c776, c60] c1807 (by decide) p (sat_cons (step776 p h) (sat_cons (step60 p h) (sat_nil p)))
def c1808 : List Lit := [(17, true), (14, true), (16, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c776, c61] c1808 (by decide) p (sat_cons (step776 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1809 : List Lit := [(18, false), (23, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c777, c68] c1809 (by decide) p (sat_cons (step777 p h) (sat_cons (step68 p h) (sat_nil p)))
def c1810 : List Lit := [(18, false), (17, true)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c777, c69] c1810 (by decide) p (sat_cons (step777 p h) (sat_cons (step69 p h) (sat_nil p)))
def c1811 : List Lit := [(23, true), (21, false), (20, true)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c778, c88] c1811 (by decide) p (sat_cons (step778 p h) (sat_cons (step88 p h) (sat_nil p)))
def c1812 : List Lit := [(19, true), (23, true), (21, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c778, c89] c1812 (by decide) p (sat_cons (step778 p h) (sat_cons (step89 p h) (sat_nil p)))
def c1813 : List Lit := [(19, true), (21, false), (20, true)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c778, c90] c1813 (by decide) p (sat_cons (step778 p h) (sat_cons (step90 p h) (sat_nil p)))
def c1814 : List Lit := [(25, true), (26, true), (24, false), (28, true)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c779, c112] c1814 (by decide) p (sat_cons (step779 p h) (sat_cons (step112 p h) (sat_nil p)))
def c1815 : List Lit := [(14, true), (26, true), (24, false), (28, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c779, c113] c1815 (by decide) p (sat_cons (step779 p h) (sat_cons (step113 p h) (sat_nil p)))
def c1816 : List Lit := [(14, true), (25, true), (24, false), (28, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c779, c114] c1816 (by decide) p (sat_cons (step779 p h) (sat_cons (step114 p h) (sat_nil p)))
def c1817 : List Lit := [(25, true), (27, false), (62, true), (26, true), (79, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c780, c155] c1817 (by decide) p (sat_cons (step780 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1818 : List Lit := [(19, true), (25, true), (29, false), (67, true)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c781, c164] c1818 (by decide) p (sat_cons (step781 p h) (sat_cons (step164 p h) (sat_nil p)))
def c1819 : List Lit := [(25, true), (10, true), (29, false), (67, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c781, c165] c1819 (by decide) p (sat_cons (step781 p h) (sat_cons (step165 p h) (sat_nil p)))
def c1820 : List Lit := [(10, true), (19, true), (67, true), (29, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c781, c166] c1820 (by decide) p (sat_cons (step781 p h) (sat_cons (step166 p h) (sat_nil p)))
def c1821 : List Lit := [(25, true), (10, true), (29, false), (19, true)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c781, c167] c1821 (by decide) p (sat_cons (step781 p h) (sat_cons (step167 p h) (sat_nil p)))
def c1822 : List Lit := [(26, true), (82, true), (30, false), (32, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c782, c171] c1822 (by decide) p (sat_cons (step782 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1823 : List Lit := [(11, true), (82, true), (32, true), (30, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c782, c172] c1823 (by decide) p (sat_cons (step782 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1824 : List Lit := [(26, true), (11, true), (30, false), (82, true)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c782, c173] c1824 (by decide) p (sat_cons (step782 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1825 : List Lit := [(11, true), (26, true), (32, true), (30, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c782, c174] c1825 (by decide) p (sat_cons (step782 p h) (sat_cons (step174 p h) (sat_nil p)))
def c1826 : List Lit := [(32, true), (28, true), (31, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c783, c176] c1826 (by decide) p (sat_cons (step783 p h) (sat_cons (step176 p h) (sat_nil p)))
def c1827 : List Lit := [(32, true), (31, false), (20, true)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c783, c177] c1827 (by decide) p (sat_cons (step783 p h) (sat_cons (step177 p h) (sat_nil p)))
def c1828 : List Lit := [(28, true), (31, false), (20, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c783, c178] c1828 (by decide) p (sat_cons (step783 p h) (sat_cons (step178 p h) (sat_nil p)))
def c1829 : List Lit := [(36, true), (33, true), (34, false), (43, true), (86, true)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c784, c184] c1829 (by decide) p (sat_cons (step784 p h) (sat_cons (step184 p h) (sat_nil p)))
def c1830 : List Lit := [(36, true), (33, true), (34, false), (43, true), (51, true)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c784, c185] c1830 (by decide) p (sat_cons (step784 p h) (sat_cons (step185 p h) (sat_nil p)))
def c1831 : List Lit := [(35, false), (36, true)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c785, c186] c1831 (by decide) p (sat_cons (step785 p h) (sat_cons (step186 p h) (sat_nil p)))
def c1832 : List Lit := [(35, false), (33, true)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c785, c187] c1832 (by decide) p (sat_cons (step785 p h) (sat_cons (step187 p h) (sat_nil p)))
def c1833 : List Lit := [(89, true), (37, false), (36, true)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c786, c193] c1833 (by decide) p (sat_cons (step786 p h) (sat_cons (step193 p h) (sat_nil p)))
def c1834 : List Lit := [(57, true), (36, true), (38, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c787, c196] c1834 (by decide) p (sat_cons (step787 p h) (sat_cons (step196 p h) (sat_nil p)))
def c1835 : List Lit := [(40, false), (41, true)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c788, c199] c1835 (by decide) p (sat_cons (step788 p h) (sat_cons (step199 p h) (sat_nil p)))
def c1836 : List Lit := [(40, false), (39, true)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c788, c200] c1836 (by decide) p (sat_cons (step788 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1837 : List Lit := [(44, true), (42, false), (43, true), (46, true)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c789, c206] c1837 (by decide) p (sat_cons (step789 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1838 : List Lit := [(64, true), (50, true), (45, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c790, c229] c1838 (by decide) p (sat_cons (step790 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1839 : List Lit := [(64, true), (44, true), (45, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c790, c230] c1839 (by decide) p (sat_cons (step790 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1840 : List Lit := [(50, true), (44, true), (45, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c790, c231] c1840 (by decide) p (sat_cons (step790 p h) (sat_cons (step231 p h) (sat_nil p)))
def c1841 : List Lit := [(47, false), (46, true), (67, true), (43, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c791, c246] c1841 (by decide) p (sat_cons (step791 p h) (sat_cons (step246 p h) (sat_nil p)))
def c1842 : List Lit := [(10, true), (47, false), (46, true), (67, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c791, c247] c1842 (by decide) p (sat_cons (step791 p h) (sat_cons (step247 p h) (sat_nil p)))
def c1843 : List Lit := [(10, true), (47, false), (67, true), (43, true)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c791, c248] c1843 (by decide) p (sat_cons (step791 p h) (sat_cons (step248 p h) (sat_nil p)))
def c1844 : List Lit := [(10, true), (46, true), (43, true), (47, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c791, c249] c1844 (by decide) p (sat_cons (step791 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1845 : List Lit := [(98, true), (50, true), (48, false), (46, true)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c792, c251] c1845 (by decide) p (sat_cons (step792 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1846 : List Lit := [(11, true), (98, true), (46, true), (48, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c792, c252] c1846 (by decide) p (sat_cons (step792 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1847 : List Lit := [(11, true), (50, true), (48, false), (46, true)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c792, c253] c1847 (by decide) p (sat_cons (step792 p h) (sat_cons (step253 p h) (sat_nil p)))
def c1848 : List Lit := [(50, true), (44, true), (49, false), (46, true)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c793, c258] c1848 (by decide) p (sat_cons (step793 p h) (sat_cons (step258 p h) (sat_nil p)))
def c1849 : List Lit := [(50, true), (39, true), (46, true), (49, false)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c793, c259] c1849 (by decide) p (sat_cons (step793 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1850 : List Lit := [(39, true), (44, true), (49, false), (50, true)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c793, c260] c1850 (by decide) p (sat_cons (step793 p h) (sat_cons (step260 p h) (sat_nil p)))
def c1851 : List Lit := [(39, true), (44, true), (49, false), (46, true)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c793, c261] c1851 (by decide) p (sat_cons (step793 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1852 : List Lit := [(52, true), (63, true), (53, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c794, c274] c1852 (by decide) p (sat_cons (step794 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1853 : List Lit := [(63, true), (53, false), (51, true)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c794, c275] c1853 (by decide) p (sat_cons (step794 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1854 : List Lit := [(52, true), (53, false), (51, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c794, c276] c1854 (by decide) p (sat_cons (step794 p h) (sat_cons (step276 p h) (sat_nil p)))
def c1855 : List Lit := [(59, true), (64, true), (54, false)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c795, c278] c1855 (by decide) p (sat_cons (step795 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1856 : List Lit := [(52, true), (64, true), (54, false)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c795, c279] c1856 (by decide) p (sat_cons (step795 p h) (sat_cons (step279 p h) (sat_nil p)))
def c1857 : List Lit := [(52, true), (59, true), (54, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c795, c280] c1857 (by decide) p (sat_cons (step795 p h) (sat_cons (step280 p h) (sat_nil p)))
def c1858 : List Lit := [(56, false), (59, true), (57, true)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c796, c288] c1858 (by decide) p (sat_cons (step796 p h) (sat_cons (step288 p h) (sat_nil p)))
def c1859 : List Lit := [(56, false), (55, true), (59, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c796, c289] c1859 (by decide) p (sat_cons (step796 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1860 : List Lit := [(56, false), (55, true), (57, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c796, c290] c1860 (by decide) p (sat_cons (step796 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1861 : List Lit := [(63, true), (62, true), (114, true), (43, true), (51, true), (67, true), (60, false)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c797, c332] c1861 (by decide) p (sat_cons (step797 p h) (sat_cons (step332 p h) (sat_nil p)))
def c1862 : List Lit := [(25, true), (114, true), (62, true), (43, true), (51, true), (67, true), (60, false)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c797, c333] c1862 (by decide) p (sat_cons (step797 p h) (sat_cons (step333 p h) (sat_nil p)))
def c1863 : List Lit := [(115, true), (61, false), (62, true), (64, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c798, c337] c1863 (by decide) p (sat_cons (step798 p h) (sat_cons (step337 p h) (sat_nil p)))
def c1864 : List Lit := [(115, true), (26, true), (64, true), (61, false)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c798, c338] c1864 (by decide) p (sat_cons (step798 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1865 : List Lit := [(115, true), (26, true), (61, false), (62, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c798, c339] c1865 (by decide) p (sat_cons (step798 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1866 : List Lit := [(26, true), (62, true), (61, false), (64, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c798, c340] c1866 (by decide) p (sat_cons (step798 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1867 : List Lit := [(63, true), (70, true), (65, false), (64, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c799, c379] c1867 (by decide) p (sat_cons (step799 p h) (sat_cons (step379 p h) (sat_nil p)))
end B112E020
