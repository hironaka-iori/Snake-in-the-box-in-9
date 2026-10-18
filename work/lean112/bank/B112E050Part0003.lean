import B112E050Part0002
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2008 : List Lit := [(97, true), (1788, true), (54, false), (105, true)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c891, c1555, c1529, c1518, c1520, c1526, c1551, c1538, c1540, c1536, c1533, c634, c471, c607] c2008 (by decide) p (sat_cons (step891 p h) (sat_cons (step1555 p h) (sat_cons (step1529 p h) (sat_cons (step1518 p h) (sat_cons (step1520 p h) (sat_cons (step1526 p h) (sat_cons (step1551 p h) (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step1536 p h) (sat_cons (step1533 p h) (sat_cons (step634 p h) (sat_cons (step471 p h) (sat_cons (step607 p h) (sat_nil p)))))))))))))))
def c2009 : List Lit := [(1726, true), (1713, false), (1708, false), (72, false), (62, false)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1412, c1382, c1389, c1972] c2009 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1412 p h) (sat_cons (step1382 p h) (sat_cons (step1389 p h) (sat_cons (step1972 p h) (sat_nil p))))))
def c2010 : List Lit := [(1817, true), (1807, false), (113, true)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1608, c1920, c1599, c1584] c2010 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1608 p h) (sat_cons (step1920 p h) (sat_cons (step1599 p h) (sat_cons (step1584 p h) (sat_nil p))))))
def c2011 : List Lit := [(1580, false), (21, false), (1619, true), (1596, true)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c856, c1159, c1864, c1133, c1155, c1862, c1141, c1143, c1138, c1139, c1135, c1913, c70, c1188, c68, c28] c2011 (by decide) p (sat_cons (step856 p h) (sat_cons (step1159 p h) (sat_cons (step1864 p h) (sat_cons (step1133 p h) (sat_cons (step1155 p h) (sat_cons (step1862 p h) (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step1913 p h) (sat_cons (step70 p h) (sat_cons (step1188 p h) (sat_cons (step68 p h) (sat_cons (step28 p h) (sat_nil p)))))))))))))))))
def c2012 : List Lit := [(1595, true), (93, true)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c855, c1867, c1154, c1143, c1864, c1136, c1125, c1126, c44, c55] c2012 (by decide) p (sat_cons (step855 p h) (sat_cons (step1867 p h) (sat_cons (step1154 p h) (sat_cons (step1143 p h) (sat_cons (step1864 p h) (sat_cons (step1136 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step44 p h) (sat_cons (step55 p h) (sat_nil p)))))))))))
def c2013 : List Lit := [(16, false), (33, false), (25, false), (27, false)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c856, c70, c28, c68] c2013 (by decide) p (sat_cons (step856 p h) (sat_cons (step70 p h) (sat_cons (step28 p h) (sat_cons (step68 p h) (sat_nil p)))))
def c2014 : List Lit := [(3, false), (75, true), (38, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c846, c6] c2014 (by decide) p (sat_cons (step846 p h) (sat_cons (step6 p h) (sat_nil p)))
def c2015 : List Lit := [(3, false), (9, true), (75, true)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c846, c7] c2015 (by decide) p (sat_cons (step846 p h) (sat_cons (step7 p h) (sat_nil p)))
def c2016 : List Lit := [(4, true), (6, true), (5, false)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c847, c9] c2016 (by decide) p (sat_cons (step847 p h) (sat_cons (step9 p h) (sat_nil p)))
def c2017 : List Lit := [(2, true), (6, true), (5, false)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c847, c10] c2017 (by decide) p (sat_cons (step847 p h) (sat_cons (step10 p h) (sat_nil p)))
def c2018 : List Lit := [(2, true), (4, true), (5, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c847, c11] c2018 (by decide) p (sat_cons (step847 p h) (sat_cons (step11 p h) (sat_nil p)))
def c2019 : List Lit := [(9, true), (8, false), (81, true)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c848, c17] c2019 (by decide) p (sat_cons (step848 p h) (sat_cons (step17 p h) (sat_nil p)))
def c2020 : List Lit := [(8, false), (4, true), (81, true)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c848, c18] c2020 (by decide) p (sat_cons (step848 p h) (sat_cons (step18 p h) (sat_nil p)))
def c2021 : List Lit := [(9, true), (8, false), (4, true)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c848, c19] c2021 (by decide) p (sat_cons (step848 p h) (sat_cons (step19 p h) (sat_nil p)))
def c2022 : List Lit := [(9, false), (10, true), (3, true), (137, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c1821, c21] c2022 (by decide) p (sat_cons (step1821 p h) (sat_cons (step21 p h) (sat_nil p)))
def c2023 : List Lit := [(10, false), (48, true)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c849, c22] c2023 (by decide) p (sat_cons (step849 p h) (sat_cons (step22 p h) (sat_nil p)))
def c2024 : List Lit := [(142, true), (7, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c1822, c1823, c1820] c2024 (by decide) p (sat_cons (step1822 p h) (sat_cons (step1823 p h) (sat_cons (step1820 p h) (sat_nil p))))
def c2025 : List Lit := [(26, true), (20, true), (16, false)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c853, c33] c2025 (by decide) p (sat_cons (step853 p h) (sat_cons (step33 p h) (sat_nil p)))
def c2026 : List Lit := [(15, true), (26, true), (16, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c853, c34] c2026 (by decide) p (sat_cons (step853 p h) (sat_cons (step34 p h) (sat_nil p)))
def c2027 : List Lit := [(15, true), (20, true), (16, false)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c853, c35] c2027 (by decide) p (sat_cons (step853 p h) (sat_cons (step35 p h) (sat_nil p)))
def c2028 : List Lit := [(22, true), (89, true), (18, false)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c854, c40] c2028 (by decide) p (sat_cons (step854 p h) (sat_cons (step40 p h) (sat_nil p)))
def c2029 : List Lit := [(17, true), (89, true), (18, false)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c854, c41] c2029 (by decide) p (sat_cons (step854 p h) (sat_cons (step41 p h) (sat_nil p)))
def c2030 : List Lit := [(17, true), (22, true), (18, false)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c854, c42] c2030 (by decide) p (sat_cons (step854 p h) (sat_cons (step42 p h) (sat_nil p)))
def c2031 : List Lit := [(22, true), (93, true), (19, false)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c855, c44] c2031 (by decide) p (sat_cons (step855 p h) (sat_cons (step44 p h) (sat_nil p)))
def c2032 : List Lit := [(20, true), (93, true), (19, false)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c855, c45] c2032 (by decide) p (sat_cons (step855 p h) (sat_cons (step45 p h) (sat_nil p)))
def c2033 : List Lit := [(20, true), (22, true), (19, false)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c855, c46] c2033 (by decide) p (sat_cons (step855 p h) (sat_cons (step46 p h) (sat_nil p)))
def c2034 : List Lit := [(24, true), (26, true), (25, false)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c856, c67] c2034 (by decide) p (sat_cons (step856 p h) (sat_cons (step67 p h) (sat_nil p)))
def c2035 : List Lit := [(15, true), (26, true), (25, false)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c856, c68] c2035 (by decide) p (sat_cons (step856 p h) (sat_cons (step68 p h) (sat_nil p)))
def c2036 : List Lit := [(24, true), (15, true), (25, false)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c856, c69] c2036 (by decide) p (sat_cons (step856 p h) (sat_cons (step69 p h) (sat_nil p)))
def c2037 : List Lit := [(31, true), (102, true), (44, true), (27, false)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c857, c75] c2037 (by decide) p (sat_cons (step857 p h) (sat_cons (step75 p h) (sat_nil p)))
def c2038 : List Lit := [(26, true), (102, true), (44, true), (27, false)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c857, c76] c2038 (by decide) p (sat_cons (step857 p h) (sat_cons (step76 p h) (sat_nil p)))
def c2039 : List Lit := [(26, true), (31, true), (102, true), (27, false)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c857, c77] c2039 (by decide) p (sat_cons (step857 p h) (sat_cons (step77 p h) (sat_nil p)))
def c2040 : List Lit := [(26, true), (31, true), (44, true), (27, false)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c857, c78] c2040 (by decide) p (sat_cons (step857 p h) (sat_cons (step78 p h) (sat_nil p)))
def c2041 : List Lit := [(28, false), (29, true)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c858, c79] c2041 (by decide) p (sat_cons (step858 p h) (sat_cons (step79 p h) (sat_nil p)))
def c2042 : List Lit := [(28, false), (24, true)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c858, c80] c2042 (by decide) p (sat_cons (step858 p h) (sat_cons (step80 p h) (sat_nil p)))
def c2043 : List Lit := [(30, false), (31, true), (107, true), (23, true)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c859, c85] c2043 (by decide) p (sat_cons (step859 p h) (sat_cons (step85 p h) (sat_nil p)))
def c2044 : List Lit := [(35, false), (114, true), (44, true)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c860, c106] c2044 (by decide) p (sat_cons (step860 p h) (sat_cons (step106 p h) (sat_nil p)))
def c2045 : List Lit := [(34, true), (35, false), (114, true)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c860, c107] c2045 (by decide) p (sat_cons (step860 p h) (sat_cons (step107 p h) (sat_nil p)))
def c2046 : List Lit := [(34, true), (35, false), (44, true)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c860, c108] c2046 (by decide) p (sat_cons (step860 p h) (sat_cons (step108 p h) (sat_nil p)))
def c2047 : List Lit := [(37, true), (36, false), (38, true)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c861, c109] c2047 (by decide) p (sat_cons (step861 p h) (sat_cons (step109 p h) (sat_nil p)))
def c2048 : List Lit := [(32, true), (36, false), (38, true)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c861, c110] c2048 (by decide) p (sat_cons (step861 p h) (sat_cons (step110 p h) (sat_nil p)))
def c2049 : List Lit := [(37, true), (32, true), (36, false)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c861, c111] c2049 (by decide) p (sat_cons (step861 p h) (sat_cons (step111 p h) (sat_nil p)))
def c2050 : List Lit := [(37, true), (34, true), (39, false), (118, true), (23, true)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c862, c125] c2050 (by decide) p (sat_cons (step862 p h) (sat_cons (step125 p h) (sat_nil p)))
def c2051 : List Lit := [(48, true), (41, true), (42, false), (44, true)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c863, c130] c2051 (by decide) p (sat_cons (step863 p h) (sat_cons (step130 p h) (sat_nil p)))
def c2052 : List Lit := [(40, true), (41, true), (44, true), (42, false)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c863, c131] c2052 (by decide) p (sat_cons (step863 p h) (sat_cons (step131 p h) (sat_nil p)))
def c2053 : List Lit := [(41, true), (43, false), (44, true)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c864, c132] c2053 (by decide) p (sat_cons (step864 p h) (sat_cons (step132 p h) (sat_nil p)))
def c2054 : List Lit := [(34, true), (43, false), (44, true)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c864, c133] c2054 (by decide) p (sat_cons (step864 p h) (sat_cons (step133 p h) (sat_nil p)))
def c2055 : List Lit := [(48, true), (45, false), (47, true)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c865, c156] c2055 (by decide) p (sat_cons (step865 p h) (sat_cons (step156 p h) (sat_nil p)))
def c2056 : List Lit := [(40, true), (45, false), (47, true)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c865, c157] c2056 (by decide) p (sat_cons (step865 p h) (sat_cons (step157 p h) (sat_nil p)))
def c2057 : List Lit := [(47, true), (46, false), (125, true)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c866, c159] c2057 (by decide) p (sat_cons (step866 p h) (sat_cons (step159 p h) (sat_nil p)))
def c2058 : List Lit := [(37, true), (46, false), (125, true)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c866, c160] c2058 (by decide) p (sat_cons (step866 p h) (sat_cons (step160 p h) (sat_nil p)))
def c2059 : List Lit := [(47, true), (37, true), (46, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c866, c161] c2059 (by decide) p (sat_cons (step866 p h) (sat_cons (step161 p h) (sat_nil p)))
def c2060 : List Lit := [(49, true), (55, true), (51, false), (61, true)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c867, c175] c2060 (by decide) p (sat_cons (step867 p h) (sat_cons (step175 p h) (sat_nil p)))
def c2061 : List Lit := [(50, true), (61, true), (51, false), (49, true)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c867, c176] c2061 (by decide) p (sat_cons (step867 p h) (sat_cons (step176 p h) (sat_nil p)))
def c2062 : List Lit := [(50, true), (49, true), (55, true), (51, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c867, c177] c2062 (by decide) p (sat_cons (step867 p h) (sat_cons (step177 p h) (sat_nil p)))
def c2063 : List Lit := [(52, true), (70, true), (53, false), (57, true), (89, true)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c868, c181] c2063 (by decide) p (sat_cons (step868 p h) (sat_cons (step181 p h) (sat_nil p)))
def c2064 : List Lit := [(70, true), (89, true), (53, false), (49, true), (57, true)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c868, c182] c2064 (by decide) p (sat_cons (step868 p h) (sat_cons (step182 p h) (sat_nil p)))
def c2065 : List Lit := [(89, true), (52, true), (53, false), (70, true), (49, true)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c868, c183] c2065 (by decide) p (sat_cons (step868 p h) (sat_cons (step183 p h) (sat_nil p)))
def c2066 : List Lit := [(89, true), (52, true), (53, false), (57, true), (49, true)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c868, c184] c2066 (by decide) p (sat_cons (step868 p h) (sat_cons (step184 p h) (sat_nil p)))
def c2067 : List Lit := [(49, true), (52, true), (53, false), (57, true), (70, true)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c868, c185] c2067 (by decide) p (sat_cons (step868 p h) (sat_cons (step185 p h) (sat_nil p)))
def c2068 : List Lit := [(55, true), (57, true), (54, false), (93, true)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c869, c187] c2068 (by decide) p (sat_cons (step869 p h) (sat_cons (step187 p h) (sat_nil p)))
def c2069 : List Lit := [(49, true), (57, true), (54, false), (93, true)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c869, c188] c2069 (by decide) p (sat_cons (step869 p h) (sat_cons (step188 p h) (sat_nil p)))
def c2070 : List Lit := [(55, true), (49, true), (54, false), (93, true)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c869, c189] c2070 (by decide) p (sat_cons (step869 p h) (sat_cons (step189 p h) (sat_nil p)))
def c2071 : List Lit := [(55, true), (49, true), (54, false), (57, true)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c869, c190] c2071 (by decide) p (sat_cons (step869 p h) (sat_cons (step190 p h) (sat_nil p)))
end B112E050
