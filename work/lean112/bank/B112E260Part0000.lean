import B112E260Inputs
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2103 : List Lit := [(85, false), (78, false), (87, false)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c592, c594] c2103 (by decide) p (sat_cons (step592 p h) (sat_cons (step594 p h) (sat_nil p)))
def c2104 : List Lit := [(86, false), (88, false), (97, false)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c592, c595] c2104 (by decide) p (sat_cons (step592 p h) (sat_cons (step595 p h) (sat_nil p)))
def c2105 : List Lit := [(108, false), (102, false), (121, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c592, c723] c2105 (by decide) p (sat_cons (step592 p h) (sat_cons (step723 p h) (sat_nil p)))
def c2106 : List Lit := [(18, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c824, c147] c2106 (by decide) p (sat_cons (step824 p h) (sat_cons (step147 p h) (sat_nil p)))
def c2107 : List Lit := [(502, false)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c1142, c1139] c2107 (by decide) p (sat_cons (step1142 p h) (sat_cons (step1139 p h) (sat_nil p)))
def c2108 : List Lit := [(378, false)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c1142, c1141] c2108 (by decide) p (sat_cons (step1142 p h) (sat_cons (step1141 p h) (sat_nil p)))
def c2109 : List Lit := [(500, false)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c2107, c1135] c2109 (by decide) p (sat_cons (step2107 p h) (sat_cons (step1135 p h) (sat_nil p)))
def c2110 : List Lit := [(438, false)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c2107, c1138] c2110 (by decide) p (sat_cons (step2107 p h) (sat_cons (step1138 p h) (sat_nil p)))
def c2111 : List Lit := [(376, false)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c2108, c1001] c2111 (by decide) p (sat_cons (step2108 p h) (sat_cons (step1001 p h) (sat_nil p)))
def c2112 : List Lit := [(314, false)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c2108, c1004] c2112 (by decide) p (sat_cons (step2108 p h) (sat_cons (step1004 p h) (sat_nil p)))
def c2113 : List Lit := [(498, false)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c2109, c1130] c2113 (by decide) p (sat_cons (step2109 p h) (sat_cons (step1130 p h) (sat_nil p)))
def c2114 : List Lit := [(468, false)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c2109, c1133] c2114 (by decide) p (sat_cons (step2109 p h) (sat_cons (step1133 p h) (sat_nil p)))
def c2115 : List Lit := [(436, false)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c2110, c1064] c2115 (by decide) p (sat_cons (step2110 p h) (sat_cons (step1064 p h) (sat_nil p)))
def c2116 : List Lit := [(406, false)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c2110, c1067] c2116 (by decide) p (sat_cons (step2110 p h) (sat_cons (step1067 p h) (sat_nil p)))
def c2117 : List Lit := [(374, false)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c2111, c996] c2117 (by decide) p (sat_cons (step2111 p h) (sat_cons (step996 p h) (sat_nil p)))
def c2118 : List Lit := [(344, false)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c2111, c999] c2118 (by decide) p (sat_cons (step2111 p h) (sat_cons (step999 p h) (sat_nil p)))
def c2119 : List Lit := [(312, false)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c2112, c942] c2119 (by decide) p (sat_cons (step2112 p h) (sat_cons (step942 p h) (sat_nil p)))
def c2120 : List Lit := [(282, false)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c2112, c945] c2120 (by decide) p (sat_cons (step2112 p h) (sat_cons (step945 p h) (sat_nil p)))
def c2121 : List Lit := [(496, false)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c2113, c1125] c2121 (by decide) p (sat_cons (step2113 p h) (sat_cons (step1125 p h) (sat_nil p)))
def c2122 : List Lit := [(482, false)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c2113, c1128] c2122 (by decide) p (sat_cons (step2113 p h) (sat_cons (step1128 p h) (sat_nil p)))
def c2123 : List Lit := [(466, false)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c2114, c1093] c2123 (by decide) p (sat_cons (step2114 p h) (sat_cons (step1093 p h) (sat_nil p)))
def c2124 : List Lit := [(452, false)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c2114, c1096] c2124 (by decide) p (sat_cons (step2114 p h) (sat_cons (step1096 p h) (sat_nil p)))
def c2125 : List Lit := [(434, false)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c2115, c1060] c2125 (by decide) p (sat_cons (step2115 p h) (sat_cons (step1060 p h) (sat_nil p)))
def c2126 : List Lit := [(404, false)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c2116, c1037] c2126 (by decide) p (sat_cons (step2116 p h) (sat_cons (step1037 p h) (sat_nil p)))
def c2127 : List Lit := [(390, false)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c2116, c1040] c2127 (by decide) p (sat_cons (step2116 p h) (sat_cons (step1040 p h) (sat_nil p)))
def c2128 : List Lit := [(358, false)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c2117, c994] c2128 (by decide) p (sat_cons (step2117 p h) (sat_cons (step994 p h) (sat_nil p)))
def c2129 : List Lit := [(342, false)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c2118, c971] c2129 (by decide) p (sat_cons (step2118 p h) (sat_cons (step971 p h) (sat_nil p)))
def c2130 : List Lit := [(328, false)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c2118, c974] c2130 (by decide) p (sat_cons (step2118 p h) (sat_cons (step974 p h) (sat_nil p)))
def c2131 : List Lit := [(310, false)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c2119, c937] c2131 (by decide) p (sat_cons (step2119 p h) (sat_cons (step937 p h) (sat_nil p)))
def c2132 : List Lit := [(296, false)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c2119, c940] c2132 (by decide) p (sat_cons (step2119 p h) (sat_cons (step940 p h) (sat_nil p)))
def c2133 : List Lit := [(280, false)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c2120, c909] c2133 (by decide) p (sat_cons (step2120 p h) (sat_cons (step909 p h) (sat_nil p)))
def c2134 : List Lit := [(266, false)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c2120, c912] c2134 (by decide) p (sat_cons (step2120 p h) (sat_cons (step912 p h) (sat_nil p)))
def c2135 : List Lit := [(494, false)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c2121, c1121] c2135 (by decide) p (sat_cons (step2121 p h) (sat_cons (step1121 p h) (sat_nil p)))
def c2136 : List Lit := [(474, false)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c2122, c1109] c2136 (by decide) p (sat_cons (step2122 p h) (sat_cons (step1109 p h) (sat_nil p)))
def c2137 : List Lit := [(464, false)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c2123, c1090] c2137 (by decide) p (sat_cons (step2123 p h) (sat_cons (step1090 p h) (sat_nil p)))
def c2138 : List Lit := [(426, false)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c2125, c1058] c2138 (by decide) p (sat_cons (step2125 p h) (sat_cons (step1058 p h) (sat_nil p)))
def c2139 : List Lit := [(396, false)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c2126, c1035] c2139 (by decide) p (sat_cons (step2126 p h) (sat_cons (step1035 p h) (sat_nil p)))
def c2140 : List Lit := [(388, false)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c2127, c1018] c2140 (by decide) p (sat_cons (step2127 p h) (sat_cons (step1018 p h) (sat_nil p)))
def c2141 : List Lit := [(382, false)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c2127, c1021] c2141 (by decide) p (sat_cons (step2127 p h) (sat_cons (step1021 p h) (sat_nil p)))
def c2142 : List Lit := [(350, false)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c2128, c983] c2142 (by decide) p (sat_cons (step2128 p h) (sat_cons (step983 p h) (sat_nil p)))
def c2143 : List Lit := [(340, false)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c2129, c967] c2143 (by decide) p (sat_cons (step2129 p h) (sat_cons (step967 p h) (sat_nil p)))
def c2144 : List Lit := [(320, false)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c2130, c956] c2144 (by decide) p (sat_cons (step2130 p h) (sat_cons (step956 p h) (sat_nil p)))
def c2145 : List Lit := [(308, false)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c2131, c932] c2145 (by decide) p (sat_cons (step2131 p h) (sat_cons (step932 p h) (sat_nil p)))
def c2146 : List Lit := [(302, false)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c2131, c935] c2146 (by decide) p (sat_cons (step2131 p h) (sat_cons (step935 p h) (sat_nil p)))
def c2147 : List Lit := [(278, false)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c2133, c905] c2147 (by decide) p (sat_cons (step2133 p h) (sat_cons (step905 p h) (sat_nil p)))
def c2148 : List Lit := [(264, false)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c2134, c893] c2148 (by decide) p (sat_cons (step2134 p h) (sat_cons (step893 p h) (sat_nil p)))
def c2149 : List Lit := [(258, false)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c2134, c896] c2149 (by decide) p (sat_cons (step2134 p h) (sat_cons (step896 p h) (sat_nil p)))
def c2150 : List Lit := [(492, false)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c2135, c1117] c2150 (by decide) p (sat_cons (step2135 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c2151 : List Lit := [(462, false)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c2137, c1086] c2151 (by decide) p (sat_cons (step2137 p h) (sat_cons (step1086 p h) (sat_nil p)))
def c2152 : List Lit := [(394, false)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c2139, c1027] c2152 (by decide) p (sat_cons (step2139 p h) (sat_cons (step1027 p h) (sat_nil p)))
def c2153 : List Lit := [(384, false)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c2140, c1016] c2153 (by decide) p (sat_cons (step2140 p h) (sat_cons (step1016 p h) (sat_nil p)))
def c2154 : List Lit := [(262, false)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c2148, c890] c2154 (by decide) p (sat_cons (step2148 p h) (sat_cons (step890 p h) (sat_nil p)))
def c2155 : List Lit := [(128, true), (129, true), (132, true), (133, true), (134, true), (137, true), (139, true), (142, true), (143, true), (147, true), (148, true), (151, true), (153, true), (155, true), (157, true), (159, true), (161, true), (163, true), (167, true), (169, true), (171, true), (173, true), (175, true), (176, true), (177, true), (178, true), (183, true), (187, true), (189, true), (191, true), (192, true), (194, true), (195, true), (196, true), (199, true), (200, true), (201, true), (203, true), (206, true), (208, true), (209, true), (212, true), (213, true), (216, true), (217, true), (223, true), (225, true), (227, true), (230, true), (232, true), (235, true), (237, true), (238, true), (240, true), (242, true), (244, true), (246, true), (249, true), (251, true), (253, true), (254, true)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.TreeRup.prove_clause [c816, c817, c818, c819, c820, c821, c822, c823, c824, c825, c826, c827, c828, c829, c830, c831, c832, c833, c834, c835, c836, c837, c838, c839, c840, c841, c842, c843, c844, c845, c846, c847, c848, c849, c850, c851, c852, c853, c854, c855, c856, c857, c858, c859, c860, c861, c862, c863, c864, c865, c866, c867, c868, c869, c870, c871, c872, c873, c874, c875, c876, c877, c878, c879, c880, c1143] c2155 (by decide) p (sat_cons (step816 p h) (sat_cons (step817 p h) (sat_cons (step818 p h) (sat_cons (step819 p h) (sat_cons (step820 p h) (sat_cons (step821 p h) (sat_cons (step822 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step825 p h) (sat_cons (step826 p h) (sat_cons (step827 p h) (sat_cons (step828 p h) (sat_cons (step829 p h) (sat_cons (step830 p h) (sat_cons (step831 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step834 p h) (sat_cons (step835 p h) (sat_cons (step836 p h) (sat_cons (step837 p h) (sat_cons (step838 p h) (sat_cons (step839 p h) (sat_cons (step840 p h) (sat_cons (step841 p h) (sat_cons (step842 p h) (sat_cons (step843 p h) (sat_cons (step844 p h) (sat_cons (step845 p h) (sat_cons (step846 p h) (sat_cons (step847 p h) (sat_cons (step848 p h) (sat_cons (step849 p h) (sat_cons (step850 p h) (sat_cons (step851 p h) (sat_cons (step852 p h) (sat_cons (step853 p h) (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step856 p h) (sat_cons (step857 p h) (sat_cons (step858 p h) (sat_cons (step859 p h) (sat_cons (step860 p h) (sat_cons (step861 p h) (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step864 p h) (sat_cons (step865 p h) (sat_cons (step866 p h) (sat_cons (step867 p h) (sat_cons (step868 p h) (sat_cons (step869 p h) (sat_cons (step870 p h) (sat_cons (step871 p h) (sat_cons (step872 p h) (sat_cons (step873 p h) (sat_cons (step874 p h) (sat_cons (step875 p h) (sat_cons (step876 p h) (sat_cons (step877 p h) (sat_cons (step878 p h) (sat_cons (step879 p h) (sat_cons (step880 p h) (sat_cons (step1143 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2156 : List Lit := [(1553, true)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c2106, c1793] c2156 (by decide) p (sat_cons (step2106 p h) (sat_cons (step1793 p h) (sat_nil p)))
def c2157 : List Lit := [(19, true), (1554, true)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c2106, c1794] c2157 (by decide) p (sat_cons (step2106 p h) (sat_cons (step1794 p h) (sat_nil p)))
def c2158 : List Lit := [(1557, true)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c2156, c1798] c2158 (by decide) p (sat_cons (step2156 p h) (sat_cons (step1798 p h) (sat_nil p)))
def c2159 : List Lit := [(1555, false), (1558, true)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c2156, c1799] c2159 (by decide) p (sat_cons (step2156 p h) (sat_cons (step1799 p h) (sat_nil p)))
def c2160 : List Lit := [(1556, false), (1559, true)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c2156, c1800] c2160 (by decide) p (sat_cons (step2156 p h) (sat_cons (step1800 p h) (sat_nil p)))
def c2161 : List Lit := [(1569, true)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c2158, c1817] c2161 (by decide) p (sat_cons (step2158 p h) (sat_cons (step1817 p h) (sat_nil p)))
def c2162 : List Lit := [(1565, false), (1570, true)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c2158, c1818] c2162 (by decide) p (sat_cons (step2158 p h) (sat_cons (step1818 p h) (sat_nil p)))
def c2163 : List Lit := [(1566, false), (1571, true)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c2158, c1819] c2163 (by decide) p (sat_cons (step2158 p h) (sat_cons (step1819 p h) (sat_nil p)))
def c2164 : List Lit := [(1567, false), (1572, true)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c2158, c1820] c2164 (by decide) p (sat_cons (step2158 p h) (sat_cons (step1820 p h) (sat_nil p)))
def c2165 : List Lit := [(1546, false), (1579, true)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c2161, c1834] c2165 (by decide) p (sat_cons (step2161 p h) (sat_cons (step1834 p h) (sat_nil p)))
def c2166 : List Lit := [(1547, false), (1580, true)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c2161, c1838] c2166 (by decide) p (sat_cons (step2161 p h) (sat_cons (step1838 p h) (sat_nil p)))
end B112E260
