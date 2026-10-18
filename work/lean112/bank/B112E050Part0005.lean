import B112E050Part0004
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2136 : List Lit := [(90, true), (99, true), (101, false), (102, true)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c890, c562] c2136 (by decide) p (sat_cons (step890 p h) (sat_cons (step562 p h) (sat_nil p)))
def c2137 : List Lit := [(98, true), (106, true), (103, false), (105, true)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c891, c606] c2137 (by decide) p (sat_cons (step891 p h) (sat_cons (step606 p h) (sat_nil p)))
def c2138 : List Lit := [(106, true), (105, true), (93, true), (103, false)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c891, c607] c2138 (by decide) p (sat_cons (step891 p h) (sat_cons (step607 p h) (sat_nil p)))
def c2139 : List Lit := [(98, true), (106, true), (103, false), (93, true)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c891, c608] c2139 (by decide) p (sat_cons (step891 p h) (sat_cons (step608 p h) (sat_nil p)))
def c2140 : List Lit := [(98, true), (105, true), (103, false), (93, true)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c891, c609] c2140 (by decide) p (sat_cons (step891 p h) (sat_cons (step609 p h) (sat_nil p)))
def c2141 : List Lit := [(125, true), (105, true), (104, false), (107, true)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c892, c611] c2141 (by decide) p (sat_cons (step892 p h) (sat_cons (step611 p h) (sat_nil p)))
def c2142 : List Lit := [(94, true), (125, true), (104, false), (107, true)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c892, c612] c2142 (by decide) p (sat_cons (step892 p h) (sat_cons (step612 p h) (sat_nil p)))
def c2143 : List Lit := [(94, true), (125, true), (104, false), (105, true)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c892, c613] c2143 (by decide) p (sat_cons (step892 p h) (sat_cons (step613 p h) (sat_nil p)))
def c2144 : List Lit := [(94, true), (105, true), (104, false), (107, true)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c892, c614] c2144 (by decide) p (sat_cons (step892 p h) (sat_cons (step614 p h) (sat_nil p)))
def c2145 : List Lit := [(107, true), (102, true), (108, false), (105, true), (67, true), (106, true)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c893, c690] c2145 (by decide) p (sat_cons (step893 p h) (sat_cons (step690 p h) (sat_nil p)))
def c2146 : List Lit := [(31, true), (107, true), (105, true), (108, false), (106, true), (102, true)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c893, c691] c2146 (by decide) p (sat_cons (step893 p h) (sat_cons (step691 p h) (sat_nil p)))
def c2147 : List Lit := [(31, true), (107, true), (105, true), (108, false), (67, true), (106, true)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c893, c692] c2147 (by decide) p (sat_cons (step893 p h) (sat_cons (step692 p h) (sat_nil p)))
def c2148 : List Lit := [(31, true), (107, true), (67, true), (106, true), (102, true), (108, false)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c893, c693] c2148 (by decide) p (sat_cons (step893 p h) (sat_cons (step693 p h) (sat_nil p)))
def c2149 : List Lit := [(86, true), (110, true), (120, true), (109, false), (112, true)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c894, c695] c2149 (by decide) p (sat_cons (step894 p h) (sat_cons (step695 p h) (sat_nil p)))
def c2150 : List Lit := [(32, true), (86, true), (120, true), (110, true), (109, false)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c894, c696] c2150 (by decide) p (sat_cons (step894 p h) (sat_cons (step696 p h) (sat_nil p)))
def c2151 : List Lit := [(86, true), (32, true), (110, true), (112, true), (109, false)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c894, c697] c2151 (by decide) p (sat_cons (step894 p h) (sat_cons (step697 p h) (sat_nil p)))
def c2152 : List Lit := [(122, true), (116, true), (111, false), (114, true)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c895, c707] c2152 (by decide) p (sat_cons (step895 p h) (sat_cons (step707 p h) (sat_nil p)))
def c2153 : List Lit := [(110, true), (122, true), (111, false), (114, true)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c895, c708] c2153 (by decide) p (sat_cons (step895 p h) (sat_cons (step708 p h) (sat_nil p)))
def c2154 : List Lit := [(116, true), (110, true), (111, false), (114, true)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c895, c709] c2154 (by decide) p (sat_cons (step895 p h) (sat_cons (step709 p h) (sat_nil p)))
def c2155 : List Lit := [(110, true), (112, true), (113, false), (89, true), (114, true), (117, true)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c896, c718] c2155 (by decide) p (sat_cons (step896 p h) (sat_cons (step718 p h) (sat_nil p)))
def c2156 : List Lit := [(112, true), (110, true), (113, false), (70, true), (114, true), (117, true)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c896, c719] c2156 (by decide) p (sat_cons (step896 p h) (sat_cons (step719 p h) (sat_nil p)))
def c2157 : List Lit := [(110, true), (70, true), (114, true), (89, true), (113, false), (117, true)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c896, c720] c2157 (by decide) p (sat_cons (step896 p h) (sat_cons (step720 p h) (sat_nil p)))
def c2158 : List Lit := [(112, true), (70, true), (110, true), (89, true), (113, false), (114, true)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c896, c721] c2158 (by decide) p (sat_cons (step896 p h) (sat_cons (step721 p h) (sat_nil p)))
def c2159 : List Lit := [(116, true), (110, true), (115, false), (117, true)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c897, c759] c2159 (by decide) p (sat_cons (step897 p h) (sat_cons (step759 p h) (sat_nil p)))
def c2160 : List Lit := [(116, true), (117, true), (115, false), (93, true)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c897, c760] c2160 (by decide) p (sat_cons (step897 p h) (sat_cons (step760 p h) (sat_nil p)))
def c2161 : List Lit := [(110, true), (117, true), (115, false), (93, true)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c897, c761] c2161 (by decide) p (sat_cons (step897 p h) (sat_cons (step761 p h) (sat_nil p)))
def c2162 : List Lit := [(116, true), (110, true), (93, true), (115, false)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c897, c762] c2162 (by decide) p (sat_cons (step897 p h) (sat_cons (step762 p h) (sat_nil p)))
def c2163 : List Lit := [(118, true), (114, true), (119, false), (117, true)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c898, c787] c2163 (by decide) p (sat_cons (step898 p h) (sat_cons (step787 p h) (sat_nil p)))
def c2164 : List Lit := [(118, true), (116, true), (119, false), (114, true)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c898, c788] c2164 (by decide) p (sat_cons (step898 p h) (sat_cons (step788 p h) (sat_nil p)))
def c2165 : List Lit := [(116, true), (114, true), (119, false), (117, true)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c898, c789] c2165 (by decide) p (sat_cons (step898 p h) (sat_cons (step789 p h) (sat_nil p)))
def c2166 : List Lit := [(122, true), (125, true), (121, false)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c899, c793] c2166 (by decide) p (sat_cons (step899 p h) (sat_cons (step793 p h) (sat_nil p)))
def c2167 : List Lit := [(120, true), (125, true), (121, false)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c899, c794] c2167 (by decide) p (sat_cons (step899 p h) (sat_cons (step794 p h) (sat_nil p)))
def c2168 : List Lit := [(122, true), (120, true), (121, false)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c899, c795] c2168 (by decide) p (sat_cons (step899 p h) (sat_cons (step795 p h) (sat_nil p)))
def c2169 : List Lit := [(122, true), (123, false), (102, true), (44, true), (80, true)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c900, c807] c2169 (by decide) p (sat_cons (step900 p h) (sat_cons (step807 p h) (sat_nil p)))
def c2170 : List Lit := [(102, true), (123, false), (80, true), (44, true), (114, true)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c900, c808] c2170 (by decide) p (sat_cons (step900 p h) (sat_cons (step808 p h) (sat_nil p)))
def c2171 : List Lit := [(126, true), (125, true), (81, true), (124, false)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c901, c812] c2171 (by decide) p (sat_cons (step901 p h) (sat_cons (step812 p h) (sat_nil p)))
def c2172 : List Lit := [(120, true), (81, true), (124, false), (126, true)]
theorem step2172 (p : Nat → Bool) (h : Constraints p) : clause p c2172 = true :=
  Snake9.LocalRup.prove_clause [c901, c813] c2172 (by decide) p (sat_cons (step901 p h) (sat_cons (step813 p h) (sat_nil p)))
def c2173 : List Lit := [(117, true), (127, false), (126, true), (106, true)]
theorem step2173 (p : Nat → Bool) (h : Constraints p) : clause p c2173 = true :=
  Snake9.LocalRup.prove_clause [c902, c837] c2173 (by decide) p (sat_cons (step902 p h) (sat_cons (step837 p h) (sat_nil p)))
def c2174 : List Lit := [(48, true), (117, true), (127, false), (126, true)]
theorem step2174 (p : Nat → Bool) (h : Constraints p) : clause p c2174 = true :=
  Snake9.LocalRup.prove_clause [c902, c838] c2174 (by decide) p (sat_cons (step902 p h) (sat_cons (step838 p h) (sat_nil p)))
def c2175 : List Lit := [(48, true), (117, true), (106, true), (127, false)]
theorem step2175 (p : Nat → Bool) (h : Constraints p) : clause p c2175 = true :=
  Snake9.LocalRup.prove_clause [c902, c839] c2175 (by decide) p (sat_cons (step902 p h) (sat_cons (step839 p h) (sat_nil p)))
def c2176 : List Lit := [(126, true), (125, true), (128, false), (118, true)]
theorem step2176 (p : Nat → Bool) (h : Constraints p) : clause p c2176 = true :=
  Snake9.LocalRup.prove_clause [c903, c842] c2176 (by decide) p (sat_cons (step903 p h) (sat_cons (step842 p h) (sat_nil p)))
def c2177 : List Lit := [(126, true), (125, true), (128, false), (107, true)]
theorem step2177 (p : Nat → Bool) (h : Constraints p) : clause p c2177 = true :=
  Snake9.LocalRup.prove_clause [c903, c843] c2177 (by decide) p (sat_cons (step903 p h) (sat_cons (step843 p h) (sat_nil p)))
def c2178 : List Lit := [(118, true), (126, true), (128, false), (107, true)]
theorem step2178 (p : Nat → Bool) (h : Constraints p) : clause p c2178 = true :=
  Snake9.LocalRup.prove_clause [c903, c844] c2178 (by decide) p (sat_cons (step903 p h) (sat_cons (step844 p h) (sat_nil p)))
def c2179 : List Lit := [(125, true), (118, true), (107, true), (128, false)]
theorem step2179 (p : Nat → Bool) (h : Constraints p) : clause p c2179 = true :=
  Snake9.LocalRup.prove_clause [c903, c845] c2179 (by decide) p (sat_cons (step903 p h) (sat_cons (step845 p h) (sat_nil p)))
def c2180 : List Lit := [(273, false), (279, false)]
theorem step2180 (p : Nat → Bool) (h : Constraints p) : clause p c2180 = true :=
  Snake9.LocalRup.prove_clause [c1846, c918] c2180 (by decide) p (sat_cons (step1846 p h) (sat_cons (step918 p h) (sat_nil p)))
def c2181 : List Lit := [(267, false), (281, false)]
theorem step2181 (p : Nat → Bool) (h : Constraints p) : clause p c2181 = true :=
  Snake9.LocalRup.prove_clause [c1837, c922] c2181 (by decide) p (sat_cons (step1837 p h) (sat_cons (step922 p h) (sat_nil p)))
def c2182 : List Lit := [(285, false), (287, false)]
theorem step2182 (p : Nat → Bool) (h : Constraints p) : clause p c2182 = true :=
  Snake9.LocalRup.prove_clause [c1851, c927] c2182 (by decide) p (sat_cons (step1851 p h) (sat_cons (step927 p h) (sat_nil p)))
def c2183 : List Lit := [(289, false), (295, false)]
theorem step2183 (p : Nat → Bool) (h : Constraints p) : clause p c2183 = true :=
  Snake9.LocalRup.prove_clause [c1845, c935] c2183 (by decide) p (sat_cons (step1845 p h) (sat_cons (step935 p h) (sat_nil p)))
def c2184 : List Lit := [(159, false), (160, false)]
theorem step2184 (p : Nat → Bool) (h : Constraints p) : clause p c2184 = true :=
  Snake9.LocalRup.prove_clause [c1852, c942] c2184 (by decide) p (sat_cons (step1852 p h) (sat_cons (step942 p h) (sat_nil p)))
def c2185 : List Lit := [(297, false), (311, false)]
theorem step2185 (p : Nat → Bool) (h : Constraints p) : clause p c2185 = true :=
  Snake9.LocalRup.prove_clause [c1836, c952] c2185 (by decide) p (sat_cons (step1836 p h) (sat_cons (step952 p h) (sat_nil p)))
def c2186 : List Lit := [(283, false), (313, false)]
theorem step2186 (p : Nat → Bool) (h : Constraints p) : clause p c2186 = true :=
  Snake9.LocalRup.prove_clause [c1829, c957] c2186 (by decide) p (sat_cons (step1829 p h) (sat_cons (step957 p h) (sat_nil p)))
def c2187 : List Lit := [(335, false), (341, false)]
theorem step2187 (p : Nat → Bool) (h : Constraints p) : clause p c2187 = true :=
  Snake9.LocalRup.prove_clause [c1843, c973] c2187 (by decide) p (sat_cons (step1843 p h) (sat_cons (step973 p h) (sat_nil p)))
def c2188 : List Lit := [(351, false), (357, false)]
theorem step2188 (p : Nat → Bool) (h : Constraints p) : clause p c2188 = true :=
  Snake9.LocalRup.prove_clause [c1842, c983] c2188 (by decide) p (sat_cons (step1842 p h) (sat_cons (step983 p h) (sat_nil p)))
def c2189 : List Lit := [(361, false), (363, false)]
theorem step2189 (p : Nat → Bool) (h : Constraints p) : clause p c2189 = true :=
  Snake9.LocalRup.prove_clause [c1849, c989] c2189 (by decide) p (sat_cons (step1849 p h) (sat_cons (step989 p h) (sat_nil p)))
def c2190 : List Lit := [(359, false), (373, false)]
theorem step2190 (p : Nat → Bool) (h : Constraints p) : clause p c2190 = true :=
  Snake9.LocalRup.prove_clause [c1834, c998] c2190 (by decide) p (sat_cons (step1834 p h) (sat_cons (step998 p h) (sat_nil p)))
def c2191 : List Lit := [(345, false), (375, false)]
theorem step2191 (p : Nat → Bool) (h : Constraints p) : clause p c2191 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1003] c2191 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1003 p h) (sat_nil p)))
def c2192 : List Lit := [(315, false), (377, false)]
theorem step2192 (p : Nat → Bool) (h : Constraints p) : clause p c2192 = true :=
  Snake9.LocalRup.prove_clause [c1825, c1008] c2192 (by decide) p (sat_cons (step1825 p h) (sat_cons (step1008 p h) (sat_nil p)))
def c2193 : List Lit := [(395, false), (397, false)]
theorem step2193 (p : Nat → Bool) (h : Constraints p) : clause p c2193 = true :=
  Snake9.LocalRup.prove_clause [c1848, c1020] c2193 (by decide) p (sat_cons (step1848 p h) (sat_cons (step1020 p h) (sat_nil p)))
def c2194 : List Lit := [(429, false), (435, false)]
theorem step2194 (p : Nat → Bool) (h : Constraints p) : clause p c2194 = true :=
  Snake9.LocalRup.prove_clause [c1839, c1041] c2194 (by decide) p (sat_cons (step1839 p h) (sat_cons (step1041 p h) (sat_nil p)))
def c2195 : List Lit := [(443, false), (445, false)]
theorem step2195 (p : Nat → Bool) (h : Constraints p) : clause p c2195 = true :=
  Snake9.LocalRup.prove_clause [c1847, c1053] c2195 (by decide) p (sat_cons (step1847 p h) (sat_cons (step1053 p h) (sat_nil p)))
def c2196 : List Lit := [(455, false), (469, false)]
theorem step2196 (p : Nat → Bool) (h : Constraints p) : clause p c2196 = true :=
  Snake9.LocalRup.prove_clause [c1831, c1067] c2196 (by decide) p (sat_cons (step1831 p h) (sat_cons (step1067 p h) (sat_nil p)))
def c2197 : List Lit := [(485, false), (499, false)]
theorem step2197 (p : Nat → Bool) (h : Constraints p) : clause p c2197 = true :=
  Snake9.LocalRup.prove_clause [c1830, c1083] c2197 (by decide) p (sat_cons (step1830 p h) (sat_cons (step1083 p h) (sat_nil p)))
def c2198 : List Lit := [(471, false), (501, false)]
theorem step2198 (p : Nat → Bool) (h : Constraints p) : clause p c2198 = true :=
  Snake9.LocalRup.prove_clause [c1826, c1087] c2198 (by decide) p (sat_cons (step1826 p h) (sat_cons (step1087 p h) (sat_nil p)))
def c2199 : List Lit := [(441, false), (503, false)]
theorem step2199 (p : Nat → Bool) (h : Constraints p) : clause p c2199 = true :=
  Snake9.LocalRup.prove_clause [c1824, c1092] c2199 (by decide) p (sat_cons (step1824 p h) (sat_cons (step1092 p h) (sat_nil p)))
end B112E050
