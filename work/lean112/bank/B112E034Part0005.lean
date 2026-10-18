import B112E034Part0004
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2099 : List Lit := [(118, false), (116, true), (111, true)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c896, c741] c2099 (by decide) p (sat_cons (step896 p h) (sat_cons (step741 p h) (sat_nil p)))
def c2100 : List Lit := [(118, false), (115, true), (111, true)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c896, c742] c2100 (by decide) p (sat_cons (step896 p h) (sat_cons (step742 p h) (sat_nil p)))
def c2101 : List Lit := [(119, true), (123, true), (121, false), (128, true)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c897, c792] c2101 (by decide) p (sat_cons (step897 p h) (sat_cons (step792 p h) (sat_nil p)))
def c2102 : List Lit := [(123, true), (110, true), (128, true), (121, false)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c897, c793] c2102 (by decide) p (sat_cons (step897 p h) (sat_cons (step793 p h) (sat_nil p)))
def c2103 : List Lit := [(119, true), (110, true), (128, true), (121, false)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c897, c794] c2103 (by decide) p (sat_cons (step897 p h) (sat_cons (step794 p h) (sat_nil p)))
def c2104 : List Lit := [(123, true), (119, true), (110, true), (121, false)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c897, c795] c2104 (by decide) p (sat_cons (step897 p h) (sat_cons (step795 p h) (sat_nil p)))
def c2105 : List Lit := [(123, true), (111, true), (122, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c898, c797] c2105 (by decide) p (sat_cons (step898 p h) (sat_cons (step797 p h) (sat_nil p)))
def c2106 : List Lit := [(123, true), (45, true), (122, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c898, c798] c2106 (by decide) p (sat_cons (step898 p h) (sat_cons (step798 p h) (sat_nil p)))
def c2107 : List Lit := [(111, true), (45, true), (122, false)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c898, c799] c2107 (by decide) p (sat_cons (step898 p h) (sat_cons (step799 p h) (sat_nil p)))
def c2108 : List Lit := [(124, true), (127, true), (125, false), (119, true), (128, true)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c899, c821] c2108 (by decide) p (sat_cons (step899 p h) (sat_cons (step821 p h) (sat_nil p)))
def c2109 : List Lit := [(124, true), (127, true), (125, false), (114, true), (128, true)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c899, c822] c2109 (by decide) p (sat_cons (step899 p h) (sat_cons (step822 p h) (sat_nil p)))
def c2110 : List Lit := [(114, true), (127, true), (125, false), (128, true), (119, true)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c899, c823] c2110 (by decide) p (sat_cons (step899 p h) (sat_cons (step823 p h) (sat_nil p)))
def c2111 : List Lit := [(124, true), (114, true), (125, false), (119, true), (128, true)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c899, c824] c2111 (by decide) p (sat_cons (step899 p h) (sat_cons (step824 p h) (sat_nil p)))
def c2112 : List Lit := [(124, true), (114, true), (119, true), (127, true), (125, false)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c899, c825] c2112 (by decide) p (sat_cons (step899 p h) (sat_cons (step825 p h) (sat_nil p)))
def c2113 : List Lit := [(124, true), (127, true), (115, true), (126, false)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c900, c830] c2113 (by decide) p (sat_cons (step900 p h) (sat_cons (step830 p h) (sat_nil p)))
def c2114 : List Lit := [(101, true), (127, true), (124, true), (126, false)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c900, c831] c2114 (by decide) p (sat_cons (step900 p h) (sat_cons (step831 p h) (sat_nil p)))
def c2115 : List Lit := [(101, true), (115, true), (127, true), (126, false)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c900, c832] c2115 (by decide) p (sat_cons (step900 p h) (sat_cons (step832 p h) (sat_nil p)))
def c2116 : List Lit := [(101, true), (124, true), (115, true), (126, false)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c900, c833] c2116 (by decide) p (sat_cons (step900 p h) (sat_cons (step833 p h) (sat_nil p)))
def c2117 : List Lit := [(273, false), (279, false)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c1807, c911] c2117 (by decide) p (sat_cons (step1807 p h) (sat_cons (step911 p h) (sat_nil p)))
def c2118 : List Lit := [(289, false), (295, false)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c1806, c923] c2118 (by decide) p (sat_cons (step1806 p h) (sat_cons (step923 p h) (sat_nil p)))
def c2119 : List Lit := [(159, false), (160, false)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c1813, c929] c2119 (by decide) p (sat_cons (step1813 p h) (sat_cons (step929 p h) (sat_nil p)))
def c2120 : List Lit := [(305, false), (307, false)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c1811, c933] c2120 (by decide) p (sat_cons (step1811 p h) (sat_cons (step933 p h) (sat_nil p)))
def c2121 : List Lit := [(303, false), (309, false)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c1805, c937] c2121 (by decide) p (sat_cons (step1805 p h) (sat_cons (step937 p h) (sat_nil p)))
def c2122 : List Lit := [(297, false), (311, false)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c1797, c941] c2122 (by decide) p (sat_cons (step1797 p h) (sat_cons (step941 p h) (sat_nil p)))
def c2123 : List Lit := [(283, false), (313, false)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c1791, c946] c2123 (by decide) p (sat_cons (step1791 p h) (sat_cons (step946 p h) (sat_nil p)))
def c2124 : List Lit := [(331, false), (333, false)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c1810, c957] c2124 (by decide) p (sat_cons (step1810 p h) (sat_cons (step957 p h) (sat_nil p)))
def c2125 : List Lit := [(335, false), (341, false)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c1804, c962] c2125 (by decide) p (sat_cons (step1804 p h) (sat_cons (step962 p h) (sat_nil p)))
def c2126 : List Lit := [(345, false), (375, false)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c1790, c983] c2126 (by decide) p (sat_cons (step1790 p h) (sat_cons (step983 p h) (sat_nil p)))
def c2127 : List Lit := [(315, false), (377, false)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c1787, c988] c2127 (by decide) p (sat_cons (step1787 p h) (sat_cons (step988 p h) (sat_nil p)))
def c2128 : List Lit := [(385, false), (391, false)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c1803, c996] c2128 (by decide) p (sat_cons (step1803 p h) (sat_cons (step996 p h) (sat_nil p)))
def c2129 : List Lit := [(393, false), (407, false)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c1795, c1008] c2129 (by decide) p (sat_cons (step1795 p h) (sat_cons (step1008 p h) (sat_nil p)))
def c2130 : List Lit := [(423, false), (437, false)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c1794, c1026] c2130 (by decide) p (sat_cons (step1794 p h) (sat_cons (step1026 p h) (sat_nil p)))
def c2131 : List Lit := [(409, false), (439, false)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c1789, c1030] c2131 (by decide) p (sat_cons (step1789 p h) (sat_cons (step1030 p h) (sat_nil p)))
def c2132 : List Lit := [(447, false), (453, false)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c1802, c1039] c2132 (by decide) p (sat_cons (step1802 p h) (sat_cons (step1039 p h) (sat_nil p)))
def c2133 : List Lit := [(461, false), (467, false)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c1801, c1049] c2133 (by decide) p (sat_cons (step1801 p h) (sat_cons (step1049 p h) (sat_nil p)))
def c2134 : List Lit := [(455, false), (469, false)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c1793, c1053] c2134 (by decide) p (sat_cons (step1793 p h) (sat_cons (step1053 p h) (sat_nil p)))
def c2135 : List Lit := [(473, false), (475, false)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c1809, c1059] c2135 (by decide) p (sat_cons (step1809 p h) (sat_cons (step1059 p h) (sat_nil p)))
def c2136 : List Lit := [(255, false), (256, false)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c1812, c1067] c2136 (by decide) p (sat_cons (step1812 p h) (sat_cons (step1067 p h) (sat_nil p)))
def c2137 : List Lit := [(471, false), (501, false)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1080] c2137 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c2138 : List Lit := [(441, false), (503, false)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c1786, c1085] c2138 (by decide) p (sat_cons (step1786 p h) (sat_cons (step1085 p h) (sat_nil p)))
def c2139 : List Lit := [(379, false), (505, false)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c1090, c1088] c2139 (by decide) p (sat_cons (step1090 p h) (sat_cons (step1088 p h) (sat_nil p)))
def c2140 : List Lit := [(1543, false), (1546, true)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1098] c2140 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1098 p h) (sat_nil p)))
def c2141 : List Lit := [(1553, false), (1559, true)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1110] c2141 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1110 p h) (sat_nil p)))
def c2142 : List Lit := [(1554, false), (1560, true)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1111] c2142 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1111 p h) (sat_nil p)))
def c2143 : List Lit := [(1582, false), (1593, true)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1168] c2143 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1168 p h) (sat_nil p)))
def c2144 : List Lit := [(1594, true), (1583, false)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1169] c2144 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1169 p h) (sat_nil p)))
def c2145 : List Lit := [(1584, false), (1595, true)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1170] c2145 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1170 p h) (sat_nil p)))
def c2146 : List Lit := [(1585, false), (1596, true)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1171] c2146 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1171 p h) (sat_nil p)))
def c2147 : List Lit := [(1586, false), (1597, true)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1172] c2147 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1172 p h) (sat_nil p)))
def c2148 : List Lit := [(1587, false), (1598, true)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1173] c2148 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1173 p h) (sat_nil p)))
def c2149 : List Lit := [(1559, false), (1593, true)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c1921, c1174] c2149 (by decide) p (sat_cons (step1921 p h) (sat_cons (step1174 p h) (sat_nil p)))
def c2150 : List Lit := [(1560, false), (1594, true)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c1921, c1181] c2150 (by decide) p (sat_cons (step1921 p h) (sat_cons (step1181 p h) (sat_nil p)))
def c2151 : List Lit := [(1561, false), (1595, true)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c1921, c1187] c2151 (by decide) p (sat_cons (step1921 p h) (sat_cons (step1187 p h) (sat_nil p)))
def c2152 : List Lit := [(1562, false), (1596, true)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c1921, c1190] c2152 (by decide) p (sat_cons (step1921 p h) (sat_cons (step1190 p h) (sat_nil p)))
def c2153 : List Lit := [(1632, false), (1649, true)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c1832, c1279] c2153 (by decide) p (sat_cons (step1832 p h) (sat_cons (step1279 p h) (sat_nil p)))
def c2154 : List Lit := [(1633, false), (1650, true)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c1832, c1284] c2154 (by decide) p (sat_cons (step1832 p h) (sat_cons (step1284 p h) (sat_nil p)))
def c2155 : List Lit := [(1634, false), (1651, true)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c1832, c1289] c2155 (by decide) p (sat_cons (step1832 p h) (sat_cons (step1289 p h) (sat_nil p)))
def c2156 : List Lit := [(1620, false), (1658, true)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1292] c2156 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1292 p h) (sat_nil p)))
def c2157 : List Lit := [(1621, false), (1659, true)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1297] c2157 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1297 p h) (sat_nil p)))
def c2158 : List Lit := [(1622, false), (1660, true)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1304] c2158 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1304 p h) (sat_nil p)))
def c2159 : List Lit := [(1661, true), (1623, false)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1311] c2159 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1311 p h) (sat_nil p)))
def c2160 : List Lit := [(1662, true), (1624, false)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1317] c2160 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1317 p h) (sat_nil p)))
def c2161 : List Lit := [(1685, true), (1663, false)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c1922, c1323] c2161 (by decide) p (sat_cons (step1922 p h) (sat_cons (step1323 p h) (sat_nil p)))
def c2162 : List Lit := [(1713, false), (1718, true)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1402] c2162 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1402 p h) (sat_nil p)))
end B112E034
