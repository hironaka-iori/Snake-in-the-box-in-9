import B112E019Part0003
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2062 : List Lit := [(98, true), (87, true), (118, true), (96, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c897, c523] c2062 (by decide) p (sat_cons (step897 p h) (sat_cons (step523 p h) (sat_nil p)))
def c2063 : List Lit := [(87, true), (95, true), (118, true), (96, false)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c897, c524] c2063 (by decide) p (sat_cons (step897 p h) (sat_cons (step524 p h) (sat_nil p)))
def c2064 : List Lit := [(98, true), (87, true), (95, true), (96, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c897, c525] c2064 (by decide) p (sat_cons (step897 p h) (sat_cons (step525 p h) (sat_nil p)))
def c2065 : List Lit := [(98, true), (97, false), (95, true)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c898, c527] c2065 (by decide) p (sat_cons (step898 p h) (sat_cons (step527 p h) (sat_nil p)))
def c2066 : List Lit := [(98, true), (97, false), (91, true)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c898, c528] c2066 (by decide) p (sat_cons (step898 p h) (sat_cons (step528 p h) (sat_nil p)))
def c2067 : List Lit := [(97, false), (95, true), (91, true)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c898, c529] c2067 (by decide) p (sat_cons (step898 p h) (sat_cons (step529 p h) (sat_nil p)))
def c2068 : List Lit := [(112, true), (80, true), (100, false), (102, true), (63, true), (103, true), (99, true)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c899, c597] c2068 (by decide) p (sat_cons (step899 p h) (sat_cons (step597 p h) (sat_nil p)))
def c2069 : List Lit := [(80, true), (41, true), (112, true), (102, true), (99, true), (100, false), (103, true)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c899, c598] c2069 (by decide) p (sat_cons (step899 p h) (sat_cons (step598 p h) (sat_nil p)))
def c2070 : List Lit := [(112, true), (63, true), (102, true), (41, true), (99, true), (100, false), (103, true)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c899, c599] c2070 (by decide) p (sat_cons (step899 p h) (sat_cons (step599 p h) (sat_nil p)))
def c2071 : List Lit := [(41, true), (80, true), (63, true), (112, true), (103, true), (102, true), (100, false)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c899, c600] c2071 (by decide) p (sat_cons (step899 p h) (sat_cons (step600 p h) (sat_nil p)))
def c2072 : List Lit := [(103, true), (41, true), (100, false), (80, true), (63, true), (99, true), (112, true)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c899, c601] c2072 (by decide) p (sat_cons (step899 p h) (sat_cons (step601 p h) (sat_nil p)))
def c2073 : List Lit := [(41, true), (80, true), (100, false), (102, true), (63, true), (99, true), (112, true)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c899, c602] c2073 (by decide) p (sat_cons (step899 p h) (sat_cons (step602 p h) (sat_nil p)))
def c2074 : List Lit := [(41, true), (80, true), (100, false), (102, true), (63, true), (99, true), (103, true)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c899, c603] c2074 (by decide) p (sat_cons (step899 p h) (sat_cons (step603 p h) (sat_nil p)))
def c2075 : List Lit := [(101, false), (113, true), (102, true), (99, true)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c900, c608] c2075 (by decide) p (sat_cons (step900 p h) (sat_cons (step608 p h) (sat_nil p)))
def c2076 : List Lit := [(101, false), (113, true), (99, true), (81, true)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c900, c609] c2076 (by decide) p (sat_cons (step900 p h) (sat_cons (step609 p h) (sat_nil p)))
def c2077 : List Lit := [(104, false), (110, true), (103, true), (102, true)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c901, c633] c2077 (by decide) p (sat_cons (step901 p h) (sat_cons (step633 p h) (sat_nil p)))
def c2078 : List Lit := [(104, false), (43, true), (110, true), (102, true)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c901, c634] c2078 (by decide) p (sat_cons (step901 p h) (sat_cons (step634 p h) (sat_nil p)))
def c2079 : List Lit := [(104, false), (43, true), (102, true), (103, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c901, c635] c2079 (by decide) p (sat_cons (step901 p h) (sat_cons (step635 p h) (sat_nil p)))
def c2080 : List Lit := [(110, true), (87, true), (46, true), (106, false), (102, true), (118, true)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c903, c676] c2080 (by decide) p (sat_cons (step903 p h) (sat_cons (step676 p h) (sat_nil p)))
def c2081 : List Lit := [(67, true), (110, true), (118, true), (102, true), (106, false), (46, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c903, c677] c2081 (by decide) p (sat_cons (step903 p h) (sat_cons (step677 p h) (sat_nil p)))
def c2082 : List Lit := [(110, true), (108, false), (107, true)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c904, c694] c2082 (by decide) p (sat_cons (step904 p h) (sat_cons (step694 p h) (sat_nil p)))
def c2083 : List Lit := [(108, false), (107, true), (103, true)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c904, c695] c2083 (by decide) p (sat_cons (step904 p h) (sat_cons (step695 p h) (sat_nil p)))
def c2084 : List Lit := [(110, true), (69, true), (89, true), (107, true), (109, false), (120, true)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c905, c716] c2084 (by decide) p (sat_cons (step905 p h) (sat_cons (step716 p h) (sat_nil p)))
def c2085 : List Lit := [(120, true), (89, true), (109, false), (110, true), (48, true), (69, true)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c905, c717] c2085 (by decide) p (sat_cons (step905 p h) (sat_cons (step717 p h) (sat_nil p)))
def c2086 : List Lit := [(120, true), (89, true), (109, false), (48, true), (107, true), (69, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c905, c718] c2086 (by decide) p (sat_cons (step905 p h) (sat_cons (step718 p h) (sat_nil p)))
def c2087 : List Lit := [(48, true), (110, true), (109, false), (69, true), (107, true), (89, true)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c905, c719] c2087 (by decide) p (sat_cons (step905 p h) (sat_cons (step719 p h) (sat_nil p)))
def c2088 : List Lit := [(111, false), (115, true), (116, true), (99, true), (113, true)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c906, c743] c2088 (by decide) p (sat_cons (step906 p h) (sat_cons (step743 p h) (sat_nil p)))
def c2089 : List Lit := [(111, false), (113, true), (116, true), (99, true), (112, true)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c906, c744] c2089 (by decide) p (sat_cons (step906 p h) (sat_cons (step744 p h) (sat_nil p)))
def c2090 : List Lit := [(111, false), (113, true), (99, true), (112, true), (115, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c906, c745] c2090 (by decide) p (sat_cons (step906 p h) (sat_cons (step745 p h) (sat_nil p)))
def c2091 : List Lit := [(114, false), (112, true), (118, true), (113, true)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c907, c767] c2091 (by decide) p (sat_cons (step907 p h) (sat_cons (step767 p h) (sat_nil p)))
def c2092 : List Lit := [(114, false), (113, true), (102, true), (118, true)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c907, c768] c2092 (by decide) p (sat_cons (step907 p h) (sat_cons (step768 p h) (sat_nil p)))
def c2093 : List Lit := [(114, false), (112, true), (118, true), (102, true)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c907, c769] c2093 (by decide) p (sat_cons (step907 p h) (sat_cons (step769 p h) (sat_nil p)))
def c2094 : List Lit := [(114, false), (113, true), (102, true), (112, true)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c907, c770] c2094 (by decide) p (sat_cons (step907 p h) (sat_cons (step770 p h) (sat_nil p)))
def c2095 : List Lit := [(113, true), (117, false), (76, true), (116, true), (118, true), (120, true)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c908, c815] c2095 (by decide) p (sat_cons (step908 p h) (sat_cons (step815 p h) (sat_nil p)))
def c2096 : List Lit := [(119, false), (120, true), (116, true), (107, true)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c909, c832] c2096 (by decide) p (sat_cons (step909 p h) (sat_cons (step832 p h) (sat_nil p)))
def c2097 : List Lit := [(115, true), (119, false), (120, true), (107, true)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c909, c833] c2097 (by decide) p (sat_cons (step909 p h) (sat_cons (step833 p h) (sat_nil p)))
def c2098 : List Lit := [(115, true), (119, false), (116, true), (107, true)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c909, c834] c2098 (by decide) p (sat_cons (step909 p h) (sat_cons (step834 p h) (sat_nil p)))
def c2099 : List Lit := [(121, false), (110, true), (120, true), (118, true)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c910, c847] c2099 (by decide) p (sat_cons (step910 p h) (sat_cons (step847 p h) (sat_nil p)))
def c2100 : List Lit := [(121, false), (98, true), (118, true), (120, true)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c910, c848] c2100 (by decide) p (sat_cons (step910 p h) (sat_cons (step848 p h) (sat_nil p)))
def c2101 : List Lit := [(121, false), (98, true), (110, true), (118, true)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c910, c849] c2101 (by decide) p (sat_cons (step910 p h) (sat_cons (step849 p h) (sat_nil p)))
def c2102 : List Lit := [(247, false), (249, false)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c1856, c917] c2102 (by decide) p (sat_cons (step1856 p h) (sat_cons (step917 p h) (sat_nil p)))
def c2103 : List Lit := [(253, false), (267, false)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c1823, c931] c2103 (by decide) p (sat_cons (step1823 p h) (sat_cons (step931 p h) (sat_nil p)))
def c2104 : List Lit := [(275, false), (277, false)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c1855, c940] c2104 (by decide) p (sat_cons (step1855 p h) (sat_cons (step940 p h) (sat_nil p)))
def c2105 : List Lit := [(273, false), (279, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c1837, c944] c2105 (by decide) p (sat_cons (step1837 p h) (sat_cons (step944 p h) (sat_nil p)))
def c2106 : List Lit := [(287, false), (293, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c1836, c953] c2106 (by decide) p (sat_cons (step1836 p h) (sat_cons (step953 p h) (sat_nil p)))
def c2107 : List Lit := [(269, false), (297, false)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c1815, c961] c2107 (by decide) p (sat_cons (step1815 p h) (sat_cons (step961 p h) (sat_nil p)))
def c2108 : List Lit := [(303, false), (309, false)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c1835, c972] c2108 (by decide) p (sat_cons (step1835 p h) (sat_cons (step972 p h) (sat_nil p)))
def c2109 : List Lit := [(313, false), (315, false)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c1854, c977] c2109 (by decide) p (sat_cons (step1854 p h) (sat_cons (step977 p h) (sat_nil p)))
def c2110 : List Lit := [(317, false), (323, false)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c1834, c984] c2110 (by decide) p (sat_cons (step1834 p h) (sat_cons (step984 p h) (sat_nil p)))
def c2111 : List Lit := [(311, false), (325, false)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c1821, c989] c2111 (by decide) p (sat_cons (step1821 p h) (sat_cons (step989 p h) (sat_nil p)))
def c2112 : List Lit := [(167, false), (329, false)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c1853, c994] c2112 (by decide) p (sat_cons (step1853 p h) (sat_cons (step994 p h) (sat_nil p)))
def c2113 : List Lit := [(172, false), (173, false)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c1861, c997] c2113 (by decide) p (sat_cons (step1861 p h) (sat_cons (step997 p h) (sat_nil p)))
def c2114 : List Lit := [(331, false), (337, false)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1003] c2114 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1003 p h) (sat_nil p)))
def c2115 : List Lit := [(341, false), (343, false)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c1851, c1009] c2115 (by decide) p (sat_cons (step1851 p h) (sat_cons (step1009 p h) (sat_nil p)))
def c2116 : List Lit := [(347, false), (349, false)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c1850, c1014] c2116 (by decide) p (sat_cons (step1850 p h) (sat_cons (step1014 p h) (sat_nil p)))
def c2117 : List Lit := [(345, false), (351, false)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c1832, c1018] c2117 (by decide) p (sat_cons (step1832 p h) (sat_cons (step1018 p h) (sat_nil p)))
def c2118 : List Lit := [(339, false), (353, false)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c1820, c1023] c2118 (by decide) p (sat_cons (step1820 p h) (sat_cons (step1023 p h) (sat_nil p)))
def c2119 : List Lit := [(327, false), (355, false)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1028] c2119 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1028 p h) (sat_nil p)))
def c2120 : List Lit := [(299, false), (357, false)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1033] c2120 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1033 p h) (sat_nil p)))
def c2121 : List Lit := [(184, false), (185, false)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c1860, c1037] c2121 (by decide) p (sat_cons (step1860 p h) (sat_cons (step1037 p h) (sat_nil p)))
def c2122 : List Lit := [(365, false), (367, false)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c1848, c1044] c2122 (by decide) p (sat_cons (step1848 p h) (sat_cons (step1044 p h) (sat_nil p)))
def c2123 : List Lit := [(363, false), (369, false)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c1831, c1048] c2123 (by decide) p (sat_cons (step1831 p h) (sat_cons (step1048 p h) (sat_nil p)))
def c2124 : List Lit := [(192, false), (193, false)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c1859, c1053] c2124 (by decide) p (sat_cons (step1859 p h) (sat_cons (step1053 p h) (sat_nil p)))
def c2125 : List Lit := [(373, false), (375, false)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c1847, c1057] c2125 (by decide) p (sat_cons (step1847 p h) (sat_cons (step1057 p h) (sat_nil p)))
end B112E019
