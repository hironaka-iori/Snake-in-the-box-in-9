import B112E121Part0004
namespace B112E121
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2044 : List Lit := [(113, true), (112, false), (92, true)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c930, c855] c2044 (by decide) p (sat_cons (step930 p h) (sat_cons (step855 p h) (sat_nil p)))
def c2045 : List Lit := [(113, true), (99, true), (118, false), (116, true)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c931, c863] c2045 (by decide) p (sat_cons (step931 p h) (sat_cons (step863 p h) (sat_nil p)))
def c2046 : List Lit := [(111, true), (121, true), (119, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c932, c865] c2046 (by decide) p (sat_cons (step932 p h) (sat_cons (step865 p h) (sat_nil p)))
def c2047 : List Lit := [(121, true), (119, false), (100, true)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c932, c866] c2047 (by decide) p (sat_cons (step932 p h) (sat_cons (step866 p h) (sat_nil p)))
def c2048 : List Lit := [(111, true), (119, false), (100, true)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c932, c867] c2048 (by decide) p (sat_cons (step932 p h) (sat_cons (step867 p h) (sat_nil p)))
def c2049 : List Lit := [(123, true), (122, true), (120, false)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c933, c868] c2049 (by decide) p (sat_cons (step933 p h) (sat_cons (step868 p h) (sat_nil p)))
def c2050 : List Lit := [(123, true), (121, true), (120, false)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c933, c869] c2050 (by decide) p (sat_cons (step933 p h) (sat_cons (step869 p h) (sat_nil p)))
def c2051 : List Lit := [(122, true), (121, true), (120, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c933, c870] c2051 (by decide) p (sat_cons (step933 p h) (sat_cons (step870 p h) (sat_nil p)))
def c2052 : List Lit := [(125, false), (124, true)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c934, c877] c2052 (by decide) p (sat_cons (step934 p h) (sat_cons (step877 p h) (sat_nil p)))
def c2053 : List Lit := [(125, false), (117, true)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c934, c878] c2053 (by decide) p (sat_cons (step934 p h) (sat_cons (step878 p h) (sat_nil p)))
def c2054 : List Lit := [(132, false), (133, false)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c1753, c939] c2054 (by decide) p (sat_cons (step1753 p h) (sat_cons (step939 p h) (sat_nil p)))
def c2055 : List Lit := [(255, false), (261, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c1746, c945] c2055 (by decide) p (sat_cons (step1746 p h) (sat_cons (step945 p h) (sat_nil p)))
def c2056 : List Lit := [(263, false), (277, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c1741, c954] c2056 (by decide) p (sat_cons (step1741 p h) (sat_cons (step954 p h) (sat_nil p)))
def c2057 : List Lit := [(281, false), (283, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c1750, c960] c2057 (by decide) p (sat_cons (step1750 p h) (sat_cons (step960 p h) (sat_nil p)))
def c2058 : List Lit := [(279, false), (309, false)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c1735, c975] c2058 (by decide) p (sat_cons (step1735 p h) (sat_cons (step975 p h) (sat_nil p)))
def c2059 : List Lit := [(325, false), (327, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1749, c988] c2059 (by decide) p (sat_cons (step1749 p h) (sat_cons (step988 p h) (sat_nil p)))
def c2060 : List Lit := [(323, false), (337, false)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c1739, c994] c2060 (by decide) p (sat_cons (step1739 p h) (sat_cons (step994 p h) (sat_nil p)))
def c2061 : List Lit := [(181, false), (182, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1005] c2061 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1005 p h) (sat_nil p)))
def c2062 : List Lit := [(353, false), (367, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c1738, c1015] c2062 (by decide) p (sat_cons (step1738 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c2063 : List Lit := [(339, false), (369, false)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c1734, c1019] c2063 (by decide) p (sat_cons (step1734 p h) (sat_cons (step1019 p h) (sat_nil p)))
def c2064 : List Lit := [(311, false), (371, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c1731, c1024] c2064 (by decide) p (sat_cons (step1731 p h) (sat_cons (step1024 p h) (sat_nil p)))
def c2065 : List Lit := [(190, false), (375, false)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c1747, c1029] c2065 (by decide) p (sat_cons (step1747 p h) (sat_cons (step1029 p h) (sat_nil p)))
def c2066 : List Lit := [(377, false), (383, false)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c1742, c1036] c2066 (by decide) p (sat_cons (step1742 p h) (sat_cons (step1036 p h) (sat_nil p)))
def c2067 : List Lit := [(401, false), (431, false)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c1733, c1056] c2067 (by decide) p (sat_cons (step1733 p h) (sat_cons (step1056 p h) (sat_nil p)))
def c2068 : List Lit := [(477, false), (491, false)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c1736, c1073] c2068 (by decide) p (sat_cons (step1736 p h) (sat_cons (step1073 p h) (sat_nil p)))
def c2069 : List Lit := [(433, false), (495, false)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c1730, c1080] c2069 (by decide) p (sat_cons (step1730 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c2070 : List Lit := [(373, false), (497, false)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c1085, c1083] c2070 (by decide) p (sat_cons (step1085 p h) (sat_cons (step1083 p h) (sat_nil p)))
def c2071 : List Lit := [(999, true), (979, false)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c1894, c1338] c2071 (by decide) p (sat_cons (step1894 p h) (sat_cons (step1338 p h) (sat_nil p)))
def c2072 : List Lit := [(980, false), (1000, true)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c1894, c1339] c2072 (by decide) p (sat_cons (step1894 p h) (sat_cons (step1339 p h) (sat_nil p)))
def c2073 : List Lit := [(981, false), (1001, true)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c1894, c1340] c2073 (by decide) p (sat_cons (step1894 p h) (sat_cons (step1340 p h) (sat_nil p)))
def c2074 : List Lit := [(982, false), (1002, true)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c1894, c1341] c2074 (by decide) p (sat_cons (step1894 p h) (sat_cons (step1341 p h) (sat_nil p)))
def c2075 : List Lit := [(983, false), (1003, true)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c1894, c1342] c2075 (by decide) p (sat_cons (step1894 p h) (sat_cons (step1342 p h) (sat_nil p)))
def c2076 : List Lit := [(984, false), (1004, true)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c1894, c1343] c2076 (by decide) p (sat_cons (step1894 p h) (sat_cons (step1343 p h) (sat_nil p)))
def c2077 : List Lit := [(1057, true), (1052, false)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1455] c2077 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1455 p h) (sat_nil p)))
def c2078 : List Lit := [(1058, true), (1053, false)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1456] c2078 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1456 p h) (sat_nil p)))
def c2079 : List Lit := [(1054, false), (1059, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1457] c2079 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1457 p h) (sat_nil p)))
def c2080 : List Lit := [(1044, false), (1057, true)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c1784, c1458] c2080 (by decide) p (sat_cons (step1784 p h) (sat_cons (step1458 p h) (sat_nil p)))
def c2081 : List Lit := [(1045, false), (1058, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c1784, c1462] c2081 (by decide) p (sat_cons (step1784 p h) (sat_cons (step1462 p h) (sat_nil p)))
def c2082 : List Lit := [(1065, true), (1031, false)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1471] c2082 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1471 p h) (sat_nil p)))
def c2083 : List Lit := [(1032, false), (1065, true)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c1785, c1476] c2083 (by decide) p (sat_cons (step1785 p h) (sat_cons (step1476 p h) (sat_nil p)))
def c2084 : List Lit := [(1032, false), (1066, true)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1477] c2084 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1477 p h) (sat_nil p)))
def c2085 : List Lit := [(1033, false), (1067, true)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1482] c2085 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1482 p h) (sat_nil p)))
def c2086 : List Lit := [(1034, false), (1068, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1486] c2086 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1486 p h) (sat_nil p)))
def c2087 : List Lit := [(1035, false), (1069, true)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1489] c2087 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1489 p h) (sat_nil p)))
def c2088 : List Lit := [(1120, false), (1129, true)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c1793, c1576] c2088 (by decide) p (sat_cons (step1793 p h) (sat_cons (step1576 p h) (sat_nil p)))
def c2089 : List Lit := [(1121, false), (1130, true)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c1793, c1577] c2089 (by decide) p (sat_cons (step1793 p h) (sat_cons (step1577 p h) (sat_nil p)))
def c2090 : List Lit := [(1096, false), (1129, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1578] c2090 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1578 p h) (sat_nil p)))
def c2091 : List Lit := [(1097, false), (1130, true)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1582] c2091 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1582 p h) (sat_nil p)))
def c2092 : List Lit := [(1098, false), (1131, true)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1586] c2092 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1586 p h) (sat_nil p)))
def c2093 : List Lit := [(1099, false), (1132, true)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1590] c2093 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1590 p h) (sat_nil p)))
def c2094 : List Lit := [(1100, false), (1133, true)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1593] c2094 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1593 p h) (sat_nil p)))
def c2095 : List Lit := [(1135, false), (1152, true)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c1786, c1596] c2095 (by decide) p (sat_cons (step1786 p h) (sat_cons (step1596 p h) (sat_nil p)))
def c2096 : List Lit := [(1148, true), (1130, false)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1597] c2096 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1597 p h) (sat_nil p)))
def c2097 : List Lit := [(1131, false), (1149, true)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1598] c2097 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1598 p h) (sat_nil p)))
def c2098 : List Lit := [(1132, false), (1150, true)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1599] c2098 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1599 p h) (sat_nil p)))
def c2099 : List Lit := [(1133, false), (1151, true)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1600] c2099 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1600 p h) (sat_nil p)))
def c2100 : List Lit := [(1134, false), (1152, true)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1601] c2100 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1601 p h) (sat_nil p)))
def c2101 : List Lit := [(1135, false), (1153, true)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1602] c2101 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1602 p h) (sat_nil p)))
def c2102 : List Lit := [(999, false), (1157, false)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1639] c2102 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1639 p h) (sat_nil p)))
def c2103 : List Lit := [(1000, false), (1156, false)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1640] c2103 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1640 p h) (sat_nil p)))
def c2104 : List Lit := [(1001, false), (1155, false)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1641] c2104 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1641 p h) (sat_nil p)))
def c2105 : List Lit := [(1002, false), (1154, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1642] c2105 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1642 p h) (sat_nil p)))
def c2106 : List Lit := [(1003, false), (1153, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1643] c2106 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1643 p h) (sat_nil p)))
def c2107 : List Lit := [(1004, false), (1152, false)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1644] c2107 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1644 p h) (sat_nil p)))
end B112E121
