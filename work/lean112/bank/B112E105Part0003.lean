import B112E105Part0002
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2121 : List Lit := [(68, true), (67, false), (102, true)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c976, c390] c2121 (by decide) p (sat_cons (step976 p h) (sat_cons (step390 p h) (sat_nil p)))
def c2122 : List Lit := [(67, false), (72, true), (68, true)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c976, c391] c2122 (by decide) p (sat_cons (step976 p h) (sat_cons (step391 p h) (sat_nil p)))
def c2123 : List Lit := [(69, false), (71, true), (106, true)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c977, c402] c2123 (by decide) p (sat_cons (step977 p h) (sat_cons (step402 p h) (sat_nil p)))
def c2124 : List Lit := [(70, false), (71, true), (74, true), (107, true)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c978, c407] c2124 (by decide) p (sat_cons (step978 p h) (sat_cons (step407 p h) (sat_nil p)))
def c2125 : List Lit := [(70, false), (74, true), (68, true), (107, true)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c978, c408] c2125 (by decide) p (sat_cons (step978 p h) (sat_cons (step408 p h) (sat_nil p)))
def c2126 : List Lit := [(70, false), (71, true), (107, true), (68, true)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c978, c409] c2126 (by decide) p (sat_cons (step978 p h) (sat_cons (step409 p h) (sat_nil p)))
def c2127 : List Lit := [(75, false), (74, true), (113, true), (20, true)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c980, c434] c2127 (by decide) p (sat_cons (step980 p h) (sat_cons (step434 p h) (sat_nil p)))
def c2128 : List Lit := [(75, false), (71, true), (113, true), (20, true)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c980, c435] c2128 (by decide) p (sat_cons (step980 p h) (sat_cons (step435 p h) (sat_nil p)))
def c2129 : List Lit := [(77, false), (78, true), (83, true), (117, true)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c981, c445] c2129 (by decide) p (sat_cons (step981 p h) (sat_cons (step445 p h) (sat_nil p)))
def c2130 : List Lit := [(77, false), (25, true), (83, true), (117, true)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c981, c446] c2130 (by decide) p (sat_cons (step981 p h) (sat_cons (step446 p h) (sat_nil p)))
def c2131 : List Lit := [(77, false), (25, true), (78, true), (117, true)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c981, c447] c2131 (by decide) p (sat_cons (step981 p h) (sat_cons (step447 p h) (sat_nil p)))
def c2132 : List Lit := [(77, false), (25, true), (78, true), (83, true)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c981, c448] c2132 (by decide) p (sat_cons (step981 p h) (sat_cons (step448 p h) (sat_nil p)))
def c2133 : List Lit := [(79, false), (71, true), (78, true)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c982, c458] c2133 (by decide) p (sat_cons (step982 p h) (sat_cons (step458 p h) (sat_nil p)))
def c2134 : List Lit := [(79, false), (76, true), (71, true)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c982, c459] c2134 (by decide) p (sat_cons (step982 p h) (sat_cons (step459 p h) (sat_nil p)))
def c2135 : List Lit := [(80, false), (81, true), (83, true)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c983, c461] c2135 (by decide) p (sat_cons (step983 p h) (sat_cons (step461 p h) (sat_nil p)))
def c2136 : List Lit := [(72, true), (80, false), (83, true)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c983, c462] c2136 (by decide) p (sat_cons (step983 p h) (sat_cons (step462 p h) (sat_nil p)))
def c2137 : List Lit := [(82, false), (81, true)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c984, c468] c2137 (by decide) p (sat_cons (step984 p h) (sat_cons (step468 p h) (sat_nil p)))
def c2138 : List Lit := [(82, false), (76, true)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c984, c469] c2138 (by decide) p (sat_cons (step984 p h) (sat_cons (step469 p h) (sat_nil p)))
def c2139 : List Lit := [(84, false), (89, true), (102, true)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c985, c477] c2139 (by decide) p (sat_cons (step985 p h) (sat_cons (step477 p h) (sat_nil p)))
def c2140 : List Lit := [(85, true), (84, false), (102, true)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c985, c478] c2140 (by decide) p (sat_cons (step985 p h) (sat_cons (step478 p h) (sat_nil p)))
def c2141 : List Lit := [(84, false), (89, true), (85, true)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c985, c479] c2141 (by decide) p (sat_cons (step985 p h) (sat_cons (step479 p h) (sat_nil p)))
def c2142 : List Lit := [(86, false), (88, true), (33, true), (106, true)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c986, c492] c2142 (by decide) p (sat_cons (step986 p h) (sat_cons (step492 p h) (sat_nil p)))
def c2143 : List Lit := [(88, true), (87, false), (107, true), (91, true)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c987, c497] c2143 (by decide) p (sat_cons (step987 p h) (sat_cons (step497 p h) (sat_nil p)))
def c2144 : List Lit := [(87, false), (91, true), (85, true), (107, true)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c987, c498] c2144 (by decide) p (sat_cons (step987 p h) (sat_cons (step498 p h) (sat_nil p)))
def c2145 : List Lit := [(88, true), (87, false), (85, true), (107, true)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c987, c499] c2145 (by decide) p (sat_cons (step987 p h) (sat_cons (step499 p h) (sat_nil p)))
def c2146 : List Lit := [(89, true), (98, true), (108, true), (90, false)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c988, c512] c2146 (by decide) p (sat_cons (step988 p h) (sat_cons (step512 p h) (sat_nil p)))
def c2147 : List Lit := [(90, false), (98, true), (35, true), (108, true)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c988, c513] c2147 (by decide) p (sat_cons (step988 p h) (sat_cons (step513 p h) (sat_nil p)))
def c2148 : List Lit := [(92, false), (91, true), (113, true)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c989, c520] c2148 (by decide) p (sat_cons (step989 p h) (sat_cons (step520 p h) (sat_nil p)))
def c2149 : List Lit := [(88, true), (92, false), (113, true)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c989, c521] c2149 (by decide) p (sat_cons (step989 p h) (sat_cons (step521 p h) (sat_nil p)))
def c2150 : List Lit := [(94, false), (101, true), (117, true)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c990, c527] c2150 (by decide) p (sat_cons (step990 p h) (sat_cons (step527 p h) (sat_nil p)))
def c2151 : List Lit := [(94, false), (95, true), (117, true)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c990, c528] c2151 (by decide) p (sat_cons (step990 p h) (sat_cons (step528 p h) (sat_nil p)))
def c2152 : List Lit := [(94, false), (95, true), (101, true)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c990, c529] c2152 (by decide) p (sat_cons (step990 p h) (sat_cons (step529 p h) (sat_nil p)))
def c2153 : List Lit := [(96, false), (88, true), (95, true)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c991, c540] c2153 (by decide) p (sat_cons (step991 p h) (sat_cons (step540 p h) (sat_nil p)))
def c2154 : List Lit := [(88, true), (96, false), (93, true)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c991, c541] c2154 (by decide) p (sat_cons (step991 p h) (sat_cons (step541 p h) (sat_nil p)))
def c2155 : List Lit := [(101, true), (98, true), (97, false), (99, true)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c992, c546] c2155 (by decide) p (sat_cons (step992 p h) (sat_cons (step546 p h) (sat_nil p)))
def c2156 : List Lit := [(97, false), (89, true), (98, true), (99, true)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c992, c547] c2156 (by decide) p (sat_cons (step992 p h) (sat_cons (step547 p h) (sat_nil p)))
def c2157 : List Lit := [(100, false), (98, true), (99, true)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c993, c563] c2157 (by decide) p (sat_cons (step993 p h) (sat_cons (step563 p h) (sat_nil p)))
def c2158 : List Lit := [(100, false), (93, true), (99, true)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c993, c564] c2158 (by decide) p (sat_cons (step993 p h) (sat_cons (step564 p h) (sat_nil p)))
def c2159 : List Lit := [(106, true), (103, false), (115, true), (102, true), (108, true)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c994, c602] c2159 (by decide) p (sat_cons (step994 p h) (sat_cons (step602 p h) (sat_nil p)))
def c2160 : List Lit := [(103, false), (108, true), (105, true), (102, true), (115, true)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c994, c603] c2160 (by decide) p (sat_cons (step994 p h) (sat_cons (step603 p h) (sat_nil p)))
def c2161 : List Lit := [(103, false), (106, true), (102, true), (105, true), (115, true)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c994, c604] c2161 (by decide) p (sat_cons (step994 p h) (sat_cons (step604 p h) (sat_nil p)))
def c2162 : List Lit := [(103, false), (106, true), (108, true), (105, true), (102, true)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c994, c605] c2162 (by decide) p (sat_cons (step994 p h) (sat_cons (step605 p h) (sat_nil p)))
def c2163 : List Lit := [(68, true), (107, true), (104, false), (102, true), (85, true), (105, true), (116, true)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c995, c641] c2163 (by decide) p (sat_cons (step995 p h) (sat_cons (step641 p h) (sat_nil p)))
def c2164 : List Lit := [(85, true), (116, true), (104, false), (102, true), (105, true), (107, true), (48, true)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c995, c642] c2164 (by decide) p (sat_cons (step995 p h) (sat_cons (step642 p h) (sat_nil p)))
def c2165 : List Lit := [(68, true), (116, true), (104, false), (105, true), (48, true), (107, true), (102, true)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c995, c643] c2165 (by decide) p (sat_cons (step995 p h) (sat_cons (step643 p h) (sat_nil p)))
def c2166 : List Lit := [(85, true), (116, true), (104, false), (68, true), (105, true), (107, true), (48, true)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c995, c644] c2166 (by decide) p (sat_cons (step995 p h) (sat_cons (step644 p h) (sat_nil p)))
def c2167 : List Lit := [(85, true), (116, true), (104, false), (68, true), (102, true), (107, true), (48, true)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c995, c645] c2167 (by decide) p (sat_cons (step995 p h) (sat_cons (step645 p h) (sat_nil p)))
def c2168 : List Lit := [(85, true), (116, true), (104, false), (68, true), (102, true), (105, true), (48, true)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c995, c646] c2168 (by decide) p (sat_cons (step995 p h) (sat_cons (step646 p h) (sat_nil p)))
def c2169 : List Lit := [(85, true), (48, true), (104, false), (68, true), (102, true), (105, true), (107, true)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c995, c647] c2169 (by decide) p (sat_cons (step995 p h) (sat_cons (step647 p h) (sat_nil p)))
def c2170 : List Lit := [(54, true), (113, true), (109, false), (108, true)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c996, c689] c2170 (by decide) p (sat_cons (step996 p h) (sat_cons (step689 p h) (sat_nil p)))
def c2171 : List Lit := [(111, false), (122, true), (110, true), (113, true), (108, true)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c997, c711] c2171 (by decide) p (sat_cons (step997 p h) (sat_cons (step711 p h) (sat_nil p)))
def c2172 : List Lit := [(111, false), (106, true), (122, true), (110, true), (113, true)]
theorem step2172 (p : Nat → Bool) (h : Constraints p) : clause p c2172 = true :=
  Snake9.LocalRup.prove_clause [c997, c712] c2172 (by decide) p (sat_cons (step997 p h) (sat_cons (step712 p h) (sat_nil p)))
def c2173 : List Lit := [(111, false), (122, true), (106, true), (113, true), (108, true)]
theorem step2173 (p : Nat → Bool) (h : Constraints p) : clause p c2173 = true :=
  Snake9.LocalRup.prove_clause [c997, c713] c2173 (by decide) p (sat_cons (step997 p h) (sat_cons (step713 p h) (sat_nil p)))
def c2174 : List Lit := [(111, false), (122, true), (106, true), (110, true), (108, true)]
theorem step2174 (p : Nat → Bool) (h : Constraints p) : clause p c2174 = true :=
  Snake9.LocalRup.prove_clause [c997, c714] c2174 (by decide) p (sat_cons (step997 p h) (sat_cons (step714 p h) (sat_nil p)))
def c2175 : List Lit := [(106, true), (111, false), (108, true), (110, true), (113, true)]
theorem step2175 (p : Nat → Bool) (h : Constraints p) : clause p c2175 = true :=
  Snake9.LocalRup.prove_clause [c997, c715] c2175 (by decide) p (sat_cons (step997 p h) (sat_cons (step715 p h) (sat_nil p)))
def c2176 : List Lit := [(91, true), (123, true), (74, true), (107, true), (112, false), (113, true), (110, true)]
theorem step2176 (p : Nat → Bool) (h : Constraints p) : clause p c2176 = true :=
  Snake9.LocalRup.prove_clause [c998, c751] c2176 (by decide) p (sat_cons (step998 p h) (sat_cons (step751 p h) (sat_nil p)))
def c2177 : List Lit := [(91, true), (123, true), (112, false), (107, true), (56, true), (110, true), (113, true)]
theorem step2177 (p : Nat → Bool) (h : Constraints p) : clause p c2177 = true :=
  Snake9.LocalRup.prove_clause [c998, c752] c2177 (by decide) p (sat_cons (step998 p h) (sat_cons (step752 p h) (sat_nil p)))
def c2178 : List Lit := [(123, true), (107, true), (56, true), (74, true), (112, false), (110, true), (113, true)]
theorem step2178 (p : Nat → Bool) (h : Constraints p) : clause p c2178 = true :=
  Snake9.LocalRup.prove_clause [c998, c753] c2178 (by decide) p (sat_cons (step998 p h) (sat_cons (step753 p h) (sat_nil p)))
def c2179 : List Lit := [(91, true), (74, true), (56, true), (110, true), (107, true), (112, false), (123, true)]
theorem step2179 (p : Nat → Bool) (h : Constraints p) : clause p c2179 = true :=
  Snake9.LocalRup.prove_clause [c998, c754] c2179 (by decide) p (sat_cons (step998 p h) (sat_cons (step754 p h) (sat_nil p)))
def c2180 : List Lit := [(91, true), (74, true), (56, true), (110, true), (107, true), (112, false), (113, true)]
theorem step2180 (p : Nat → Bool) (h : Constraints p) : clause p c2180 = true :=
  Snake9.LocalRup.prove_clause [c998, c755] c2180 (by decide) p (sat_cons (step998 p h) (sat_cons (step755 p h) (sat_nil p)))
def c2181 : List Lit := [(114, false), (117, true), (115, true), (116, true)]
theorem step2181 (p : Nat → Bool) (h : Constraints p) : clause p c2181 = true :=
  Snake9.LocalRup.prove_clause [c999, c776] c2181 (by decide) p (sat_cons (step999 p h) (sat_cons (step776 p h) (sat_nil p)))
def c2182 : List Lit := [(114, false), (117, true), (102, true), (116, true)]
theorem step2182 (p : Nat → Bool) (h : Constraints p) : clause p c2182 = true :=
  Snake9.LocalRup.prove_clause [c999, c777] c2182 (by decide) p (sat_cons (step999 p h) (sat_cons (step777 p h) (sat_nil p)))
def c2183 : List Lit := [(114, false), (102, true), (117, true), (115, true)]
theorem step2183 (p : Nat → Bool) (h : Constraints p) : clause p c2183 = true :=
  Snake9.LocalRup.prove_clause [c999, c778] c2183 (by decide) p (sat_cons (step999 p h) (sat_cons (step778 p h) (sat_nil p)))
def c2184 : List Lit := [(114, false), (116, true), (102, true), (115, true)]
theorem step2184 (p : Nat → Bool) (h : Constraints p) : clause p c2184 = true :=
  Snake9.LocalRup.prove_clause [c999, c779] c2184 (by decide) p (sat_cons (step999 p h) (sat_cons (step779 p h) (sat_nil p)))
end B112E105
