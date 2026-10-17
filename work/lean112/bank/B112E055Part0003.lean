import B112E055Part0002
namespace B112E055
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2134 : List Lit := [(27, true), (26, false), (5, true)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c968, c206] c2134 (by decide) p (sat_cons (step968 p h) (sat_cons (step206 p h) (sat_nil p)))
def c2135 : List Lit := [(28, false), (29, true), (27, true)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c969, c211] c2135 (by decide) p (sat_cons (step969 p h) (sat_cons (step211 p h) (sat_nil p)))
def c2136 : List Lit := [(28, false), (21, true), (29, true)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c969, c212] c2136 (by decide) p (sat_cons (step969 p h) (sat_cons (step212 p h) (sat_nil p)))
def c2137 : List Lit := [(34, true), (64, true), (100, true), (30, false), (32, true)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c970, c226] c2137 (by decide) p (sat_cons (step970 p h) (sat_cons (step226 p h) (sat_nil p)))
def c2138 : List Lit := [(32, true), (100, true), (30, false), (34, true), (31, true)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c970, c227] c2138 (by decide) p (sat_cons (step970 p h) (sat_cons (step227 p h) (sat_nil p)))
def c2139 : List Lit := [(33, false), (32, true), (23, true)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c971, c240] c2139 (by decide) p (sat_cons (step971 p h) (sat_cons (step240 p h) (sat_nil p)))
def c2140 : List Lit := [(13, true), (33, false), (23, true)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c971, c241] c2140 (by decide) p (sat_cons (step971 p h) (sat_cons (step241 p h) (sat_nil p)))
def c2141 : List Lit := [(35, false), (37, true), (34, true)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c972, c249] c2141 (by decide) p (sat_cons (step972 p h) (sat_cons (step249 p h) (sat_nil p)))
def c2142 : List Lit := [(35, false), (37, true), (31, true)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c972, c250] c2142 (by decide) p (sat_cons (step972 p h) (sat_cons (step250 p h) (sat_nil p)))
def c2143 : List Lit := [(35, false), (34, true), (31, true)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c972, c251] c2143 (by decide) p (sat_cons (step972 p h) (sat_cons (step251 p h) (sat_nil p)))
def c2144 : List Lit := [(37, true), (34, true), (18, true), (36, false), (106, true)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c973, c262] c2144 (by decide) p (sat_cons (step973 p h) (sat_cons (step262 p h) (sat_nil p)))
def c2145 : List Lit := [(34, true), (36, false), (18, true), (32, true), (106, true)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c973, c263] c2145 (by decide) p (sat_cons (step973 p h) (sat_cons (step263 p h) (sat_nil p)))
def c2146 : List Lit := [(42, false), (41, true), (40, true), (52, true)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c975, c293] c2146 (by decide) p (sat_cons (step975 p h) (sat_cons (step293 p h) (sat_nil p)))
def c2147 : List Lit := [(42, false), (41, true), (38, true), (40, true)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c975, c294] c2147 (by decide) p (sat_cons (step975 p h) (sat_cons (step294 p h) (sat_nil p)))
def c2148 : List Lit := [(46, false), (38, true), (45, true)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c977, c309] c2148 (by decide) p (sat_cons (step977 p h) (sat_cons (step309 p h) (sat_nil p)))
def c2149 : List Lit := [(47, false), (115, true), (40, true)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c978, c310] c2149 (by decide) p (sat_cons (step978 p h) (sat_cons (step310 p h) (sat_nil p)))
def c2150 : List Lit := [(47, false), (44, true), (40, true)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c978, c311] c2150 (by decide) p (sat_cons (step978 p h) (sat_cons (step311 p h) (sat_nil p)))
def c2151 : List Lit := [(54, false), (55, true), (45, true)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c982, c350] c2151 (by decide) p (sat_cons (step982 p h) (sat_cons (step350 p h) (sat_nil p)))
def c2152 : List Lit := [(58, true), (64, true), (56, false)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c983, c355] c2152 (by decide) p (sat_cons (step983 p h) (sat_cons (step355 p h) (sat_nil p)))
def c2153 : List Lit := [(56, false), (64, true), (57, true)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c983, c356] c2153 (by decide) p (sat_cons (step983 p h) (sat_cons (step356 p h) (sat_nil p)))
def c2154 : List Lit := [(58, true), (56, false), (57, true)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c983, c357] c2154 (by decide) p (sat_cons (step983 p h) (sat_cons (step357 p h) (sat_nil p)))
def c2155 : List Lit := [(40, false), (59, false), (23, false)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c1942, c365] c2155 (by decide) p (sat_cons (step1942 p h) (sat_cons (step365 p h) (sat_nil p)))
def c2156 : List Lit := [(57, false), (59, false), (23, false)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c1942, c366] c2156 (by decide) p (sat_cons (step1942 p h) (sat_cons (step366 p h) (sat_nil p)))
def c2157 : List Lit := [(40, false), (57, false), (59, false)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c1942, c367] c2157 (by decide) p (sat_cons (step1942 p h) (sat_cons (step367 p h) (sat_nil p)))
def c2158 : List Lit := [(57, true), (40, true), (59, false), (23, true)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c984, c368] c2158 (by decide) p (sat_cons (step984 p h) (sat_cons (step368 p h) (sat_nil p)))
def c2159 : List Lit := [(60, false), (62, true), (45, true)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c985, c370] c2159 (by decide) p (sat_cons (step985 p h) (sat_cons (step370 p h) (sat_nil p)))
def c2160 : List Lit := [(60, false), (58, true), (45, true)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c985, c371] c2160 (by decide) p (sat_cons (step985 p h) (sat_cons (step371 p h) (sat_nil p)))
def c2161 : List Lit := [(65, true), (62, false), (190, true), (63, true)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c1943, c374] c2161 (by decide) p (sat_cons (step1943 p h) (sat_cons (step374 p h) (sat_nil p)))
def c2162 : List Lit := [(60, true), (65, true), (190, true), (62, false)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c1943, c375] c2162 (by decide) p (sat_cons (step1943 p h) (sat_cons (step375 p h) (sat_nil p)))
def c2163 : List Lit := [(60, true), (62, false), (190, true), (63, true)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c1943, c376] c2163 (by decide) p (sat_cons (step1943 p h) (sat_cons (step376 p h) (sat_nil p)))
def c2164 : List Lit := [(63, false), (62, true)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c987, c377] c2164 (by decide) p (sat_cons (step987 p h) (sat_cons (step377 p h) (sat_nil p)))
def c2165 : List Lit := [(63, false), (29, true)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c987, c378] c2165 (by decide) p (sat_cons (step987 p h) (sat_cons (step378 p h) (sat_nil p)))
def c2166 : List Lit := [(62, true), (65, false), (55, true)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c988, c384] c2166 (by decide) p (sat_cons (step988 p h) (sat_cons (step384 p h) (sat_nil p)))
def c2167 : List Lit := [(65, false), (37, true), (62, true)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c988, c385] c2167 (by decide) p (sat_cons (step988 p h) (sat_cons (step385 p h) (sat_nil p)))
def c2168 : List Lit := [(65, false), (37, true), (55, true)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c988, c386] c2168 (by decide) p (sat_cons (step988 p h) (sat_cons (step386 p h) (sat_nil p)))
def c2169 : List Lit := [(195, true), (59, true)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c1942, c1944, c1945, c388] c2169 (by decide) p (sat_cons (step1942 p h) (sat_cons (step1944 p h) (sat_cons (step1945 p h) (sat_cons (step388 p h) (sat_nil p)))))
def c2170 : List Lit := [(70, false), (72, true), (82, true), (77, true)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c991, c399] c2170 (by decide) p (sat_cons (step991 p h) (sat_cons (step399 p h) (sat_nil p)))
def c2171 : List Lit := [(70, false), (82, true), (71, true), (77, true)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c991, c400] c2171 (by decide) p (sat_cons (step991 p h) (sat_cons (step400 p h) (sat_nil p)))
def c2172 : List Lit := [(70, false), (82, true), (72, true), (71, true)]
theorem step2172 (p : Nat → Bool) (h : Constraints p) : clause p c2172 = true :=
  Snake9.LocalRup.prove_clause [c991, c401] c2172 (by decide) p (sat_cons (step991 p h) (sat_cons (step401 p h) (sat_nil p)))
def c2173 : List Lit := [(72, true), (71, true), (77, true), (70, false)]
theorem step2173 (p : Nat → Bool) (h : Constraints p) : clause p c2173 = true :=
  Snake9.LocalRup.prove_clause [c991, c402] c2173 (by decide) p (sat_cons (step991 p h) (sat_cons (step402 p h) (sat_nil p)))
def c2174 : List Lit := [(73, false), (72, true), (71, true), (79, true), (85, true)]
theorem step2174 (p : Nat → Bool) (h : Constraints p) : clause p c2174 = true :=
  Snake9.LocalRup.prove_clause [c992, c438] c2174 (by decide) p (sat_cons (step992 p h) (sat_cons (step438 p h) (sat_nil p)))
def c2175 : List Lit := [(73, false), (69, true), (79, true), (71, true), (85, true)]
theorem step2175 (p : Nat → Bool) (h : Constraints p) : clause p c2175 = true :=
  Snake9.LocalRup.prove_clause [c992, c439] c2175 (by decide) p (sat_cons (step992 p h) (sat_cons (step439 p h) (sat_nil p)))
def c2176 : List Lit := [(73, false), (69, true), (71, true), (72, true), (85, true)]
theorem step2176 (p : Nat → Bool) (h : Constraints p) : clause p c2176 = true :=
  Snake9.LocalRup.prove_clause [c992, c440] c2176 (by decide) p (sat_cons (step992 p h) (sat_cons (step440 p h) (sat_nil p)))
def c2177 : List Lit := [(74, false), (75, true), (77, true), (86, true)]
theorem step2177 (p : Nat → Bool) (h : Constraints p) : clause p c2177 = true :=
  Snake9.LocalRup.prove_clause [c993, c445] c2177 (by decide) p (sat_cons (step993 p h) (sat_cons (step445 p h) (sat_nil p)))
def c2178 : List Lit := [(5, true), (74, false), (86, true), (77, true)]
theorem step2178 (p : Nat → Bool) (h : Constraints p) : clause p c2178 = true :=
  Snake9.LocalRup.prove_clause [c993, c446] c2178 (by decide) p (sat_cons (step993 p h) (sat_cons (step446 p h) (sat_nil p)))
def c2179 : List Lit := [(5, true), (74, false), (75, true), (77, true)]
theorem step2179 (p : Nat → Bool) (h : Constraints p) : clause p c2179 = true :=
  Snake9.LocalRup.prove_clause [c993, c447] c2179 (by decide) p (sat_cons (step993 p h) (sat_cons (step447 p h) (sat_nil p)))
def c2180 : List Lit := [(76, false), (75, true), (79, true), (89, true)]
theorem step2180 (p : Nat → Bool) (h : Constraints p) : clause p c2180 = true :=
  Snake9.LocalRup.prove_clause [c994, c460] c2180 (by decide) p (sat_cons (step994 p h) (sat_cons (step460 p h) (sat_nil p)))
def c2181 : List Lit := [(69, true), (79, true), (89, true), (76, false)]
theorem step2181 (p : Nat → Bool) (h : Constraints p) : clause p c2181 = true :=
  Snake9.LocalRup.prove_clause [c994, c461] c2181 (by decide) p (sat_cons (step994 p h) (sat_cons (step461 p h) (sat_nil p)))
def c2182 : List Lit := [(76, false), (75, true), (69, true), (89, true)]
theorem step2182 (p : Nat → Bool) (h : Constraints p) : clause p c2182 = true :=
  Snake9.LocalRup.prove_clause [c994, c462] c2182 (by decide) p (sat_cons (step994 p h) (sat_cons (step462 p h) (sat_nil p)))
def c2183 : List Lit := [(76, false), (75, true), (69, true), (79, true)]
theorem step2183 (p : Nat → Bool) (h : Constraints p) : clause p c2183 = true :=
  Snake9.LocalRup.prove_clause [c994, c463] c2183 (by decide) p (sat_cons (step994 p h) (sat_cons (step463 p h) (sat_nil p)))
def c2184 : List Lit := [(78, false), (75, true), (79, true), (77, true), (98, true), (71, true)]
theorem step2184 (p : Nat → Bool) (h : Constraints p) : clause p c2184 = true :=
  Snake9.LocalRup.prove_clause [c995, c505] c2184 (by decide) p (sat_cons (step995 p h) (sat_cons (step505 p h) (sat_nil p)))
def c2185 : List Lit := [(82, true), (100, true), (80, false), (86, true), (118, true)]
theorem step2185 (p : Nat → Bool) (h : Constraints p) : clause p c2185 = true :=
  Snake9.LocalRup.prove_clause [c996, c522] c2185 (by decide) p (sat_cons (step996 p h) (sat_cons (step522 p h) (sat_nil p)))
def c2186 : List Lit := [(80, false), (86, true), (118, true), (81, true), (100, true)]
theorem step2186 (p : Nat → Bool) (h : Constraints p) : clause p c2186 = true :=
  Snake9.LocalRup.prove_clause [c996, c523] c2186 (by decide) p (sat_cons (step996 p h) (sat_cons (step523 p h) (sat_nil p)))
def c2187 : List Lit := [(100, true), (118, true), (80, false), (81, true), (82, true)]
theorem step2187 (p : Nat → Bool) (h : Constraints p) : clause p c2187 = true :=
  Snake9.LocalRup.prove_clause [c996, c524] c2187 (by decide) p (sat_cons (step996 p h) (sat_cons (step524 p h) (sat_nil p)))
def c2188 : List Lit := [(83, false), (85, true), (71, true), (13, true)]
theorem step2188 (p : Nat → Bool) (h : Constraints p) : clause p c2188 = true :=
  Snake9.LocalRup.prove_clause [c997, c549] c2188 (by decide) p (sat_cons (step997 p h) (sat_cons (step549 p h) (sat_nil p)))
def c2189 : List Lit := [(121, true), (102, true), (81, true), (84, false), (85, true), (14, true), (82, true)]
theorem step2189 (p : Nat → Bool) (h : Constraints p) : clause p c2189 = true :=
  Snake9.LocalRup.prove_clause [c998, c585] c2189 (by decide) p (sat_cons (step998 p h) (sat_cons (step585 p h) (sat_nil p)))
def c2190 : List Lit := [(72, true), (82, true), (84, false), (102, true), (85, true), (14, true), (121, true)]
theorem step2190 (p : Nat → Bool) (h : Constraints p) : clause p c2190 = true :=
  Snake9.LocalRup.prove_clause [c998, c586] c2190 (by decide) p (sat_cons (step998 p h) (sat_cons (step586 p h) (sat_nil p)))
def c2191 : List Lit := [(121, true), (72, true), (102, true), (81, true), (85, true), (84, false), (14, true)]
theorem step2191 (p : Nat → Bool) (h : Constraints p) : clause p c2191 = true :=
  Snake9.LocalRup.prove_clause [c998, c587] c2191 (by decide) p (sat_cons (step998 p h) (sat_cons (step587 p h) (sat_nil p)))
def c2192 : List Lit := [(72, true), (82, true), (84, false), (81, true), (102, true), (14, true), (121, true)]
theorem step2192 (p : Nat → Bool) (h : Constraints p) : clause p c2192 = true :=
  Snake9.LocalRup.prove_clause [c998, c588] c2192 (by decide) p (sat_cons (step998 p h) (sat_cons (step588 p h) (sat_nil p)))
def c2193 : List Lit := [(121, true), (72, true), (81, true), (82, true), (84, false), (85, true), (14, true)]
theorem step2193 (p : Nat → Bool) (h : Constraints p) : clause p c2193 = true :=
  Snake9.LocalRup.prove_clause [c998, c589] c2193 (by decide) p (sat_cons (step998 p h) (sat_cons (step589 p h) (sat_nil p)))
def c2194 : List Lit := [(72, true), (82, true), (84, false), (81, true), (102, true), (85, true), (14, true)]
theorem step2194 (p : Nat → Bool) (h : Constraints p) : clause p c2194 = true :=
  Snake9.LocalRup.prove_clause [c998, c590] c2194 (by decide) p (sat_cons (step998 p h) (sat_cons (step590 p h) (sat_nil p)))
def c2195 : List Lit := [(75, true), (123, true), (87, false), (86, true), (89, true), (104, true)]
theorem step2195 (p : Nat → Bool) (h : Constraints p) : clause p c2195 = true :=
  Snake9.LocalRup.prove_clause [c999, c643] c2195 (by decide) p (sat_cons (step999 p h) (sat_cons (step643 p h) (sat_nil p)))
def c2196 : List Lit := [(87, false), (123, true), (104, true), (89, true), (86, true), (16, true)]
theorem step2196 (p : Nat → Bool) (h : Constraints p) : clause p c2196 = true :=
  Snake9.LocalRup.prove_clause [c999, c644] c2196 (by decide) p (sat_cons (step999 p h) (sat_cons (step644 p h) (sat_nil p)))
def c2197 : List Lit := [(123, true), (104, true), (87, false), (89, true), (75, true), (16, true)]
theorem step2197 (p : Nat → Bool) (h : Constraints p) : clause p c2197 = true :=
  Snake9.LocalRup.prove_clause [c999, c645] c2197 (by decide) p (sat_cons (step999 p h) (sat_cons (step645 p h) (sat_nil p)))
end B112E055
