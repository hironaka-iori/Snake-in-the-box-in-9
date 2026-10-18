import B112E089Part0002
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2204 : List Lit := [(31, true), (34, true), (28, false), (72, true)]
theorem step2204 (p : Nat → Bool) (h : Constraints p) : clause p c2204 = true :=
  Snake9.LocalRup.prove_clause [c983, c168] c2204 (by decide) p (sat_cons (step983 p h) (sat_cons (step168 p h) (sat_nil p)))
def c2205 : List Lit := [(34, true), (13, true), (28, false), (72, true)]
theorem step2205 (p : Nat → Bool) (h : Constraints p) : clause p c2205 = true :=
  Snake9.LocalRup.prove_clause [c983, c169] c2205 (by decide) p (sat_cons (step983 p h) (sat_cons (step169 p h) (sat_nil p)))
def c2206 : List Lit := [(30, false), (31, true)]
theorem step2206 (p : Nat → Bool) (h : Constraints p) : clause p c2206 = true :=
  Snake9.LocalRup.prove_clause [c984, c175] c2206 (by decide) p (sat_cons (step984 p h) (sat_cons (step175 p h) (sat_nil p)))
def c2207 : List Lit := [(30, false), (29, true)]
theorem step2207 (p : Nat → Bool) (h : Constraints p) : clause p c2207 = true :=
  Snake9.LocalRup.prove_clause [c984, c176] c2207 (by decide) p (sat_cons (step984 p h) (sat_cons (step176 p h) (sat_nil p)))
def c2208 : List Lit := [(33, false), (34, true), (75, true)]
theorem step2208 (p : Nat → Bool) (h : Constraints p) : clause p c2208 = true :=
  Snake9.LocalRup.prove_clause [c985, c192] c2208 (by decide) p (sat_cons (step985 p h) (sat_cons (step192 p h) (sat_nil p)))
def c2209 : List Lit := [(33, false), (32, true), (75, true)]
theorem step2209 (p : Nat → Bool) (h : Constraints p) : clause p c2209 = true :=
  Snake9.LocalRup.prove_clause [c985, c193] c2209 (by decide) p (sat_cons (step985 p h) (sat_cons (step193 p h) (sat_nil p)))
def c2210 : List Lit := [(33, false), (34, true), (32, true)]
theorem step2210 (p : Nat → Bool) (h : Constraints p) : clause p c2210 = true :=
  Snake9.LocalRup.prove_clause [c985, c194] c2210 (by decide) p (sat_cons (step985 p h) (sat_cons (step194 p h) (sat_nil p)))
def c2211 : List Lit := [(35, false), (34, true), (31, true)]
theorem step2211 (p : Nat → Bool) (h : Constraints p) : clause p c2211 = true :=
  Snake9.LocalRup.prove_clause [c986, c203] c2211 (by decide) p (sat_cons (step986 p h) (sat_cons (step203 p h) (sat_nil p)))
def c2212 : List Lit := [(35, false), (34, true), (27, true)]
theorem step2212 (p : Nat → Bool) (h : Constraints p) : clause p c2212 = true :=
  Snake9.LocalRup.prove_clause [c986, c204] c2212 (by decide) p (sat_cons (step986 p h) (sat_cons (step204 p h) (sat_nil p)))
def c2213 : List Lit := [(35, false), (31, true), (27, true)]
theorem step2213 (p : Nat → Bool) (h : Constraints p) : clause p c2213 = true :=
  Snake9.LocalRup.prove_clause [c986, c205] c2213 (by decide) p (sat_cons (step986 p h) (sat_cons (step205 p h) (sat_nil p)))
def c2214 : List Lit := [(37, false), (42, true), (91, true), (57, true)]
theorem step2214 (p : Nat → Bool) (h : Constraints p) : clause p c2214 = true :=
  Snake9.LocalRup.prove_clause [c988, c212] c2214 (by decide) p (sat_cons (step988 p h) (sat_cons (step212 p h) (sat_nil p)))
def c2215 : List Lit := [(38, false), (47, true), (44, true)]
theorem step2215 (p : Nat → Bool) (h : Constraints p) : clause p c2215 = true :=
  Snake9.LocalRup.prove_clause [c989, c214] c2215 (by decide) p (sat_cons (step989 p h) (sat_cons (step214 p h) (sat_nil p)))
def c2216 : List Lit := [(47, true), (38, false), (39, true)]
theorem step2216 (p : Nat → Bool) (h : Constraints p) : clause p c2216 = true :=
  Snake9.LocalRup.prove_clause [c989, c215] c2216 (by decide) p (sat_cons (step989 p h) (sat_cons (step215 p h) (sat_nil p)))
def c2217 : List Lit := [(38, false), (39, true), (44, true)]
theorem step2217 (p : Nat → Bool) (h : Constraints p) : clause p c2217 = true :=
  Snake9.LocalRup.prove_clause [c989, c216] c2217 (by decide) p (sat_cons (step989 p h) (sat_cons (step216 p h) (sat_nil p)))
def c2218 : List Lit := [(40, false), (41, true), (62, true), (44, true), (42, true)]
theorem step2218 (p : Nat → Bool) (h : Constraints p) : clause p c2218 = true :=
  Snake9.LocalRup.prove_clause [c990, c234] c2218 (by decide) p (sat_cons (step990 p h) (sat_cons (step234 p h) (sat_nil p)))
def c2219 : List Lit := [(48, false), (50, true), (47, true)]
theorem step2219 (p : Nat → Bool) (h : Constraints p) : clause p c2219 = true :=
  Snake9.LocalRup.prove_clause [c992, c319] c2219 (by decide) p (sat_cons (step992 p h) (sat_cons (step319 p h) (sat_nil p)))
def c2220 : List Lit := [(48, false), (50, true), (46, true)]
theorem step2220 (p : Nat → Bool) (h : Constraints p) : clause p c2220 = true :=
  Snake9.LocalRup.prove_clause [c992, c320] c2220 (by decide) p (sat_cons (step992 p h) (sat_cons (step320 p h) (sat_nil p)))
def c2221 : List Lit := [(48, false), (47, true), (46, true)]
theorem step2221 (p : Nat → Bool) (h : Constraints p) : clause p c2221 = true :=
  Snake9.LocalRup.prove_clause [c992, c321] c2221 (by decide) p (sat_cons (step992 p h) (sat_cons (step321 p h) (sat_nil p)))
def c2222 : List Lit := [(103, true), (14, true), (50, true), (49, false), (73, true), (47, true)]
theorem step2222 (p : Nat → Bool) (h : Constraints p) : clause p c2222 = true :=
  Snake9.LocalRup.prove_clause [c993, c342] c2222 (by decide) p (sat_cons (step993 p h) (sat_cons (step342 p h) (sat_nil p)))
def c2223 : List Lit := [(14, true), (50, true), (103, true), (49, false), (73, true), (39, true)]
theorem step2223 (p : Nat → Bool) (h : Constraints p) : clause p c2223 = true :=
  Snake9.LocalRup.prove_clause [c993, c343] c2223 (by decide) p (sat_cons (step993 p h) (sat_cons (step343 p h) (sat_nil p)))
def c2224 : List Lit := [(103, true), (14, true), (73, true), (49, false), (39, true), (47, true)]
theorem step2224 (p : Nat → Bool) (h : Constraints p) : clause p c2224 = true :=
  Snake9.LocalRup.prove_clause [c993, c344] c2224 (by decide) p (sat_cons (step993 p h) (sat_cons (step344 p h) (sat_nil p)))
def c2225 : List Lit := [(52, false), (41, true), (46, true), (54, true)]
theorem step2225 (p : Nat → Bool) (h : Constraints p) : clause p c2225 = true :=
  Snake9.LocalRup.prove_clause [c994, c363] c2225 (by decide) p (sat_cons (step994 p h) (sat_cons (step363 p h) (sat_nil p)))
def c2226 : List Lit := [(54, true), (53, false), (51, true), (75, true)]
theorem step2226 (p : Nat → Bool) (h : Constraints p) : clause p c2226 = true :=
  Snake9.LocalRup.prove_clause [c995, c368] c2226 (by decide) p (sat_cons (step995 p h) (sat_cons (step368 p h) (sat_nil p)))
def c2227 : List Lit := [(53, false), (54, true), (42, true), (75, true)]
theorem step2227 (p : Nat → Bool) (h : Constraints p) : clause p c2227 = true :=
  Snake9.LocalRup.prove_clause [c995, c369] c2227 (by decide) p (sat_cons (step995 p h) (sat_cons (step369 p h) (sat_nil p)))
def c2228 : List Lit := [(53, false), (51, true), (75, true), (42, true)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c995, c370] c2228 (by decide) p (sat_cons (step995 p h) (sat_cons (step370 p h) (sat_nil p)))
def c2229 : List Lit := [(55, false), (54, true), (50, true)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c996, c381] c2229 (by decide) p (sat_cons (step996 p h) (sat_cons (step381 p h) (sat_nil p)))
def c2230 : List Lit := [(55, false), (54, true), (45, true)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c996, c382] c2230 (by decide) p (sat_cons (step996 p h) (sat_cons (step382 p h) (sat_nil p)))
def c2231 : List Lit := [(55, false), (50, true), (45, true)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c996, c383] c2231 (by decide) p (sat_cons (step996 p h) (sat_cons (step383 p h) (sat_nil p)))
def c2232 : List Lit := [(58, false), (56, true), (57, true), (64, true), (72, true)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c997, c426] c2232 (by decide) p (sat_cons (step997 p h) (sat_cons (step426 p h) (sat_nil p)))
def c2233 : List Lit := [(58, false), (56, true), (57, true), (61, true), (72, true)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c997, c427] c2233 (by decide) p (sat_cons (step997 p h) (sat_cons (step427 p h) (sat_nil p)))
def c2234 : List Lit := [(59, false), (61, true), (66, true)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c998, c429] c2234 (by decide) p (sat_cons (step998 p h) (sat_cons (step429 p h) (sat_nil p)))
def c2235 : List Lit := [(59, false), (56, true), (66, true)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c998, c430] c2235 (by decide) p (sat_cons (step998 p h) (sat_cons (step430 p h) (sat_nil p)))
def c2236 : List Lit := [(59, false), (56, true), (61, true)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c998, c431] c2236 (by decide) p (sat_cons (step998 p h) (sat_cons (step431 p h) (sat_nil p)))
def c2237 : List Lit := [(41, true), (113, true), (63, false), (62, true), (64, true), (56, true), (66, true)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c1000, c531] c2237 (by decide) p (sat_cons (step1000 p h) (sat_cons (step531 p h) (sat_nil p)))
def c2238 : List Lit := [(24, true), (41, true), (56, true), (63, false), (64, true), (66, true), (113, true)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c1000, c532] c2238 (by decide) p (sat_cons (step1000 p h) (sat_cons (step532 p h) (sat_nil p)))
def c2239 : List Lit := [(65, false), (66, true), (62, true), (76, true), (44, true), (67, true)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c1001, c563] c2239 (by decide) p (sat_cons (step1001 p h) (sat_cons (step563 p h) (sat_nil p)))
def c2240 : List Lit := [(65, false), (76, true), (66, true), (62, true), (67, true), (25, true)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c1001, c564] c2240 (by decide) p (sat_cons (step1001 p h) (sat_cons (step564 p h) (sat_nil p)))
def c2241 : List Lit := [(66, true), (44, true), (65, false), (62, true), (25, true), (67, true)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c1001, c565] c2241 (by decide) p (sat_cons (step1001 p h) (sat_cons (step565 p h) (sat_nil p)))
def c2242 : List Lit := [(115, true), (61, true), (68, false), (64, true), (45, true), (67, true), (66, true)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c1002, c628] c2242 (by decide) p (sat_cons (step1002 p h) (sat_cons (step628 p h) (sat_nil p)))
def c2243 : List Lit := [(27, true), (115, true), (61, true), (68, false), (66, true), (67, true), (64, true)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c1002, c629] c2243 (by decide) p (sat_cons (step1002 p h) (sat_cons (step629 p h) (sat_nil p)))
def c2244 : List Lit := [(27, true), (115, true), (68, false), (64, true), (45, true), (67, true), (66, true)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c1002, c630] c2244 (by decide) p (sat_cons (step1002 p h) (sat_cons (step630 p h) (sat_nil p)))
def c2245 : List Lit := [(27, true), (61, true), (68, false), (66, true), (45, true), (67, true), (115, true)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c1002, c631] c2245 (by decide) p (sat_cons (step1002 p h) (sat_cons (step631 p h) (sat_nil p)))
def c2246 : List Lit := [(27, true), (61, true), (68, false), (45, true), (64, true), (115, true), (67, true)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c1002, c632] c2246 (by decide) p (sat_cons (step1002 p h) (sat_cons (step632 p h) (sat_nil p)))
def c2247 : List Lit := [(27, true), (61, true), (68, false), (45, true), (64, true), (66, true), (115, true)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c1002, c633] c2247 (by decide) p (sat_cons (step1002 p h) (sat_cons (step633 p h) (sat_nil p)))
def c2248 : List Lit := [(27, true), (45, true), (68, false), (67, true), (64, true), (66, true), (61, true)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c1002, c634] c2248 (by decide) p (sat_cons (step1002 p h) (sat_cons (step634 p h) (sat_nil p)))
def c2249 : List Lit := [(56, true), (46, true), (72, true), (70, false)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c1003, c647] c2249 (by decide) p (sat_cons (step1003 p h) (sat_cons (step647 p h) (sat_nil p)))
def c2250 : List Lit := [(57, true), (73, true), (72, true), (75, true), (71, false)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c1004, c658] c2250 (by decide) p (sat_cons (step1004 p h) (sat_cons (step658 p h) (sat_nil p)))
def c2251 : List Lit := [(57, true), (73, true), (75, true), (69, true), (71, false)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c1004, c659] c2251 (by decide) p (sat_cons (step1004 p h) (sat_cons (step659 p h) (sat_nil p)))
def c2252 : List Lit := [(71, false), (57, true), (75, true), (69, true), (72, true)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c1004, c660] c2252 (by decide) p (sat_cons (step1004 p h) (sat_cons (step660 p h) (sat_nil p)))
def c2253 : List Lit := [(120, true), (76, true), (62, true), (51, true), (69, true), (74, false), (75, true)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c1005, c716] c2253 (by decide) p (sat_cons (step1005 p h) (sat_cons (step716 p h) (sat_nil p)))
def c2254 : List Lit := [(69, true), (120, true), (74, false), (62, true), (75, true), (32, true), (76, true)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c1005, c717] c2254 (by decide) p (sat_cons (step1005 p h) (sat_cons (step717 p h) (sat_nil p)))
def c2255 : List Lit := [(120, true), (69, true), (76, true), (51, true), (75, true), (74, false), (32, true)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c1005, c718] c2255 (by decide) p (sat_cons (step1005 p h) (sat_cons (step718 p h) (sat_nil p)))
def c2256 : List Lit := [(76, true), (32, true), (74, false), (51, true), (75, true), (62, true), (120, true)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c1005, c719] c2256 (by decide) p (sat_cons (step1005 p h) (sat_cons (step719 p h) (sat_nil p)))
def c2257 : List Lit := [(32, true), (51, true), (76, true), (62, true), (120, true), (69, true), (74, false)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c1005, c720] c2257 (by decide) p (sat_cons (step1005 p h) (sat_cons (step720 p h) (sat_nil p)))
def c2258 : List Lit := [(120, true), (69, true), (32, true), (75, true), (62, true), (51, true), (74, false)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c1005, c721] c2258 (by decide) p (sat_cons (step1005 p h) (sat_cons (step721 p h) (sat_nil p)))
def c2259 : List Lit := [(76, true), (69, true), (32, true), (62, true), (75, true), (51, true), (74, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c1005, c722] c2259 (by decide) p (sat_cons (step1005 p h) (sat_cons (step722 p h) (sat_nil p)))
def c2260 : List Lit := [(77, false), (123, true), (76, true)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c1006, c751] c2260 (by decide) p (sat_cons (step1006 p h) (sat_cons (step751 p h) (sat_nil p)))
def c2261 : List Lit := [(77, false), (123, true), (66, true)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c1006, c752] c2261 (by decide) p (sat_cons (step1006 p h) (sat_cons (step752 p h) (sat_nil p)))
def c2262 : List Lit := [(77, false), (66, true), (76, true)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c1006, c753] c2262 (by decide) p (sat_cons (step1006 p h) (sat_cons (step753 p h) (sat_nil p)))
def c2263 : List Lit := [(78, false), (76, true), (75, true), (73, true)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c1007, c758] c2263 (by decide) p (sat_cons (step1007 p h) (sat_cons (step758 p h) (sat_nil p)))
def c2264 : List Lit := [(78, false), (76, true), (75, true), (67, true)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c1007, c759] c2264 (by decide) p (sat_cons (step1007 p h) (sat_cons (step759 p h) (sat_nil p)))
def c2265 : List Lit := [(78, false), (76, true), (67, true), (73, true)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c1007, c760] c2265 (by decide) p (sat_cons (step1007 p h) (sat_cons (step760 p h) (sat_nil p)))
def c2266 : List Lit := [(78, false), (73, true), (75, true), (67, true)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c1007, c761] c2266 (by decide) p (sat_cons (step1007 p h) (sat_cons (step761 p h) (sat_nil p)))
def c2267 : List Lit := [(86, true), (95, true), (81, false), (205, true)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c2012, c2013, c768] c2267 (by decide) p (sat_cons (step2012 p h) (sat_cons (step2013 p h) (sat_cons (step768 p h) (sat_nil p))))
end B112E089
