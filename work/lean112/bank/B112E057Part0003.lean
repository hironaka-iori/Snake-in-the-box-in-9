import B112E057Part0002
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2217 : List Lit := [(14, true), (84, true), (15, false), (13, true), (12, true), (52, true)]
theorem step2217 (p : Nat → Bool) (h : Constraints p) : clause p c2217 = true :=
  Snake9.LocalRup.prove_clause [c973, c147] c2217 (by decide) p (sat_cons (step973 p h) (sat_cons (step147 p h) (sat_nil p)))
def c2218 : List Lit := [(14, true), (84, true), (13, true), (12, true), (20, true), (15, false)]
theorem step2218 (p : Nat → Bool) (h : Constraints p) : clause p c2218 = true :=
  Snake9.LocalRup.prove_clause [c973, c148] c2218 (by decide) p (sat_cons (step973 p h) (sat_cons (step148 p h) (sat_nil p)))
def c2219 : List Lit := [(20, true), (14, true), (12, true), (13, true), (15, false), (52, true)]
theorem step2219 (p : Nat → Bool) (h : Constraints p) : clause p c2219 = true :=
  Snake9.LocalRup.prove_clause [c973, c149] c2219 (by decide) p (sat_cons (step973 p h) (sat_cons (step149 p h) (sat_nil p)))
def c2220 : List Lit := [(20, true), (16, true), (88, true), (17, false)]
theorem step2220 (p : Nat → Bool) (h : Constraints p) : clause p c2220 = true :=
  Snake9.LocalRup.prove_clause [c974, c160] c2220 (by decide) p (sat_cons (step974 p h) (sat_cons (step160 p h) (sat_nil p)))
def c2221 : List Lit := [(20, true), (12, true), (17, false), (88, true)]
theorem step2221 (p : Nat → Bool) (h : Constraints p) : clause p c2221 = true :=
  Snake9.LocalRup.prove_clause [c974, c161] c2221 (by decide) p (sat_cons (step974 p h) (sat_cons (step161 p h) (sat_nil p)))
def c2222 : List Lit := [(12, true), (16, true), (17, false), (88, true)]
theorem step2222 (p : Nat → Bool) (h : Constraints p) : clause p c2222 = true :=
  Snake9.LocalRup.prove_clause [c974, c162] c2222 (by decide) p (sat_cons (step974 p h) (sat_cons (step162 p h) (sat_nil p)))
def c2223 : List Lit := [(20, true), (12, true), (17, false), (16, true)]
theorem step2223 (p : Nat → Bool) (h : Constraints p) : clause p c2223 = true :=
  Snake9.LocalRup.prove_clause [c974, c163] c2223 (by decide) p (sat_cons (step974 p h) (sat_cons (step163 p h) (sat_nil p)))
def c2224 : List Lit := [(20, true), (18, true), (19, false), (16, true)]
theorem step2224 (p : Nat → Bool) (h : Constraints p) : clause p c2224 = true :=
  Snake9.LocalRup.prove_clause [c975, c176] c2224 (by decide) p (sat_cons (step975 p h) (sat_cons (step176 p h) (sat_nil p)))
def c2225 : List Lit := [(20, true), (18, true), (19, false), (13, true)]
theorem step2225 (p : Nat → Bool) (h : Constraints p) : clause p c2225 = true :=
  Snake9.LocalRup.prove_clause [c975, c177] c2225 (by decide) p (sat_cons (step975 p h) (sat_cons (step177 p h) (sat_nil p)))
def c2226 : List Lit := [(20, true), (16, true), (19, false), (13, true)]
theorem step2226 (p : Nat → Bool) (h : Constraints p) : clause p c2226 = true :=
  Snake9.LocalRup.prove_clause [c975, c178] c2226 (by decide) p (sat_cons (step975 p h) (sat_cons (step178 p h) (sat_nil p)))
def c2227 : List Lit := [(18, true), (16, true), (13, true), (19, false)]
theorem step2227 (p : Nat → Bool) (h : Constraints p) : clause p c2227 = true :=
  Snake9.LocalRup.prove_clause [c975, c179] c2227 (by decide) p (sat_cons (step975 p h) (sat_cons (step179 p h) (sat_nil p)))
def c2228 : List Lit := [(24, true), (32, true), (22, false)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c976, c194] c2228 (by decide) p (sat_cons (step976 p h) (sat_cons (step194 p h) (sat_nil p)))
def c2229 : List Lit := [(32, true), (22, false), (23, true)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c976, c195] c2229 (by decide) p (sat_cons (step976 p h) (sat_cons (step195 p h) (sat_nil p)))
def c2230 : List Lit := [(24, true), (22, false), (23, true)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c976, c196] c2230 (by decide) p (sat_cons (step976 p h) (sat_cons (step196 p h) (sat_nil p)))
def c2231 : List Lit := [(29, true), (24, true), (23, true), (25, false)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c977, c223] c2231 (by decide) p (sat_cons (step977 p h) (sat_cons (step223 p h) (sat_nil p)))
def c2232 : List Lit := [(21, true), (29, true), (25, false), (23, true)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c977, c224] c2232 (by decide) p (sat_cons (step977 p h) (sat_cons (step224 p h) (sat_nil p)))
def c2233 : List Lit := [(27, true), (34, true), (26, false)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c978, c226] c2233 (by decide) p (sat_cons (step978 p h) (sat_cons (step226 p h) (sat_nil p)))
def c2234 : List Lit := [(34, true), (5, true), (26, false)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c978, c227] c2234 (by decide) p (sat_cons (step978 p h) (sat_cons (step227 p h) (sat_nil p)))
def c2235 : List Lit := [(27, true), (5, true), (26, false)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c978, c228] c2235 (by decide) p (sat_cons (step978 p h) (sat_cons (step228 p h) (sat_nil p)))
def c2236 : List Lit := [(29, true), (27, true), (28, false)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c979, c233] c2236 (by decide) p (sat_cons (step979 p h) (sat_cons (step233 p h) (sat_nil p)))
def c2237 : List Lit := [(29, true), (21, true), (28, false)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c979, c234] c2237 (by decide) p (sat_cons (step979 p h) (sat_cons (step234 p h) (sat_nil p)))
def c2238 : List Lit := [(21, true), (27, true), (28, false)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c979, c235] c2238 (by decide) p (sat_cons (step979 p h) (sat_cons (step235 p h) (sat_nil p)))
def c2239 : List Lit := [(32, true), (33, false), (23, true)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c981, c256] c2239 (by decide) p (sat_cons (step981 p h) (sat_cons (step256 p h) (sat_nil p)))
def c2240 : List Lit := [(32, true), (13, true), (33, false)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c981, c257] c2240 (by decide) p (sat_cons (step981 p h) (sat_cons (step257 p h) (sat_nil p)))
def c2241 : List Lit := [(13, true), (33, false), (23, true)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c981, c258] c2241 (by decide) p (sat_cons (step981 p h) (sat_cons (step258 p h) (sat_nil p)))
def c2242 : List Lit := [(34, true), (37, true), (35, false)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c982, c267] c2242 (by decide) p (sat_cons (step982 p h) (sat_cons (step267 p h) (sat_nil p)))
def c2243 : List Lit := [(31, true), (37, true), (35, false)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c982, c268] c2243 (by decide) p (sat_cons (step982 p h) (sat_cons (step268 p h) (sat_nil p)))
def c2244 : List Lit := [(31, true), (34, true), (35, false)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c982, c269] c2244 (by decide) p (sat_cons (step982 p h) (sat_cons (step269 p h) (sat_nil p)))
def c2245 : List Lit := [(18, true), (34, true), (106, true), (37, true), (36, false)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c983, c277] c2245 (by decide) p (sat_cons (step983 p h) (sat_cons (step277 p h) (sat_nil p)))
def c2246 : List Lit := [(18, true), (32, true), (106, true), (37, true), (36, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c983, c278] c2246 (by decide) p (sat_cons (step983 p h) (sat_cons (step278 p h) (sat_nil p)))
def c2247 : List Lit := [(41, true), (39, false), (49, true)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c984, c285] c2247 (by decide) p (sat_cons (step984 p h) (sat_cons (step285 p h) (sat_nil p)))
def c2248 : List Lit := [(49, true), (39, false), (40, true)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c984, c286] c2248 (by decide) p (sat_cons (step984 p h) (sat_cons (step286 p h) (sat_nil p)))
def c2249 : List Lit := [(41, true), (39, false), (40, true)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c984, c287] c2249 (by decide) p (sat_cons (step984 p h) (sat_cons (step287 p h) (sat_nil p)))
def c2250 : List Lit := [(41, true), (52, true), (40, true), (42, false)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c985, c326] c2250 (by decide) p (sat_cons (step985 p h) (sat_cons (step326 p h) (sat_nil p)))
def c2251 : List Lit := [(52, true), (38, true), (42, false), (40, true)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c985, c327] c2251 (by decide) p (sat_cons (step985 p h) (sat_cons (step327 p h) (sat_nil p)))
def c2252 : List Lit := [(5, true), (53, true), (43, false), (45, true)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c986, c330] c2252 (by decide) p (sat_cons (step986 p h) (sat_cons (step330 p h) (sat_nil p)))
def c2253 : List Lit := [(5, true), (44, true), (43, false), (45, true)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c986, c331] c2253 (by decide) p (sat_cons (step986 p h) (sat_cons (step331 p h) (sat_nil p)))
def c2254 : List Lit := [(44, true), (45, true), (46, false)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c987, c358] c2254 (by decide) p (sat_cons (step987 p h) (sat_cons (step358 p h) (sat_nil p)))
def c2255 : List Lit := [(45, true), (38, true), (46, false)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c987, c359] c2255 (by decide) p (sat_cons (step987 p h) (sat_cons (step359 p h) (sat_nil p)))
def c2256 : List Lit := [(38, true), (44, true), (46, false)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c987, c360] c2256 (by decide) p (sat_cons (step987 p h) (sat_cons (step360 p h) (sat_nil p)))
def c2257 : List Lit := [(40, true), (47, false), (115, true)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c988, c362] c2257 (by decide) p (sat_cons (step988 p h) (sat_cons (step362 p h) (sat_nil p)))
def c2258 : List Lit := [(44, true), (40, true), (47, false)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c988, c363] c2258 (by decide) p (sat_cons (step988 p h) (sat_cons (step363 p h) (sat_nil p)))
def c2259 : List Lit := [(63, true), (117, true), (48, false), (53, true)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c989, c366] c2259 (by decide) p (sat_cons (step989 p h) (sat_cons (step366 p h) (sat_nil p)))
def c2260 : List Lit := [(63, true), (117, true), (48, false), (49, true)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c989, c367] c2260 (by decide) p (sat_cons (step989 p h) (sat_cons (step367 p h) (sat_nil p)))
def c2261 : List Lit := [(52, true), (49, true), (40, true), (50, false)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c990, c379] c2261 (by decide) p (sat_cons (step990 p h) (sat_cons (step379 p h) (sat_nil p)))
def c2262 : List Lit := [(52, true), (49, true), (13, true), (50, false)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c990, c380] c2262 (by decide) p (sat_cons (step990 p h) (sat_cons (step380 p h) (sat_nil p)))
def c2263 : List Lit := [(52, true), (50, false), (40, true), (13, true)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c990, c381] c2263 (by decide) p (sat_cons (step990 p h) (sat_cons (step381 p h) (sat_nil p)))
def c2264 : List Lit := [(49, true), (50, false), (40, true), (13, true)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c990, c382] c2264 (by decide) p (sat_cons (step990 p h) (sat_cons (step382 p h) (sat_nil p)))
def c2265 : List Lit := [(53, true), (55, true), (54, false)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c992, c405] c2265 (by decide) p (sat_cons (step992 p h) (sat_cons (step405 p h) (sat_nil p)))
def c2266 : List Lit := [(55, true), (54, false), (45, true)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c992, c406] c2266 (by decide) p (sat_cons (step992 p h) (sat_cons (step406 p h) (sat_nil p)))
def c2267 : List Lit := [(53, true), (54, false), (45, true)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c992, c407] c2267 (by decide) p (sat_cons (step992 p h) (sat_cons (step407 p h) (sat_nil p)))
def c2268 : List Lit := [(63, true), (58, true), (56, false)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c993, c413] c2268 (by decide) p (sat_cons (step993 p h) (sat_cons (step413 p h) (sat_nil p)))
def c2269 : List Lit := [(63, true), (57, true), (56, false)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c993, c414] c2269 (by decide) p (sat_cons (step993 p h) (sat_cons (step414 p h) (sat_nil p)))
def c2270 : List Lit := [(58, true), (57, true), (56, false)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c993, c415] c2270 (by decide) p (sat_cons (step993 p h) (sat_cons (step415 p h) (sat_nil p)))
def c2271 : List Lit := [(23, false), (59, false), (40, false)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c2025, c420] c2271 (by decide) p (sat_cons (step2025 p h) (sat_cons (step420 p h) (sat_nil p)))
def c2272 : List Lit := [(57, false), (23, false), (59, false)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c2025, c421] c2272 (by decide) p (sat_cons (step2025 p h) (sat_cons (step421 p h) (sat_nil p)))
def c2273 : List Lit := [(57, false), (59, false), (40, false)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c2025, c422] c2273 (by decide) p (sat_cons (step2025 p h) (sat_cons (step422 p h) (sat_nil p)))
def c2274 : List Lit := [(57, true), (59, false), (40, true), (23, true)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c994, c423] c2274 (by decide) p (sat_cons (step994 p h) (sat_cons (step423 p h) (sat_nil p)))
def c2275 : List Lit := [(58, true), (62, true), (60, false)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c995, c425] c2275 (by decide) p (sat_cons (step995 p h) (sat_cons (step425 p h) (sat_nil p)))
def c2276 : List Lit := [(62, true), (45, true), (60, false)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c995, c426] c2276 (by decide) p (sat_cons (step995 p h) (sat_cons (step426 p h) (sat_nil p)))
def c2277 : List Lit := [(58, true), (45, true), (60, false)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c995, c427] c2277 (by decide) p (sat_cons (step995 p h) (sat_cons (step427 p h) (sat_nil p)))
def c2278 : List Lit := [(62, false), (64, true), (189, true)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c2026, c429] c2278 (by decide) p (sat_cons (step2026 p h) (sat_cons (step429 p h) (sat_nil p)))
def c2279 : List Lit := [(62, false), (60, true), (189, true)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c2026, c430] c2279 (by decide) p (sat_cons (step2026 p h) (sat_cons (step430 p h) (sat_nil p)))
def c2280 : List Lit := [(55, true), (62, true), (64, false)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c997, c435] c2280 (by decide) p (sat_cons (step997 p h) (sat_cons (step435 p h) (sat_nil p)))
end B112E057
