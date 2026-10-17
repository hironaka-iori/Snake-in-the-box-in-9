import B112E052Part0003
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2246 : List Lit := [(37, true), (32, true), (36, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c987, c149] c2246 (by decide) p (sat_cons (step987 p h) (sat_cons (step149 p h) (sat_nil p)))
def c2247 : List Lit := [(37, true), (39, false), (22, true), (34, true), (38, true)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c988, c164] c2247 (by decide) p (sat_cons (step988 p h) (sat_cons (step164 p h) (sat_nil p)))
def c2248 : List Lit := [(41, true), (48, true), (44, true), (42, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c989, c170] c2248 (by decide) p (sat_cons (step989 p h) (sat_cons (step170 p h) (sat_nil p)))
def c2249 : List Lit := [(40, true), (48, true), (44, true), (42, false)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c989, c171] c2249 (by decide) p (sat_cons (step989 p h) (sat_cons (step171 p h) (sat_nil p)))
def c2250 : List Lit := [(41, true), (40, true), (42, false), (44, true)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c989, c172] c2250 (by decide) p (sat_cons (step989 p h) (sat_cons (step172 p h) (sat_nil p)))
def c2251 : List Lit := [(41, true), (43, false), (44, true)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c990, c173] c2251 (by decide) p (sat_cons (step990 p h) (sat_cons (step173 p h) (sat_nil p)))
def c2252 : List Lit := [(34, true), (43, false), (44, true)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c990, c174] c2252 (by decide) p (sat_cons (step990 p h) (sat_cons (step174 p h) (sat_nil p)))
def c2253 : List Lit := [(41, true), (34, true), (43, false)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c990, c175] c2253 (by decide) p (sat_cons (step990 p h) (sat_cons (step175 p h) (sat_nil p)))
def c2254 : List Lit := [(48, true), (45, false), (47, true)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c991, c199] c2254 (by decide) p (sat_cons (step991 p h) (sat_cons (step199 p h) (sat_nil p)))
def c2255 : List Lit := [(40, true), (48, true), (45, false)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c991, c200] c2255 (by decide) p (sat_cons (step991 p h) (sat_cons (step200 p h) (sat_nil p)))
def c2256 : List Lit := [(40, true), (45, false), (47, true)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c991, c201] c2256 (by decide) p (sat_cons (step991 p h) (sat_cons (step201 p h) (sat_nil p)))
def c2257 : List Lit := [(47, true), (46, false), (124, true)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c992, c203] c2257 (by decide) p (sat_cons (step992 p h) (sat_cons (step203 p h) (sat_nil p)))
def c2258 : List Lit := [(37, true), (46, false), (124, true)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c992, c204] c2258 (by decide) p (sat_cons (step992 p h) (sat_cons (step204 p h) (sat_nil p)))
def c2259 : List Lit := [(61, true), (55, true), (50, true), (51, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c993, c225] c2259 (by decide) p (sat_cons (step993 p h) (sat_cons (step225 p h) (sat_nil p)))
def c2260 : List Lit := [(61, true), (49, true), (55, true), (51, false)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c993, c226] c2260 (by decide) p (sat_cons (step993 p h) (sat_cons (step226 p h) (sat_nil p)))
def c2261 : List Lit := [(61, true), (49, true), (51, false), (50, true)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c993, c227] c2261 (by decide) p (sat_cons (step993 p h) (sat_cons (step227 p h) (sat_nil p)))
def c2262 : List Lit := [(49, true), (55, true), (50, true), (51, false)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c993, c228] c2262 (by decide) p (sat_cons (step993 p h) (sat_cons (step228 p h) (sat_nil p)))
def c2263 : List Lit := [(69, true), (52, true), (88, true), (57, true), (53, false)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c994, c235] c2263 (by decide) p (sat_cons (step994 p h) (sat_cons (step235 p h) (sat_nil p)))
def c2264 : List Lit := [(49, true), (69, true), (57, true), (88, true), (53, false)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c994, c236] c2264 (by decide) p (sat_cons (step994 p h) (sat_cons (step236 p h) (sat_nil p)))
def c2265 : List Lit := [(49, true), (52, true), (88, true), (53, false), (69, true)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c994, c237] c2265 (by decide) p (sat_cons (step994 p h) (sat_cons (step237 p h) (sat_nil p)))
def c2266 : List Lit := [(49, true), (52, true), (53, false), (57, true), (88, true)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c994, c238] c2266 (by decide) p (sat_cons (step994 p h) (sat_cons (step238 p h) (sat_nil p)))
def c2267 : List Lit := [(49, true), (69, true), (57, true), (53, false), (52, true)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c994, c239] c2267 (by decide) p (sat_cons (step994 p h) (sat_cons (step239 p h) (sat_nil p)))
def c2268 : List Lit := [(55, true), (92, true), (57, true), (54, false)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c995, c242] c2268 (by decide) p (sat_cons (step995 p h) (sat_cons (step242 p h) (sat_nil p)))
def c2269 : List Lit := [(49, true), (92, true), (57, true), (54, false)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c995, c243] c2269 (by decide) p (sat_cons (step995 p h) (sat_cons (step243 p h) (sat_nil p)))
def c2270 : List Lit := [(49, true), (55, true), (54, false), (92, true)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c995, c244] c2270 (by decide) p (sat_cons (step995 p h) (sat_cons (step244 p h) (sat_nil p)))
def c2271 : List Lit := [(55, true), (49, true), (54, false), (57, true)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c995, c245] c2271 (by decide) p (sat_cons (step995 p h) (sat_cons (step245 p h) (sat_nil p)))
def c2272 : List Lit := [(74, true), (64, true), (56, false), (52, true), (57, true)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c996, c256] c2272 (by decide) p (sat_cons (step996 p h) (sat_cons (step256 p h) (sat_nil p)))
def c2273 : List Lit := [(74, true), (52, true), (56, false), (57, true), (58, true)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c996, c257] c2273 (by decide) p (sat_cons (step996 p h) (sat_cons (step257 p h) (sat_nil p)))
def c2274 : List Lit := [(64, true), (56, false), (58, true), (52, true), (57, true)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c996, c258] c2274 (by decide) p (sat_cons (step996 p h) (sat_cons (step258 p h) (sat_nil p)))
def c2275 : List Lit := [(59, true), (61, true), (60, false)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c997, c270] c2275 (by decide) p (sat_cons (step997 p h) (sat_cons (step270 p h) (sat_nil p)))
def c2276 : List Lit := [(61, true), (50, true), (60, false)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c997, c271] c2276 (by decide) p (sat_cons (step997 p h) (sat_cons (step271 p h) (sat_nil p)))
def c2277 : List Lit := [(59, true), (50, true), (60, false)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c997, c272] c2277 (by decide) p (sat_cons (step997 p h) (sat_cons (step272 p h) (sat_nil p)))
def c2278 : List Lit := [(66, true), (62, false), (79, true), (101, true)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c998, c278] c2278 (by decide) p (sat_cons (step998 p h) (sat_cons (step278 p h) (sat_nil p)))
def c2279 : List Lit := [(61, true), (62, false), (101, true), (79, true)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c998, c279] c2279 (by decide) p (sat_cons (step998 p h) (sat_cons (step279 p h) (sat_nil p)))
def c2280 : List Lit := [(66, true), (61, true), (62, false), (101, true)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c998, c280] c2280 (by decide) p (sat_cons (step998 p h) (sat_cons (step280 p h) (sat_nil p)))
def c2281 : List Lit := [(66, true), (61, true), (62, false), (79, true)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c998, c281] c2281 (by decide) p (sat_cons (step998 p h) (sat_cons (step281 p h) (sat_nil p)))
def c2282 : List Lit := [(80, true), (64, true), (63, false)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c999, c282] c2282 (by decide) p (sat_cons (step999 p h) (sat_cons (step282 p h) (sat_nil p)))
def c2283 : List Lit := [(59, true), (80, true), (63, false)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c999, c283] c2283 (by decide) p (sat_cons (step999 p h) (sat_cons (step283 p h) (sat_nil p)))
def c2284 : List Lit := [(66, true), (64, true), (65, false), (106, true)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c1000, c289] c2284 (by decide) p (sat_cons (step1000 p h) (sat_cons (step289 p h) (sat_nil p)))
def c2285 : List Lit := [(58, true), (66, true), (65, false), (106, true)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1000, c290] c2285 (by decide) p (sat_cons (step1000 p h) (sat_cons (step290 p h) (sat_nil p)))
def c2286 : List Lit := [(58, true), (64, true), (65, false), (106, true)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c1000, c291] c2286 (by decide) p (sat_cons (step1000 p h) (sat_cons (step291 p h) (sat_nil p)))
def c2287 : List Lit := [(64, true), (66, true), (65, false), (58, true)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c1000, c292] c2287 (by decide) p (sat_cons (step1000 p h) (sat_cons (step292 p h) (sat_nil p)))
def c2288 : List Lit := [(70, true), (73, true), (67, false), (50, true)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c1001, c303] c2288 (by decide) p (sat_cons (step1001 p h) (sat_cons (step303 p h) (sat_nil p)))
def c2289 : List Lit := [(2, true), (73, true), (67, false), (50, true)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1001, c304] c2289 (by decide) p (sat_cons (step1001 p h) (sat_cons (step304 p h) (sat_nil p)))
def c2290 : List Lit := [(2, true), (70, true), (50, true), (67, false)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c1001, c305] c2290 (by decide) p (sat_cons (step1001 p h) (sat_cons (step305 p h) (sat_nil p)))
def c2291 : List Lit := [(74, true), (69, true), (111, true), (68, false), (76, true), (52, true)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c1002, c313] c2291 (by decide) p (sat_cons (step1002 p h) (sat_cons (step313 p h) (sat_nil p)))
def c2292 : List Lit := [(76, true), (69, true), (52, true), (111, true), (68, false), (70, true)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c1002, c314] c2292 (by decide) p (sat_cons (step1002 p h) (sat_cons (step314 p h) (sat_nil p)))
def c2293 : List Lit := [(74, true), (69, true), (68, false), (111, true), (70, true), (52, true)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c1002, c315] c2293 (by decide) p (sat_cons (step1002 p h) (sat_cons (step315 p h) (sat_nil p)))
def c2294 : List Lit := [(76, true), (69, true), (68, false), (70, true), (52, true), (74, true)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1002, c316] c2294 (by decide) p (sat_cons (step1002 p h) (sat_cons (step316 p h) (sat_nil p)))
def c2295 : List Lit := [(113, true), (70, true), (71, false), (79, true)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c1003, c336] c2295 (by decide) p (sat_cons (step1003 p h) (sat_cons (step336 p h) (sat_nil p)))
def c2296 : List Lit := [(69, true), (113, true), (71, false), (79, true)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c1003, c337] c2296 (by decide) p (sat_cons (step1003 p h) (sat_cons (step337 p h) (sat_nil p)))
def c2297 : List Lit := [(69, true), (70, true), (71, false), (113, true)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1003, c338] c2297 (by decide) p (sat_cons (step1003 p h) (sat_cons (step338 p h) (sat_nil p)))
def c2298 : List Lit := [(69, true), (70, true), (71, false), (79, true)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c1003, c339] c2298 (by decide) p (sat_cons (step1003 p h) (sat_cons (step339 p h) (sat_nil p)))
def c2299 : List Lit := [(80, true), (74, true), (72, false)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c1004, c341] c2299 (by decide) p (sat_cons (step1004 p h) (sat_cons (step341 p h) (sat_nil p)))
def c2300 : List Lit := [(73, true), (80, true), (72, false)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c1004, c342] c2300 (by decide) p (sat_cons (step1004 p h) (sat_cons (step342 p h) (sat_nil p)))
def c2301 : List Lit := [(74, true), (72, false), (73, true)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c1004, c343] c2301 (by decide) p (sat_cons (step1004 p h) (sat_cons (step343 p h) (sat_nil p)))
def c2302 : List Lit := [(75, true), (76, true), (77, false), (79, true)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1005, c361] c2302 (by decide) p (sat_cons (step1005 p h) (sat_cons (step361 p h) (sat_nil p)))
def c2303 : List Lit := [(76, true), (69, true), (77, false), (79, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c1005, c362] c2303 (by decide) p (sat_cons (step1005 p h) (sat_cons (step362 p h) (sat_nil p)))
def c2304 : List Lit := [(75, true), (69, true), (77, false), (79, true)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1005, c363] c2304 (by decide) p (sat_cons (step1005 p h) (sat_cons (step363 p h) (sat_nil p)))
def c2305 : List Lit := [(76, true), (78, false), (79, true)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c1006, c364] c2305 (by decide) p (sat_cons (step1006 p h) (sat_cons (step364 p h) (sat_nil p)))
def c2306 : List Lit := [(78, false), (70, true), (79, true)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c1006, c365] c2306 (by decide) p (sat_cons (step1006 p h) (sat_cons (step365 p h) (sat_nil p)))
def c2307 : List Lit := [(76, true), (70, true), (78, false)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c1006, c366] c2307 (by decide) p (sat_cons (step1006 p h) (sat_cons (step366 p h) (sat_nil p)))
def c2308 : List Lit := [(83, true), (80, true), (81, false)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1007, c423] c2308 (by decide) p (sat_cons (step1007 p h) (sat_cons (step423 p h) (sat_nil p)))
def c2309 : List Lit := [(83, true), (75, true), (81, false)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c1007, c424] c2309 (by decide) p (sat_cons (step1007 p h) (sat_cons (step424 p h) (sat_nil p)))
end B112E052
