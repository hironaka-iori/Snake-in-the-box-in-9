import B112E057Part0003
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2281 : List Lit := [(37, true), (62, true), (64, false)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c997, c436] c2281 (by decide) p (sat_cons (step997 p h) (sat_cons (step436 p h) (sat_nil p)))
def c2282 : List Lit := [(37, true), (55, true), (64, false)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c997, c437] c2282 (by decide) p (sat_cons (step997 p h) (sat_cons (step437 p h) (sat_nil p)))
def c2283 : List Lit := [(193, false), (59, false)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c965, c439] c2283 (by decide) p (sat_cons (step965 p h) (sat_cons (step439 p h) (sat_nil p)))
def c2284 : List Lit := [(193, true), (59, true)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c2025, c2027, c2028, c440] c2284 (by decide) p (sat_cons (step2025 p h) (sat_cons (step2027 p h) (sat_cons (step2028 p h) (sat_cons (step440 p h) (sat_nil p)))))
def c2285 : List Lit := [(71, true), (81, true), (76, true), (69, false)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1000, c449] c2285 (by decide) p (sat_cons (step1000 p h) (sat_cons (step449 p h) (sat_nil p)))
def c2286 : List Lit := [(81, true), (69, false), (76, true), (70, true)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c1000, c450] c2286 (by decide) p (sat_cons (step1000 p h) (sat_cons (step450 p h) (sat_nil p)))
def c2287 : List Lit := [(71, true), (81, true), (69, false), (70, true)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c1000, c451] c2287 (by decide) p (sat_cons (step1000 p h) (sat_cons (step451 p h) (sat_nil p)))
def c2288 : List Lit := [(71, true), (69, false), (70, true), (76, true)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c1000, c452] c2288 (by decide) p (sat_cons (step1000 p h) (sat_cons (step452 p h) (sat_nil p)))
def c2289 : List Lit := [(84, true), (71, true), (70, true), (78, true), (72, false)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1001, c504] c2289 (by decide) p (sat_cons (step1001 p h) (sat_cons (step504 p h) (sat_nil p)))
def c2290 : List Lit := [(68, true), (84, true), (78, true), (72, false), (70, true)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c1001, c505] c2290 (by decide) p (sat_cons (step1001 p h) (sat_cons (step505 p h) (sat_nil p)))
def c2291 : List Lit := [(68, true), (84, true), (72, false), (70, true), (71, true)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c1001, c506] c2291 (by decide) p (sat_cons (step1001 p h) (sat_cons (step506 p h) (sat_nil p)))
def c2292 : List Lit := [(71, true), (68, true), (72, false), (70, true), (78, true)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c1001, c507] c2292 (by decide) p (sat_cons (step1001 p h) (sat_cons (step507 p h) (sat_nil p)))
def c2293 : List Lit := [(74, true), (85, true), (73, false), (76, true)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c1002, c511] c2293 (by decide) p (sat_cons (step1002 p h) (sat_cons (step511 p h) (sat_nil p)))
def c2294 : List Lit := [(85, true), (5, true), (73, false), (76, true)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1002, c512] c2294 (by decide) p (sat_cons (step1002 p h) (sat_cons (step512 p h) (sat_nil p)))
def c2295 : List Lit := [(85, true), (5, true), (73, false), (74, true)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c1002, c513] c2295 (by decide) p (sat_cons (step1002 p h) (sat_cons (step513 p h) (sat_nil p)))
def c2296 : List Lit := [(74, true), (5, true), (73, false), (76, true)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c1002, c514] c2296 (by decide) p (sat_cons (step1002 p h) (sat_cons (step514 p h) (sat_nil p)))
def c2297 : List Lit := [(75, false), (78, true), (74, true), (88, true)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1003, c529] c2297 (by decide) p (sat_cons (step1003 p h) (sat_cons (step529 p h) (sat_nil p)))
def c2298 : List Lit := [(68, true), (75, false), (78, true), (88, true)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c1003, c530] c2298 (by decide) p (sat_cons (step1003 p h) (sat_cons (step530 p h) (sat_nil p)))
def c2299 : List Lit := [(68, true), (75, false), (74, true), (88, true)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c1003, c531] c2299 (by decide) p (sat_cons (step1003 p h) (sat_cons (step531 p h) (sat_nil p)))
def c2300 : List Lit := [(68, true), (75, false), (74, true), (78, true)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c1003, c532] c2300 (by decide) p (sat_cons (step1003 p h) (sat_cons (step532 p h) (sat_nil p)))
def c2301 : List Lit := [(78, true), (98, true), (70, true), (77, false), (76, true), (115, true)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c1004, c586] c2301 (by decide) p (sat_cons (step1004 p h) (sat_cons (step586 p h) (sat_nil p)))
def c2302 : List Lit := [(98, true), (115, true), (77, false), (76, true), (74, true), (70, true)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1004, c587] c2302 (by decide) p (sat_cons (step1004 p h) (sat_cons (step587 p h) (sat_nil p)))
def c2303 : List Lit := [(78, true), (115, true), (77, false), (76, true), (70, true), (74, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c1004, c588] c2303 (by decide) p (sat_cons (step1004 p h) (sat_cons (step588 p h) (sat_nil p)))
def c2304 : List Lit := [(74, true), (78, true), (77, false), (70, true), (76, true), (98, true)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1004, c589] c2304 (by decide) p (sat_cons (step1004 p h) (sat_cons (step589 p h) (sat_nil p)))
def c2305 : List Lit := [(100, true), (117, true), (85, true), (81, true), (79, false)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c1005, c611] c2305 (by decide) p (sat_cons (step1005 p h) (sat_cons (step611 p h) (sat_nil p)))
def c2306 : List Lit := [(85, true), (117, true), (80, true), (100, true), (79, false)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c1005, c612] c2306 (by decide) p (sat_cons (step1005 p h) (sat_cons (step612 p h) (sat_nil p)))
def c2307 : List Lit := [(100, true), (117, true), (81, true), (79, false), (80, true)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c1005, c613] c2307 (by decide) p (sat_cons (step1005 p h) (sat_cons (step613 p h) (sat_nil p)))
def c2308 : List Lit := [(80, true), (85, true), (81, true), (117, true), (79, false)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1005, c614] c2308 (by decide) p (sat_cons (step1005 p h) (sat_cons (step614 p h) (sat_nil p)))
def c2309 : List Lit := [(100, true), (80, true), (81, true), (79, false), (85, true)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c1005, c615] c2309 (by decide) p (sat_cons (step1005 p h) (sat_cons (step615 p h) (sat_nil p)))
def c2310 : List Lit := [(81, true), (84, true), (82, false), (70, true)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c1006, c638] c2310 (by decide) p (sat_cons (step1006 p h) (sat_cons (step638 p h) (sat_nil p)))
def c2311 : List Lit := [(81, true), (84, true), (13, true), (82, false)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c1006, c639] c2311 (by decide) p (sat_cons (step1006 p h) (sat_cons (step639 p h) (sat_nil p)))
def c2312 : List Lit := [(13, true), (84, true), (82, false), (70, true)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c1006, c640] c2312 (by decide) p (sat_cons (step1006 p h) (sat_cons (step640 p h) (sat_nil p)))
def c2313 : List Lit := [(13, true), (81, true), (82, false), (70, true)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c1006, c641] c2313 (by decide) p (sat_cons (step1006 p h) (sat_cons (step641 p h) (sat_nil p)))
def c2314 : List Lit := [(80, true), (120, true), (14, true), (71, true), (83, false), (84, true), (81, true)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c1007, c658] c2314 (by decide) p (sat_cons (step1007 p h) (sat_cons (step658 p h) (sat_nil p)))
def c2315 : List Lit := [(85, true), (86, false), (122, true), (74, true), (16, true), (88, true)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c1008, c724] c2315 (by decide) p (sat_cons (step1008 p h) (sat_cons (step724 p h) (sat_nil p)))
def c2316 : List Lit := [(85, true), (87, false), (88, true)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c1009, c725] c2316 (by decide) p (sat_cons (step1009 p h) (sat_cons (step725 p h) (sat_nil p)))
def c2317 : List Lit := [(80, true), (87, false), (88, true)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c1009, c726] c2317 (by decide) p (sat_cons (step1009 p h) (sat_cons (step726 p h) (sat_nil p)))
def c2318 : List Lit := [(85, true), (80, true), (87, false)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c1009, c727] c2318 (by decide) p (sat_cons (step1009 p h) (sat_cons (step727 p h) (sat_nil p)))
def c2319 : List Lit := [(124, true), (106, true), (76, true), (85, true), (81, true), (89, false)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c1010, c774] c2319 (by decide) p (sat_cons (step1010 p h) (sat_cons (step774 p h) (sat_nil p)))
def c2320 : List Lit := [(124, true), (106, true), (76, true), (85, true), (89, false), (18, true)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c1010, c775] c2320 (by decide) p (sat_cons (step1010 p h) (sat_cons (step775 p h) (sat_nil p)))
def c2321 : List Lit := [(124, true), (106, true), (89, false), (76, true), (81, true), (18, true)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c1010, c776] c2321 (by decide) p (sat_cons (step1010 p h) (sat_cons (step776 p h) (sat_nil p)))
def c2322 : List Lit := [(85, true), (89, false), (76, true), (124, true), (81, true), (18, true)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c1010, c777] c2322 (by decide) p (sat_cons (step1010 p h) (sat_cons (step777 p h) (sat_nil p)))
def c2323 : List Lit := [(85, true), (106, true), (18, true), (76, true), (89, false), (81, true)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c1010, c778] c2323 (by decide) p (sat_cons (step1010 p h) (sat_cons (step778 p h) (sat_nil p)))
def c2324 : List Lit := [(108, true), (84, true), (88, true), (126, true), (78, true), (90, false)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c1011, c786] c2324 (by decide) p (sat_cons (step1011 p h) (sat_cons (step786 p h) (sat_nil p)))
def c2325 : List Lit := [(108, true), (90, false), (20, true), (84, true), (78, true), (126, true)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c1011, c787] c2325 (by decide) p (sat_cons (step1011 p h) (sat_cons (step787 p h) (sat_nil p)))
def c2326 : List Lit := [(20, true), (84, true), (88, true), (126, true), (78, true), (90, false)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c1011, c788] c2326 (by decide) p (sat_cons (step1011 p h) (sat_cons (step788 p h) (sat_nil p)))
def c2327 : List Lit := [(93, true), (100, true), (91, false)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c1012, c790] c2327 (by decide) p (sat_cons (step1012 p h) (sat_cons (step790 p h) (sat_nil p)))
def c2328 : List Lit := [(100, true), (92, true), (91, false)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c1012, c791] c2328 (by decide) p (sat_cons (step1012 p h) (sat_cons (step791 p h) (sat_nil p)))
def c2329 : List Lit := [(92, true), (93, true), (91, false)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c1012, c792] c2329 (by decide) p (sat_cons (step1012 p h) (sat_cons (step792 p h) (sat_nil p)))
def c2330 : List Lit := [(21, true), (92, true), (68, true), (94, false)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c1013, c807] c2330 (by decide) p (sat_cons (step1013 p h) (sat_cons (step807 p h) (sat_nil p)))
def c2331 : List Lit := [(92, true), (95, false), (70, true), (98, true)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c1014, c810] c2331 (by decide) p (sat_cons (step1014 p h) (sat_cons (step810 p h) (sat_nil p)))
def c2332 : List Lit := [(92, true), (95, false), (98, true), (23, true)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c1014, c811] c2332 (by decide) p (sat_cons (step1014 p h) (sat_cons (step811 p h) (sat_nil p)))
def c2333 : List Lit := [(23, true), (95, false), (98, true), (70, true)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c1014, c812] c2333 (by decide) p (sat_cons (step1014 p h) (sat_cons (step812 p h) (sat_nil p)))
def c2334 : List Lit := [(92, true), (95, false), (23, true), (70, true)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c1014, c813] c2334 (by decide) p (sat_cons (step1014 p h) (sat_cons (step813 p h) (sat_nil p)))
def c2335 : List Lit := [(96, false), (99, true)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c1015, c814] c2335 (by decide) p (sat_cons (step1015 p h) (sat_cons (step814 p h) (sat_nil p)))
def c2336 : List Lit := [(96, false), (93, true)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c1015, c815] c2336 (by decide) p (sat_cons (step1015 p h) (sat_cons (step815 p h) (sat_nil p)))
def c2337 : List Lit := [(99, true), (106, true), (97, false), (76, true)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c1016, c818] c2337 (by decide) p (sat_cons (step1016 p h) (sat_cons (step818 p h) (sat_nil p)))
def c2338 : List Lit := [(106, true), (97, false), (98, true), (76, true)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c1016, c819] c2338 (by decide) p (sat_cons (step1016 p h) (sat_cons (step819 p h) (sat_nil p)))
def c2339 : List Lit := [(99, true), (97, false), (76, true), (98, true)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c1016, c820] c2339 (by decide) p (sat_cons (step1016 p h) (sat_cons (step820 p h) (sat_nil p)))
def c2340 : List Lit := [(100, true), (104, true), (101, false)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c1017, c838] c2340 (by decide) p (sat_cons (step1017 p h) (sat_cons (step838 p h) (sat_nil p)))
def c2341 : List Lit := [(104, true), (92, true), (101, false)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c1017, c839] c2341 (by decide) p (sat_cons (step1017 p h) (sat_cons (step839 p h) (sat_nil p)))
def c2342 : List Lit := [(100, true), (92, true), (101, false)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c1017, c840] c2342 (by decide) p (sat_cons (step1017 p h) (sat_cons (step840 p h) (sat_nil p)))
def c2343 : List Lit := [(108, true), (102, true), (103, false)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c1018, c848] c2343 (by decide) p (sat_cons (step1018 p h) (sat_cons (step848 p h) (sat_nil p)))
def c2344 : List Lit := [(108, true), (84, true), (103, false)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c1018, c849] c2344 (by decide) p (sat_cons (step1018 p h) (sat_cons (step849 p h) (sat_nil p)))
end B112E057
