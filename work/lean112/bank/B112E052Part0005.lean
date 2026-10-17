import B112E052Part0004
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2310 : List Lit := [(75, true), (80, true), (81, false)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c1007, c425] c2310 (by decide) p (sat_cons (step1007 p h) (sat_cons (step425 p h) (sat_nil p)))
def c2311 : List Lit := [(83, true), (80, true), (82, false), (124, true)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c1008, c428] c2311 (by decide) p (sat_cons (step1008 p h) (sat_cons (step428 p h) (sat_nil p)))
def c2312 : List Lit := [(73, true), (80, true), (82, false), (124, true)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c1008, c429] c2312 (by decide) p (sat_cons (step1008 p h) (sat_cons (step429 p h) (sat_nil p)))
def c2313 : List Lit := [(73, true), (83, true), (82, false), (80, true)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c1008, c430] c2313 (by decide) p (sat_cons (step1008 p h) (sat_cons (step430 p h) (sat_nil p)))
def c2314 : List Lit := [(83, true), (84, false), (79, true)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c1009, c437] c2314 (by decide) p (sat_cons (step1009 p h) (sat_cons (step437 p h) (sat_nil p)))
def c2315 : List Lit := [(83, true), (66, true), (84, false)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c1009, c438] c2315 (by decide) p (sat_cons (step1009 p h) (sat_cons (step438 p h) (sat_nil p)))
def c2316 : List Lit := [(66, true), (84, false), (79, true)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c1009, c439] c2316 (by decide) p (sat_cons (step1009 p h) (sat_cons (step439 p h) (sat_nil p)))
def c2317 : List Lit := [(93, true), (89, true), (50, true), (86, false), (85, true)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c1010, c449] c2317 (by decide) p (sat_cons (step1010 p h) (sat_cons (step449 p h) (sat_nil p)))
def c2318 : List Lit := [(93, true), (89, true), (86, false), (14, true), (85, true)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c1010, c450] c2318 (by decide) p (sat_cons (step1010 p h) (sat_cons (step450 p h) (sat_nil p)))
def c2319 : List Lit := [(93, true), (50, true), (86, false), (89, true), (14, true)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c1010, c451] c2319 (by decide) p (sat_cons (step1010 p h) (sat_cons (step451 p h) (sat_nil p)))
def c2320 : List Lit := [(50, true), (89, true), (86, false), (85, true), (14, true)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c1010, c452] c2320 (by decide) p (sat_cons (step1010 p h) (sat_cons (step452 p h) (sat_nil p)))
def c2321 : List Lit := [(98, true), (111, true), (88, true), (89, true), (87, false), (85, true), (52, true)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c1011, c474] c2321 (by decide) p (sat_cons (step1011 p h) (sat_cons (step474 p h) (sat_nil p)))
def c2322 : List Lit := [(89, true), (113, true), (90, false), (101, true)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c1012, c530] c2322 (by decide) p (sat_cons (step1012 p h) (sat_cons (step530 p h) (sat_nil p)))
def c2323 : List Lit := [(113, true), (88, true), (90, false), (101, true)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c1012, c531] c2323 (by decide) p (sat_cons (step1012 p h) (sat_cons (step531 p h) (sat_nil p)))
def c2324 : List Lit := [(89, true), (113, true), (90, false), (88, true)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c1012, c532] c2324 (by decide) p (sat_cons (step1012 p h) (sat_cons (step532 p h) (sat_nil p)))
def c2325 : List Lit := [(89, true), (90, false), (88, true), (101, true)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c1012, c533] c2325 (by decide) p (sat_cons (step1012 p h) (sat_cons (step533 p h) (sat_nil p)))
def c2326 : List Lit := [(93, true), (92, true), (91, false)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c1013, c534] c2326 (by decide) p (sat_cons (step1013 p h) (sat_cons (step534 p h) (sat_nil p)))
def c2327 : List Lit := [(93, true), (91, false), (85, true)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c1013, c535] c2327 (by decide) p (sat_cons (step1013 p h) (sat_cons (step535 p h) (sat_nil p)))
def c2328 : List Lit := [(92, true), (91, false), (85, true)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c1013, c536] c2328 (by decide) p (sat_cons (step1013 p h) (sat_cons (step536 p h) (sat_nil p)))
def c2329 : List Lit := [(116, true), (105, true), (57, true), (95, false), (92, true), (88, true)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c1014, c613] c2329 (by decide) p (sat_cons (step1014 p h) (sat_cons (step613 p h) (sat_nil p)))
def c2330 : List Lit := [(116, true), (105, true), (21, true), (95, false), (92, true), (88, true)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c1014, c614] c2330 (by decide) p (sat_cons (step1014 p h) (sat_cons (step614 p h) (sat_nil p)))
def c2331 : List Lit := [(117, true), (93, true), (89, true), (106, true), (22, true), (96, false)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c1015, c626] c2331 (by decide) p (sat_cons (step1015 p h) (sat_cons (step626 p h) (sat_nil p)))
def c2332 : List Lit := [(93, true), (89, true), (96, false), (22, true), (106, true), (58, true)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c1015, c627] c2332 (by decide) p (sat_cons (step1015 p h) (sat_cons (step627 p h) (sat_nil p)))
def c2333 : List Lit := [(97, true), (98, true), (105, true), (99, false), (101, true)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c1016, c645] c2333 (by decide) p (sat_cons (step1016 p h) (sat_cons (step645 p h) (sat_nil p)))
def c2334 : List Lit := [(98, true), (99, false), (88, true), (105, true), (101, true)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c1016, c646] c2334 (by decide) p (sat_cons (step1016 p h) (sat_cons (step646 p h) (sat_nil p)))
def c2335 : List Lit := [(97, true), (99, false), (105, true), (88, true), (101, true)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c1016, c647] c2335 (by decide) p (sat_cons (step1016 p h) (sat_cons (step647 p h) (sat_nil p)))
def c2336 : List Lit := [(97, true), (98, true), (99, false), (88, true), (105, true)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c1016, c648] c2336 (by decide) p (sat_cons (step1016 p h) (sat_cons (step648 p h) (sat_nil p)))
def c2337 : List Lit := [(97, true), (98, true), (99, false), (88, true), (101, true)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c1016, c649] c2337 (by decide) p (sat_cons (step1016 p h) (sat_cons (step649 p h) (sat_nil p)))
def c2338 : List Lit := [(98, true), (100, false), (101, true), (106, true)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c1017, c655] c2338 (by decide) p (sat_cons (step1017 p h) (sat_cons (step655 p h) (sat_nil p)))
def c2339 : List Lit := [(89, true), (100, false), (101, true), (106, true)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c1017, c656] c2339 (by decide) p (sat_cons (step1017 p h) (sat_cons (step656 p h) (sat_nil p)))
def c2340 : List Lit := [(98, true), (89, true), (100, false), (106, true)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c1017, c657] c2340 (by decide) p (sat_cons (step1017 p h) (sat_cons (step657 p h) (sat_nil p)))
def c2341 : List Lit := [(98, true), (100, false), (101, true), (89, true)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c1017, c658] c2341 (by decide) p (sat_cons (step1017 p h) (sat_cons (step658 p h) (sat_nil p)))
def c2342 : List Lit := [(97, true), (104, true), (102, false), (105, true)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c1018, c699] c2342 (by decide) p (sat_cons (step1018 p h) (sat_cons (step699 p h) (sat_nil p)))
def c2343 : List Lit := [(105, true), (104, true), (92, true), (102, false)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c1018, c700] c2343 (by decide) p (sat_cons (step1018 p h) (sat_cons (step700 p h) (sat_nil p)))
def c2344 : List Lit := [(97, true), (105, true), (92, true), (102, false)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c1018, c701] c2344 (by decide) p (sat_cons (step1018 p h) (sat_cons (step701 p h) (sat_nil p)))
def c2345 : List Lit := [(97, true), (104, true), (102, false), (92, true)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c1018, c702] c2345 (by decide) p (sat_cons (step1018 p h) (sat_cons (step702 p h) (sat_nil p)))
def c2346 : List Lit := [(124, true), (104, true), (103, false), (106, true)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c1019, c707] c2346 (by decide) p (sat_cons (step1019 p h) (sat_cons (step707 p h) (sat_nil p)))
def c2347 : List Lit := [(124, true), (93, true), (103, false), (106, true)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c1019, c708] c2347 (by decide) p (sat_cons (step1019 p h) (sat_cons (step708 p h) (sat_nil p)))
def c2348 : List Lit := [(104, true), (93, true), (124, true), (103, false)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c1019, c709] c2348 (by decide) p (sat_cons (step1019 p h) (sat_cons (step709 p h) (sat_nil p)))
def c2349 : List Lit := [(104, true), (93, true), (106, true), (103, false)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c1019, c710] c2349 (by decide) p (sat_cons (step1019 p h) (sat_cons (step710 p h) (sat_nil p)))
def c2350 : List Lit := [(66, true), (104, true), (105, true), (101, true), (107, false), (106, true)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c1020, c783] c2350 (by decide) p (sat_cons (step1020 p h) (sat_cons (step783 p h) (sat_nil p)))
def c2351 : List Lit := [(31, true), (104, true), (105, true), (106, true), (107, false), (101, true)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c1020, c784] c2351 (by decide) p (sat_cons (step1020 p h) (sat_cons (step784 p h) (sat_nil p)))
def c2352 : List Lit := [(119, true), (109, true), (85, true), (111, true), (108, false)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c1021, c788] c2352 (by decide) p (sat_cons (step1021 p h) (sat_cons (step788 p h) (sat_nil p)))
def c2353 : List Lit := [(109, true), (111, true), (108, false), (85, true), (32, true)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c1021, c789] c2353 (by decide) p (sat_cons (step1021 p h) (sat_cons (step789 p h) (sat_nil p)))
def c2354 : List Lit := [(110, false), (115, true), (113, true), (121, true)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c1022, c801] c2354 (by decide) p (sat_cons (step1022 p h) (sat_cons (step801 p h) (sat_nil p)))
def c2355 : List Lit := [(115, true), (109, true), (110, false), (121, true)]
theorem step2355 (p : Nat → Bool) (h : Constraints p) : clause p c2355 = true :=
  Snake9.LocalRup.prove_clause [c1022, c802] c2355 (by decide) p (sat_cons (step1022 p h) (sat_cons (step802 p h) (sat_nil p)))
def c2356 : List Lit := [(109, true), (110, false), (121, true), (113, true)]
theorem step2356 (p : Nat → Bool) (h : Constraints p) : clause p c2356 = true :=
  Snake9.LocalRup.prove_clause [c1022, c803] c2356 (by decide) p (sat_cons (step1022 p h) (sat_cons (step803 p h) (sat_nil p)))
def c2357 : List Lit := [(109, true), (115, true), (113, true), (110, false)]
theorem step2357 (p : Nat → Bool) (h : Constraints p) : clause p c2357 = true :=
  Snake9.LocalRup.prove_clause [c1022, c804] c2357 (by decide) p (sat_cons (step1022 p h) (sat_cons (step804 p h) (sat_nil p)))
def c2358 : List Lit := [(109, true), (116, true), (88, true), (111, true), (112, false), (113, true)]
theorem step2358 (p : Nat → Bool) (h : Constraints p) : clause p c2358 = true :=
  Snake9.LocalRup.prove_clause [c1023, c817] c2358 (by decide) p (sat_cons (step1023 p h) (sat_cons (step817 p h) (sat_nil p)))
def c2359 : List Lit := [(109, true), (116, true), (111, true), (69, true), (112, false), (113, true)]
theorem step2359 (p : Nat → Bool) (h : Constraints p) : clause p c2359 = true :=
  Snake9.LocalRup.prove_clause [c1023, c818] c2359 (by decide) p (sat_cons (step1023 p h) (sat_cons (step818 p h) (sat_nil p)))
def c2360 : List Lit := [(116, true), (112, false), (111, true), (69, true), (113, true), (88, true)]
theorem step2360 (p : Nat → Bool) (h : Constraints p) : clause p c2360 = true :=
  Snake9.LocalRup.prove_clause [c1023, c819] c2360 (by decide) p (sat_cons (step1023 p h) (sat_cons (step819 p h) (sat_nil p)))
def c2361 : List Lit := [(109, true), (116, true), (69, true), (88, true), (112, false), (113, true)]
theorem step2361 (p : Nat → Bool) (h : Constraints p) : clause p c2361 = true :=
  Snake9.LocalRup.prove_clause [c1023, c820] c2361 (by decide) p (sat_cons (step1023 p h) (sat_cons (step820 p h) (sat_nil p)))
def c2362 : List Lit := [(109, true), (116, true), (69, true), (111, true), (112, false), (88, true)]
theorem step2362 (p : Nat → Bool) (h : Constraints p) : clause p c2362 = true :=
  Snake9.LocalRup.prove_clause [c1023, c821] c2362 (by decide) p (sat_cons (step1023 p h) (sat_cons (step821 p h) (sat_nil p)))
def c2363 : List Lit := [(109, true), (112, false), (111, true), (69, true), (113, true), (88, true)]
theorem step2363 (p : Nat → Bool) (h : Constraints p) : clause p c2363 = true :=
  Snake9.LocalRup.prove_clause [c1023, c822] c2363 (by decide) p (sat_cons (step1023 p h) (sat_cons (step822 p h) (sat_nil p)))
def c2364 : List Lit := [(116, true), (115, true), (114, false), (109, true)]
theorem step2364 (p : Nat → Bool) (h : Constraints p) : clause p c2364 = true :=
  Snake9.LocalRup.prove_clause [c1024, c860] c2364 (by decide) p (sat_cons (step1024 p h) (sat_cons (step860 p h) (sat_nil p)))
def c2365 : List Lit := [(116, true), (115, true), (114, false), (92, true)]
theorem step2365 (p : Nat → Bool) (h : Constraints p) : clause p c2365 = true :=
  Snake9.LocalRup.prove_clause [c1024, c861] c2365 (by decide) p (sat_cons (step1024 p h) (sat_cons (step861 p h) (sat_nil p)))
def c2366 : List Lit := [(116, true), (109, true), (114, false), (92, true)]
theorem step2366 (p : Nat → Bool) (h : Constraints p) : clause p c2366 = true :=
  Snake9.LocalRup.prove_clause [c1024, c862] c2366 (by decide) p (sat_cons (step1024 p h) (sat_cons (step862 p h) (sat_nil p)))
def c2367 : List Lit := [(109, true), (115, true), (92, true), (114, false)]
theorem step2367 (p : Nat → Bool) (h : Constraints p) : clause p c2367 = true :=
  Snake9.LocalRup.prove_clause [c1024, c863] c2367 (by decide) p (sat_cons (step1024 p h) (sat_cons (step863 p h) (sat_nil p)))
def c2368 : List Lit := [(116, true), (115, true), (117, true), (118, false)]
theorem step2368 (p : Nat → Bool) (h : Constraints p) : clause p c2368 = true :=
  Snake9.LocalRup.prove_clause [c1025, c893] c2368 (by decide) p (sat_cons (step1025 p h) (sat_cons (step893 p h) (sat_nil p)))
def c2369 : List Lit := [(116, true), (117, true), (118, false), (113, true)]
theorem step2369 (p : Nat → Bool) (h : Constraints p) : clause p c2369 = true :=
  Snake9.LocalRup.prove_clause [c1025, c894] c2369 (by decide) p (sat_cons (step1025 p h) (sat_cons (step894 p h) (sat_nil p)))
def c2370 : List Lit := [(117, true), (115, true), (113, true), (118, false)]
theorem step2370 (p : Nat → Bool) (h : Constraints p) : clause p c2370 = true :=
  Snake9.LocalRup.prove_clause [c1025, c895] c2370 (by decide) p (sat_cons (step1025 p h) (sat_cons (step895 p h) (sat_nil p)))
def c2371 : List Lit := [(116, true), (115, true), (113, true), (118, false)]
theorem step2371 (p : Nat → Bool) (h : Constraints p) : clause p c2371 = true :=
  Snake9.LocalRup.prove_clause [c1025, c896] c2371 (by decide) p (sat_cons (step1025 p h) (sat_cons (step896 p h) (sat_nil p)))
def c2372 : List Lit := [(124, true), (120, false), (121, true)]
theorem step2372 (p : Nat → Bool) (h : Constraints p) : clause p c2372 = true :=
  Snake9.LocalRup.prove_clause [c1026, c901] c2372 (by decide) p (sat_cons (step1026 p h) (sat_cons (step901 p h) (sat_nil p)))
def c2373 : List Lit := [(119, true), (124, true), (120, false)]
theorem step2373 (p : Nat → Bool) (h : Constraints p) : clause p c2373 = true :=
  Snake9.LocalRup.prove_clause [c1026, c902] c2373 (by decide) p (sat_cons (step1026 p h) (sat_cons (step902 p h) (sat_nil p)))
end B112E052
