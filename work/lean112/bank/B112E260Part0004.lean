import B112E260Part0003
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2359 : List Lit := [(69, true), (31, false), (21, true)]
theorem step2359 (p : Nat → Bool) (h : Constraints p) : clause p c2359 = true :=
  Snake9.LocalRup.prove_clause [c831, c221] c2359 (by decide) p (sat_cons (step831 p h) (sat_cons (step221 p h) (sat_nil p)))
def c2360 : List Lit := [(30, true), (31, false), (21, true)]
theorem step2360 (p : Nat → Bool) (h : Constraints p) : clause p c2360 = true :=
  Snake9.LocalRup.prove_clause [c831, c222] c2360 (by decide) p (sat_cons (step831 p h) (sat_cons (step222 p h) (sat_nil p)))
def c2361 : List Lit := [(33, false), (32, true)]
theorem step2361 (p : Nat → Bool) (h : Constraints p) : clause p c2361 = true :=
  Snake9.LocalRup.prove_clause [c832, c228] c2361 (by decide) p (sat_cons (step832 p h) (sat_cons (step228 p h) (sat_nil p)))
def c2362 : List Lit := [(33, false), (16, true)]
theorem step2362 (p : Nat → Bool) (h : Constraints p) : clause p c2362 = true :=
  Snake9.LocalRup.prove_clause [c832, c229] c2362 (by decide) p (sat_cons (step832 p h) (sat_cons (step229 p h) (sat_nil p)))
def c2363 : List Lit := [(35, false), (73, true)]
theorem step2363 (p : Nat → Bool) (h : Constraints p) : clause p c2363 = true :=
  Snake9.LocalRup.prove_clause [c833, c235] c2363 (by decide) p (sat_cons (step833 p h) (sat_cons (step235 p h) (sat_nil p)))
def c2364 : List Lit := [(35, false), (34, true)]
theorem step2364 (p : Nat → Bool) (h : Constraints p) : clause p c2364 = true :=
  Snake9.LocalRup.prove_clause [c833, c236] c2364 (by decide) p (sat_cons (step833 p h) (sat_cons (step236 p h) (sat_nil p)))
def c2365 : List Lit := [(103, true), (36, true), (37, false), (40, true), (48, true)]
theorem step2365 (p : Nat → Bool) (h : Constraints p) : clause p c2365 = true :=
  Snake9.LocalRup.prove_clause [c834, c250] c2365 (by decide) p (sat_cons (step834 p h) (sat_cons (step250 p h) (sat_nil p)))
def c2366 : List Lit := [(103, true), (36, true), (37, false), (40, true), (1, true)]
theorem step2366 (p : Nat → Bool) (h : Constraints p) : clause p c2366 = true :=
  Snake9.LocalRup.prove_clause [c834, c251] c2366 (by decide) p (sat_cons (step834 p h) (sat_cons (step251 p h) (sat_nil p)))
def c2367 : List Lit := [(42, true), (36, true), (49, true), (38, false), (56, true)]
theorem step2367 (p : Nat → Bool) (h : Constraints p) : clause p c2367 = true :=
  Snake9.LocalRup.prove_clause [c835, c263] c2367 (by decide) p (sat_cons (step835 p h) (sat_cons (step263 p h) (sat_nil p)))
def c2368 : List Lit := [(56, true), (36, true), (38, false), (49, true), (2, true)]
theorem step2368 (p : Nat → Bool) (h : Constraints p) : clause p c2368 = true :=
  Snake9.LocalRup.prove_clause [c835, c264] c2368 (by decide) p (sat_cons (step835 p h) (sat_cons (step264 p h) (sat_nil p)))
def c2369 : List Lit := [(51, true), (46, true), (5, true), (41, false)]
theorem step2369 (p : Nat → Bool) (h : Constraints p) : clause p c2369 = true :=
  Snake9.LocalRup.prove_clause [c837, c289] c2369 (by decide) p (sat_cons (step837 p h) (sat_cons (step289 p h) (sat_nil p)))
def c2370 : List Lit := [(51, true), (40, true), (41, false), (5, true)]
theorem step2370 (p : Nat → Bool) (h : Constraints p) : clause p c2370 = true :=
  Snake9.LocalRup.prove_clause [c837, c290] c2370 (by decide) p (sat_cons (step837 p h) (sat_cons (step290 p h) (sat_nil p)))
def c2371 : List Lit := [(46, true), (40, true), (41, false), (5, true)]
theorem step2371 (p : Nat → Bool) (h : Constraints p) : clause p c2371 = true :=
  Snake9.LocalRup.prove_clause [c837, c291] c2371 (by decide) p (sat_cons (step837 p h) (sat_cons (step291 p h) (sat_nil p)))
def c2372 : List Lit := [(110, true), (62, true), (43, false), (42, true), (46, true)]
theorem step2372 (p : Nat → Bool) (h : Constraints p) : clause p c2372 = true :=
  Snake9.LocalRup.prove_clause [c838, c307] c2372 (by decide) p (sat_cons (step838 p h) (sat_cons (step307 p h) (sat_nil p)))
def c2373 : List Lit := [(7, true), (62, true), (43, false), (42, true), (110, true)]
theorem step2373 (p : Nat → Bool) (h : Constraints p) : clause p c2373 = true :=
  Snake9.LocalRup.prove_clause [c838, c308] c2373 (by decide) p (sat_cons (step838 p h) (sat_cons (step308 p h) (sat_nil p)))
def c2374 : List Lit := [(7, true), (62, true), (43, false), (46, true), (42, true)]
theorem step2374 (p : Nat → Bool) (h : Constraints p) : clause p c2374 = true :=
  Snake9.LocalRup.prove_clause [c838, c309] c2374 (by decide) p (sat_cons (step838 p h) (sat_cons (step309 p h) (sat_nil p)))
def c2375 : List Lit := [(64, true), (40, true), (44, true), (45, false), (46, true)]
theorem step2375 (p : Nat → Bool) (h : Constraints p) : clause p c2375 = true :=
  Snake9.LocalRup.prove_clause [c839, c329] c2375 (by decide) p (sat_cons (step839 p h) (sat_cons (step329 p h) (sat_nil p)))
def c2376 : List Lit := [(36, true), (48, true), (50, true), (49, true), (47, false)]
theorem step2376 (p : Nat → Bool) (h : Constraints p) : clause p c2376 = true :=
  Snake9.LocalRup.prove_clause [c840, c351] c2376 (by decide) p (sat_cons (step840 p h) (sat_cons (step351 p h) (sat_nil p)))
def c2377 : List Lit := [(10, true), (36, true), (50, true), (49, true), (47, false)]
theorem step2377 (p : Nat → Bool) (h : Constraints p) : clause p c2377 = true :=
  Snake9.LocalRup.prove_clause [c840, c352] c2377 (by decide) p (sat_cons (step840 p h) (sat_cons (step352 p h) (sat_nil p)))
def c2378 : List Lit := [(52, false), (48, true)]
theorem step2378 (p : Nat → Bool) (h : Constraints p) : clause p c2378 = true :=
  Snake9.LocalRup.prove_clause [c841, c382] c2378 (by decide) p (sat_cons (step841 p h) (sat_cons (step382 p h) (sat_nil p)))
def c2379 : List Lit := [(52, false), (15, true)]
theorem step2379 (p : Nat → Bool) (h : Constraints p) : clause p c2379 = true :=
  Snake9.LocalRup.prove_clause [c841, c383] c2379 (by decide) p (sat_cons (step841 p h) (sat_cons (step383 p h) (sat_nil p)))
def c2380 : List Lit := [(42, true), (53, false), (49, true)]
theorem step2380 (p : Nat → Bool) (h : Constraints p) : clause p c2380 = true :=
  Snake9.LocalRup.prove_clause [c842, c385] c2380 (by decide) p (sat_cons (step842 p h) (sat_cons (step385 p h) (sat_nil p)))
def c2381 : List Lit := [(16, true), (53, false), (49, true)]
theorem step2381 (p : Nat → Bool) (h : Constraints p) : clause p c2381 = true :=
  Snake9.LocalRup.prove_clause [c842, c386] c2381 (by decide) p (sat_cons (step842 p h) (sat_cons (step386 p h) (sat_nil p)))
def c2382 : List Lit := [(16, true), (42, true), (53, false)]
theorem step2382 (p : Nat → Bool) (h : Constraints p) : clause p c2382 = true :=
  Snake9.LocalRup.prove_clause [c842, c387] c2382 (by decide) p (sat_cons (step842 p h) (sat_cons (step387 p h) (sat_nil p)))
def c2383 : List Lit := [(72, true), (50, true), (54, false)]
theorem step2383 (p : Nat → Bool) (h : Constraints p) : clause p c2383 = true :=
  Snake9.LocalRup.prove_clause [c843, c389] c2383 (by decide) p (sat_cons (step843 p h) (sat_cons (step389 p h) (sat_nil p)))
def c2384 : List Lit := [(50, true), (44, true), (54, false)]
theorem step2384 (p : Nat → Bool) (h : Constraints p) : clause p c2384 = true :=
  Snake9.LocalRup.prove_clause [c843, c390] c2384 (by decide) p (sat_cons (step843 p h) (sat_cons (step390 p h) (sat_nil p)))
def c2385 : List Lit := [(55, false), (60, true), (56, true)]
theorem step2385 (p : Nat → Bool) (h : Constraints p) : clause p c2385 = true :=
  Snake9.LocalRup.prove_clause [c844, c392] c2385 (by decide) p (sat_cons (step844 p h) (sat_cons (step392 p h) (sat_nil p)))
def c2386 : List Lit := [(117, true), (62, true), (56, true), (57, false)]
theorem step2386 (p : Nat → Bool) (h : Constraints p) : clause p c2386 = true :=
  Snake9.LocalRup.prove_clause [c845, c412] c2386 (by decide) p (sat_cons (step845 p h) (sat_cons (step412 p h) (sat_nil p)))
def c2387 : List Lit := [(119, true), (64, true), (40, true), (68, true), (58, false)]
theorem step2387 (p : Nat → Bool) (h : Constraints p) : clause p c2387 = true :=
  Snake9.LocalRup.prove_clause [c846, c418] c2387 (by decide) p (sat_cons (step846 p h) (sat_cons (step418 p h) (sat_nil p)))
def c2388 : List Lit := [(64, true), (68, true), (40, true), (58, false), (20, true)]
theorem step2388 (p : Nat → Bool) (h : Constraints p) : clause p c2388 = true :=
  Snake9.LocalRup.prove_clause [c846, c419] c2388 (by decide) p (sat_cons (step846 p h) (sat_cons (step419 p h) (sat_nil p)))
def c2389 : List Lit := [(69, true), (59, false), (56, true), (21, true)]
theorem step2389 (p : Nat → Bool) (h : Constraints p) : clause p c2389 = true :=
  Snake9.LocalRup.prove_clause [c847, c424] c2389 (by decide) p (sat_cons (step847 p h) (sat_cons (step424 p h) (sat_nil p)))
def c2390 : List Lit := [(65, true), (59, false), (56, true), (21, true)]
theorem step2390 (p : Nat → Bool) (h : Constraints p) : clause p c2390 = true :=
  Snake9.LocalRup.prove_clause [c847, c425] c2390 (by decide) p (sat_cons (step847 p h) (sat_cons (step425 p h) (sat_nil p)))
def c2391 : List Lit := [(64, true), (62, true), (61, false), (60, true)]
theorem step2391 (p : Nat → Bool) (h : Constraints p) : clause p c2391 = true :=
  Snake9.LocalRup.prove_clause [c848, c441] c2391 (by decide) p (sat_cons (step848 p h) (sat_cons (step441 p h) (sat_nil p)))
def c2392 : List Lit := [(69, true), (66, false), (56, true), (49, true)]
theorem step2392 (p : Nat → Bool) (h : Constraints p) : clause p c2392 = true :=
  Snake9.LocalRup.prove_clause [c850, c486] c2392 (by decide) p (sat_cons (step850 p h) (sat_cons (step486 p h) (sat_nil p)))
def c2393 : List Lit := [(67, true), (66, false), (56, true), (49, true)]
theorem step2393 (p : Nat → Bool) (h : Constraints p) : clause p c2393 = true :=
  Snake9.LocalRup.prove_clause [c850, c487] c2393 (by decide) p (sat_cons (step850 p h) (sat_cons (step487 p h) (sat_nil p)))
def c2394 : List Lit := [(72, true), (70, false), (60, true)]
theorem step2394 (p : Nat → Bool) (h : Constraints p) : clause p c2394 = true :=
  Snake9.LocalRup.prove_clause [c851, c503] c2394 (by decide) p (sat_cons (step851 p h) (sat_cons (step503 p h) (sat_nil p)))
def c2395 : List Lit := [(32, true), (70, false), (60, true)]
theorem step2395 (p : Nat → Bool) (h : Constraints p) : clause p c2395 = true :=
  Snake9.LocalRup.prove_clause [c851, c504] c2395 (by decide) p (sat_cons (step851 p h) (sat_cons (step504 p h) (sat_nil p)))
def c2396 : List Lit := [(73, true), (71, false), (62, true)]
theorem step2396 (p : Nat → Bool) (h : Constraints p) : clause p c2396 = true :=
  Snake9.LocalRup.prove_clause [c852, c506] c2396 (by decide) p (sat_cons (step852 p h) (sat_cons (step506 p h) (sat_nil p)))
def c2397 : List Lit := [(71, false), (62, true), (67, true)]
theorem step2397 (p : Nat → Bool) (h : Constraints p) : clause p c2397 = true :=
  Snake9.LocalRup.prove_clause [c852, c507] c2397 (by decide) p (sat_cons (step852 p h) (sat_cons (step507 p h) (sat_nil p)))
def c2398 : List Lit := [(75, false), (76, true), (81, true)]
theorem step2398 (p : Nat → Bool) (h : Constraints p) : clause p c2398 = true :=
  Snake9.LocalRup.prove_clause [c853, c526] c2398 (by decide) p (sat_cons (step853 p h) (sat_cons (step526 p h) (sat_nil p)))
def c2399 : List Lit := [(75, false), (74, true), (81, true)]
theorem step2399 (p : Nat → Bool) (h : Constraints p) : clause p c2399 = true :=
  Snake9.LocalRup.prove_clause [c853, c527] c2399 (by decide) p (sat_cons (step853 p h) (sat_cons (step527 p h) (sat_nil p)))
def c2400 : List Lit := [(76, true), (75, false), (74, true)]
theorem step2400 (p : Nat → Bool) (h : Constraints p) : clause p c2400 = true :=
  Snake9.LocalRup.prove_clause [c853, c528] c2400 (by decide) p (sat_cons (step853 p h) (sat_cons (step528 p h) (sat_nil p)))
def c2401 : List Lit := [(77, false), (96, true)]
theorem step2401 (p : Nat → Bool) (h : Constraints p) : clause p c2401 = true :=
  Snake9.LocalRup.prove_clause [c854, c535] c2401 (by decide) p (sat_cons (step854 p h) (sat_cons (step535 p h) (sat_nil p)))
def c2402 : List Lit := [(77, false), (76, true)]
theorem step2402 (p : Nat → Bool) (h : Constraints p) : clause p c2402 = true :=
  Snake9.LocalRup.prove_clause [c854, c536] c2402 (by decide) p (sat_cons (step854 p h) (sat_cons (step536 p h) (sat_nil p)))
def c2403 : List Lit := [(79, true), (78, false), (74, true), (81, true), (85, true), (89, true), (103, true)]
theorem step2403 (p : Nat → Bool) (h : Constraints p) : clause p c2403 = true :=
  Snake9.LocalRup.prove_clause [c855, c558] c2403 (by decide) p (sat_cons (step855 p h) (sat_cons (step558 p h) (sat_nil p)))
def c2404 : List Lit := [(79, true), (78, false), (1, true), (74, true), (81, true), (85, true), (89, true)]
theorem step2404 (p : Nat → Bool) (h : Constraints p) : clause p c2404 = true :=
  Snake9.LocalRup.prove_clause [c855, c559] c2404 (by decide) p (sat_cons (step855 p h) (sat_cons (step559 p h) (sat_nil p)))
def c2405 : List Lit := [(80, false), (81, true), (82, true)]
theorem step2405 (p : Nat → Bool) (h : Constraints p) : clause p c2405 = true :=
  Snake9.LocalRup.prove_clause [c856, c565] c2405 (by decide) p (sat_cons (step856 p h) (sat_cons (step565 p h) (sat_nil p)))
def c2406 : List Lit := [(96, true), (79, true), (81, true), (83, false), (82, true)]
theorem step2406 (p : Nat → Bool) (h : Constraints p) : clause p c2406 = true :=
  Snake9.LocalRup.prove_clause [c857, c584] c2406 (by decide) p (sat_cons (step857 p h) (sat_cons (step584 p h) (sat_nil p)))
def c2407 : List Lit := [(79, true), (81, true), (5, true), (96, true), (83, false)]
theorem step2407 (p : Nat → Bool) (h : Constraints p) : clause p c2407 = true :=
  Snake9.LocalRup.prove_clause [c857, c585] c2407 (by decide) p (sat_cons (step857 p h) (sat_cons (step585 p h) (sat_nil p)))
def c2408 : List Lit := [(6, false), (85, false)]
theorem step2408 (p : Nat → Bool) (h : Constraints p) : clause p c2408 = true :=
  Snake9.LocalRup.prove_clause [c593, c586] c2408 (by decide) p (sat_cons (step593 p h) (sat_cons (step586 p h) (sat_nil p)))
def c2409 : List Lit := [(6, false), (86, false)]
theorem step2409 (p : Nat → Bool) (h : Constraints p) : clause p c2409 = true :=
  Snake9.LocalRup.prove_clause [c593, c587] c2409 (by decide) p (sat_cons (step593 p h) (sat_cons (step587 p h) (sat_nil p)))
def c2410 : List Lit := [(6, false), (108, false)]
theorem step2410 (p : Nat → Bool) (h : Constraints p) : clause p c2410 = true :=
  Snake9.LocalRup.prove_clause [c593, c588] c2410 (by decide) p (sat_cons (step593 p h) (sat_cons (step588 p h) (sat_nil p)))
def c2411 : List Lit := [(85, false), (86, false)]
theorem step2411 (p : Nat → Bool) (h : Constraints p) : clause p c2411 = true :=
  Snake9.LocalRup.prove_clause [c593, c589] c2411 (by decide) p (sat_cons (step593 p h) (sat_cons (step589 p h) (sat_nil p)))
def c2412 : List Lit := [(85, false), (108, false)]
theorem step2412 (p : Nat → Bool) (h : Constraints p) : clause p c2412 = true :=
  Snake9.LocalRup.prove_clause [c593, c590] c2412 (by decide) p (sat_cons (step593 p h) (sat_cons (step590 p h) (sat_nil p)))
def c2413 : List Lit := [(86, false), (108, false)]
theorem step2413 (p : Nat → Bool) (h : Constraints p) : clause p c2413 = true :=
  Snake9.LocalRup.prove_clause [c593, c591] c2413 (by decide) p (sat_cons (step593 p h) (sat_cons (step591 p h) (sat_nil p)))
def c2414 : List Lit := [(87, false), (111, true), (81, true), (85, true)]
theorem step2414 (p : Nat → Bool) (h : Constraints p) : clause p c2414 = true :=
  Snake9.LocalRup.prove_clause [c858, c598] c2414 (by decide) p (sat_cons (step858 p h) (sat_cons (step598 p h) (sat_nil p)))
def c2415 : List Lit := [(98, true), (87, false), (81, true), (85, true)]
theorem step2415 (p : Nat → Bool) (h : Constraints p) : clause p c2415 = true :=
  Snake9.LocalRup.prove_clause [c858, c599] c2415 (by decide) p (sat_cons (step858 p h) (sat_cons (step599 p h) (sat_nil p)))
def c2416 : List Lit := [(88, false), (86, true)]
theorem step2416 (p : Nat → Bool) (h : Constraints p) : clause p c2416 = true :=
  Snake9.LocalRup.prove_clause [c859, c600] c2416 (by decide) p (sat_cons (step859 p h) (sat_cons (step600 p h) (sat_nil p)))
def c2417 : List Lit := [(88, false), (82, true)]
theorem step2417 (p : Nat → Bool) (h : Constraints p) : clause p c2417 = true :=
  Snake9.LocalRup.prove_clause [c859, c601] c2417 (by decide) p (sat_cons (step859 p h) (sat_cons (step601 p h) (sat_nil p)))
def c2418 : List Lit := [(100, true), (91, false), (81, true), (115, true)]
theorem step2418 (p : Nat → Bool) (h : Constraints p) : clause p c2418 = true :=
  Snake9.LocalRup.prove_clause [c860, c615] c2418 (by decide) p (sat_cons (step860 p h) (sat_cons (step615 p h) (sat_nil p)))
def c2419 : List Lit := [(91, false), (115, true), (81, true), (89, true)]
theorem step2419 (p : Nat → Bool) (h : Constraints p) : clause p c2419 = true :=
  Snake9.LocalRup.prove_clause [c860, c616] c2419 (by decide) p (sat_cons (step860 p h) (sat_cons (step616 p h) (sat_nil p)))
def c2420 : List Lit := [(100, true), (91, false), (81, true), (89, true)]
theorem step2420 (p : Nat → Bool) (h : Constraints p) : clause p c2420 = true :=
  Snake9.LocalRup.prove_clause [c860, c617] c2420 (by decide) p (sat_cons (step860 p h) (sat_cons (step617 p h) (sat_nil p)))
def c2421 : List Lit := [(92, false), (90, true)]
theorem step2421 (p : Nat → Bool) (h : Constraints p) : clause p c2421 = true :=
  Snake9.LocalRup.prove_clause [c861, c618] c2421 (by decide) p (sat_cons (step861 p h) (sat_cons (step618 p h) (sat_nil p)))
def c2422 : List Lit := [(92, false), (82, true)]
theorem step2422 (p : Nat → Bool) (h : Constraints p) : clause p c2422 = true :=
  Snake9.LocalRup.prove_clause [c861, c619] c2422 (by decide) p (sat_cons (step861 p h) (sat_cons (step619 p h) (sat_nil p)))
end B112E260
