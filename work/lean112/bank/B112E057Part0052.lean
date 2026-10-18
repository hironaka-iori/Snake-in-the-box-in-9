import B112E057Part0051
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5353 : List Lit := [(1040, false), (1096, false), (1051, false), (70, true), (1048, false), (23, true), (1123, false)]
theorem step5353 (p : Nat → Bool) (h : Constraints p) : clause p c5353 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4340] c5353 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4340 p h) (sat_nil p)))
def c5354 : List Lit := [(69, true), (88, true), (95, false), (79, true), (1027, false), (70, false), (1045, false), (1124, false), (4, false)]
theorem step5354 (p : Nat → Bool) (h : Constraints p) : clause p c5354 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4177] c5354 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4177 p h) (sat_nil p)))
def c5355 : List Lit := [(1032, false), (88, true), (1124, false), (89, true), (79, false), (1039, false), (1053, true), (69, true), (1043, false)]
theorem step5355 (p : Nat → Bool) (h : Constraints p) : clause p c5355 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4287] c5355 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4287 p h) (sat_nil p)))
def c5356 : List Lit := [(1040, false), (89, true), (1032, false), (1043, false), (69, true), (1087, false), (1062, true), (88, true), (1124, false), (1045, false)]
theorem step5356 (p : Nat → Bool) (h : Constraints p) : clause p c5356 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4067] c5356 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4067 p h) (sat_nil p)))
def c5357 : List Lit := [(88, true), (95, true), (1039, false), (1124, false), (1055, false), (86, true), (1043, false), (79, false), (1089, true), (1087, false)]
theorem step5357 (p : Nat → Bool) (h : Constraints p) : clause p c5357 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4270] c5357 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4270 p h) (sat_nil p)))
def c5358 : List Lit := [(1063, false), (1095, false), (70, true), (1124, false), (1053, true), (1037, false), (1027, false), (79, false)]
theorem step5358 (p : Nat → Bool) (h : Constraints p) : clause p c5358 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4064] c5358 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4064 p h) (sat_nil p)))
def c5359 : List Lit := [(1039, false), (1063, false), (70, true), (23, true), (1049, false), (1077, true), (1096, false), (1123, false), (1051, false)]
theorem step5359 (p : Nat → Bool) (h : Constraints p) : clause p c5359 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4366] c5359 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4366 p h) (sat_nil p)))
def c5360 : List Lit := [(5, true), (88, true), (4, false), (23, true), (13, true), (70, false), (7, false)]
theorem step5360 (p : Nat → Bool) (h : Constraints p) : clause p c5360 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4553] c5360 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4553 p h) (sat_nil p)))
def c5361 : List Lit := [(1050, false), (88, true), (1031, false), (89, true), (23, true), (70, true), (1124, false), (79, false)]
theorem step5361 (p : Nat → Bool) (h : Constraints p) : clause p c5361 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3965] c5361 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3965 p h) (sat_nil p)))
def c5362 : List Lit := [(1049, false), (1051, false), (1095, false), (1124, false), (1039, false), (70, true), (23, true)]
theorem step5362 (p : Nat → Bool) (h : Constraints p) : clause p c5362 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3950] c5362 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3950 p h) (sat_nil p)))
def c5363 : List Lit := [(1049, false), (88, true), (70, true), (1124, false), (23, true), (1032, false), (1045, false), (69, true)]
theorem step5363 (p : Nat → Bool) (h : Constraints p) : clause p c5363 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3959] c5363 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3959 p h) (sat_nil p)))
def c5364 : List Lit := [(1040, false), (88, true), (1124, false), (86, false), (70, true), (23, true), (1043, false), (89, true)]
theorem step5364 (p : Nat → Bool) (h : Constraints p) : clause p c5364 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3944] c5364 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3944 p h) (sat_nil p)))
def c5365 : List Lit := [(1089, false), (88, true), (1045, false), (1048, false), (1103, true), (1039, false), (1124, false)]
theorem step5365 (p : Nat → Bool) (h : Constraints p) : clause p c5365 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4156] c5365 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4156 p h) (sat_nil p)))
def c5366 : List Lit := [(88, true), (1046, false), (4, false), (70, false), (95, false), (79, false), (1027, false), (1124, false)]
theorem step5366 (p : Nat → Bool) (h : Constraints p) : clause p c5366 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4148] c5366 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4148 p h) (sat_nil p)))
def c5367 : List Lit := [(1046, false), (1049, false), (89, true), (1056, false), (88, true), (1039, false), (1124, false)]
theorem step5367 (p : Nat → Bool) (h : Constraints p) : clause p c5367 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4192] c5367 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4192 p h) (sat_nil p)))
def c5368 : List Lit := [(1041, false), (1087, false), (1045, false), (90, false), (1055, false), (1061, false), (1077, true), (88, true)]
theorem step5368 (p : Nat → Bool) (h : Constraints p) : clause p c5368 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4551] c5368 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4551 p h) (sat_nil p)))
def c5369 : List Lit := [(1050, false), (88, true), (1038, false), (1032, false), (1087, false), (1124, false), (1053, false)]
theorem step5369 (p : Nat → Bool) (h : Constraints p) : clause p c5369 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4284] c5369 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4284 p h) (sat_nil p)))
def c5370 : List Lit := [(1050, false), (72, false), (1087, false), (1124, false), (88, true), (1053, false), (89, true), (1037, false)]
theorem step5370 (p : Nat → Bool) (h : Constraints p) : clause p c5370 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4196] c5370 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4196 p h) (sat_nil p)))
def c5371 : List Lit := [(1049, false), (69, true), (1087, false), (1053, false), (1032, false), (1124, false), (1056, true), (1045, false), (88, true)]
theorem step5371 (p : Nat → Bool) (h : Constraints p) : clause p c5371 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4263] c5371 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4263 p h) (sat_nil p)))
def c5372 : List Lit := [(1033, false), (90, false), (1039, false), (1062, false), (1076, true), (1087, false), (88, true), (1124, false)]
theorem step5372 (p : Nat → Bool) (h : Constraints p) : clause p c5372 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3941] c5372 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3941 p h) (sat_nil p)))
def c5373 : List Lit := [(1049, false), (72, false), (1038, false), (1124, false), (1053, false), (88, true), (89, true), (1087, false), (1057, true)]
theorem step5373 (p : Nat → Bool) (h : Constraints p) : clause p c5373 = true :=
  Snake9.LocalRup.prove_clause [c4887, c3973] c5373 (by decide) p (sat_cons (step4887 p h) (sat_cons (step3973 p h) (sat_nil p)))
def c5374 : List Lit := [(97, true), (1096, false), (1089, true), (1083, false), (1039, false), (79, false), (1043, false), (1124, false)]
theorem step5374 (p : Nat → Bool) (h : Constraints p) : clause p c5374 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4630] c5374 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4630 p h) (sat_nil p)))
def c5375 : List Lit := [(1096, false), (1049, false), (1051, false), (1039, false), (1124, false)]
theorem step5375 (p : Nat → Bool) (h : Constraints p) : clause p c5375 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4644] c5375 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4644 p h) (sat_nil p)))
def c5376 : List Lit := [(1062, false), (1091, false), (1027, false), (82, false), (1039, false), (1124, false), (70, false), (1076, true)]
theorem step5376 (p : Nat → Bool) (h : Constraints p) : clause p c5376 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4645] c5376 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4645 p h) (sat_nil p)))
def c5377 : List Lit := [(76, false), (1051, true), (1134, true), (1096, false)]
theorem step5377 (p : Nat → Bool) (h : Constraints p) : clause p c5377 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4650] c5377 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4650 p h) (sat_nil p)))
def c5378 : List Lit := [(1033, false), (97, true), (73, true), (69, true), (114, false), (124, true), (77, true), (1075, true), (79, false), (89, false)]
theorem step5378 (p : Nat → Bool) (h : Constraints p) : clause p c5378 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4662] c5378 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4662 p h) (sat_nil p)))
def c5379 : List Lit := [(1033, false), (89, false), (1061, false), (1124, false), (79, false), (1135, true), (1043, true), (69, true), (1085, false)]
theorem step5379 (p : Nat → Bool) (h : Constraints p) : clause p c5379 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4663] c5379 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4663 p h) (sat_nil p)))
def c5380 : List Lit := [(1063, false), (1091, false), (1123, false), (1040, true), (1027, false), (4, false), (70, false)]
theorem step5380 (p : Nat → Bool) (h : Constraints p) : clause p c5380 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4676] c5380 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4676 p h) (sat_nil p)))
def c5381 : List Lit := [(1089, false), (1056, false), (1045, false), (82, true), (1123, false), (1039, false), (1102, true)]
theorem step5381 (p : Nat → Bool) (h : Constraints p) : clause p c5381 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4725] c5381 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4725 p h) (sat_nil p)))
def c5382 : List Lit := [(1026, false), (77, true), (1056, false), (1076, true), (1101, false), (70, true), (1027, false), (1045, false), (123, true)]
theorem step5382 (p : Nat → Bool) (h : Constraints p) : clause p c5382 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4736] c5382 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4736 p h) (sat_nil p)))
def c5383 : List Lit := [(1125, false), (1084, true), (1039, false), (1051, false), (95, true), (1047, false), (1091, false)]
theorem step5383 (p : Nat → Bool) (h : Constraints p) : clause p c5383 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4783] c5383 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4783 p h) (sat_nil p)))
def c5384 : List Lit := [(1102, false), (75, false), (89, true), (1038, false), (1053, false), (1049, false)]
theorem step5384 (p : Nat → Bool) (h : Constraints p) : clause p c5384 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4798] c5384 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4798 p h) (sat_nil p)))
def c5385 : List Lit := [(97, true), (1049, false), (1051, false), (1039, false), (1124, false), (1063, true), (79, false)]
theorem step5385 (p : Nat → Bool) (h : Constraints p) : clause p c5385 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4802] c5385 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4802 p h) (sat_nil p)))
def c5386 : List Lit := [(97, true), (89, false), (79, false), (1039, false), (1137, true), (1045, false), (1053, true), (109, false), (88, true), (114, true)]
theorem step5386 (p : Nat → Bool) (h : Constraints p) : clause p c5386 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4803] c5386 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4803 p h) (sat_nil p)))
def c5387 : List Lit := [(86, false), (1045, false), (97, true), (1125, false), (1096, true), (1039, false), (88, true), (1056, false)]
theorem step5387 (p : Nat → Bool) (h : Constraints p) : clause p c5387 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4805] c5387 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4805 p h) (sat_nil p)))
def c5388 : List Lit := [(76, false), (1101, false), (1032, false), (1063, false), (77, false), (88, true)]
theorem step5388 (p : Nat → Bool) (h : Constraints p) : clause p c5388 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4808] c5388 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4808 p h) (sat_nil p)))
def c5389 : List Lit := [(76, false), (1063, false), (79, false), (1027, false), (75, false), (1021, true), (89, true), (77, false), (88, true)]
theorem step5389 (p : Nat → Bool) (h : Constraints p) : clause p c5389 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4809] c5389 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4809 p h) (sat_nil p)))
def c5390 : List Lit := [(1063, false), (1101, false), (1049, false), (89, true), (77, false), (73, true), (88, true)]
theorem step5390 (p : Nat → Bool) (h : Constraints p) : clause p c5390 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4813] c5390 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4813 p h) (sat_nil p)))
def c5391 : List Lit := [(1125, false), (1048, false), (95, true), (1095, false), (79, false), (1039, false), (1061, true)]
theorem step5391 (p : Nat → Bool) (h : Constraints p) : clause p c5391 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4844] c5391 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4844 p h) (sat_nil p)))
def c5392 : List Lit := [(104, true), (101, false), (1091, false), (1124, false), (1039, false), (1051, false), (1100, false), (1048, false)]
theorem step5392 (p : Nat → Bool) (h : Constraints p) : clause p c5392 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4871] c5392 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4871 p h) (sat_nil p)))
def c5393 : List Lit := [(1087, true), (1040, false), (1051, false), (1048, false), (1091, false), (1124, false)]
theorem step5393 (p : Nat → Bool) (h : Constraints p) : clause p c5393 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4883] c5393 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4883 p h) (sat_nil p)))
def c5394 : List Lit := [(1033, false), (1040, false), (90, true), (123, true), (105, true), (72, false), (1048, false), (88, false), (86, false)]
theorem step5394 (p : Nat → Bool) (h : Constraints p) : clause p c5394 = true :=
  Snake9.LocalRup.prove_clause [c4887, c4884] c5394 (by decide) p (sat_cons (step4887 p h) (sat_cons (step4884 p h) (sat_nil p)))
def c5395 : List Lit := [(26, false), (932, true), (920, true), (4, true), (73, false), (30, false)]
theorem step5395 (p : Nat → Bool) (h : Constraints p) : clause p c5395 = true :=
  Snake9.LocalRup.prove_clause [c2413, c2463, c5288, c5289, c5008, c1310] c5395 (by decide) p (sat_cons (step2413 p h) (sat_cons (step2463 p h) (sat_cons (step5288 p h) (sat_cons (step5289 p h) (sat_cons (step5008 p h) (sat_cons (step1310 p h) (sat_nil p)))))))
def c5396 : List Lit := [(5, false), (886, true), (920, true), (4, true), (73, false)]
theorem step5396 (p : Nat → Bool) (h : Constraints p) : clause p c5396 = true :=
  Snake9.LocalRup.prove_clause [c5010, c5288, c1306, c5008] c5396 (by decide) p (sat_cons (step5010 p h) (sat_cons (step5288 p h) (sat_cons (step1306 p h) (sat_cons (step5008 p h) (sat_nil p)))))
def c5397 : List Lit := [(869, false), (26, true), (886, true), (891, true), (920, true), (5, true), (4, true)]
theorem step5397 (p : Nat → Bool) (h : Constraints p) : clause p c5397 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1334, c5008, c1306, c1313, c1312, c1264, c1273, c1276, c1302, c1303, c1266, c1375, c5159, c2193, c1342, c1350, c1281, c1282, c185, c93, c2223, c2597, c10, c1030, c1031, c1032, c1043, c1074, c2381, c1135, c1068, c2408, c1067, c1256, c1060, c1061, c1188, c1059, c1058, c1158, c232, c1143, c2957, c1139, c1138, c2284, c5157, c2622, c2230, c1338, c219, c1328, c2794] c5397 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1334 p h) (sat_cons (step5008 p h) (sat_cons (step1306 p h) (sat_cons (step1313 p h) (sat_cons (step1312 p h) (sat_cons (step1264 p h) (sat_cons (step1273 p h) (sat_cons (step1276 p h) (sat_cons (step1302 p h) (sat_cons (step1303 p h) (sat_cons (step1266 p h) (sat_cons (step1375 p h) (sat_cons (step5159 p h) (sat_cons (step2193 p h) (sat_cons (step1342 p h) (sat_cons (step1350 p h) (sat_cons (step1281 p h) (sat_cons (step1282 p h) (sat_cons (step185 p h) (sat_cons (step93 p h) (sat_cons (step2223 p h) (sat_cons (step2597 p h) (sat_cons (step10 p h) (sat_cons (step1030 p h) (sat_cons (step1031 p h) (sat_cons (step1032 p h) (sat_cons (step1043 p h) (sat_cons (step1074 p h) (sat_cons (step2381 p h) (sat_cons (step1135 p h) (sat_cons (step1068 p h) (sat_cons (step2408 p h) (sat_cons (step1067 p h) (sat_cons (step1256 p h) (sat_cons (step1060 p h) (sat_cons (step1061 p h) (sat_cons (step1188 p h) (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step1158 p h) (sat_cons (step232 p h) (sat_cons (step1143 p h) (sat_cons (step2957 p h) (sat_cons (step1139 p h) (sat_cons (step1138 p h) (sat_cons (step2284 p h) (sat_cons (step5157 p h) (sat_cons (step2622 p h) (sat_cons (step2230 p h) (sat_cons (step1338 p h) (sat_cons (step219 p h) (sat_cons (step1328 p h) (sat_cons (step2794 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5398 : List Lit := [(901, false), (9, false), (20, true), (909, true), (6, false), (7, false), (26, true)]
theorem step5398 (p : Nat → Bool) (h : Constraints p) : clause p c5398 = true :=
  Snake9.LocalRup.prove_clause [c1342, c1327, c1335, c1338, c1346, c1328, c1318, c4697, c1315] c5398 (by decide) p (sat_cons (step1342 p h) (sat_cons (step1327 p h) (sat_cons (step1335 p h) (sat_cons (step1338 p h) (sat_cons (step1346 p h) (sat_cons (step1328 p h) (sat_cons (step1318 p h) (sat_cons (step4697 p h) (sat_cons (step1315 p h) (sat_nil p))))))))))
def c5399 : List Lit := [(872, false), (869, true), (26, true), (886, true), (891, true), (920, true), (5, true)]
theorem step5399 (p : Nat → Bool) (h : Constraints p) : clause p c5399 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1267, c1327, c1334, c5008, c1313, c1312, c1302, c1303, c1375, c1289, c5159, c1350, c1281, c1282, c1319, c185, c93, c2223, c2597, c1280, c5150, c2208, c2204, c172, c5398, c1329, c2622, c2240, c1978, c2957, c1317, c229, c236] c5399 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1267 p h) (sat_cons (step1327 p h) (sat_cons (step1334 p h) (sat_cons (step5008 p h) (sat_cons (step1313 p h) (sat_cons (step1312 p h) (sat_cons (step1302 p h) (sat_cons (step1303 p h) (sat_cons (step1375 p h) (sat_cons (step1289 p h) (sat_cons (step5159 p h) (sat_cons (step1350 p h) (sat_cons (step1281 p h) (sat_cons (step1282 p h) (sat_cons (step1319 p h) (sat_cons (step185 p h) (sat_cons (step93 p h) (sat_cons (step2223 p h) (sat_cons (step2597 p h) (sat_cons (step1280 p h) (sat_cons (step5150 p h) (sat_cons (step2208 p h) (sat_cons (step2204 p h) (sat_cons (step172 p h) (sat_cons (step5398 p h) (sat_cons (step1329 p h) (sat_cons (step2622 p h) (sat_cons (step2240 p h) (sat_cons (step1978 p h) (sat_cons (step2957 p h) (sat_cons (step1317 p h) (sat_cons (step229 p h) (sat_cons (step236 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c5400 : List Lit := [(909, true), (15, false), (901, true), (26, true)]
theorem step5400 (p : Nat → Bool) (h : Constraints p) : clause p c5400 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1334, c1350, c2622, c5157, c2284, c1138, c1139, c1143, c1158, c1188, c1256, c2408, c1135, c1072, c1068, c1067, c1060, c1061, c1059, c1058, c232, c4989, c2957, c2228, c2126] c5400 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1334 p h) (sat_cons (step1350 p h) (sat_cons (step2622 p h) (sat_cons (step5157 p h) (sat_cons (step2284 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1143 p h) (sat_cons (step1158 p h) (sat_cons (step1188 p h) (sat_cons (step1256 p h) (sat_cons (step2408 p h) (sat_cons (step1135 p h) (sat_cons (step1072 p h) (sat_cons (step1068 p h) (sat_cons (step1067 p h) (sat_cons (step1060 p h) (sat_cons (step1061 p h) (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step232 p h) (sat_cons (step4989 p h) (sat_cons (step2957 p h) (sat_cons (step2228 p h) (sat_cons (step2126 p h) (sat_nil p)))))))))))))))))))))))))))
def c5401 : List Lit := [(15, false), (901, true), (5, true), (869, true), (26, true), (920, true), (4, true)]
theorem step5401 (p : Nat → Bool) (h : Constraints p) : clause p c5401 = true :=
  Snake9.LocalRup.prove_clause [c1329, c1268, c1267, c1327, c1334, c5400, c1375, c2741, c1278, c1279, c4721, c113, c5150, c2241, c2240, c2200, c1978, c2152, c1316, c1369, c1321, c1355, c1351, c1322, c1324, c1337, c1317, c1328, c4697, c181, c180, c1314] c5401 (by decide) p (sat_cons (step1329 p h) (sat_cons (step1268 p h) (sat_cons (step1267 p h) (sat_cons (step1327 p h) (sat_cons (step1334 p h) (sat_cons (step5400 p h) (sat_cons (step1375 p h) (sat_cons (step2741 p h) (sat_cons (step1278 p h) (sat_cons (step1279 p h) (sat_cons (step4721 p h) (sat_cons (step113 p h) (sat_cons (step5150 p h) (sat_cons (step2241 p h) (sat_cons (step2240 p h) (sat_cons (step2200 p h) (sat_cons (step1978 p h) (sat_cons (step2152 p h) (sat_cons (step1316 p h) (sat_cons (step1369 p h) (sat_cons (step1321 p h) (sat_cons (step1355 p h) (sat_cons (step1351 p h) (sat_cons (step1322 p h) (sat_cons (step1324 p h) (sat_cons (step1337 p h) (sat_cons (step1317 p h) (sat_cons (step1328 p h) (sat_cons (step4697 p h) (sat_cons (step181 p h) (sat_cons (step180 p h) (sat_cons (step1314 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c5402 : List Lit := [(23, false), (909, true), (901, true), (26, true)]
theorem step5402 (p : Nat → Bool) (h : Constraints p) : clause p c5402 = true :=
  Snake9.LocalRup.prove_clause [c1327, c5157, c2284, c1138, c1139, c1143, c1158, c1188, c1256, c2408, c1135, c1072, c1068, c1067, c1060, c1061, c1059, c1058, c232, c4989, c2957, c2228, c2126] c5402 (by decide) p (sat_cons (step1327 p h) (sat_cons (step5157 p h) (sat_cons (step2284 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1143 p h) (sat_cons (step1158 p h) (sat_cons (step1188 p h) (sat_cons (step1256 p h) (sat_cons (step2408 p h) (sat_cons (step1135 p h) (sat_cons (step1072 p h) (sat_cons (step1068 p h) (sat_cons (step1067 p h) (sat_cons (step1060 p h) (sat_cons (step1061 p h) (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step232 p h) (sat_cons (step4989 p h) (sat_cons (step2957 p h) (sat_cons (step2228 p h) (sat_cons (step2126 p h) (sat_nil p))))))))))))))))))))))))
def c5403 : List Lit := [(901, true), (5, true), (869, true), (26, true), (920, true), (4, true)]
theorem step5403 (p : Nat → Bool) (h : Constraints p) : clause p c5403 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1334, c1329, c5401, c2700, c1375, c1350, c5402, c2241, c2239, c2126, c1316, c1318, c1321, c1345, c1312, c1380, c116, c5037, c1278] c5403 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1334 p h) (sat_cons (step1329 p h) (sat_cons (step5401 p h) (sat_cons (step2700 p h) (sat_cons (step1375 p h) (sat_cons (step1350 p h) (sat_cons (step5402 p h) (sat_cons (step2241 p h) (sat_cons (step2239 p h) (sat_cons (step2126 p h) (sat_cons (step1316 p h) (sat_cons (step1318 p h) (sat_cons (step1321 p h) (sat_cons (step1345 p h) (sat_cons (step1312 p h) (sat_cons (step1380 p h) (sat_cons (step116 p h) (sat_cons (step5037 p h) (sat_cons (step1278 p h) (sat_nil p)))))))))))))))))))))
def c5404 : List Lit := [(9, false), (6, false), (7, false), (909, true), (901, false), (26, true)]
theorem step5404 (p : Nat → Bool) (h : Constraints p) : clause p c5404 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1335, c1346, c1320, c1313, c1312, c5398, c183] c5404 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1335 p h) (sat_cons (step1346 p h) (sat_cons (step1320 p h) (sat_cons (step1313 p h) (sat_cons (step1312 p h) (sat_cons (step5398 p h) (sat_cons (step183 p h) (sat_nil p)))))))))
def c5405 : List Lit := [(909, true), (5, true), (901, false), (26, true), (920, true), (4, true)]
theorem step5405 (p : Nat → Bool) (h : Constraints p) : clause p c5405 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1335, c1341, c1380, c1342, c1346, c1338, c1318, c1320, c1328, c1315, c1312, c5397, c2794, c1267, c1268, c5399, c232, c2973, c1059, c1282, c1060, c1067, c1068, c2381, c1043, c1032, c1031, c1030, c4953, c5404, c1279, c5037, c5295, c112] c5405 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1335 p h) (sat_cons (step1341 p h) (sat_cons (step1380 p h) (sat_cons (step1342 p h) (sat_cons (step1346 p h) (sat_cons (step1338 p h) (sat_cons (step1318 p h) (sat_cons (step1320 p h) (sat_cons (step1328 p h) (sat_cons (step1315 p h) (sat_cons (step1312 p h) (sat_cons (step5397 p h) (sat_cons (step2794 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step5399 p h) (sat_cons (step232 p h) (sat_cons (step2973 p h) (sat_cons (step1059 p h) (sat_cons (step1282 p h) (sat_cons (step1060 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step2381 p h) (sat_cons (step1043 p h) (sat_cons (step1032 p h) (sat_cons (step1031 p h) (sat_cons (step1030 p h) (sat_cons (step4953 p h) (sat_cons (step5404 p h) (sat_cons (step1279 p h) (sat_cons (step5037 p h) (sat_cons (step5295 p h) (sat_cons (step112 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c5406 : List Lit := [(869, true), (5, true), (901, false), (26, true), (920, true), (4, true)]
theorem step5406 (p : Nat → Bool) (h : Constraints p) : clause p c5406 = true :=
  Snake9.LocalRup.prove_clause [c5405, c1375, c2700, c1327, c1335, c1267, c1268, c2741, c1279, c4721, c5150, c1320, c2200, c2152, c1369, c1347, c1351, c1338, c1323, c1321, c1328, c1315, c4697, c181, c180, c1314] c5406 (by decide) p (sat_cons (step5405 p h) (sat_cons (step1375 p h) (sat_cons (step2700 p h) (sat_cons (step1327 p h) (sat_cons (step1335 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step2741 p h) (sat_cons (step1279 p h) (sat_cons (step4721 p h) (sat_cons (step5150 p h) (sat_cons (step1320 p h) (sat_cons (step2200 p h) (sat_cons (step2152 p h) (sat_cons (step1369 p h) (sat_cons (step1347 p h) (sat_cons (step1351 p h) (sat_cons (step1338 p h) (sat_cons (step1323 p h) (sat_cons (step1321 p h) (sat_cons (step1328 p h) (sat_cons (step1315 p h) (sat_cons (step4697 p h) (sat_cons (step181 p h) (sat_cons (step180 p h) (sat_cons (step1314 p h) (sat_nil p)))))))))))))))))))))))))))
def c5407 : List Lit := [(18, false), (1043, false), (86, true), (88, false), (19, true), (36, true), (23, true), (201, true), (220, true), (145, true), (1053, false), (8, false), (78, false), (7, false), (9, false), (5, true), (73, false)]
theorem step5407 (p : Nat → Bool) (h : Constraints p) : clause p c5407 = true :=
  Snake9.LocalRup.prove_clause [c59, c169, c2294, c2296, c5014, c3780, c4280, c5013, c3350, c528, c2286, c522, c2980, c591, c595, c1766, c1545, c2106, c5317, c2082, c1661, c1576] c5407 (by decide) p (sat_cons (step59 p h) (sat_cons (step169 p h) (sat_cons (step2294 p h) (sat_cons (step2296 p h) (sat_cons (step5014 p h) (sat_cons (step3780 p h) (sat_cons (step4280 p h) (sat_cons (step5013 p h) (sat_cons (step3350 p h) (sat_cons (step528 p h) (sat_cons (step2286 p h) (sat_cons (step522 p h) (sat_cons (step2980 p h) (sat_cons (step591 p h) (sat_cons (step595 p h) (sat_cons (step1766 p h) (sat_cons (step1545 p h) (sat_cons (step2106 p h) (sat_cons (step5317 p h) (sat_cons (step2082 p h) (sat_cons (step1661 p h) (sat_cons (step1576 p h) (sat_nil p)))))))))))))))))))))))
def c5408 : List Lit := [(1032, false), (1096, true), (1040, true), (1111, false), (1063, false), (69, true), (88, false), (17, false), (1087, false), (15, false)]
theorem step5408 (p : Nat → Bool) (h : Constraints p) : clause p c5408 = true :=
  Snake9.LocalRup.prove_clause [c1544, c2081, c1571, c1576, c1653, c2082, c5316, c1545, c4766, c5196, c743] c5408 (by decide) p (sat_cons (step1544 p h) (sat_cons (step2081 p h) (sat_cons (step1571 p h) (sat_cons (step1576 p h) (sat_cons (step1653 p h) (sat_cons (step2082 p h) (sat_cons (step5316 p h) (sat_cons (step1545 p h) (sat_cons (step4766 p h) (sat_cons (step5196 p h) (sat_cons (step743 p h) (sat_nil p))))))))))))
def c5409 : List Lit := [(95, true), (1040, true), (1135, true), (1111, false), (1085, false), (1063, false), (77, true), (69, true), (88, false), (17, false), (1087, false), (205, true), (78, false), (9, false), (15, false)]
theorem step5409 (p : Nat → Bool) (h : Constraints p) : clause p c5409 = true :=
  Snake9.LocalRup.prove_clause [c1749, c1776, c1554, c1676, c2969, c1684, c1768, c1714, c1751, c1744, c5408, c1559, c1550, c732, c590, c4769] c5409 (by decide) p (sat_cons (step1749 p h) (sat_cons (step1776 p h) (sat_cons (step1554 p h) (sat_cons (step1676 p h) (sat_cons (step2969 p h) (sat_cons (step1684 p h) (sat_cons (step1768 p h) (sat_cons (step1714 p h) (sat_cons (step1751 p h) (sat_cons (step1744 p h) (sat_cons (step5408 p h) (sat_cons (step1559 p h) (sat_cons (step1550 p h) (sat_cons (step732 p h) (sat_cons (step590 p h) (sat_cons (step4769 p h) (sat_nil p)))))))))))))))))
def c5410 : List Lit := [(1032, true), (85, false), (1077, true), (1029, false), (89, true), (69, true), (1043, false), (1053, false), (78, false), (7, false), (9, false), (5, true), (73, false)]
theorem step5410 (p : Nat → Bool) (h : Constraints p) : clause p c5410 = true :=
  Snake9.LocalRup.prove_clause [c3877, c1559, c4485, c1550, c2112, c590, c594, c1589, c1545, c1595, c2082, c1605, c1575, c1624, c1654] c5410 (by decide) p (sat_cons (step3877 p h) (sat_cons (step1559 p h) (sat_cons (step4485 p h) (sat_cons (step1550 p h) (sat_cons (step2112 p h) (sat_cons (step590 p h) (sat_cons (step594 p h) (sat_cons (step1589 p h) (sat_cons (step1545 p h) (sat_cons (step1595 p h) (sat_cons (step2082 p h) (sat_cons (step1605 p h) (sat_cons (step1575 p h) (sat_cons (step1624 p h) (sat_cons (step1654 p h) (sat_nil p))))))))))))))))
def c5411 : List Lit := [(1077, true), (1111, false), (1085, false), (98, true), (77, true), (89, true), (69, true), (1043, false), (86, true), (88, false), (17, false), (1087, false), (23, true), (201, true), (205, true), (1053, false), (78, false), (7, false), (9, false), (15, false), (5, true), (73, false)]
theorem step5411 (p : Nat → Bool) (h : Constraints p) : clause p c5411 = true :=
  Snake9.LocalRup.prove_clause [c4708, c3877, c1544, c2081, c1570, c1645, c5309, c1749, c1554, c1661, c5409, c2333, c5013, c2295, c5410, c1571, c5408, c1653, c1709, c5316, c1771] c5411 (by decide) p (sat_cons (step4708 p h) (sat_cons (step3877 p h) (sat_cons (step1544 p h) (sat_cons (step2081 p h) (sat_cons (step1570 p h) (sat_cons (step1645 p h) (sat_cons (step5309 p h) (sat_cons (step1749 p h) (sat_cons (step1554 p h) (sat_cons (step1661 p h) (sat_cons (step5409 p h) (sat_cons (step2333 p h) (sat_cons (step5013 p h) (sat_cons (step2295 p h) (sat_cons (step5410 p h) (sat_cons (step1571 p h) (sat_cons (step5408 p h) (sat_cons (step1653 p h) (sat_cons (step1709 p h) (sat_cons (step5316 p h) (sat_cons (step1771 p h) (sat_nil p))))))))))))))))))))))
def c5412 : List Lit := [(19, true), (1087, false), (36, true), (23, true), (201, true), (205, true), (220, true), (225, true), (145, true), (1053, false), (8, false), (78, false), (7, false), (20, true), (892, true), (9, false), (10, false), (11, false), (2, false), (15, false), (5, true), (73, false)]
theorem step5412 (p : Nat → Bool) (h : Constraints p) : clause p c5412 = true :=
  Snake9.LocalRup.prove_clause [c90, c1314, c2221, c2223, c1974, c76, c4712, c5407, c2202, c534, c540, c539, c541, c542, c3014, c1679, c1727, c1729, c1749, c5411, c5317, c1766, c5022, c1712, c2332, c1682, c1684, c1680, c2872] c5412 (by decide) p (sat_cons (step90 p h) (sat_cons (step1314 p h) (sat_cons (step2221 p h) (sat_cons (step2223 p h) (sat_cons (step1974 p h) (sat_cons (step76 p h) (sat_cons (step4712 p h) (sat_cons (step5407 p h) (sat_cons (step2202 p h) (sat_cons (step534 p h) (sat_cons (step540 p h) (sat_cons (step539 p h) (sat_cons (step541 p h) (sat_cons (step542 p h) (sat_cons (step3014 p h) (sat_cons (step1679 p h) (sat_cons (step1727 p h) (sat_cons (step1729 p h) (sat_cons (step1749 p h) (sat_cons (step5411 p h) (sat_cons (step5317 p h) (sat_cons (step1766 p h) (sat_cons (step5022 p h) (sat_cons (step1712 p h) (sat_cons (step2332 p h) (sat_cons (step1682 p h) (sat_cons (step1684 p h) (sat_cons (step1680 p h) (sat_cons (step2872 p h) (sat_nil p))))))))))))))))))))))))))))))
def c5413 : List Lit := [(88, true), (1133, true), (1087, false)]
theorem step5413 (p : Nat → Bool) (h : Constraints p) : clause p c5413 = true :=
  Snake9.LocalRup.prove_clause [c3003, c4376, c1708, c1766] c5413 (by decide) p (sat_cons (step3003 p h) (sat_cons (step4376 p h) (sat_cons (step1708 p h) (sat_cons (step1766 p h) (sat_nil p)))))
def c5414 : List Lit := [(1133, true), (74, false), (76, true), (86, true), (1087, false), (23, true), (201, true), (220, true), (78, false)]
theorem step5414 (p : Nat → Bool) (h : Constraints p) : clause p c5414 = true :=
  Snake9.LocalRup.prove_clause [c5413, c5013, c528, c522, c5240, c2980, c1766] c5414 (by decide) p (sat_cons (step5413 p h) (sat_cons (step5013 p h) (sat_cons (step528 p h) (sat_cons (step522 p h) (sat_cons (step5240 p h) (sat_cons (step2980 p h) (sat_cons (step1766 p h) (sat_nil p))))))))
def c5415 : List Lit := [(77, false), (69, true), (1077, true), (85, false), (89, true), (86, true), (1043, false), (1053, false), (78, false), (7, false), (9, false), (5, true), (73, false)]
theorem step5415 (p : Nat → Bool) (h : Constraints p) : clause p c5415 = true :=
  Snake9.LocalRup.prove_clause [c3877, c591, c595, c1545, c2106, c1595, c2082, c1661, c1605, c1575, c1576, c1654, c4485, c1624, c2112, c1589] c5415 (by decide) p (sat_cons (step3877 p h) (sat_cons (step591 p h) (sat_cons (step595 p h) (sat_cons (step1545 p h) (sat_cons (step2106 p h) (sat_cons (step1595 p h) (sat_cons (step2082 p h) (sat_cons (step1661 p h) (sat_cons (step1605 p h) (sat_cons (step1575 p h) (sat_cons (step1576 p h) (sat_cons (step1654 p h) (sat_cons (step4485 p h) (sat_cons (step1624 p h) (sat_cons (step2112 p h) (sat_cons (step1589 p h) (sat_nil p)))))))))))))))))
def c5416 : List Lit := [(69, true), (1077, true), (74, false), (85, false), (89, true), (86, true), (1043, false), (201, true), (1053, false), (78, false), (7, false), (9, false), (5, true), (73, false)]
theorem step5416 (p : Nat → Bool) (h : Constraints p) : clause p c5416 = true :=
  Snake9.LocalRup.prove_clause [c5415, c1554, c522, c5410, c590, c528, c594, c1545, c4996, c2082, c1661, c1576] c5416 (by decide) p (sat_cons (step5415 p h) (sat_cons (step1554 p h) (sat_cons (step522 p h) (sat_cons (step5410 p h) (sat_cons (step590 p h) (sat_cons (step528 p h) (sat_cons (step594 p h) (sat_cons (step1545 p h) (sat_cons (step4996 p h) (sat_cons (step2082 p h) (sat_cons (step1661 p h) (sat_cons (step1576 p h) (sat_nil p)))))))))))))
end B112E057
