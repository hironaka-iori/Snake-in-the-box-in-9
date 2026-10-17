import B112E154Inputs
namespace B112E154
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c450 : List Lit := [(70, true)]
theorem step450 (p : Nat → Bool) (h : Constraints p) : clause p c450 = true :=
  Snake9.LocalRup.prove_clause [c89, c88] c450 (by decide) p (sat_cons (step89 p h) (sat_cons (step88 p h) (sat_nil p)))
def c451 : List Lit := [(171, true), (69, true)]
theorem step451 (p : Nat → Bool) (h : Constraints p) : clause p c451 = true :=
  Snake9.LocalRup.prove_clause [c450, c91] c451 (by decide) p (sat_cons (step450 p h) (sat_cons (step91 p h) (sat_nil p)))
def c452 : List Lit := [(45, false)]
theorem step452 (p : Nat → Bool) (h : Constraints p) : clause p c452 = true :=
  Snake9.LocalRup.prove_clause [c151, c61] c452 (by decide) p (sat_cons (step151 p h) (sat_cons (step61 p h) (sat_nil p)))
def c453 : List Lit := [(54, false)]
theorem step453 (p : Nat → Bool) (h : Constraints p) : clause p c453 = true :=
  Snake9.LocalRup.prove_clause [c155, c75] c453 (by decide) p (sat_cons (step155 p h) (sat_cons (step75 p h) (sat_nil p)))
def c454 : List Lit := [(398, false)]
theorem step454 (p : Nat → Bool) (h : Constraints p) : clause p c454 = true :=
  Snake9.LocalRup.prove_clause [c254, c251] c454 (by decide) p (sat_cons (step254 p h) (sat_cons (step251 p h) (sat_nil p)))
def c455 : List Lit := [(300, false)]
theorem step455 (p : Nat → Bool) (h : Constraints p) : clause p c455 = true :=
  Snake9.LocalRup.prove_clause [c254, c253] c455 (by decide) p (sat_cons (step254 p h) (sat_cons (step253 p h) (sat_nil p)))
def c456 : List Lit := [(348, false)]
theorem step456 (p : Nat → Bool) (h : Constraints p) : clause p c456 = true :=
  Snake9.LocalRup.prove_clause [c454, c250] c456 (by decide) p (sat_cons (step454 p h) (sat_cons (step250 p h) (sat_nil p)))
def c457 : List Lit := [(298, false)]
theorem step457 (p : Nat → Bool) (h : Constraints p) : clause p c457 = true :=
  Snake9.LocalRup.prove_clause [c455, c191] c457 (by decide) p (sat_cons (step455 p h) (sat_cons (step191 p h) (sat_nil p)))
def c458 : List Lit := [(346, false)]
theorem step458 (p : Nat → Bool) (h : Constraints p) : clause p c458 = true :=
  Snake9.LocalRup.prove_clause [c456, c221] c458 (by decide) p (sat_cons (step456 p h) (sat_cons (step221 p h) (sat_nil p)))
def c459 : List Lit := [(296, false)]
theorem step459 (p : Nat → Bool) (h : Constraints p) : clause p c459 = true :=
  Snake9.LocalRup.prove_clause [c457, c189] c459 (by decide) p (sat_cons (step457 p h) (sat_cons (step189 p h) (sat_nil p)))
def c460 : List Lit := [(282, false)]
theorem step460 (p : Nat → Bool) (h : Constraints p) : clause p c460 = true :=
  Snake9.LocalRup.prove_clause [c459, c187] c460 (by decide) p (sat_cons (step459 p h) (sat_cons (step187 p h) (sat_nil p)))
def c461 : List Lit := [(1243, true)]
theorem step461 (p : Nat → Bool) (h : Constraints p) : clause p c461 = true :=
  Snake9.LocalRup.prove_clause [c452, c304] c461 (by decide) p (sat_cons (step452 p h) (sat_cons (step304 p h) (sat_nil p)))
def c462 : List Lit := [(46, true), (1244, true)]
theorem step462 (p : Nat → Bool) (h : Constraints p) : clause p c462 = true :=
  Snake9.LocalRup.prove_clause [c452, c305] c462 (by decide) p (sat_cons (step452 p h) (sat_cons (step305 p h) (sat_nil p)))
def c463 : List Lit := [(1247, true)]
theorem step463 (p : Nat → Bool) (h : Constraints p) : clause p c463 = true :=
  Snake9.LocalRup.prove_clause [c461, c309] c463 (by decide) p (sat_cons (step461 p h) (sat_cons (step309 p h) (sat_nil p)))
def c464 : List Lit := [(1245, false), (1248, true)]
theorem step464 (p : Nat → Bool) (h : Constraints p) : clause p c464 = true :=
  Snake9.LocalRup.prove_clause [c461, c310] c464 (by decide) p (sat_cons (step461 p h) (sat_cons (step310 p h) (sat_nil p)))
def c465 : List Lit := [(1246, false), (1249, true)]
theorem step465 (p : Nat → Bool) (h : Constraints p) : clause p c465 = true :=
  Snake9.LocalRup.prove_clause [c461, c311] c465 (by decide) p (sat_cons (step461 p h) (sat_cons (step311 p h) (sat_nil p)))
def c466 : List Lit := [(1251, true)]
theorem step466 (p : Nat → Bool) (h : Constraints p) : clause p c466 = true :=
  Snake9.LocalRup.prove_clause [c463, c314] c466 (by decide) p (sat_cons (step463 p h) (sat_cons (step314 p h) (sat_nil p)))
def c467 : List Lit := [(1240, false), (1252, true)]
theorem step467 (p : Nat → Bool) (h : Constraints p) : clause p c467 = true :=
  Snake9.LocalRup.prove_clause [c463, c317] c467 (by decide) p (sat_cons (step463 p h) (sat_cons (step317 p h) (sat_nil p)))
def c468 : List Lit := [(1241, false), (1253, true)]
theorem step468 (p : Nat → Bool) (h : Constraints p) : clause p c468 = true :=
  Snake9.LocalRup.prove_clause [c463, c319] c468 (by decide) p (sat_cons (step463 p h) (sat_cons (step319 p h) (sat_nil p)))
def c469 : List Lit := [(1233, false), (1260, true)]
theorem step469 (p : Nat → Bool) (h : Constraints p) : clause p c469 = true :=
  Snake9.LocalRup.prove_clause [c466, c326] c469 (by decide) p (sat_cons (step466 p h) (sat_cons (step326 p h) (sat_nil p)))
def c470 : List Lit := [(1234, false), (1261, true)]
theorem step470 (p : Nat → Bool) (h : Constraints p) : clause p c470 = true :=
  Snake9.LocalRup.prove_clause [c466, c331] c470 (by decide) p (sat_cons (step466 p h) (sat_cons (step331 p h) (sat_nil p)))
def c471 : List Lit := [(1278, true)]
theorem step471 (p : Nat → Bool) (h : Constraints p) : clause p c471 = true :=
  Snake9.LocalRup.prove_clause [c453, c342] c471 (by decide) p (sat_cons (step453 p h) (sat_cons (step342 p h) (sat_nil p)))
def c472 : List Lit := [(56, true), (1279, true)]
theorem step472 (p : Nat → Bool) (h : Constraints p) : clause p c472 = true :=
  Snake9.LocalRup.prove_clause [c453, c343] c472 (by decide) p (sat_cons (step453 p h) (sat_cons (step343 p h) (sat_nil p)))
def c473 : List Lit := [(1280, true)]
theorem step473 (p : Nat → Bool) (h : Constraints p) : clause p c473 = true :=
  Snake9.LocalRup.prove_clause [c471, c344] c473 (by decide) p (sat_cons (step471 p h) (sat_cons (step344 p h) (sat_nil p)))
def c474 : List Lit := [(53, true), (1281, true)]
theorem step474 (p : Nat → Bool) (h : Constraints p) : clause p c474 = true :=
  Snake9.LocalRup.prove_clause [c471, c346] c474 (by decide) p (sat_cons (step471 p h) (sat_cons (step346 p h) (sat_nil p)))
def c475 : List Lit := [(1288, true)]
theorem step475 (p : Nat → Bool) (h : Constraints p) : clause p c475 = true :=
  Snake9.LocalRup.prove_clause [c473, c351] c475 (by decide) p (sat_cons (step473 p h) (sat_cons (step351 p h) (sat_nil p)))
def c476 : List Lit := [(1285, false), (1289, true)]
theorem step476 (p : Nat → Bool) (h : Constraints p) : clause p c476 = true :=
  Snake9.LocalRup.prove_clause [c473, c352] c476 (by decide) p (sat_cons (step473 p h) (sat_cons (step352 p h) (sat_nil p)))
def c477 : List Lit := [(1286, false), (1290, true)]
theorem step477 (p : Nat → Bool) (h : Constraints p) : clause p c477 = true :=
  Snake9.LocalRup.prove_clause [c473, c353] c477 (by decide) p (sat_cons (step473 p h) (sat_cons (step353 p h) (sat_nil p)))
def c478 : List Lit := [(1310, true)]
theorem step478 (p : Nat → Bool) (h : Constraints p) : clause p c478 = true :=
  Snake9.LocalRup.prove_clause [c475, c368] c478 (by decide) p (sat_cons (step475 p h) (sat_cons (step368 p h) (sat_nil p)))
def c479 : List Lit := [(1304, false), (1311, true)]
theorem step479 (p : Nat → Bool) (h : Constraints p) : clause p c479 = true :=
  Snake9.LocalRup.prove_clause [c475, c369] c479 (by decide) p (sat_cons (step475 p h) (sat_cons (step369 p h) (sat_nil p)))
def c480 : List Lit := [(1305, false), (1312, true)]
theorem step480 (p : Nat → Bool) (h : Constraints p) : clause p c480 = true :=
  Snake9.LocalRup.prove_clause [c475, c370] c480 (by decide) p (sat_cons (step475 p h) (sat_cons (step370 p h) (sat_nil p)))
def c481 : List Lit := [(1358, false), (1369, true)]
theorem step481 (p : Nat → Bool) (h : Constraints p) : clause p c481 = true :=
  Snake9.LocalRup.prove_clause [c478, c425] c481 (by decide) p (sat_cons (step478 p h) (sat_cons (step425 p h) (sat_nil p)))
def c482 : List Lit := [(1359, false), (1370, true)]
theorem step482 (p : Nat → Bool) (h : Constraints p) : clause p c482 = true :=
  Snake9.LocalRup.prove_clause [c478, c426] c482 (by decide) p (sat_cons (step478 p h) (sat_cons (step426 p h) (sat_nil p)))
def c483 : List Lit := [(1360, false), (1371, true)]
theorem step483 (p : Nat → Bool) (h : Constraints p) : clause p c483 = true :=
  Snake9.LocalRup.prove_clause [c478, c427] c483 (by decide) p (sat_cons (step478 p h) (sat_cons (step427 p h) (sat_nil p)))
def c484 : List Lit := [(1212, true)]
theorem step484 (p : Nat → Bool) (h : Constraints p) : clause p c484 = true :=
  Snake9.LocalRup.prove_clause [c143, c270, c272, c268, c262, c266, c267, c256, c265, c5, c255, c6] c484 (by decide) p (sat_cons (step143 p h) (sat_cons (step270 p h) (sat_cons (step272 p h) (sat_cons (step268 p h) (sat_cons (step262 p h) (sat_cons (step266 p h) (sat_cons (step267 p h) (sat_cons (step256 p h) (sat_cons (step265 p h) (sat_cons (step5 p h) (sat_cons (step255 p h) (sat_cons (step6 p h) (sat_nil p)))))))))))))
def c485 : List Lit := [(1311, true), (1233, true)]
theorem step485 (p : Nat → Bool) (h : Constraints p) : clause p c485 = true :=
  Snake9.LocalRup.prove_clause [c163, c158, c144, c289, c479, c371, c364, c476, c354, c362, c348, c474, c359, c360, c347, c93, c80, c94, c101, c285, c286, c292, c281, c282, c279, c33, c8] c485 (by decide) p (sat_cons (step163 p h) (sat_cons (step158 p h) (sat_cons (step144 p h) (sat_cons (step289 p h) (sat_cons (step479 p h) (sat_cons (step371 p h) (sat_cons (step364 p h) (sat_cons (step476 p h) (sat_cons (step354 p h) (sat_cons (step362 p h) (sat_cons (step348 p h) (sat_cons (step474 p h) (sat_cons (step359 p h) (sat_cons (step360 p h) (sat_cons (step347 p h) (sat_cons (step93 p h) (sat_cons (step80 p h) (sat_cons (step94 p h) (sat_cons (step101 p h) (sat_cons (step285 p h) (sat_cons (step286 p h) (sat_cons (step292 p h) (sat_cons (step281 p h) (sat_cons (step282 p h) (sat_cons (step279 p h) (sat_cons (step33 p h) (sat_cons (step8 p h) (sat_nil p))))))))))))))))))))))))))))
def c486 : List Lit := [(1229, false), (1260, true)]
theorem step486 (p : Nat → Bool) (h : Constraints p) : clause p c486 = true :=
  Snake9.LocalRup.prove_clause [c149, c469, c288, c292, c323, c277, c467, c274, c275, c300, c302, c297, c298, c52, c46, c14] c486 (by decide) p (sat_cons (step149 p h) (sat_cons (step469 p h) (sat_cons (step288 p h) (sat_cons (step292 p h) (sat_cons (step323 p h) (sat_cons (step277 p h) (sat_cons (step467 p h) (sat_cons (step274 p h) (sat_cons (step275 p h) (sat_cons (step300 p h) (sat_cons (step302 p h) (sat_cons (step297 p h) (sat_cons (step298 p h) (sat_cons (step52 p h) (sat_cons (step46 p h) (sat_cons (step14 p h) (sat_nil p)))))))))))))))))
def c487 : List Lit := [(28, false), (73, false), (1229, true)]
theorem step487 (p : Nat → Bool) (h : Constraints p) : clause p c487 = true :=
  Snake9.LocalRup.prove_clause [c144, c284, c282, c281, c285, c11, c28, c8] c487 (by decide) p (sat_cons (step144 p h) (sat_cons (step284 p h) (sat_cons (step282 p h) (sat_cons (step281 p h) (sat_cons (step285 p h) (sat_cons (step11 p h) (sat_cons (step28 p h) (sat_cons (step8 p h) (sat_nil p)))))))))
def c488 : List Lit := [(28, true), (1260, true)]
theorem step488 (p : Nat → Bool) (h : Constraints p) : clause p c488 = true :=
  Snake9.LocalRup.prove_clause [c145, c486, c285, c469, c295, c279, c280, c291, c274, c275, c323, c13, c467, c16, c300, c302, c47, c298] c488 (by decide) p (sat_cons (step145 p h) (sat_cons (step486 p h) (sat_cons (step285 p h) (sat_cons (step469 p h) (sat_cons (step295 p h) (sat_cons (step279 p h) (sat_cons (step280 p h) (sat_cons (step291 p h) (sat_cons (step274 p h) (sat_cons (step275 p h) (sat_cons (step323 p h) (sat_cons (step13 p h) (sat_cons (step467 p h) (sat_cons (step16 p h) (sat_cons (step300 p h) (sat_cons (step302 p h) (sat_cons (step47 p h) (sat_cons (step298 p h) (sat_nil p)))))))))))))))))))
def c489 : List Lit := [(1260, true)]
theorem step489 (p : Nat → Bool) (h : Constraints p) : clause p c489 = true :=
  Snake9.LocalRup.prove_clause [c144, c147, c322, c486, c284, c285, c281, c282, c488, c28, c8, c39, c10, c27, c306, c302, c464, c318] c489 (by decide) p (sat_cons (step144 p h) (sat_cons (step147 p h) (sat_cons (step322 p h) (sat_cons (step486 p h) (sat_cons (step284 p h) (sat_cons (step285 p h) (sat_cons (step281 p h) (sat_cons (step282 p h) (sat_cons (step488 p h) (sat_cons (step28 p h) (sat_cons (step8 p h) (sat_cons (step39 p h) (sat_cons (step10 p h) (sat_cons (step27 p h) (sat_cons (step306 p h) (sat_cons (step302 p h) (sat_cons (step464 p h) (sat_cons (step318 p h) (sat_nil p)))))))))))))))))))
def c490 : List Lit := [(1271, true)]
theorem step490 (p : Nat → Bool) (h : Constraints p) : clause p c490 = true :=
  Snake9.LocalRup.prove_clause [c489, c484, c335] c490 (by decide) p (sat_cons (step489 p h) (sat_cons (step484 p h) (sat_cons (step335 p h) (sat_nil p))))
def c491 : List Lit := [(1371, false)]
theorem step491 (p : Nat → Bool) (h : Constraints p) : clause p c491 = true :=
  Snake9.LocalRup.prove_clause [c490, c445, c440] c491 (by decide) p (sat_cons (step490 p h) (sat_cons (step445 p h) (sat_cons (step440 p h) (sat_nil p))))
def c492 : List Lit := [(1360, false)]
theorem step492 (p : Nat → Bool) (h : Constraints p) : clause p c492 = true :=
  Snake9.LocalRup.prove_clause [c491, c483] c492 (by decide) p (sat_cons (step491 p h) (sat_cons (step483 p h) (sat_nil p)))
def c493 : List Lit := [(1238, true), (1253, false), (30, true), (29, false), (40, false), (1304, false), (33, false)]
theorem step493 (p : Nat → Bool) (h : Constraints p) : clause p c493 = true :=
  Snake9.LocalRup.prove_clause [c149, c165, c484, c445, c297, c298, c56, c44, c45, c50, c55, c58, c18, c276, c349, c107, c278, c476, c379, c295, c372, c381, c328, c390, c337, c417, c442, c434] c493 (by decide) p (sat_cons (step149 p h) (sat_cons (step165 p h) (sat_cons (step484 p h) (sat_cons (step445 p h) (sat_cons (step297 p h) (sat_cons (step298 p h) (sat_cons (step56 p h) (sat_cons (step44 p h) (sat_cons (step45 p h) (sat_cons (step50 p h) (sat_cons (step55 p h) (sat_cons (step58 p h) (sat_cons (step18 p h) (sat_cons (step276 p h) (sat_cons (step349 p h) (sat_cons (step107 p h) (sat_cons (step278 p h) (sat_cons (step476 p h) (sat_cons (step379 p h) (sat_cons (step295 p h) (sat_cons (step372 p h) (sat_cons (step381 p h) (sat_cons (step328 p h) (sat_cons (step390 p h) (sat_cons (step337 p h) (sat_cons (step417 p h) (sat_cons (step442 p h) (sat_cons (step434 p h) (sat_nil p)))))))))))))))))))))))))))))
def c494 : List Lit := [(1233, false), (1241, false), (50, true), (1304, false)]
theorem step494 (p : Nat → Bool) (h : Constraints p) : clause p c494 = true :=
  Snake9.LocalRup.prove_clause [c484, c445, c152, c306, c464, c320, c479, c428, c444, c339, c330, c329, c321, c338, c465, c443, c308, c433, c429, c65, c372, c414, c476, c408, c349, c404, c69, c402] c494 (by decide) p (sat_cons (step484 p h) (sat_cons (step445 p h) (sat_cons (step152 p h) (sat_cons (step306 p h) (sat_cons (step464 p h) (sat_cons (step320 p h) (sat_cons (step479 p h) (sat_cons (step428 p h) (sat_cons (step444 p h) (sat_cons (step339 p h) (sat_cons (step330 p h) (sat_cons (step329 p h) (sat_cons (step321 p h) (sat_cons (step338 p h) (sat_cons (step465 p h) (sat_cons (step443 p h) (sat_cons (step308 p h) (sat_cons (step433 p h) (sat_cons (step429 p h) (sat_cons (step65 p h) (sat_cons (step372 p h) (sat_cons (step414 p h) (sat_cons (step476 p h) (sat_cons (step408 p h) (sat_cons (step349 p h) (sat_cons (step404 p h) (sat_cons (step69 p h) (sat_cons (step402 p h) (sat_nil p)))))))))))))))))))))))))))))
def c495 : List Lit := [(34, false), (32, false), (1369, true), (29, false), (1304, false), (33, false)]
theorem step495 (p : Nat → Bool) (h : Constraints p) : clause p c495 = true :=
  Snake9.LocalRup.prove_clause [c158, c22, c19, c379, c80, c381, c347, c390, c348, c417, c476, c434, c372] c495 (by decide) p (sat_cons (step158 p h) (sat_cons (step22 p h) (sat_cons (step19 p h) (sat_cons (step379 p h) (sat_cons (step80 p h) (sat_cons (step381 p h) (sat_cons (step347 p h) (sat_cons (step390 p h) (sat_cons (step348 p h) (sat_cons (step417 p h) (sat_cons (step476 p h) (sat_cons (step434 p h) (sat_cons (step372 p h) (sat_nil p))))))))))))))
def c496 : List Lit := [(32, false), (1369, true), (33, false), (29, false), (1304, false)]
theorem step496 (p : Nat → Bool) (h : Constraints p) : clause p c496 = true :=
  Snake9.LocalRup.prove_clause [c165, c158, c145, c495, c17, c18, c80, c107, c347, c379, c348, c381, c476, c390, c372, c417, c434] c496 (by decide) p (sat_cons (step165 p h) (sat_cons (step158 p h) (sat_cons (step145 p h) (sat_cons (step495 p h) (sat_cons (step17 p h) (sat_cons (step18 p h) (sat_cons (step80 p h) (sat_cons (step107 p h) (sat_cons (step347 p h) (sat_cons (step379 p h) (sat_cons (step348 p h) (sat_cons (step381 p h) (sat_cons (step476 p h) (sat_cons (step390 p h) (sat_cons (step372 p h) (sat_cons (step417 p h) (sat_cons (step434 p h) (sat_nil p))))))))))))))))))
def c497 : List Lit := [(28, false), (1304, false), (1232, false), (1229, true)]
theorem step497 (p : Nat → Bool) (h : Constraints p) : clause p c497 = true :=
  Snake9.LocalRup.prove_clause [c144, c147, c484, c445, c284, c282, c281, c285, c28, c37, c8, c9, c39, c10, c7, c27, c306, c302, c464, c318, c493, c303, c320, c325, c337, c442, c494, c295, c278, c276, c496] c497 (by decide) p (sat_cons (step144 p h) (sat_cons (step147 p h) (sat_cons (step484 p h) (sat_cons (step445 p h) (sat_cons (step284 p h) (sat_cons (step282 p h) (sat_cons (step281 p h) (sat_cons (step285 p h) (sat_cons (step28 p h) (sat_cons (step37 p h) (sat_cons (step8 p h) (sat_cons (step9 p h) (sat_cons (step39 p h) (sat_cons (step10 p h) (sat_cons (step7 p h) (sat_cons (step27 p h) (sat_cons (step306 p h) (sat_cons (step302 p h) (sat_cons (step464 p h) (sat_cons (step318 p h) (sat_cons (step493 p h) (sat_cons (step303 p h) (sat_cons (step320 p h) (sat_cons (step325 p h) (sat_cons (step337 p h) (sat_cons (step442 p h) (sat_cons (step494 p h) (sat_cons (step295 p h) (sat_cons (step278 p h) (sat_cons (step276 p h) (sat_cons (step496 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c498 : List Lit := [(41, true), (1356, false), (1281, false), (42, false), (39, false), (1233, false), (1304, false)]
theorem step498 (p : Nat → Bool) (h : Constraints p) : clause p c498 = true :=
  Snake9.LocalRup.prove_clause [c484, c445, c354, c372, c434, c442, c337, c328, c468, c301, c298, c299, c300, c54, c467, c349, c327, c355, c336, c375, c441, c437] c498 (by decide) p (sat_cons (step484 p h) (sat_cons (step445 p h) (sat_cons (step354 p h) (sat_cons (step372 p h) (sat_cons (step434 p h) (sat_cons (step442 p h) (sat_cons (step337 p h) (sat_cons (step328 p h) (sat_cons (step468 p h) (sat_cons (step301 p h) (sat_cons (step298 p h) (sat_cons (step299 p h) (sat_cons (step300 p h) (sat_cons (step54 p h) (sat_cons (step467 p h) (sat_cons (step349 p h) (sat_cons (step327 p h) (sat_cons (step355 p h) (sat_cons (step336 p h) (sat_cons (step375 p h) (sat_cons (step441 p h) (sat_cons (step437 p h) (sat_nil p)))))))))))))))))))))))
def c499 : List Lit := [(1356, false), (1281, false), (1304, false), (42, false), (39, false), (1233, false)]
theorem step499 (p : Nat → Bool) (h : Constraints p) : clause p c499 = true :=
  Snake9.LocalRup.prove_clause [c445, c484, c498, c52, c53, c297, c349, c300, c355, c467, c375, c327, c437, c336, c441] c499 (by decide) p (sat_cons (step445 p h) (sat_cons (step484 p h) (sat_cons (step498 p h) (sat_cons (step52 p h) (sat_cons (step53 p h) (sat_cons (step297 p h) (sat_cons (step349 p h) (sat_cons (step300 p h) (sat_cons (step355 p h) (sat_cons (step467 p h) (sat_cons (step375 p h) (sat_cons (step327 p h) (sat_cons (step437 p h) (sat_cons (step336 p h) (sat_cons (step441 p h) (sat_nil p))))))))))))))))
def c500 : List Lit := [(39, false), (1233, false), (1304, false), (1227, true)]
theorem step500 (p : Nat → Bool) (h : Constraints p) : clause p c500 = true :=
  Snake9.LocalRup.prove_clause [c146, c148, c282, c281, c27, c25, c42, c33, c34, c474, c378, c381, c390, c417, c499] c500 (by decide) p (sat_cons (step146 p h) (sat_cons (step148 p h) (sat_cons (step282 p h) (sat_cons (step281 p h) (sat_cons (step27 p h) (sat_cons (step25 p h) (sat_cons (step42 p h) (sat_cons (step33 p h) (sat_cons (step34 p h) (sat_cons (step474 p h) (sat_cons (step378 p h) (sat_cons (step381 p h) (sat_cons (step390 p h) (sat_cons (step417 p h) (sat_cons (step499 p h) (sat_nil p))))))))))))))))
def c501 : List Lit := [(88, false), (95, false), (94, false)]
theorem step501 (p : Nat → Bool) (h : Constraints p) : clause p c501 = true :=
  Snake9.LocalRup.prove_clause [c173, c134, c130] c501 (by decide) p (sat_cons (step173 p h) (sat_cons (step134 p h) (sat_cons (step130 p h) (sat_nil p))))
def c502 : List Lit := [(1349, true)]
theorem step502 (p : Nat → Bool) (h : Constraints p) : clause p c502 = true :=
  Snake9.LocalRup.prove_clause [c408, c409, c405, c397, c399, c400, c501] c502 (by decide) p (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step405 p h) (sat_cons (step397 p h) (sat_cons (step399 p h) (sat_cons (step400 p h) (sat_cons (step501 p h) (sat_nil p))))))))
def c503 : List Lit := [(1356, true)]
theorem step503 (p : Nat → Bool) (h : Constraints p) : clause p c503 = true :=
  Snake9.LocalRup.prove_clause [c502, c414] c503 (by decide) p (sat_cons (step502 p h) (sat_cons (step414 p h) (sat_nil p)))
def c504 : List Lit := [(97, true), (1351, true)]
theorem step504 (p : Nat → Bool) (h : Constraints p) : clause p c504 = true :=
  Snake9.LocalRup.prove_clause [c172, c173, c170, c129, c130, c401, c407, c411, c396, c397, c394, c122, c123, c449] c504 (by decide) p (sat_cons (step172 p h) (sat_cons (step173 p h) (sat_cons (step170 p h) (sat_cons (step129 p h) (sat_cons (step130 p h) (sat_cons (step401 p h) (sat_cons (step407 p h) (sat_cons (step411 p h) (sat_cons (step396 p h) (sat_cons (step397 p h) (sat_cons (step394 p h) (sat_cons (step122 p h) (sat_cons (step123 p h) (sat_cons (step449 p h) (sat_nil p)))))))))))))))
def c505 : List Lit := [(1338, true), (97, false)]
theorem step505 (p : Nat → Bool) (h : Constraints p) : clause p c505 = true :=
  Snake9.LocalRup.prove_clause [c171, c396, c397, c394, c126, c127, c121] c505 (by decide) p (sat_cons (step171 p h) (sat_cons (step396 p h) (sat_cons (step397 p h) (sat_cons (step394 p h) (sat_cons (step126 p h) (sat_cons (step127 p h) (sat_cons (step121 p h) (sat_nil p))))))))
def c506 : List Lit := [(347, true), (1331, true), (73, true), (33, false)]
theorem step506 (p : Nat → Bool) (h : Constraints p) : clause p c506 = true :=
  Snake9.LocalRup.prove_clause [c162, c160, c159, c161, c158, c163, c164, c392, c220, c222, c217, c218, c202, c215, c216, c208, c209, c200, c214, c211, c212, c207, c205, c206, c199, c213, c210, c451, c204, c198, c90, c84, c85, c81, c82, c83, c87, c86, c80, c102, c379, c97, c381, c384, c93, c391, c92, c387, c99, c100, c386, c448] c506 (by decide) p (sat_cons (step162 p h) (sat_cons (step160 p h) (sat_cons (step159 p h) (sat_cons (step161 p h) (sat_cons (step158 p h) (sat_cons (step163 p h) (sat_cons (step164 p h) (sat_cons (step392 p h) (sat_cons (step220 p h) (sat_cons (step222 p h) (sat_cons (step217 p h) (sat_cons (step218 p h) (sat_cons (step202 p h) (sat_cons (step215 p h) (sat_cons (step216 p h) (sat_cons (step208 p h) (sat_cons (step209 p h) (sat_cons (step200 p h) (sat_cons (step214 p h) (sat_cons (step211 p h) (sat_cons (step212 p h) (sat_cons (step207 p h) (sat_cons (step205 p h) (sat_cons (step206 p h) (sat_cons (step199 p h) (sat_cons (step213 p h) (sat_cons (step210 p h) (sat_cons (step451 p h) (sat_cons (step204 p h) (sat_cons (step198 p h) (sat_cons (step90 p h) (sat_cons (step84 p h) (sat_cons (step85 p h) (sat_cons (step81 p h) (sat_cons (step82 p h) (sat_cons (step83 p h) (sat_cons (step87 p h) (sat_cons (step86 p h) (sat_cons (step80 p h) (sat_cons (step102 p h) (sat_cons (step379 p h) (sat_cons (step97 p h) (sat_cons (step381 p h) (sat_cons (step384 p h) (sat_cons (step93 p h) (sat_cons (step391 p h) (sat_cons (step92 p h) (sat_cons (step387 p h) (sat_cons (step99 p h) (sat_cons (step100 p h) (sat_cons (step386 p h) (sat_cons (step448 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))
def c507 : List Lit := [(1233, false), (73, true), (1229, true)]
theorem step507 (p : Nat → Bool) (h : Constraints p) : clause p c507 = true :=
  Snake9.LocalRup.prove_clause [c484, c445, c502, c454, c167, c166, c359, c362, c364, c479, c284, c282, c281, c285, c500, c302, c467, c327, c336, c441, c431, c421, c506, c249, c247, c233, c228, c227, c225, c226, c113, c112, c388, c115, c391, c381, c378, c110, c34] c507 (by decide) p (sat_cons (step484 p h) (sat_cons (step445 p h) (sat_cons (step502 p h) (sat_cons (step454 p h) (sat_cons (step167 p h) (sat_cons (step166 p h) (sat_cons (step359 p h) (sat_cons (step362 p h) (sat_cons (step364 p h) (sat_cons (step479 p h) (sat_cons (step284 p h) (sat_cons (step282 p h) (sat_cons (step281 p h) (sat_cons (step285 p h) (sat_cons (step500 p h) (sat_cons (step302 p h) (sat_cons (step467 p h) (sat_cons (step327 p h) (sat_cons (step336 p h) (sat_cons (step441 p h) (sat_cons (step431 p h) (sat_cons (step421 p h) (sat_cons (step506 p h) (sat_cons (step249 p h) (sat_cons (step247 p h) (sat_cons (step233 p h) (sat_cons (step228 p h) (sat_cons (step227 p h) (sat_cons (step225 p h) (sat_cons (step226 p h) (sat_cons (step113 p h) (sat_cons (step112 p h) (sat_cons (step388 p h) (sat_cons (step115 p h) (sat_cons (step391 p h) (sat_cons (step381 p h) (sat_cons (step378 p h) (sat_cons (step110 p h) (sat_cons (step34 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c508 : List Lit := [(1314, false)]
theorem step508 (p : Nat → Bool) (h : Constraints p) : clause p c508 = true :=
  Snake9.LocalRup.prove_clause [c503, c491, c439] c508 (by decide) p (sat_cons (step503 p h) (sat_cons (step491 p h) (sat_cons (step439 p h) (sat_nil p))))
def c509 : List Lit := [(40, true), (1227, true)]
theorem step509 (p : Nat → Bool) (h : Constraints p) : clause p c509 = true :=
  Snake9.LocalRup.prove_clause [c147, c282, c281, c37, c38, c446] c509 (by decide) p (sat_cons (step147 p h) (sat_cons (step282 p h) (sat_cons (step281 p h) (sat_cons (step37 p h) (sat_cons (step38 p h) (sat_cons (step446 p h) (sat_nil p)))))))
def c510 : List Lit := [(73, true), (1232, false), (1229, true)]
theorem step510 (p : Nat → Bool) (h : Constraints p) : clause p c510 = true :=
  Snake9.LocalRup.prove_clause [c145, c254, c502, c491, c163, c284, c509, c285, c359, c362, c364, c497, c507, c295, c280, c274, c275, c13, c17, c21, c22, c43, c176, c177, c180, c186, c188, c190, c252, c248, c220, c506, c217, c421, c215, c436, c214, c480, c213, c365, c97, c363, c93, c361] c510 (by decide) p (sat_cons (step145 p h) (sat_cons (step254 p h) (sat_cons (step502 p h) (sat_cons (step491 p h) (sat_cons (step163 p h) (sat_cons (step284 p h) (sat_cons (step509 p h) (sat_cons (step285 p h) (sat_cons (step359 p h) (sat_cons (step362 p h) (sat_cons (step364 p h) (sat_cons (step497 p h) (sat_cons (step507 p h) (sat_cons (step295 p h) (sat_cons (step280 p h) (sat_cons (step274 p h) (sat_cons (step275 p h) (sat_cons (step13 p h) (sat_cons (step17 p h) (sat_cons (step21 p h) (sat_cons (step22 p h) (sat_cons (step43 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_cons (step180 p h) (sat_cons (step186 p h) (sat_cons (step188 p h) (sat_cons (step190 p h) (sat_cons (step252 p h) (sat_cons (step248 p h) (sat_cons (step220 p h) (sat_cons (step506 p h) (sat_cons (step217 p h) (sat_cons (step421 p h) (sat_cons (step215 p h) (sat_cons (step436 p h) (sat_cons (step214 p h) (sat_cons (step480 p h) (sat_cons (step213 p h) (sat_cons (step365 p h) (sat_cons (step97 p h) (sat_cons (step363 p h) (sat_cons (step93 p h) (sat_cons (step361 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c511 : List Lit := [(60, false), (73, false), (33, false)]
theorem step511 (p : Nat → Bool) (h : Constraints p) : clause p c511 = true :=
  Snake9.LocalRup.prove_clause [c158, c80, c101] c511 (by decide) p (sat_cons (step158 p h) (sat_cons (step80 p h) (sat_cons (step101 p h) (sat_nil p))))
def c512 : List Lit := [(78, true), (1331, true), (73, false), (1227, true)]
theorem step512 (p : Nat → Bool) (h : Constraints p) : clause p c512 = true :=
  Snake9.LocalRup.prove_clause [c166, c392, c382, c282, c281, c379, c380, c381, c34, c391, c110, c388, c114] c512 (by decide) p (sat_cons (step166 p h) (sat_cons (step392 p h) (sat_cons (step382 p h) (sat_cons (step282 p h) (sat_cons (step281 p h) (sat_cons (step379 p h) (sat_cons (step380 p h) (sat_cons (step381 p h) (sat_cons (step34 p h) (sat_cons (step391 p h) (sat_cons (step110 p h) (sat_cons (step388 p h) (sat_cons (step114 p h) (sat_nil p))))))))))))))
def c513 : List Lit := [(1304, false), (73, false), (1229, true)]
theorem step513 (p : Nat → Bool) (h : Constraints p) : clause p c513 = true :=
  Snake9.LocalRup.prove_clause [c491, c503, c502, c445, c484, c165, c285, c511, c347, c348, c476, c487, c284, c372, c436, c434, c421, c442, c337, c512, c103, c107, c22, c24, c274, c297, c280, c295, c500, c328, c303, c468] c513 (by decide) p (sat_cons (step491 p h) (sat_cons (step503 p h) (sat_cons (step502 p h) (sat_cons (step445 p h) (sat_cons (step484 p h) (sat_cons (step165 p h) (sat_cons (step285 p h) (sat_cons (step511 p h) (sat_cons (step347 p h) (sat_cons (step348 p h) (sat_cons (step476 p h) (sat_cons (step487 p h) (sat_cons (step284 p h) (sat_cons (step372 p h) (sat_cons (step436 p h) (sat_cons (step434 p h) (sat_cons (step421 p h) (sat_cons (step442 p h) (sat_cons (step337 p h) (sat_cons (step512 p h) (sat_cons (step103 p h) (sat_cons (step107 p h) (sat_cons (step22 p h) (sat_cons (step24 p h) (sat_cons (step274 p h) (sat_cons (step297 p h) (sat_cons (step280 p h) (sat_cons (step295 p h) (sat_cons (step500 p h) (sat_cons (step328 p h) (sat_cons (step303 p h) (sat_cons (step468 p h) (sat_nil p)))))))))))))))))))))))))))))))))
end B112E154
