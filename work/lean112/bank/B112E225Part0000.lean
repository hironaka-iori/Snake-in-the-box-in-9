import B112E225Inputs
namespace B112E225
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c517 : List Lit := [(55, true)]
theorem step517 (p : Nat → Bool) (h : Constraints p) : clause p c517 = true :=
  Snake9.LocalRup.prove_clause [c50, c49] c517 (by decide) p (sat_cons (step50 p h) (sat_cons (step49 p h) (sat_nil p)))
def c518 : List Lit := [(90, false)]
theorem step518 (p : Nat → Bool) (h : Constraints p) : clause p c518 = true :=
  Snake9.LocalRup.prove_clause [c163, c111] c518 (by decide) p (sat_cons (step163 p h) (sat_cons (step111 p h) (sat_nil p)))
def c519 : List Lit := [(104, false)]
theorem step519 (p : Nat → Bool) (h : Constraints p) : clause p c519 = true :=
  Snake9.LocalRup.prove_clause [c169, c151] c519 (by decide) p (sat_cons (step169 p h) (sat_cons (step151 p h) (sat_nil p)))
def c520 : List Lit := [(410, false)]
theorem step520 (p : Nat → Bool) (h : Constraints p) : clause p c520 = true :=
  Snake9.LocalRup.prove_clause [c323, c320] c520 (by decide) p (sat_cons (step323 p h) (sat_cons (step320 p h) (sat_nil p)))
def c521 : List Lit := [(308, false)]
theorem step521 (p : Nat → Bool) (h : Constraints p) : clause p c521 = true :=
  Snake9.LocalRup.prove_clause [c323, c322] c521 (by decide) p (sat_cons (step323 p h) (sat_cons (step322 p h) (sat_nil p)))
def c522 : List Lit := [(408, false)]
theorem step522 (p : Nat → Bool) (h : Constraints p) : clause p c522 = true :=
  Snake9.LocalRup.prove_clause [c520, c316] c522 (by decide) p (sat_cons (step520 p h) (sat_cons (step316 p h) (sat_nil p)))
def c523 : List Lit := [(358, false)]
theorem step523 (p : Nat → Bool) (h : Constraints p) : clause p c523 = true :=
  Snake9.LocalRup.prove_clause [c520, c319] c523 (by decide) p (sat_cons (step520 p h) (sat_cons (step319 p h) (sat_nil p)))
def c524 : List Lit := [(306, false)]
theorem step524 (p : Nat → Bool) (h : Constraints p) : clause p c524 = true :=
  Snake9.LocalRup.prove_clause [c521, c230] c524 (by decide) p (sat_cons (step521 p h) (sat_cons (step230 p h) (sat_nil p)))
def c525 : List Lit := [(256, false)]
theorem step525 (p : Nat → Bool) (h : Constraints p) : clause p c525 = true :=
  Snake9.LocalRup.prove_clause [c521, c233] c525 (by decide) p (sat_cons (step521 p h) (sat_cons (step233 p h) (sat_nil p)))
def c526 : List Lit := [(406, false)]
theorem step526 (p : Nat → Bool) (h : Constraints p) : clause p c526 = true :=
  Snake9.LocalRup.prove_clause [c522, c311] c526 (by decide) p (sat_cons (step522 p h) (sat_cons (step311 p h) (sat_nil p)))
def c527 : List Lit := [(382, false)]
theorem step527 (p : Nat → Bool) (h : Constraints p) : clause p c527 = true :=
  Snake9.LocalRup.prove_clause [c522, c314] c527 (by decide) p (sat_cons (step522 p h) (sat_cons (step314 p h) (sat_nil p)))
def c528 : List Lit := [(356, false)]
theorem step528 (p : Nat → Bool) (h : Constraints p) : clause p c528 = true :=
  Snake9.LocalRup.prove_clause [c523, c267] c528 (by decide) p (sat_cons (step523 p h) (sat_cons (step267 p h) (sat_nil p)))
def c529 : List Lit := [(332, false)]
theorem step529 (p : Nat → Bool) (h : Constraints p) : clause p c529 = true :=
  Snake9.LocalRup.prove_clause [c523, c269] c529 (by decide) p (sat_cons (step523 p h) (sat_cons (step269 p h) (sat_nil p)))
def c530 : List Lit := [(304, false)]
theorem step530 (p : Nat → Bool) (h : Constraints p) : clause p c530 = true :=
  Snake9.LocalRup.prove_clause [c524, c226] c530 (by decide) p (sat_cons (step524 p h) (sat_cons (step226 p h) (sat_nil p)))
def c531 : List Lit := [(280, false)]
theorem step531 (p : Nat → Bool) (h : Constraints p) : clause p c531 = true :=
  Snake9.LocalRup.prove_clause [c524, c228] c531 (by decide) p (sat_cons (step524 p h) (sat_cons (step228 p h) (sat_nil p)))
def c532 : List Lit := [(230, false)]
theorem step532 (p : Nat → Bool) (h : Constraints p) : clause p c532 = true :=
  Snake9.LocalRup.prove_clause [c525, c191] c532 (by decide) p (sat_cons (step525 p h) (sat_cons (step191 p h) (sat_nil p)))
def c533 : List Lit := [(404, false)]
theorem step533 (p : Nat → Bool) (h : Constraints p) : clause p c533 = true :=
  Snake9.LocalRup.prove_clause [c526, c307] c533 (by decide) p (sat_cons (step526 p h) (sat_cons (step307 p h) (sat_nil p)))
def c534 : List Lit := [(380, false)]
theorem step534 (p : Nat → Bool) (h : Constraints p) : clause p c534 = true :=
  Snake9.LocalRup.prove_clause [c527, c286] c534 (by decide) p (sat_cons (step527 p h) (sat_cons (step286 p h) (sat_nil p)))
def c535 : List Lit := [(354, false)]
theorem step535 (p : Nat → Bool) (h : Constraints p) : clause p c535 = true :=
  Snake9.LocalRup.prove_clause [c528, c264] c535 (by decide) p (sat_cons (step528 p h) (sat_cons (step264 p h) (sat_nil p)))
def c536 : List Lit := [(302, false)]
theorem step536 (p : Nat → Bool) (h : Constraints p) : clause p c536 = true :=
  Snake9.LocalRup.prove_clause [c530, c223] c536 (by decide) p (sat_cons (step530 p h) (sat_cons (step223 p h) (sat_nil p)))
def c537 : List Lit := [(278, false)]
theorem step537 (p : Nat → Bool) (h : Constraints p) : clause p c537 = true :=
  Snake9.LocalRup.prove_clause [c531, c205] c537 (by decide) p (sat_cons (step531 p h) (sat_cons (step205 p h) (sat_nil p)))
def c538 : List Lit := [(396, false)]
theorem step538 (p : Nat → Bool) (h : Constraints p) : clause p c538 = true :=
  Snake9.LocalRup.prove_clause [c533, c305] c538 (by decide) p (sat_cons (step533 p h) (sat_cons (step305 p h) (sat_nil p)))
def c539 : List Lit := [(372, false)]
theorem step539 (p : Nat → Bool) (h : Constraints p) : clause p c539 = true :=
  Snake9.LocalRup.prove_clause [c534, c284] c539 (by decide) p (sat_cons (step534 p h) (sat_cons (step284 p h) (sat_nil p)))
def c540 : List Lit := [(346, false)]
theorem step540 (p : Nat → Bool) (h : Constraints p) : clause p c540 = true :=
  Snake9.LocalRup.prove_clause [c535, c262] c540 (by decide) p (sat_cons (step535 p h) (sat_cons (step262 p h) (sat_nil p)))
def c541 : List Lit := [(294, false)]
theorem step541 (p : Nat → Bool) (h : Constraints p) : clause p c541 = true :=
  Snake9.LocalRup.prove_clause [c536, c221] c541 (by decide) p (sat_cons (step536 p h) (sat_cons (step221 p h) (sat_nil p)))
def c542 : List Lit := [(270, false)]
theorem step542 (p : Nat → Bool) (h : Constraints p) : clause p c542 = true :=
  Snake9.LocalRup.prove_clause [c537, c203] c542 (by decide) p (sat_cons (step537 p h) (sat_cons (step203 p h) (sat_nil p)))
def c543 : List Lit := [(344, false)]
theorem step543 (p : Nat → Bool) (h : Constraints p) : clause p c543 = true :=
  Snake9.LocalRup.prove_clause [c540, c257] c543 (by decide) p (sat_cons (step540 p h) (sat_cons (step257 p h) (sat_nil p)))
def c544 : List Lit := [(268, false)]
theorem step544 (p : Nat → Bool) (h : Constraints p) : clause p c544 = true :=
  Snake9.LocalRup.prove_clause [c542, c199] c544 (by decide) p (sat_cons (step542 p h) (sat_cons (step199 p h) (sat_nil p)))
def c545 : List Lit := [(1267, true)]
theorem step545 (p : Nat → Bool) (h : Constraints p) : clause p c545 = true :=
  Snake9.LocalRup.prove_clause [c341, c342, c340, c336, c337, c334, c335, c10, c8, c9] c545 (by decide) p (sat_cons (step341 p h) (sat_cons (step342 p h) (sat_cons (step340 p h) (sat_cons (step336 p h) (sat_cons (step337 p h) (sat_cons (step334 p h) (sat_cons (step335 p h) (sat_cons (step10 p h) (sat_cons (step8 p h) (sat_cons (step9 p h) (sat_nil p)))))))))))
def c546 : List Lit := [(1273, true)]
theorem step546 (p : Nat → Bool) (h : Constraints p) : clause p c546 = true :=
  Snake9.LocalRup.prove_clause [c545, c344] c546 (by decide) p (sat_cons (step545 p h) (sat_cons (step344 p h) (sat_nil p)))
def c547 : List Lit := [(1391, true)]
theorem step547 (p : Nat → Bool) (h : Constraints p) : clause p c547 = true :=
  Snake9.LocalRup.prove_clause [c442, c445, c437, c429, c431, c434, c435, c426, c427, c86, c109, c105] c547 (by decide) p (sat_cons (step442 p h) (sat_cons (step445 p h) (sat_cons (step437 p h) (sat_cons (step429 p h) (sat_cons (step431 p h) (sat_cons (step434 p h) (sat_cons (step435 p h) (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_cons (step86 p h) (sat_cons (step109 p h) (sat_cons (step105 p h) (sat_nil p)))))))))))))
def c548 : List Lit := [(1383, true), (1386, true)]
theorem step548 (p : Nat → Bool) (h : Constraints p) : clause p c548 = true :=
  Snake9.LocalRup.prove_clause [c435, c434, c429, c431, c426, c427, c86, c109, c105] c548 (by decide) p (sat_cons (step435 p h) (sat_cons (step434 p h) (sat_cons (step429 p h) (sat_cons (step431 p h) (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_cons (step86 p h) (sat_cons (step109 p h) (sat_cons (step105 p h) (sat_nil p))))))))))
def c549 : List Lit := [(1381, true), (1386, true), (73, false)]
theorem step549 (p : Nat → Bool) (h : Constraints p) : clause p c549 = true :=
  Snake9.LocalRup.prove_clause [c435, c434, c426, c427, c109, c85, c105] c549 (by decide) p (sat_cons (step435 p h) (sat_cons (step434 p h) (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_cons (step109 p h) (sat_cons (step85 p h) (sat_cons (step105 p h) (sat_nil p))))))))
def c550 : List Lit := [(1386, true), (1384, true), (1362, true)]
theorem step550 (p : Nat → Bool) (h : Constraints p) : clause p c550 = true :=
  Snake9.LocalRup.prove_clause [c411, c408, c409, c413, c69, c434, c549, c432, c62, c84, c63] c550 (by decide) p (sat_cons (step411 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step413 p h) (sat_cons (step69 p h) (sat_cons (step434 p h) (sat_cons (step549 p h) (sat_cons (step432 p h) (sat_cons (step62 p h) (sat_cons (step84 p h) (sat_cons (step63 p h) (sat_nil p))))))))))))
def c551 : List Lit := [(1383, true), (1362, true)]
theorem step551 (p : Nat → Bool) (h : Constraints p) : clause p c551 = true :=
  Snake9.LocalRup.prove_clause [c411, c408, c409, c413, c69, c429, c431, c427, c62, c83, c63] c551 (by decide) p (sat_cons (step411 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step413 p h) (sat_cons (step69 p h) (sat_cons (step429 p h) (sat_cons (step431 p h) (sat_cons (step427 p h) (sat_cons (step62 p h) (sat_cons (step83 p h) (sat_cons (step63 p h) (sat_nil p))))))))))))
def c552 : List Lit := [(1399, true), (195, true), (83, false)]
theorem step552 (p : Nat → Bool) (h : Constraints p) : clause p c552 = true :=
  Snake9.LocalRup.prove_clause [c518, c454, c456, c451, c115, c131] c552 (by decide) p (sat_cons (step518 p h) (sat_cons (step454 p h) (sat_cons (step456 p h) (sat_cons (step451 p h) (sat_cons (step115 p h) (sat_cons (step131 p h) (sat_nil p)))))))
def c553 : List Lit := [(85, false), (189, true), (82, true), (83, false), (76, false)]
theorem step553 (p : Nat → Bool) (h : Constraints p) : clause p c553 = true :=
  Snake9.LocalRup.prove_clause [c101, c100] c553 (by decide) p (sat_cons (step101 p h) (sat_cons (step100 p h) (sat_nil p)))
def c554 : List Lit := [(1308, true), (52, false)]
theorem step554 (p : Nat → Bool) (h : Constraints p) : clause p c554 = true :=
  Snake9.LocalRup.prove_clause [c372, c373, c370, c371, c368, c43, c38, c41] c554 (by decide) p (sat_cons (step372 p h) (sat_cons (step373 p h) (sat_cons (step370 p h) (sat_cons (step371 p h) (sat_cons (step368 p h) (sat_cons (step43 p h) (sat_cons (step38 p h) (sat_cons (step41 p h) (sat_nil p)))))))))
def c555 : List Lit := [(1312, false), (1331, true)]
theorem step555 (p : Nat → Bool) (h : Constraints p) : clause p c555 = true :=
  Snake9.LocalRup.prove_clause [c546, c545, c387, c380, c381, c390, c357, c359, c346, c354, c355, c349, c333, c352, c353, c24, c347, c326, c350, c18, c325, c22, c14] c555 (by decide) p (sat_cons (step546 p h) (sat_cons (step545 p h) (sat_cons (step387 p h) (sat_cons (step380 p h) (sat_cons (step381 p h) (sat_cons (step390 p h) (sat_cons (step357 p h) (sat_cons (step359 p h) (sat_cons (step346 p h) (sat_cons (step354 p h) (sat_cons (step355 p h) (sat_cons (step349 p h) (sat_cons (step333 p h) (sat_cons (step352 p h) (sat_cons (step353 p h) (sat_cons (step24 p h) (sat_cons (step347 p h) (sat_cons (step326 p h) (sat_cons (step350 p h) (sat_cons (step18 p h) (sat_cons (step325 p h) (sat_cons (step22 p h) (sat_cons (step14 p h) (sat_nil p))))))))))))))))))))))))
def c556 : List Lit := [(1312, true)]
theorem step556 (p : Nat → Bool) (h : Constraints p) : clause p c556 = true :=
  Snake9.LocalRup.prove_clause [c155, c541, c375, c376, c372, c373, c554, c364, c366, c370, c371, c368, c369, c45, c362, c38, c30, c36, c40, c216, c213] c556 (by decide) p (sat_cons (step155 p h) (sat_cons (step541 p h) (sat_cons (step375 p h) (sat_cons (step376 p h) (sat_cons (step372 p h) (sat_cons (step373 p h) (sat_cons (step554 p h) (sat_cons (step364 p h) (sat_cons (step366 p h) (sat_cons (step370 p h) (sat_cons (step371 p h) (sat_cons (step368 p h) (sat_cons (step369 p h) (sat_cons (step45 p h) (sat_cons (step362 p h) (sat_cons (step38 p h) (sat_cons (step30 p h) (sat_cons (step36 p h) (sat_cons (step40 p h) (sat_cons (step216 p h) (sat_cons (step213 p h) (sat_nil p))))))))))))))))))))))
def c557 : List Lit := [(1331, true)]
theorem step557 (p : Nat → Bool) (h : Constraints p) : clause p c557 = true :=
  Snake9.LocalRup.prove_clause [c556, c555] c557 (by decide) p (sat_cons (step556 p h) (sat_cons (step555 p h) (sat_nil p)))
def c558 : List Lit := [(1433, false)]
theorem step558 (p : Nat → Bool) (h : Constraints p) : clause p c558 = true :=
  Snake9.LocalRup.prove_clause [c557, c513, c508] c558 (by decide) p (sat_cons (step557 p h) (sat_cons (step513 p h) (sat_cons (step508 p h) (sat_nil p))))
def c559 : List Lit := [(1423, false)]
theorem step559 (p : Nat → Bool) (h : Constraints p) : clause p c559 = true :=
  Snake9.LocalRup.prove_clause [c558, c495] c559 (by decide) p (sat_cons (step558 p h) (sat_cons (step495 p h) (sat_nil p)))
def c560 : List Lit := [(47, false), (50, false), (49, false)]
theorem step560 (p : Nat → Bool) (h : Constraints p) : clause p c560 = true :=
  Snake9.LocalRup.prove_clause [c536, c38, c42, c40, c217, c213, c218, c214, c220] c560 (by decide) p (sat_cons (step536 p h) (sat_cons (step38 p h) (sat_cons (step42 p h) (sat_cons (step40 p h) (sat_cons (step217 p h) (sat_cons (step213 p h) (sat_cons (step218 p h) (sat_cons (step214 p h) (sat_cons (step220 p h) (sat_nil p))))))))))
def c561 : List Lit := [(1308, true)]
theorem step561 (p : Nat → Bool) (h : Constraints p) : clause p c561 = true :=
  Snake9.LocalRup.prove_clause [c372, c373, c370, c371, c368, c560] c561 (by decide) p (sat_cons (step372 p h) (sat_cons (step373 p h) (sat_cons (step370 p h) (sat_cons (step371 p h) (sat_cons (step368 p h) (sat_cons (step560 p h) (sat_nil p)))))))
def c562 : List Lit := [(1290, true), (140, true)]
theorem step562 (p : Nat → Bool) (h : Constraints p) : clause p c562 = true :=
  Snake9.LocalRup.prove_clause [c354, c355, c352, c353, c24, c26] c562 (by decide) p (sat_cons (step354 p h) (sat_cons (step355 p h) (sat_cons (step352 p h) (sat_cons (step353 p h) (sat_cons (step24 p h) (sat_cons (step26 p h) (sat_nil p)))))))
def c563 : List Lit := [(1274, true), (229, true)]
theorem step563 (p : Nat → Bool) (h : Constraints p) : clause p c563 = true :=
  Snake9.LocalRup.prove_clause [c545, c180, c172, c171, c170, c179, c177, c176, c175, c345, c346, c332, c333, c330, c331, c326, c327, c329, c325, c1, c6, c2, c5, c338, c334, c339, c336, c343] c563 (by decide) p (sat_cons (step545 p h) (sat_cons (step180 p h) (sat_cons (step172 p h) (sat_cons (step171 p h) (sat_cons (step170 p h) (sat_cons (step179 p h) (sat_cons (step177 p h) (sat_cons (step176 p h) (sat_cons (step175 p h) (sat_cons (step345 p h) (sat_cons (step346 p h) (sat_cons (step332 p h) (sat_cons (step333 p h) (sat_cons (step330 p h) (sat_cons (step331 p h) (sat_cons (step326 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step325 p h) (sat_cons (step1 p h) (sat_cons (step6 p h) (sat_cons (step2 p h) (sat_cons (step5 p h) (sat_cons (step338 p h) (sat_cons (step334 p h) (sat_cons (step339 p h) (sat_cons (step336 p h) (sat_cons (step343 p h) (sat_nil p)))))))))))))))))))))))))))))
def c564 : List Lit := [(98, true), (1407, true), (203, true), (205, true), (42, false)]
theorem step564 (p : Nat → Bool) (h : Constraints p) : clause p c564 = true :=
  Snake9.LocalRup.prove_clause [c469, c460, c461, c468, c139, c462, c463, c148, c143] c564 (by decide) p (sat_cons (step469 p h) (sat_cons (step460 p h) (sat_cons (step461 p h) (sat_cons (step468 p h) (sat_cons (step139 p h) (sat_cons (step462 p h) (sat_cons (step463 p h) (sat_cons (step148 p h) (sat_cons (step143 p h) (sat_nil p))))))))))
def c565 : List Lit := [(73, false), (74, false), (77, false), (81, false), (177, true)]
theorem step565 (p : Nat → Bool) (h : Constraints p) : clause p c565 = true :=
  Snake9.LocalRup.prove_clause [c70, c83, c64] c565 (by decide) p (sat_cons (step70 p h) (sat_cons (step83 p h) (sat_cons (step64 p h) (sat_nil p))))
def c566 : List Lit := [(103, true), (1405, true), (205, true)]
theorem step566 (p : Nat → Bool) (h : Constraints p) : clause p c566 = true :=
  Snake9.LocalRup.prove_clause [c168, c140, c464, c143] c566 (by decide) p (sat_cons (step168 p h) (sat_cons (step140 p h) (sat_cons (step464 p h) (sat_cons (step143 p h) (sat_nil p)))))
def c567 : List Lit := [(1411, false), (1430, true)]
theorem step567 (p : Nat → Bool) (h : Constraints p) : clause p c567 = true :=
  Snake9.LocalRup.prove_clause [c547, c492, c481, c485, c497, c448, c418, c415, c551, c550, c446, c437] c567 (by decide) p (sat_cons (step547 p h) (sat_cons (step492 p h) (sat_cons (step481 p h) (sat_cons (step485 p h) (sat_cons (step497 p h) (sat_cons (step448 p h) (sat_cons (step418 p h) (sat_cons (step415 p h) (sat_cons (step551 p h) (sat_cons (step550 p h) (sat_cons (step446 p h) (sat_cons (step437 p h) (sat_nil p)))))))))))))
def c568 : List Lit := [(1406, true), (103, false), (203, true), (205, true), (42, false)]
theorem step568 (p : Nat → Bool) (h : Constraints p) : clause p c568 = true :=
  Snake9.LocalRup.prove_clause [c465, c467, c463, c459, c143, c139, c148] c568 (by decide) p (sat_cons (step465 p h) (sat_cons (step467 p h) (sat_cons (step463 p h) (sat_cons (step459 p h) (sat_cons (step143 p h) (sat_cons (step139 p h) (sat_cons (step148 p h) (sat_nil p))))))))
def c569 : List Lit := [(59, true), (1350, true), (61, false), (168, true)]
theorem step569 (p : Nat → Bool) (h : Constraints p) : clause p c569 = true :=
  Snake9.LocalRup.prove_clause [c157, c402, c54, c399, c400, c404, c398, c396, c55, c395, c53] c569 (by decide) p (sat_cons (step157 p h) (sat_cons (step402 p h) (sat_cons (step54 p h) (sat_cons (step399 p h) (sat_cons (step400 p h) (sat_cons (step404 p h) (sat_cons (step398 p h) (sat_cons (step396 p h) (sat_cons (step55 p h) (sat_cons (step395 p h) (sat_cons (step53 p h) (sat_nil p))))))))))))
def c570 : List Lit := [(96, false), (98, false), (99, false)]
theorem step570 (p : Nat → Bool) (h : Constraints p) : clause p c570 = true :=
  Snake9.LocalRup.prove_clause [c538, c125, c138, c135, c294, c297] c570 (by decide) p (sat_cons (step538 p h) (sat_cons (step125 p h) (sat_cons (step138 p h) (sat_cons (step135 p h) (sat_cons (step294 p h) (sat_cons (step297 p h) (sat_nil p)))))))
def c571 : List Lit := [(1392, true), (1362, true)]
theorem step571 (p : Nat → Bool) (h : Constraints p) : clause p c571 = true :=
  Snake9.LocalRup.prove_clause [c551, c448, c446, c550, c437] c571 (by decide) p (sat_cons (step551 p h) (sat_cons (step448 p h) (sat_cons (step446 p h) (sat_cons (step550 p h) (sat_cons (step437 p h) (sat_nil p))))))
def c572 : List Lit := [(192, true), (1382, true), (1386, true), (73, false)]
theorem step572 (p : Nat → Bool) (h : Constraints p) : clause p c572 = true :=
  Snake9.LocalRup.prove_clause [c435, c434, c108, c107, c85, c109, c428] c572 (by decide) p (sat_cons (step435 p h) (sat_cons (step434 p h) (sat_cons (step108 p h) (sat_cons (step107 p h) (sat_cons (step85 p h) (sat_cons (step109 p h) (sat_cons (step428 p h) (sat_nil p))))))))
def c573 : List Lit := [(1382, true), (1388, true), (1362, true)]
theorem step573 (p : Nat → Bool) (h : Constraints p) : clause p c573 = true :=
  Snake9.LocalRup.prove_clause [c534, c520, c437, c435, c434, c439, c411, c408, c409, c413, c69, c572, c277, c280, c281, c283, c285, c274, c312, c273, c318, c266, c263, c261, c256, c254, c64, c85, c106, c428, c102, c90] c573 (by decide) p (sat_cons (step534 p h) (sat_cons (step520 p h) (sat_cons (step437 p h) (sat_cons (step435 p h) (sat_cons (step434 p h) (sat_cons (step439 p h) (sat_cons (step411 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step413 p h) (sat_cons (step69 p h) (sat_cons (step572 p h) (sat_cons (step277 p h) (sat_cons (step280 p h) (sat_cons (step281 p h) (sat_cons (step283 p h) (sat_cons (step285 p h) (sat_cons (step274 p h) (sat_cons (step312 p h) (sat_cons (step273 p h) (sat_cons (step318 p h) (sat_cons (step266 p h) (sat_cons (step263 p h) (sat_cons (step261 p h) (sat_cons (step256 p h) (sat_cons (step254 p h) (sat_cons (step64 p h) (sat_cons (step85 p h) (sat_cons (step106 p h) (sat_cons (step428 p h) (sat_cons (step102 p h) (sat_cons (step90 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c574 : List Lit := [(1388, true), (1362, true), (1385, true)]
theorem step574 (p : Nat → Bool) (h : Constraints p) : clause p c574 = true :=
  Snake9.LocalRup.prove_clause [c411, c408, c409, c413, c69, c437, c434, c573, c433, c62, c84, c63] c574 (by decide) p (sat_cons (step411 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step413 p h) (sat_cons (step69 p h) (sat_cons (step437 p h) (sat_cons (step434 p h) (sat_cons (step573 p h) (sat_cons (step433 p h) (sat_cons (step62 p h) (sat_cons (step84 p h) (sat_cons (step63 p h) (sat_nil p)))))))))))))
def c575 : List Lit := [(77, false), (85, false), (1382, true), (1387, true), (74, false), (76, false), (73, false)]
theorem step575 (p : Nat → Bool) (h : Constraints p) : clause p c575 = true :=
  Snake9.LocalRup.prove_clause [c543, c539, c69, c62, c65, c63, c255, c83, c84, c68, c428, c436, c80, c90, c553, c104, c276, c273] c575 (by decide) p (sat_cons (step543 p h) (sat_cons (step539 p h) (sat_cons (step69 p h) (sat_cons (step62 p h) (sat_cons (step65 p h) (sat_cons (step63 p h) (sat_cons (step255 p h) (sat_cons (step83 p h) (sat_cons (step84 p h) (sat_cons (step68 p h) (sat_cons (step428 p h) (sat_cons (step436 p h) (sat_cons (step80 p h) (sat_cons (step90 p h) (sat_cons (step553 p h) (sat_cons (step104 p h) (sat_cons (step276 p h) (sat_cons (step273 p h) (sat_nil p)))))))))))))))))))
def c576 : List Lit := [(82, true), (81, false), (83, false), (85, false), (1333, true), (74, false), (76, false), (73, false)]
theorem step576 (p : Nat → Bool) (h : Constraints p) : clause p c576 = true :=
  Snake9.LocalRup.prove_clause [c527, c520, c323, c556, c101, c69, c553, c98, c275, c96, c282, c355, c285, c288, c312, c272, c315, c318, c271, c321, c266, c270, c229, c231, c263, c227, c189, c260, c261, c204, c563, c259, c256, c202, c392, c258, c254, c201, c384, c78, c65, c200, c358, c360, c66, c356, c349, c89, c352, c348, c17, c25] c576 (by decide) p (sat_cons (step527 p h) (sat_cons (step520 p h) (sat_cons (step323 p h) (sat_cons (step556 p h) (sat_cons (step101 p h) (sat_cons (step69 p h) (sat_cons (step553 p h) (sat_cons (step98 p h) (sat_cons (step275 p h) (sat_cons (step96 p h) (sat_cons (step282 p h) (sat_cons (step355 p h) (sat_cons (step285 p h) (sat_cons (step288 p h) (sat_cons (step312 p h) (sat_cons (step272 p h) (sat_cons (step315 p h) (sat_cons (step318 p h) (sat_cons (step271 p h) (sat_cons (step321 p h) (sat_cons (step266 p h) (sat_cons (step270 p h) (sat_cons (step229 p h) (sat_cons (step231 p h) (sat_cons (step263 p h) (sat_cons (step227 p h) (sat_cons (step189 p h) (sat_cons (step260 p h) (sat_cons (step261 p h) (sat_cons (step204 p h) (sat_cons (step563 p h) (sat_cons (step259 p h) (sat_cons (step256 p h) (sat_cons (step202 p h) (sat_cons (step392 p h) (sat_cons (step258 p h) (sat_cons (step254 p h) (sat_cons (step201 p h) (sat_cons (step384 p h) (sat_cons (step78 p h) (sat_cons (step65 p h) (sat_cons (step200 p h) (sat_cons (step358 p h) (sat_cons (step360 p h) (sat_cons (step66 p h) (sat_cons (step356 p h) (sat_cons (step349 p h) (sat_cons (step89 p h) (sat_cons (step352 p h) (sat_cons (step348 p h) (sat_cons (step17 p h) (sat_cons (step25 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))
def c577 : List Lit := [(1362, true), (1393, true), (1412, false)]
theorem step577 (p : Nat → Bool) (h : Constraints p) : clause p c577 = true :=
  Snake9.LocalRup.prove_clause [c513, c520, c450, c411, c413, c551, c408, c409, c69, c447, c438, c571, c486, c493, c510, c574, c449, c430, c550, c440, c575, c432, c426, c427, c576, c90, c436, c85, c64, c108, c254, c277, c256, c280, c261, c281, c263, c285, c266, c312, c318] c577 (by decide) p (sat_cons (step513 p h) (sat_cons (step520 p h) (sat_cons (step450 p h) (sat_cons (step411 p h) (sat_cons (step413 p h) (sat_cons (step551 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step69 p h) (sat_cons (step447 p h) (sat_cons (step438 p h) (sat_cons (step571 p h) (sat_cons (step486 p h) (sat_cons (step493 p h) (sat_cons (step510 p h) (sat_cons (step574 p h) (sat_cons (step449 p h) (sat_cons (step430 p h) (sat_cons (step550 p h) (sat_cons (step440 p h) (sat_cons (step575 p h) (sat_cons (step432 p h) (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_cons (step576 p h) (sat_cons (step90 p h) (sat_cons (step436 p h) (sat_cons (step85 p h) (sat_cons (step64 p h) (sat_cons (step108 p h) (sat_cons (step254 p h) (sat_cons (step277 p h) (sat_cons (step256 p h) (sat_cons (step280 p h) (sat_cons (step261 p h) (sat_cons (step281 p h) (sat_cons (step263 p h) (sat_cons (step285 p h) (sat_cons (step266 p h) (sat_cons (step312 p h) (sat_cons (step318 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c578 : List Lit := [(75, true), (79, true), (83, false), (77, false), (85, false), (73, false), (1387, true), (1361, true)]
theorem step578 (p : Nat → Bool) (h : Constraints p) : clause p c578 = true :=
  Snake9.LocalRup.prove_clause [c520, c63, c64, c62, c254, c410, c256, c261, c263, c266, c318, c312, c285, c281, c282, c280, c275, c277, c553, c108, c90, c436] c578 (by decide) p (sat_cons (step520 p h) (sat_cons (step63 p h) (sat_cons (step64 p h) (sat_cons (step62 p h) (sat_cons (step254 p h) (sat_cons (step410 p h) (sat_cons (step256 p h) (sat_cons (step261 p h) (sat_cons (step263 p h) (sat_cons (step266 p h) (sat_cons (step318 p h) (sat_cons (step312 p h) (sat_cons (step285 p h) (sat_cons (step281 p h) (sat_cons (step282 p h) (sat_cons (step280 p h) (sat_cons (step275 p h) (sat_cons (step277 p h) (sat_cons (step553 p h) (sat_cons (step108 p h) (sat_cons (step90 p h) (sat_cons (step436 p h) (sat_nil p)))))))))))))))))))))))
def c579 : List Lit := [(1386, false), (73, false), (1392, true), (1361, true)]
theorem step579 (p : Nat → Bool) (h : Constraints p) : clause p c579 = true :=
  Snake9.LocalRup.prove_clause [c443, c438, c437, c440, c446, c429, c431, c426, c427, c83, c578, c70, c71, c410] c579 (by decide) p (sat_cons (step443 p h) (sat_cons (step438 p h) (sat_cons (step437 p h) (sat_cons (step440 p h) (sat_cons (step446 p h) (sat_cons (step429 p h) (sat_cons (step431 p h) (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_cons (step83 p h) (sat_cons (step578 p h) (sat_cons (step70 p h) (sat_cons (step71 p h) (sat_cons (step410 p h) (sat_nil p)))))))))))))))
def c580 : List Lit := [(73, false), (1392, true), (1361, true)]
theorem step580 (p : Nat → Bool) (h : Constraints p) : clause p c580 = true :=
  Snake9.LocalRup.prove_clause [c520, c448, c430, c579, c434, c435, c549, c572, c432, c277, c84, c280, c105, c281, c109, c285, c428, c312, c318, c266, c263, c261, c256, c254, c64, c565, c71, c410] c580 (by decide) p (sat_cons (step520 p h) (sat_cons (step448 p h) (sat_cons (step430 p h) (sat_cons (step579 p h) (sat_cons (step434 p h) (sat_cons (step435 p h) (sat_cons (step549 p h) (sat_cons (step572 p h) (sat_cons (step432 p h) (sat_cons (step277 p h) (sat_cons (step84 p h) (sat_cons (step280 p h) (sat_cons (step105 p h) (sat_cons (step281 p h) (sat_cons (step109 p h) (sat_cons (step285 p h) (sat_cons (step428 p h) (sat_cons (step312 p h) (sat_cons (step318 p h) (sat_cons (step266 p h) (sat_cons (step263 p h) (sat_cons (step261 p h) (sat_cons (step256 p h) (sat_cons (step254 p h) (sat_cons (step64 p h) (sat_cons (step565 p h) (sat_cons (step71 p h) (sat_cons (step410 p h) (sat_nil p)))))))))))))))))))))))))))))
end B112E225
