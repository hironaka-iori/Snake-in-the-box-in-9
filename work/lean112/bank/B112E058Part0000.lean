import B112E058Inputs
namespace B112E058
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c683 : List Lit := [(1464, true)]
theorem step683 (p : Nat → Bool) (h : Constraints p) : clause p c683 = true :=
  Snake9.LocalRup.prove_clause [c270, c406, c408, c403, c400, c401, c64, c66] c683 (by decide) p (sat_cons (step270 p h) (sat_cons (step406 p h) (sat_cons (step408 p h) (sat_cons (step403 p h) (sat_cons (step400 p h) (sat_cons (step401 p h) (sat_cons (step64 p h) (sat_cons (step66 p h) (sat_nil p)))))))))
def c684 : List Lit := [(1468, true)]
theorem step684 (p : Nat → Bool) (h : Constraints p) : clause p c684 = true :=
  Snake9.LocalRup.prove_clause [c683, c412] c684 (by decide) p (sat_cons (step683 p h) (sat_cons (step412 p h) (sat_nil p)))
def c685 : List Lit := [(1559, true)]
theorem step685 (p : Nat → Bool) (h : Constraints p) : clause p c685 = true :=
  Snake9.LocalRup.prove_clause [c285, c551, c553, c548, c538, c544, c535, c536, c202, c207] c685 (by decide) p (sat_cons (step285 p h) (sat_cons (step551 p h) (sat_cons (step553 p h) (sat_cons (step548 p h) (sat_cons (step538 p h) (sat_cons (step544 p h) (sat_cons (step535 p h) (sat_cons (step536 p h) (sat_cons (step202 p h) (sat_cons (step207 p h) (sat_nil p)))))))))))
def c686 : List Lit := [(1539, true)]
theorem step686 (p : Nat → Bool) (h : Constraints p) : clause p c686 = true :=
  Snake9.LocalRup.prove_clause [c284, c520, c524, c512, c514, c501, c509, c510, c506, c498, c175, c155, c172] c686 (by decide) p (sat_cons (step284 p h) (sat_cons (step520 p h) (sat_cons (step524 p h) (sat_cons (step512 p h) (sat_cons (step514 p h) (sat_cons (step501 p h) (sat_cons (step509 p h) (sat_cons (step510 p h) (sat_cons (step506 p h) (sat_cons (step498 p h) (sat_cons (step175 p h) (sat_cons (step155 p h) (sat_cons (step172 p h) (sat_nil p))))))))))))))
def c687 : List Lit := [(1546, true), (79, false)]
theorem step687 (p : Nat → Bool) (h : Constraints p) : clause p c687 = true :=
  Snake9.LocalRup.prove_clause [c285, c535, c536, c202, c207] c687 (by decide) p (sat_cons (step285 p h) (sat_cons (step535 p h) (sat_cons (step536 p h) (sat_cons (step202 p h) (sat_cons (step207 p h) (sat_nil p))))))
def c688 : List Lit := [(77, false), (78, false), (79, false), (1536, true)]
theorem step688 (p : Nat → Bool) (h : Constraints p) : clause p c688 = true :=
  Snake9.LocalRup.prove_clause [c285, c517, c203, c206, c507, c508, c515, c127, c509] c688 (by decide) p (sat_cons (step285 p h) (sat_cons (step517 p h) (sat_cons (step203 p h) (sat_cons (step206 p h) (sat_cons (step507 p h) (sat_cons (step508 p h) (sat_cons (step515 p h) (sat_cons (step127 p h) (sat_cons (step509 p h) (sat_nil p))))))))))
def c689 : List Lit := [(78, false), (1551, true), (1568, true)]
theorem step689 (p : Nat → Bool) (h : Constraints p) : clause p c689 = true :=
  Snake9.LocalRup.prove_clause [c685, c686, c286, c543, c544, c562, c556, c687, c541, c218, c539, c565, c521, c517, c688, c537, c681, c205, c211, c508, c147] c689 (by decide) p (sat_cons (step685 p h) (sat_cons (step686 p h) (sat_cons (step286 p h) (sat_cons (step543 p h) (sat_cons (step544 p h) (sat_cons (step562 p h) (sat_cons (step556 p h) (sat_cons (step687 p h) (sat_cons (step541 p h) (sat_cons (step218 p h) (sat_cons (step539 p h) (sat_cons (step565 p h) (sat_cons (step521 p h) (sat_cons (step517 p h) (sat_cons (step688 p h) (sat_cons (step537 p h) (sat_cons (step681 p h) (sat_cons (step205 p h) (sat_cons (step211 p h) (sat_cons (step508 p h) (sat_cons (step147 p h) (sat_nil p))))))))))))))))))))))
def c690 : List Lit := [(1551, true), (1568, true)]
theorem step690 (p : Nat → Bool) (h : Constraints p) : clause p c690 = true :=
  Snake9.LocalRup.prove_clause [c686, c285, c286, c562, c556, c539, c543, c544, c687, c541, c218, c689, c202, c209, c537, c198] c690 (by decide) p (sat_cons (step686 p h) (sat_cons (step285 p h) (sat_cons (step286 p h) (sat_cons (step562 p h) (sat_cons (step556 p h) (sat_cons (step539 p h) (sat_cons (step543 p h) (sat_cons (step544 p h) (sat_cons (step687 p h) (sat_cons (step541 p h) (sat_cons (step218 p h) (sat_cons (step689 p h) (sat_cons (step202 p h) (sat_cons (step209 p h) (sat_cons (step537 p h) (sat_cons (step198 p h) (sat_nil p)))))))))))))))))
def c691 : List Lit := [(1568, true)]
theorem step691 (p : Nat → Bool) (h : Constraints p) : clause p c691 = true :=
  Snake9.LocalRup.prove_clause [c685, c686, c285, c565, c562, c521, c517, c690, c548, c554, c538, c535, c536, c202, c203, c204, c507, c508, c515, c127, c509] c691 (by decide) p (sat_cons (step685 p h) (sat_cons (step686 p h) (sat_cons (step285 p h) (sat_cons (step565 p h) (sat_cons (step562 p h) (sat_cons (step521 p h) (sat_cons (step517 p h) (sat_cons (step690 p h) (sat_cons (step548 p h) (sat_cons (step554 p h) (sat_cons (step538 p h) (sat_cons (step535 p h) (sat_cons (step536 p h) (sat_cons (step202 p h) (sat_cons (step203 p h) (sat_cons (step204 p h) (sat_cons (step507 p h) (sat_cons (step508 p h) (sat_cons (step515 p h) (sat_cons (step127 p h) (sat_cons (step509 p h) (sat_nil p))))))))))))))))))))))
def c692 : List Lit := [(1434, true)]
theorem step692 (p : Nat → Bool) (h : Constraints p) : clause p c692 = true :=
  Snake9.LocalRup.prove_clause [c265, c361, c364, c356, c343, c348, c349, c340, c21, c24] c692 (by decide) p (sat_cons (step265 p h) (sat_cons (step361 p h) (sat_cons (step364 p h) (sat_cons (step356 p h) (sat_cons (step343 p h) (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step340 p h) (sat_cons (step21 p h) (sat_cons (step24 p h) (sat_nil p)))))))))))
def c693 : List Lit := [(1441, true)]
theorem step693 (p : Nat → Bool) (h : Constraints p) : clause p c693 = true :=
  Snake9.LocalRup.prove_clause [c692, c375] c693 (by decide) p (sat_cons (step692 p h) (sat_cons (step375 p h) (sat_nil p)))
def c694 : List Lit := [(1488, true)]
theorem step694 (p : Nat → Bool) (h : Constraints p) : clause p c694 = true :=
  Snake9.LocalRup.prove_clause [c276, c442, c445, c437, c425, c427, c430, c431, c423, c90, c97, c95] c694 (by decide) p (sat_cons (step276 p h) (sat_cons (step442 p h) (sat_cons (step445 p h) (sat_cons (step437 p h) (sat_cons (step425 p h) (sat_cons (step427 p h) (sat_cons (step430 p h) (sat_cons (step431 p h) (sat_cons (step423 p h) (sat_cons (step90 p h) (sat_cons (step97 p h) (sat_cons (step95 p h) (sat_nil p)))))))))))))
def c695 : List Lit := [(1496, true)]
theorem step695 (p : Nat → Bool) (h : Constraints p) : clause p c695 = true :=
  Snake9.LocalRup.prove_clause [c694, c684, c453] c695 (by decide) p (sat_cons (step694 p h) (sat_cons (step684 p h) (sat_cons (step453 p h) (sat_nil p))))
def c696 : List Lit := [(1593, true)]
theorem step696 (p : Nat → Bool) (h : Constraints p) : clause p c696 = true :=
  Snake9.LocalRup.prove_clause [c289, c592, c594, c590, c584, c586, c587, c583, c222, c220] c696 (by decide) p (sat_cons (step289 p h) (sat_cons (step592 p h) (sat_cons (step594 p h) (sat_cons (step590 p h) (sat_cons (step584 p h) (sat_cons (step586 p h) (sat_cons (step587 p h) (sat_cons (step583 p h) (sat_cons (step222 p h) (sat_cons (step220 p h) (sat_nil p)))))))))))
def c697 : List Lit := [(77, false), (1543, true), (70, true), (58, true), (1531, false), (65, false), (67, false)]
theorem step697 (p : Nat → Bool) (h : Constraints p) : clause p c697 = true :=
  Snake9.LocalRup.prove_clause [c127, c124, c511, c498, c516, c504, c531] c697 (by decide) p (sat_cons (step127 p h) (sat_cons (step124 p h) (sat_cons (step511 p h) (sat_cons (step498 p h) (sat_cons (step516 p h) (sat_cons (step504 p h) (sat_cons (step531 p h) (sat_nil p))))))))
def c698 : List Lit := [(1477, true), (52, false), (51, false)]
theorem step698 (p : Nat → Bool) (h : Constraints p) : clause p c698 = true :=
  Snake9.LocalRup.prove_clause [c276, c425, c427, c423, c90, c97, c95] c698 (by decide) p (sat_cons (step276 p h) (sat_cons (step425 p h) (sat_cons (step427 p h) (sat_cons (step423 p h) (sat_cons (step90 p h) (sat_cons (step97 p h) (sat_cons (step95 p h) (sat_nil p))))))))
def c699 : List Lit := [(1489, true), (51, false), (1482, false)]
theorem step699 (p : Nat → Bool) (h : Constraints p) : clause p c699 = true :=
  Snake9.LocalRup.prove_clause [c436, c443, c446, c438, c698, c430] c699 (by decide) p (sat_cons (step436 p h) (sat_cons (step443 p h) (sat_cons (step446 p h) (sat_cons (step438 p h) (sat_cons (step698 p h) (sat_cons (step430 p h) (sat_nil p)))))))
def c700 : List Lit := [(1513, true), (1489, false)]
theorem step700 (p : Nat → Bool) (h : Constraints p) : clause p c700 = true :=
  Snake9.LocalRup.prove_clause [c684, c693, c683, c269, c265, c454, c469, c458, c473, c414, c376, c395, c397, c362, c392, c393, c51, c60, c63, c351, c354, c357, c365, c348, c349, c343, c21, c340, c24] c700 (by decide) p (sat_cons (step684 p h) (sat_cons (step693 p h) (sat_cons (step683 p h) (sat_cons (step269 p h) (sat_cons (step265 p h) (sat_cons (step454 p h) (sat_cons (step469 p h) (sat_cons (step458 p h) (sat_cons (step473 p h) (sat_cons (step414 p h) (sat_cons (step376 p h) (sat_cons (step395 p h) (sat_cons (step397 p h) (sat_cons (step362 p h) (sat_cons (step392 p h) (sat_cons (step393 p h) (sat_cons (step51 p h) (sat_cons (step60 p h) (sat_cons (step63 p h) (sat_cons (step351 p h) (sat_cons (step354 p h) (sat_cons (step357 p h) (sat_cons (step365 p h) (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step343 p h) (sat_cons (step21 p h) (sat_cons (step340 p h) (sat_cons (step24 p h) (sat_nil p))))))))))))))))))))))))))))))
def c701 : List Lit := [(1435, true), (1428, false)]
theorem step701 (p : Nat → Bool) (h : Constraints p) : clause p c701 = true :=
  Snake9.LocalRup.prove_clause [c265, c354, c362, c365, c357, c343, c348, c349, c340, c21, c24] c701 (by decide) p (sat_cons (step265 p h) (sat_cons (step354 p h) (sat_cons (step362 p h) (sat_cons (step365 p h) (sat_cons (step357 p h) (sat_cons (step343 p h) (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step340 p h) (sat_cons (step21 p h) (sat_cons (step24 p h) (sat_nil p))))))))))))
def c702 : List Lit := [(1457, true), (86, false), (1443, true)]
theorem step702 (p : Nat → Bool) (h : Constraints p) : clause p c702 = true :=
  Snake9.LocalRup.prove_clause [c269, c261, c263, c262, c377, c395, c397, c392, c393, c51, c60, c63, c351, c354, c369, c344, c701, c381, c332, c327, c324, c325, c13, c11, c19, c340, c342, c346, c17, c16] c702 (by decide) p (sat_cons (step269 p h) (sat_cons (step261 p h) (sat_cons (step263 p h) (sat_cons (step262 p h) (sat_cons (step377 p h) (sat_cons (step395 p h) (sat_cons (step397 p h) (sat_cons (step392 p h) (sat_cons (step393 p h) (sat_cons (step51 p h) (sat_cons (step60 p h) (sat_cons (step63 p h) (sat_cons (step351 p h) (sat_cons (step354 p h) (sat_cons (step369 p h) (sat_cons (step344 p h) (sat_cons (step701 p h) (sat_cons (step381 p h) (sat_cons (step332 p h) (sat_cons (step327 p h) (sat_cons (step324 p h) (sat_cons (step325 p h) (sat_cons (step13 p h) (sat_cons (step11 p h) (sat_cons (step19 p h) (sat_cons (step340 p h) (sat_cons (step342 p h) (sat_cons (step346 p h) (sat_cons (step17 p h) (sat_cons (step16 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c703 : List Lit := [(1627, false), (1550, false), (1551, false), (1489, false), (1572, false), (1541, false)]
theorem step703 (p : Nat → Bool) (h : Constraints p) : clause p c703 = true :=
  Snake9.TreeRup.prove_clause [c684, c668, c693, c288, c683, c692, c261, c263, c265, c264, c270, c700, c661, c454, c656, c662, c470, c461, c479, c417, c660, c396, c573, c561, c549, c546, c219, c702, c414, c415, c458, c407, c474, c376, c380, c368, c701, c332, c344, c352, c327, c324, c325, c13, c11, c19, c340, c342, c343, c365, c356, c348, c349, c22, c20, c23, c403, c405, c409, c71, c401, c394, c65, c31] c703 (by decide) p (sat_cons (step684 p h) (sat_cons (step668 p h) (sat_cons (step693 p h) (sat_cons (step288 p h) (sat_cons (step683 p h) (sat_cons (step692 p h) (sat_cons (step261 p h) (sat_cons (step263 p h) (sat_cons (step265 p h) (sat_cons (step264 p h) (sat_cons (step270 p h) (sat_cons (step700 p h) (sat_cons (step661 p h) (sat_cons (step454 p h) (sat_cons (step656 p h) (sat_cons (step662 p h) (sat_cons (step470 p h) (sat_cons (step461 p h) (sat_cons (step479 p h) (sat_cons (step417 p h) (sat_cons (step660 p h) (sat_cons (step396 p h) (sat_cons (step573 p h) (sat_cons (step561 p h) (sat_cons (step549 p h) (sat_cons (step546 p h) (sat_cons (step219 p h) (sat_cons (step702 p h) (sat_cons (step414 p h) (sat_cons (step415 p h) (sat_cons (step458 p h) (sat_cons (step407 p h) (sat_cons (step474 p h) (sat_cons (step376 p h) (sat_cons (step380 p h) (sat_cons (step368 p h) (sat_cons (step701 p h) (sat_cons (step332 p h) (sat_cons (step344 p h) (sat_cons (step352 p h) (sat_cons (step327 p h) (sat_cons (step324 p h) (sat_cons (step325 p h) (sat_cons (step13 p h) (sat_cons (step11 p h) (sat_cons (step19 p h) (sat_cons (step340 p h) (sat_cons (step342 p h) (sat_cons (step343 p h) (sat_cons (step365 p h) (sat_cons (step356 p h) (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step22 p h) (sat_cons (step20 p h) (sat_cons (step23 p h) (sat_cons (step403 p h) (sat_cons (step405 p h) (sat_cons (step409 p h) (sat_cons (step71 p h) (sat_cons (step401 p h) (sat_cons (step394 p h) (sat_cons (step65 p h) (sat_cons (step31 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c704 : List Lit := [(35, false), (18, false), (1428, true)]
theorem step704 (p : Nat → Bool) (h : Constraints p) : clause p c704 = true :=
  Snake9.LocalRup.prove_clause [c269, c352, c351, c38, c29, c62] c704 (by decide) p (sat_cons (step269 p h) (sat_cons (step352 p h) (sat_cons (step351 p h) (sat_cons (step38 p h) (sat_cons (step29 p h) (sat_cons (step62 p h) (sat_nil p)))))))
def c705 : List Lit := [(33, true), (1460, false), (35, true), (43, true), (23, false), (1472, true)]
theorem step705 (p : Nat → Bool) (h : Constraints p) : clause p c705 = true :=
  Snake9.LocalRup.prove_clause [c264, c403, c409, c421, c392, c20, c398, c399, c419, c394, c410, c71, c405] c705 (by decide) p (sat_cons (step264 p h) (sat_cons (step403 p h) (sat_cons (step409 p h) (sat_cons (step421 p h) (sat_cons (step392 p h) (sat_cons (step20 p h) (sat_cons (step398 p h) (sat_cons (step399 p h) (sat_cons (step419 p h) (sat_cons (step394 p h) (sat_cons (step410 p h) (sat_cons (step71 p h) (sat_cons (step405 p h) (sat_nil p))))))))))))))
def c706 : List Lit := [(33, false), (18, false), (20, false), (27, false)]
theorem step706 (p : Nat → Bool) (h : Constraints p) : clause p c706 = true :=
  Snake9.LocalRup.prove_clause [c262, c36, c17, c16] c706 (by decide) p (sat_cons (step262 p h) (sat_cons (step36 p h) (sat_cons (step17 p h) (sat_cons (step16 p h) (sat_nil p)))))
def c707 : List Lit := [(37, false), (1428, true)]
theorem step707 (p : Nat → Bool) (h : Constraints p) : clause p c707 = true :=
  Snake9.LocalRup.prove_clause [c270, c352, c351, c65, c30] c707 (by decide) p (sat_cons (step270 p h) (sat_cons (step352 p h) (sat_cons (step351 p h) (sat_cons (step65 p h) (sat_cons (step30 p h) (sat_nil p))))))
def c708 : List Lit := [(1612, true)]
theorem step708 (p : Nat → Bool) (h : Constraints p) : clause p c708 = true :=
  Snake9.LocalRup.prove_clause [c296, c616, c618, c613, c614, c610, c255, c257] c708 (by decide) p (sat_cons (step296 p h) (sat_cons (step616 p h) (sat_cons (step618 p h) (sat_cons (step613 p h) (sat_cons (step614 p h) (sat_cons (step610 p h) (sat_cons (step255 p h) (sat_cons (step257 p h) (sat_nil p)))))))))
def c709 : List Lit := [(1616, true)]
theorem step709 (p : Nat → Bool) (h : Constraints p) : clause p c709 = true :=
  Snake9.LocalRup.prove_clause [c708, c621] c709 (by decide) p (sat_cons (step708 p h) (sat_cons (step621 p h) (sat_nil p)))
def c710 : List Lit := [(1625, true)]
theorem step710 (p : Nat → Bool) (h : Constraints p) : clause p c710 = true :=
  Snake9.LocalRup.prove_clause [c709, c696, c629] c710 (by decide) p (sat_cons (step709 p h) (sat_cons (step696 p h) (sat_cons (step629 p h) (sat_nil p))))
def c711 : List Lit := [(1604, true)]
theorem step711 (p : Nat → Bool) (h : Constraints p) : clause p c711 = true :=
  Snake9.LocalRup.prove_clause [c293, c603, c605, c600, c601, c597, c598, c243, c252, c244] c711 (by decide) p (sat_cons (step293 p h) (sat_cons (step603 p h) (sat_cons (step605 p h) (sat_cons (step600 p h) (sat_cons (step601 p h) (sat_cons (step597 p h) (sat_cons (step598 p h) (sat_cons (step243 p h) (sat_cons (step252 p h) (sat_cons (step244 p h) (sat_nil p)))))))))))
def c712 : List Lit := [(1617, true)]
theorem step712 (p : Nat → Bool) (h : Constraints p) : clause p c712 = true :=
  Snake9.LocalRup.prove_clause [c711, c708, c622] c712 (by decide) p (sat_cons (step711 p h) (sat_cons (step708 p h) (sat_cons (step622 p h) (sat_nil p))))
def c713 : List Lit := [(1626, true)]
theorem step713 (p : Nat → Bool) (h : Constraints p) : clause p c713 = true :=
  Snake9.LocalRup.prove_clause [c712, c696, c630] c713 (by decide) p (sat_cons (step712 p h) (sat_cons (step696 p h) (sat_cons (step630 p h) (sat_nil p))))
def c714 : List Lit := [(1644, true)]
theorem step714 (p : Nat → Bool) (h : Constraints p) : clause p c714 = true :=
  Snake9.LocalRup.prove_clause [c713, c691, c639] c714 (by decide) p (sat_cons (step713 p h) (sat_cons (step691 p h) (sat_cons (step639 p h) (sat_nil p))))
def c715 : List Lit := [(1519, false)]
theorem step715 (p : Nat → Bool) (h : Constraints p) : clause p c715 = true :=
  Snake9.LocalRup.prove_clause [c714, c668, c667] c715 (by decide) p (sat_cons (step714 p h) (sat_cons (step668 p h) (sat_cons (step667 p h) (sat_nil p))))
def c716 : List Lit := [(1469, true), (32, true), (1460, false), (105, true)]
theorem step716 (p : Nat → Bool) (h : Constraints p) : clause p c716 = true :=
  Snake9.LocalRup.prove_clause [c683, c267, c413, c414, c409, c397, c403, c404, c55, c70] c716 (by decide) p (sat_cons (step683 p h) (sat_cons (step267 p h) (sat_cons (step413 p h) (sat_cons (step414 p h) (sat_cons (step409 p h) (sat_cons (step397 p h) (sat_cons (step403 p h) (sat_cons (step404 p h) (sat_cons (step55 p h) (sat_cons (step70 p h) (sat_nil p)))))))))))
def c717 : List Lit := [(1541, true), (1490, true), (70, true), (51, false), (62, true), (69, false), (104, false)]
theorem step717 (p : Nat → Bool) (h : Constraints p) : clause p c717 = true :=
  Snake9.LocalRup.prove_clause [c281, c274, c510, c512, c498, c501, c526, c529, c513, c515, c502, c504, c511, c506, c507, c500, c154, c108, c422, c109, c425, c433, c436, c449, c447, c426, c438, c424, c430, c97, c134, c82] c717 (by decide) p (sat_cons (step281 p h) (sat_cons (step274 p h) (sat_cons (step510 p h) (sat_cons (step512 p h) (sat_cons (step498 p h) (sat_cons (step501 p h) (sat_cons (step526 p h) (sat_cons (step529 p h) (sat_cons (step513 p h) (sat_cons (step515 p h) (sat_cons (step502 p h) (sat_cons (step504 p h) (sat_cons (step511 p h) (sat_cons (step506 p h) (sat_cons (step507 p h) (sat_cons (step500 p h) (sat_cons (step154 p h) (sat_cons (step108 p h) (sat_cons (step422 p h) (sat_cons (step109 p h) (sat_cons (step425 p h) (sat_cons (step433 p h) (sat_cons (step436 p h) (sat_cons (step449 p h) (sat_cons (step447 p h) (sat_cons (step426 p h) (sat_cons (step438 p h) (sat_cons (step424 p h) (sat_cons (step430 p h) (sat_cons (step97 p h) (sat_cons (step134 p h) (sat_cons (step82 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c718 : List Lit := [(1594, true), (1587, false)]
theorem step718 (p : Nat → Bool) (h : Constraints p) : clause p c718 = true :=
  Snake9.LocalRup.prove_clause [c289, c589, c593, c595, c591, c584, c586, c587, c583, c222, c220] c718 (by decide) p (sat_cons (step289 p h) (sat_cons (step589 p h) (sat_cons (step593 p h) (sat_cons (step595 p h) (sat_cons (step591 p h) (sat_cons (step584 p h) (sat_cons (step586 p h) (sat_cons (step587 p h) (sat_cons (step583 p h) (sat_cons (step222 p h) (sat_cons (step220 p h) (sat_nil p))))))))))))
def c719 : List Lit := [(1585, true)]
theorem step719 (p : Nat → Bool) (h : Constraints p) : clause p c719 = true :=
  Snake9.LocalRup.prove_clause [c289, c586, c587, c221, c222, c682] c719 (by decide) p (sat_cons (step289 p h) (sat_cons (step586 p h) (sat_cons (step587 p h) (sat_cons (step221 p h) (sat_cons (step222 p h) (sat_cons (step682 p h) (sat_nil p)))))))
def c720 : List Lit := [(1589, true)]
theorem step720 (p : Nat → Bool) (h : Constraints p) : clause p c720 = true :=
  Snake9.LocalRup.prove_clause [c719, c590] c720 (by decide) p (sat_cons (step719 p h) (sat_cons (step590 p h) (sat_nil p)))
def c721 : List Lit := [(82, true), (1561, true), (74, true)]
theorem step721 (p : Nat → Bool) (h : Constraints p) : clause p c721 = true :=
  Snake9.LocalRup.prove_clause [c540, c555, c550, c543, c545, c548, c687, c557, c541] c721 (by decide) p (sat_cons (step540 p h) (sat_cons (step555 p h) (sat_cons (step550 p h) (sat_cons (step543 p h) (sat_cons (step545 p h) (sat_cons (step548 p h) (sat_cons (step687 p h) (sat_cons (step557 p h) (sat_cons (step541 p h) (sat_nil p))))))))))
def c722 : List Lit := [(1537, true), (77, false), (70, true)]
theorem step722 (p : Nat → Bool) (h : Constraints p) : clause p c722 = true :=
  Snake9.LocalRup.prove_clause [c285, c202, c203, c678, c507, c510, c518, c516, c508, c511, c127] c722 (by decide) p (sat_cons (step285 p h) (sat_cons (step202 p h) (sat_cons (step203 p h) (sat_cons (step678 p h) (sat_cons (step507 p h) (sat_cons (step510 p h) (sat_cons (step518 p h) (sat_cons (step516 p h) (sat_cons (step508 p h) (sat_cons (step511 p h) (sat_cons (step127 p h) (sat_nil p))))))))))))
def c723 : List Lit := [(1555, false), (70, true), (1561, true), (1571, true), (74, true)]
theorem step723 (p : Nat → Bool) (h : Constraints p) : clause p c723 = true :=
  Snake9.LocalRup.prove_clause [c285, c540, c554, c557, c576, c541, c523, c535, c202, c203, c678, c722, c527, c501, c498, c124, c125, c508, c511, c519] c723 (by decide) p (sat_cons (step285 p h) (sat_cons (step540 p h) (sat_cons (step554 p h) (sat_cons (step557 p h) (sat_cons (step576 p h) (sat_cons (step541 p h) (sat_cons (step523 p h) (sat_cons (step535 p h) (sat_cons (step202 p h) (sat_cons (step203 p h) (sat_cons (step678 p h) (sat_cons (step722 p h) (sat_cons (step527 p h) (sat_cons (step501 p h) (sat_cons (step498 p h) (sat_cons (step124 p h) (sat_cons (step125 p h) (sat_cons (step508 p h) (sat_cons (step511 p h) (sat_cons (step519 p h) (sat_nil p)))))))))))))))))))))
def c724 : List Lit := [(1514, true), (86, false), (1489, false), (1442, false)]
theorem step724 (p : Nat → Bool) (h : Constraints p) : clause p c724 = true :=
  Snake9.LocalRup.prove_clause [c684, c683, c454, c479, c474, c702, c458, c414] c724 (by decide) p (sat_cons (step684 p h) (sat_cons (step683 p h) (sat_cons (step454 p h) (sat_cons (step479 p h) (sat_cons (step474 p h) (sat_cons (step702 p h) (sat_cons (step458 p h) (sat_cons (step414 p h) (sat_nil p)))))))))
def c725 : List Lit := [(1490, true), (1528, true), (51, true)]
theorem step725 (p : Nat → Bool) (h : Constraints p) : clause p c725 = true :=
  Snake9.LocalRup.prove_clause [c281, c275, c431, c503, c501, c499, c108, c109, c433, c438, c498, c444, c447, c441, c425, c427, c432, c422, c89, c78, c87] c725 (by decide) p (sat_cons (step281 p h) (sat_cons (step275 p h) (sat_cons (step431 p h) (sat_cons (step503 p h) (sat_cons (step501 p h) (sat_cons (step499 p h) (sat_cons (step108 p h) (sat_cons (step109 p h) (sat_cons (step433 p h) (sat_cons (step438 p h) (sat_cons (step498 p h) (sat_cons (step444 p h) (sat_cons (step447 p h) (sat_cons (step441 p h) (sat_cons (step425 p h) (sat_cons (step427 p h) (sat_cons (step432 p h) (sat_cons (step422 p h) (sat_cons (step89 p h) (sat_cons (step78 p h) (sat_cons (step87 p h) (sat_nil p))))))))))))))))))))))
def c726 : List Lit := [(1469, true), (105, true), (1436, true)]
theorem step726 (p : Nat → Bool) (h : Constraints p) : clause p c726 = true :=
  Snake9.LocalRup.prove_clause [c683, c267, c269, c414, c395, c397, c392, c393, c51, c716, c56, c62, c60, c401, c63, c31, c353, c355, c366, c343, c345, c341, c17] c726 (by decide) p (sat_cons (step683 p h) (sat_cons (step267 p h) (sat_cons (step269 p h) (sat_cons (step414 p h) (sat_cons (step395 p h) (sat_cons (step397 p h) (sat_cons (step392 p h) (sat_cons (step393 p h) (sat_cons (step51 p h) (sat_cons (step716 p h) (sat_cons (step56 p h) (sat_cons (step62 p h) (sat_cons (step60 p h) (sat_cons (step401 p h) (sat_cons (step63 p h) (sat_cons (step31 p h) (sat_cons (step353 p h) (sat_cons (step355 p h) (sat_cons (step366 p h) (sat_cons (step343 p h) (sat_cons (step345 p h) (sat_cons (step341 p h) (sat_cons (step17 p h) (sat_nil p))))))))))))))))))))))))
def c727 : List Lit := [(1627, true), (105, false), (106, false)]
theorem step727 (p : Nat → Bool) (h : Constraints p) : clause p c727 = true :=
  Snake9.LocalRup.prove_clause [c696, c712, c708, c631, c634, c624, c718, c588, c240, c242, c597, c600, c606] c727 (by decide) p (sat_cons (step696 p h) (sat_cons (step712 p h) (sat_cons (step708 p h) (sat_cons (step631 p h) (sat_cons (step634 p h) (sat_cons (step624 p h) (sat_cons (step718 p h) (sat_cons (step588 p h) (sat_cons (step240 p h) (sat_cons (step242 p h) (sat_cons (step597 p h) (sat_cons (step600 p h) (sat_cons (step606 p h) (sat_nil p))))))))))))))
def c728 : List Lit := [(1455, true), (30, false), (27, false)]
theorem step728 (p : Nat → Bool) (h : Constraints p) : clause p c728 = true :=
  Snake9.LocalRup.prove_clause [c392, c393, c29, c63, c48, c59] c728 (by decide) p (sat_cons (step392 p h) (sat_cons (step393 p h) (sat_cons (step29 p h) (sat_cons (step63 p h) (sat_cons (step48 p h) (sat_cons (step59 p h) (sat_nil p)))))))
def c729 : List Lit := [(1516, true), (1490, false), (1414, false), (1457, false), (33, false)]
theorem step729 (p : Nat → Bool) (h : Constraints p) : clause p c729 = true :=
  Snake9.LocalRup.prove_clause [c692, c683, c272, c414, c459, c380, c476, c481, c462, c381, c415, c701, c411, c707, c402, c401, c409, c403, c404, c77, c70, c74] c729 (by decide) p (sat_cons (step692 p h) (sat_cons (step683 p h) (sat_cons (step272 p h) (sat_cons (step414 p h) (sat_cons (step459 p h) (sat_cons (step380 p h) (sat_cons (step476 p h) (sat_cons (step481 p h) (sat_cons (step462 p h) (sat_cons (step381 p h) (sat_cons (step415 p h) (sat_cons (step701 p h) (sat_cons (step411 p h) (sat_cons (step707 p h) (sat_cons (step402 p h) (sat_cons (step401 p h) (sat_cons (step409 p h) (sat_cons (step403 p h) (sat_cons (step404 p h) (sat_cons (step77 p h) (sat_cons (step70 p h) (sat_cons (step74 p h) (sat_nil p)))))))))))))))))))))))
def c730 : List Lit := [(37, true), (1465, true), (103, false), (30, false)]
theorem step730 (p : Nat → Bool) (h : Constraints p) : clause p c730 = true :=
  Snake9.LocalRup.prove_clause [c271, c411, c401, c402, c409, c35, c403, c404, c69, c77] c730 (by decide) p (sat_cons (step271 p h) (sat_cons (step411 p h) (sat_cons (step401 p h) (sat_cons (step402 p h) (sat_cons (step409 p h) (sat_cons (step35 p h) (sat_cons (step403 p h) (sat_cons (step404 p h) (sat_cons (step69 p h) (sat_cons (step77 p h) (sat_nil p)))))))))))
def c731 : List Lit := [(1415, true), (75, false), (1401, false), (82, false)]
theorem step731 (p : Nat → Bool) (h : Constraints p) : clause p c731 = true :=
  Snake9.LocalRup.prove_clause [c260, c319, c338, c336, c322, c329, c323, c191, c9, c10] c731 (by decide) p (sat_cons (step260 p h) (sat_cons (step319 p h) (sat_cons (step338 p h) (sat_cons (step336 p h) (sat_cons (step322 p h) (sat_cons (step329 p h) (sat_cons (step323 p h) (sat_cons (step191 p h) (sat_cons (step9 p h) (sat_cons (step10 p h) (sat_nil p)))))))))))
def c732 : List Lit := [(66, false), (76, true), (79, false), (103, false), (75, false)]
theorem step732 (p : Nat → Bool) (h : Constraints p) : clause p c732 = true :=
  Snake9.LocalRup.prove_clause [c286, c146, c205, c212] c732 (by decide) p (sat_cons (step286 p h) (sat_cons (step146 p h) (sat_cons (step205 p h) (sat_cons (step212 p h) (sat_nil p)))))
def c733 : List Lit := [(1489, true), (76, true), (1480, false), (75, false)]
theorem step733 (p : Nat → Bool) (h : Constraints p) : clause p c733 = true :=
  Snake9.LocalRup.prove_clause [c278, c437, c443, c446, c438, c427, c434, c101, c104] c733 (by decide) p (sat_cons (step278 p h) (sat_cons (step437 p h) (sat_cons (step443 p h) (sat_cons (step446 p h) (sat_cons (step438 p h) (sat_cons (step427 p h) (sat_cons (step434 p h) (sat_cons (step101 p h) (sat_cons (step104 p h) (sat_nil p))))))))))
def c734 : List Lit := [(1414, true), (76, true), (75, false)]
theorem step734 (p : Nat → Bool) (h : Constraints p) : clause p c734 = true :=
  Snake9.LocalRup.prove_clause [c260, c332, c335, c329, c321, c323, c9, c10] c734 (by decide) p (sat_cons (step260 p h) (sat_cons (step332 p h) (sat_cons (step335 p h) (sat_cons (step329 p h) (sat_cons (step321 p h) (sat_cons (step323 p h) (sat_cons (step9 p h) (sat_cons (step10 p h) (sat_nil p)))))))))
def c735 : List Lit := [(1482, false), (1489, true)]
theorem step735 (p : Nat → Bool) (h : Constraints p) : clause p c735 = true :=
  Snake9.LocalRup.prove_clause [c443, c438, c699, c431] c735 (by decide) p (sat_cons (step443 p h) (sat_cons (step438 p h) (sat_cons (step699 p h) (sat_cons (step431 p h) (sat_nil p)))))
def c736 : List Lit := [(49, true), (1489, true)]
theorem step736 (p : Nat → Bool) (h : Constraints p) : clause p c736 = true :=
  Snake9.LocalRup.prove_clause [c276, c448, c426, c422, c424, c425, c428, c446, c437, c430, c431, c90, c97, c95] c736 (by decide) p (sat_cons (step276 p h) (sat_cons (step448 p h) (sat_cons (step426 p h) (sat_cons (step422 p h) (sat_cons (step424 p h) (sat_cons (step425 p h) (sat_cons (step428 p h) (sat_cons (step446 p h) (sat_cons (step437 p h) (sat_cons (step430 p h) (sat_cons (step431 p h) (sat_cons (step90 p h) (sat_cons (step97 p h) (sat_cons (step95 p h) (sat_nil p)))))))))))))))
def c737 : List Lit := [(75, false), (1416, true), (1401, false), (46, false), (50, true), (56, false)]
theorem step737 (p : Nat → Bool) (h : Constraints p) : clause p c737 = true :=
  Snake9.LocalRup.prove_clause [c278, c273, c101, c104, c79, c186, c111, c323, c322, c329, c339] c737 (by decide) p (sat_cons (step278 p h) (sat_cons (step273 p h) (sat_cons (step101 p h) (sat_cons (step104 p h) (sat_cons (step79 p h) (sat_cons (step186 p h) (sat_cons (step111 p h) (sat_cons (step323 p h) (sat_cons (step322 p h) (sat_cons (step329 p h) (sat_cons (step339 p h) (sat_nil p))))))))))))
def c738 : List Lit := [(1529, false), (75, true), (1572, true), (1533, false), (82, true), (74, true)]
theorem step738 (p : Nat → Bool) (h : Constraints p) : clause p c738 = true :=
  Snake9.LocalRup.prove_clause [c285, c536, c541, c721, c577, c543, c548, c512, c529, c530, c572, c515, c560, c558, c507, c542, c550, c537, c545, c202, c206] c738 (by decide) p (sat_cons (step285 p h) (sat_cons (step536 p h) (sat_cons (step541 p h) (sat_cons (step721 p h) (sat_cons (step577 p h) (sat_cons (step543 p h) (sat_cons (step548 p h) (sat_cons (step512 p h) (sat_cons (step529 p h) (sat_cons (step530 p h) (sat_cons (step572 p h) (sat_cons (step515 p h) (sat_cons (step560 p h) (sat_cons (step558 p h) (sat_cons (step507 p h) (sat_cons (step542 p h) (sat_cons (step550 p h) (sat_cons (step537 p h) (sat_cons (step545 p h) (sat_cons (step202 p h) (sat_cons (step206 p h) (sat_nil p))))))))))))))))))))))
def c739 : List Lit := [(70, false), (1480, true), (1489, true), (1498, false)]
theorem step739 (p : Nat → Bool) (h : Constraints p) : clause p c739 = true :=
  Snake9.LocalRup.prove_clause [c276, c275, c708, c696, c668, c692, c280, c736, c430, c431, c91, c85, c87, c673, c498, c501, c448, c95, c97, c423, c428, c100, c94, c735, c434, c433, c152, c153, c169, c159, c168, c162, c509, c597, c601, c721, c317, c512, c606, c319, c525, c624, c335, c567, c631, c380, c649, c474, c664, c662, c486, c656, c389, c737, c738, c504, c107, c102] c739 (by decide) p (sat_cons (step276 p h) (sat_cons (step275 p h) (sat_cons (step708 p h) (sat_cons (step696 p h) (sat_cons (step668 p h) (sat_cons (step692 p h) (sat_cons (step280 p h) (sat_cons (step736 p h) (sat_cons (step430 p h) (sat_cons (step431 p h) (sat_cons (step91 p h) (sat_cons (step85 p h) (sat_cons (step87 p h) (sat_cons (step673 p h) (sat_cons (step498 p h) (sat_cons (step501 p h) (sat_cons (step448 p h) (sat_cons (step95 p h) (sat_cons (step97 p h) (sat_cons (step423 p h) (sat_cons (step428 p h) (sat_cons (step100 p h) (sat_cons (step94 p h) (sat_cons (step735 p h) (sat_cons (step434 p h) (sat_cons (step433 p h) (sat_cons (step152 p h) (sat_cons (step153 p h) (sat_cons (step169 p h) (sat_cons (step159 p h) (sat_cons (step168 p h) (sat_cons (step162 p h) (sat_cons (step509 p h) (sat_cons (step597 p h) (sat_cons (step601 p h) (sat_cons (step721 p h) (sat_cons (step317 p h) (sat_cons (step512 p h) (sat_cons (step606 p h) (sat_cons (step319 p h) (sat_cons (step525 p h) (sat_cons (step624 p h) (sat_cons (step335 p h) (sat_cons (step567 p h) (sat_cons (step631 p h) (sat_cons (step380 p h) (sat_cons (step649 p h) (sat_cons (step474 p h) (sat_cons (step664 p h) (sat_cons (step662 p h) (sat_cons (step486 p h) (sat_cons (step656 p h) (sat_cons (step389 p h) (sat_cons (step737 p h) (sat_cons (step738 p h) (sat_cons (step504 p h) (sat_cons (step107 p h) (sat_cons (step102 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c740 : List Lit := [(1572, true), (1541, false), (70, true), (75, true), (1528, false), (82, true), (74, true)]
theorem step740 (p : Nat → Bool) (h : Constraints p) : clause p c740 = true :=
  Snake9.LocalRup.prove_clause [c543, c548, c721, c577, c572, c527, c560, c722, c542, c537] c740 (by decide) p (sat_cons (step543 p h) (sat_cons (step548 p h) (sat_cons (step721 p h) (sat_cons (step577 p h) (sat_cons (step572 p h) (sat_cons (step527 p h) (sat_cons (step560 p h) (sat_cons (step722 p h) (sat_cons (step542 p h) (sat_cons (step537 p h) (sat_nil p)))))))))))
def c741 : List Lit := [(111, true), (1613, true)]
theorem step741 (p : Nat → Bool) (h : Constraints p) : clause p c741 = true :=
  Snake9.LocalRup.prove_clause [c296, c620, c611, c612, c619, c613, c614, c255, c257] c741 (by decide) p (sat_cons (step296 p h) (sat_cons (step620 p h) (sat_cons (step611 p h) (sat_cons (step612 p h) (sat_cons (step619 p h) (sat_cons (step613 p h) (sat_cons (step614 p h) (sat_cons (step255 p h) (sat_cons (step257 p h) (sat_nil p))))))))))
def c742 : List Lit := [(1403, true), (66, false)]
theorem step742 (p : Nat → Bool) (h : Constraints p) : clause p c742 = true :=
  Snake9.LocalRup.prove_clause [c259, c319, c321, c316, c6, c2] c742 (by decide) p (sat_cons (step259 p h) (sat_cons (step319 p h) (sat_cons (step321 p h) (sat_cons (step316 p h) (sat_cons (step6 p h) (sat_cons (step2 p h) (sat_nil p)))))))
def c743 : List Lit := [(105, false), (106, false), (101, false), (1605, true)]
theorem step743 (p : Nat → Bool) (h : Constraints p) : clause p c743 = true :=
  Snake9.LocalRup.prove_clause [c240, c242, c597, c600, c606] c743 (by decide) p (sat_cons (step240 p h) (sat_cons (step242 p h) (sat_cons (step597 p h) (sat_cons (step600 p h) (sat_cons (step606 p h) (sat_nil p))))))
def c744 : List Lit := [(105, false), (101, false), (1605, true)]
theorem step744 (p : Nat → Bool) (h : Constraints p) : clause p c744 = true :=
  Snake9.LocalRup.prove_clause [c604, c743, c601, c602, c606, c241, c597] c744 (by decide) p (sat_cons (step604 p h) (sat_cons (step743 p h) (sat_cons (step601 p h) (sat_cons (step602 p h) (sat_cons (step606 p h) (sat_cons (step241 p h) (sat_cons (step597 p h) (sat_nil p))))))))
def c745 : List Lit := [(1514, true), (86, false), (1414, false), (1601, true), (105, true), (101, false)]
theorem step745 (p : Nat → Bool) (h : Constraints p) : clause p c745 = true :=
  Snake9.LocalRup.prove_clause [c692, c695, c683, c694, c292, c380, c484, c474, c382, c460, c726, c417, c457, c479, c381, c702, c701, c415, c351, c352, c707, c728, c730, c398, c599, c225, c47, c232] c745 (by decide) p (sat_cons (step692 p h) (sat_cons (step695 p h) (sat_cons (step683 p h) (sat_cons (step694 p h) (sat_cons (step292 p h) (sat_cons (step380 p h) (sat_cons (step484 p h) (sat_cons (step474 p h) (sat_cons (step382 p h) (sat_cons (step460 p h) (sat_cons (step726 p h) (sat_cons (step417 p h) (sat_cons (step457 p h) (sat_cons (step479 p h) (sat_cons (step381 p h) (sat_cons (step702 p h) (sat_cons (step701 p h) (sat_cons (step415 p h) (sat_cons (step351 p h) (sat_cons (step352 p h) (sat_cons (step707 p h) (sat_cons (step728 p h) (sat_cons (step730 p h) (sat_cons (step398 p h) (sat_cons (step599 p h) (sat_cons (step225 p h) (sat_cons (step47 p h) (sat_cons (step232 p h) (sat_nil p)))))))))))))))))))))))))))))
def c746 : List Lit := [(18, true), (1435, true)]
theorem step746 (p : Nat → Bool) (h : Constraints p) : clause p c746 = true :=
  Snake9.LocalRup.prove_clause [c263, c368, c345, c346, c365, c340, c356, c18, c348, c349, c24] c746 (by decide) p (sat_cons (step263 p h) (sat_cons (step368 p h) (sat_cons (step345 p h) (sat_cons (step346 p h) (sat_cons (step365 p h) (sat_cons (step340 p h) (sat_cons (step356 p h) (sat_cons (step18 p h) (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step24 p h) (sat_nil p))))))))))))
end B112E058
