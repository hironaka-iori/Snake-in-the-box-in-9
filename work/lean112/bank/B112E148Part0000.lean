import B112E148Inputs
namespace B112E148
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c540 : List Lit := [(58, true)]
theorem step540 (p : Nat → Bool) (h : Constraints p) : clause p c540 = true :=
  Snake9.LocalRup.prove_clause [c135, c134] c540 (by decide) p (sat_cons (step135 p h) (sat_cons (step134 p h) (sat_nil p)))
def c541 : List Lit := [(2, false)]
theorem step541 (p : Nat → Bool) (h : Constraints p) : clause p c541 = true :=
  Snake9.LocalRup.prove_clause [c180, c3] c541 (by decide) p (sat_cons (step180 p h) (sat_cons (step3 p h) (sat_nil p)))
def c542 : List Lit := [(438, false)]
theorem step542 (p : Nat → Bool) (h : Constraints p) : clause p c542 = true :=
  Snake9.LocalRup.prove_clause [c292, c289] c542 (by decide) p (sat_cons (step292 p h) (sat_cons (step289 p h) (sat_nil p)))
def c543 : List Lit := [(330, false)]
theorem step543 (p : Nat → Bool) (h : Constraints p) : clause p c543 = true :=
  Snake9.LocalRup.prove_clause [c292, c291] c543 (by decide) p (sat_cons (step292 p h) (sat_cons (step291 p h) (sat_nil p)))
def c544 : List Lit := [(436, false)]
theorem step544 (p : Nat → Bool) (h : Constraints p) : clause p c544 = true :=
  Snake9.LocalRup.prove_clause [c542, c285] c544 (by decide) p (sat_cons (step542 p h) (sat_cons (step285 p h) (sat_nil p)))
def c545 : List Lit := [(382, false)]
theorem step545 (p : Nat → Bool) (h : Constraints p) : clause p c545 = true :=
  Snake9.LocalRup.prove_clause [c542, c288] c545 (by decide) p (sat_cons (step542 p h) (sat_cons (step288 p h) (sat_nil p)))
def c546 : List Lit := [(328, false)]
theorem step546 (p : Nat → Bool) (h : Constraints p) : clause p c546 = true :=
  Snake9.LocalRup.prove_clause [c543, c252] c546 (by decide) p (sat_cons (step543 p h) (sat_cons (step252 p h) (sat_nil p)))
def c547 : List Lit := [(274, false)]
theorem step547 (p : Nat → Bool) (h : Constraints p) : clause p c547 = true :=
  Snake9.LocalRup.prove_clause [c543, c255] c547 (by decide) p (sat_cons (step543 p h) (sat_cons (step255 p h) (sat_nil p)))
def c548 : List Lit := [(408, false)]
theorem step548 (p : Nat → Bool) (h : Constraints p) : clause p c548 = true :=
  Snake9.LocalRup.prove_clause [c544, c283] c548 (by decide) p (sat_cons (step544 p h) (sat_cons (step283 p h) (sat_nil p)))
def c549 : List Lit := [(394, false)]
theorem step549 (p : Nat → Bool) (h : Constraints p) : clause p c549 = true :=
  Snake9.LocalRup.prove_clause [c548, c281] c549 (by decide) p (sat_cons (step548 p h) (sat_cons (step281 p h) (sat_nil p)))
def c550 : List Lit := [(392, false)]
theorem step550 (p : Nat → Bool) (h : Constraints p) : clause p c550 = true :=
  Snake9.LocalRup.prove_clause [c549, c279] c550 (by decide) p (sat_cons (step549 p h) (sat_cons (step279 p h) (sat_nil p)))
def c551 : List Lit := [(1327, true)]
theorem step551 (p : Nat → Bool) (h : Constraints p) : clause p c551 = true :=
  Snake9.LocalRup.prove_clause [c541, c293] c551 (by decide) p (sat_cons (step541 p h) (sat_cons (step293 p h) (sat_nil p)))
def c552 : List Lit := [(6, true), (1328, true)]
theorem step552 (p : Nat → Bool) (h : Constraints p) : clause p c552 = true :=
  Snake9.LocalRup.prove_clause [c541, c294] c552 (by decide) p (sat_cons (step541 p h) (sat_cons (step294 p h) (sat_nil p)))
def c553 : List Lit := [(1329, true)]
theorem step553 (p : Nat → Bool) (h : Constraints p) : clause p c553 = true :=
  Snake9.LocalRup.prove_clause [c551, c295] c553 (by decide) p (sat_cons (step551 p h) (sat_cons (step295 p h) (sat_nil p)))
def c554 : List Lit := [(1, true), (1330, true)]
theorem step554 (p : Nat → Bool) (h : Constraints p) : clause p c554 = true :=
  Snake9.LocalRup.prove_clause [c551, c297] c554 (by decide) p (sat_cons (step551 p h) (sat_cons (step297 p h) (sat_nil p)))
def c555 : List Lit := [(1334, false), (1338, true)]
theorem step555 (p : Nat → Bool) (h : Constraints p) : clause p c555 = true :=
  Snake9.LocalRup.prove_clause [c553, c307] c555 (by decide) p (sat_cons (step553 p h) (sat_cons (step307 p h) (sat_nil p)))
def c556 : List Lit := [(1335, false), (1339, true)]
theorem step556 (p : Nat → Bool) (h : Constraints p) : clause p c556 = true :=
  Snake9.LocalRup.prove_clause [c553, c308] c556 (by decide) p (sat_cons (step553 p h) (sat_cons (step308 p h) (sat_nil p)))
def c557 : List Lit := [(1336, false), (1340, true)]
theorem step557 (p : Nat → Bool) (h : Constraints p) : clause p c557 = true :=
  Snake9.LocalRup.prove_clause [c553, c309] c557 (by decide) p (sat_cons (step553 p h) (sat_cons (step309 p h) (sat_nil p)))
def c558 : List Lit := [(1501, true)]
theorem step558 (p : Nat → Bool) (h : Constraints p) : clause p c558 = true :=
  Snake9.LocalRup.prove_clause [c211, c482, c483, c479, c480, c157, c166] c558 (by decide) p (sat_cons (step211 p h) (sat_cons (step482 p h) (sat_cons (step483 p h) (sat_cons (step479 p h) (sat_cons (step480 p h) (sat_cons (step157 p h) (sat_cons (step166 p h) (sat_nil p))))))))
def c559 : List Lit := [(1512, true)]
theorem step559 (p : Nat → Bool) (h : Constraints p) : clause p c559 = true :=
  Snake9.LocalRup.prove_clause [c558, c498] c559 (by decide) p (sat_cons (step558 p h) (sat_cons (step498 p h) (sat_nil p)))
def c560 : List Lit := [(1378, true)]
theorem step560 (p : Nat → Bool) (h : Constraints p) : clause p c560 = true :=
  Snake9.LocalRup.prove_clause [c190, c359, c361, c356, c357, c81, c74] c560 (by decide) p (sat_cons (step190 p h) (sat_cons (step359 p h) (sat_cons (step361 p h) (sat_cons (step356 p h) (sat_cons (step357 p h) (sat_cons (step81 p h) (sat_cons (step74 p h) (sat_nil p))))))))
def c561 : List Lit := [(1389, true)]
theorem step561 (p : Nat → Bool) (h : Constraints p) : clause p c561 = true :=
  Snake9.LocalRup.prove_clause [c560, c373] c561 (by decide) p (sat_cons (step560 p h) (sat_cons (step373 p h) (sat_nil p)))
def c562 : List Lit := [(1381, false), (1418, true)]
theorem step562 (p : Nat → Bool) (h : Constraints p) : clause p c562 = true :=
  Snake9.LocalRup.prove_clause [c560, c197, c413, c375, c370, c371, c374, c365, c410, c399, c395, c387, c388, c118, c119] c562 (by decide) p (sat_cons (step560 p h) (sat_cons (step197 p h) (sat_cons (step413 p h) (sat_cons (step375 p h) (sat_cons (step370 p h) (sat_cons (step371 p h) (sat_cons (step374 p h) (sat_cons (step365 p h) (sat_cons (step410 p h) (sat_cons (step399 p h) (sat_cons (step395 p h) (sat_cons (step387 p h) (sat_cons (step388 p h) (sat_cons (step118 p h) (sat_cons (step119 p h) (sat_nil p))))))))))))))))
def c563 : List Lit := [(1405, true), (36, false)]
theorem step563 (p : Nat → Bool) (h : Constraints p) : clause p c563 = true :=
  Snake9.LocalRup.prove_clause [c197, c393, c395, c391, c388, c117, c127] c563 (by decide) p (sat_cons (step197 p h) (sat_cons (step393 p h) (sat_cons (step395 p h) (sat_cons (step391 p h) (sat_cons (step388 p h) (sat_cons (step117 p h) (sat_cons (step127 p h) (sat_nil p))))))))
def c564 : List Lit := [(1418, true)]
theorem step564 (p : Nat → Bool) (h : Constraints p) : clause p c564 = true :=
  Snake9.LocalRup.prove_clause [c561, c560, c196, c197, c408, c400, c397, c562, c364, c563, c399, c403, c410, c382, c374, c379, c368, c116, c365, c97, c387, c389, c396, c117, c391, c127] c564 (by decide) p (sat_cons (step561 p h) (sat_cons (step560 p h) (sat_cons (step196 p h) (sat_cons (step197 p h) (sat_cons (step408 p h) (sat_cons (step400 p h) (sat_cons (step397 p h) (sat_cons (step562 p h) (sat_cons (step364 p h) (sat_cons (step563 p h) (sat_cons (step399 p h) (sat_cons (step403 p h) (sat_cons (step410 p h) (sat_cons (step382 p h) (sat_cons (step374 p h) (sat_cons (step379 p h) (sat_cons (step368 p h) (sat_cons (step116 p h) (sat_cons (step365 p h) (sat_cons (step97 p h) (sat_cons (step387 p h) (sat_cons (step389 p h) (sat_cons (step396 p h) (sat_cons (step117 p h) (sat_cons (step391 p h) (sat_cons (step127 p h) (sat_nil p)))))))))))))))))))))))))))
def c565 : List Lit := [(1338, true), (8, false), (45, false)]
theorem step565 (p : Nat → Bool) (h : Constraints p) : clause p c565 = true :=
  Snake9.LocalRup.prove_clause [c555, c310, c304, c554, c14] c565 (by decide) p (sat_cons (step555 p h) (sat_cons (step310 p h) (sat_cons (step304 p h) (sat_cons (step554 p h) (sat_cons (step14 p h) (sat_nil p))))))
def c566 : List Lit := [(1357, true), (13, false), (18, true)]
theorem step566 (p : Nat → Bool) (h : Constraints p) : clause p c566 = true :=
  Snake9.LocalRup.prove_clause [c184, c317, c320, c342, c339, c321, c323, c331, c319, c31, c326, c43, c41] c566 (by decide) p (sat_cons (step184 p h) (sat_cons (step317 p h) (sat_cons (step320 p h) (sat_cons (step342 p h) (sat_cons (step339 p h) (sat_cons (step321 p h) (sat_cons (step323 p h) (sat_cons (step331 p h) (sat_cons (step319 p h) (sat_cons (step31 p h) (sat_cons (step326 p h) (sat_cons (step43 p h) (sat_cons (step41 p h) (sat_nil p))))))))))))))
def c567 : List Lit := [(28, false), (25, true), (1381, true)]
theorem step567 (p : Nat → Bool) (h : Constraints p) : clause p c567 = true :=
  Snake9.LocalRup.prove_clause [c188, c364, c363, c90, c72] c567 (by decide) p (sat_cons (step188 p h) (sat_cons (step364 p h) (sat_cons (step363 p h) (sat_cons (step90 p h) (sat_cons (step72 p h) (sat_nil p))))))
def c568 : List Lit := [(1390, true), (24, false), (33, true)]
theorem step568 (p : Nat → Bool) (h : Constraints p) : clause p c568 = true :=
  Snake9.LocalRup.prove_clause [c560, c189, c356, c377, c374, c360, c362, c368, c358, c78, c366, c76, c62] c568 (by decide) p (sat_cons (step560 p h) (sat_cons (step189 p h) (sat_cons (step356 p h) (sat_cons (step377 p h) (sat_cons (step374 p h) (sat_cons (step360 p h) (sat_cons (step362 p h) (sat_cons (step368 p h) (sat_cons (step358 p h) (sat_cons (step78 p h) (sat_cons (step366 p h) (sat_cons (step76 p h) (sat_cons (step62 p h) (sat_nil p))))))))))))))
def c569 : List Lit := [(99, false), (106, false), (103, false)]
theorem step569 (p : Nat → Bool) (h : Constraints p) : clause p c569 = true :=
  Snake9.LocalRup.prove_clause [c216, c177, c178] c569 (by decide) p (sat_cons (step216 p h) (sat_cons (step177 p h) (sat_cons (step178 p h) (sat_nil p))))
def c570 : List Lit := [(1532, true)]
theorem step570 (p : Nat → Bool) (h : Constraints p) : clause p c570 = true :=
  Snake9.LocalRup.prove_clause [c511, c512, c510, c507, c508, c509, c506, c569] c570 (by decide) p (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step510 p h) (sat_cons (step507 p h) (sat_cons (step508 p h) (sat_cons (step509 p h) (sat_cons (step506 p h) (sat_cons (step569 p h) (sat_nil p)))))))))
def c571 : List Lit := [(1540, true)]
theorem step571 (p : Nat → Bool) (h : Constraints p) : clause p c571 = true :=
  Snake9.LocalRup.prove_clause [c570, c559, c513] c571 (by decide) p (sat_cons (step570 p h) (sat_cons (step559 p h) (sat_cons (step513 p h) (sat_nil p))))
def c572 : List Lit := [(1478, true), (1453, true)]
theorem step572 (p : Nat → Bool) (h : Constraints p) : clause p c572 = true :=
  Snake9.LocalRup.prove_clause [c207, c206, c458, c461, c452, c454, c443, c444, c450, c446, c447, c442, c155, c148, c144, c137, c143, c430] c572 (by decide) p (sat_cons (step207 p h) (sat_cons (step206 p h) (sat_cons (step458 p h) (sat_cons (step461 p h) (sat_cons (step452 p h) (sat_cons (step454 p h) (sat_cons (step443 p h) (sat_cons (step444 p h) (sat_cons (step450 p h) (sat_cons (step446 p h) (sat_cons (step447 p h) (sat_cons (step442 p h) (sat_cons (step155 p h) (sat_cons (step148 p h) (sat_cons (step144 p h) (sat_cons (step137 p h) (sat_cons (step143 p h) (sat_cons (step430 p h) (sat_nil p)))))))))))))))))))
def c573 : List Lit := [(1474, true), (1486, true)]
theorem step573 (p : Nat → Bool) (h : Constraints p) : clause p c573 = true :=
  Snake9.LocalRup.prove_clause [c208, c207, c474, c436, c432, c572, c471, c435, c433, c427, c431, c429, c428, c468, c465, c452, c454, c450, c446, c447, c142, c151, c155, c445, c442, c148, c137] c573 (by decide) p (sat_cons (step208 p h) (sat_cons (step207 p h) (sat_cons (step474 p h) (sat_cons (step436 p h) (sat_cons (step432 p h) (sat_cons (step572 p h) (sat_cons (step471 p h) (sat_cons (step435 p h) (sat_cons (step433 p h) (sat_cons (step427 p h) (sat_cons (step431 p h) (sat_cons (step429 p h) (sat_cons (step428 p h) (sat_cons (step468 p h) (sat_cons (step465 p h) (sat_cons (step452 p h) (sat_cons (step454 p h) (sat_cons (step450 p h) (sat_cons (step446 p h) (sat_cons (step447 p h) (sat_cons (step142 p h) (sat_cons (step151 p h) (sat_cons (step155 p h) (sat_cons (step445 p h) (sat_cons (step442 p h) (sat_cons (step148 p h) (sat_cons (step137 p h) (sat_nil p))))))))))))))))))))))))))))
def c574 : List Lit := [(1486, true)]
theorem step574 (p : Nat → Bool) (h : Constraints p) : clause p c574 = true :=
  Snake9.LocalRup.prove_clause [c206, c207, c468, c474, c459, c436, c457, c432, c572, c471, c435, c431, c433, c428, c429, c427, c573, c462, c443, c444, c442, c141, c144, c148, c137, c447, c448, c455, c155, c450] c574 (by decide) p (sat_cons (step206 p h) (sat_cons (step207 p h) (sat_cons (step468 p h) (sat_cons (step474 p h) (sat_cons (step459 p h) (sat_cons (step436 p h) (sat_cons (step457 p h) (sat_cons (step432 p h) (sat_cons (step572 p h) (sat_cons (step471 p h) (sat_cons (step435 p h) (sat_cons (step431 p h) (sat_cons (step433 p h) (sat_cons (step428 p h) (sat_cons (step429 p h) (sat_cons (step427 p h) (sat_cons (step573 p h) (sat_cons (step462 p h) (sat_cons (step443 p h) (sat_cons (step444 p h) (sat_cons (step442 p h) (sat_cons (step141 p h) (sat_cons (step144 p h) (sat_cons (step148 p h) (sat_cons (step137 p h) (sat_cons (step447 p h) (sat_cons (step448 p h) (sat_cons (step455 p h) (sat_cons (step155 p h) (sat_cons (step450 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c575 : List Lit := [(1333, false), (1340, true)]
theorem step575 (p : Nat → Bool) (h : Constraints p) : clause p c575 = true :=
  Snake9.LocalRup.prove_clause [c179, c557, c303, c306, c312, c296, c554, c552, c1, c10] c575 (by decide) p (sat_cons (step179 p h) (sat_cons (step557 p h) (sat_cons (step303 p h) (sat_cons (step306 p h) (sat_cons (step312 p h) (sat_cons (step296 p h) (sat_cons (step554 p h) (sat_cons (step552 p h) (sat_cons (step1 p h) (sat_cons (step10 p h) (sat_nil p)))))))))))
def c576 : List Lit := [(26, false), (24, false), (88, false), (81, false)]
theorem step576 (p : Nat → Bool) (h : Constraints p) : clause p c576 = true :=
  Snake9.LocalRup.prove_clause [c210, c159, c61, c156] c576 (by decide) p (sat_cons (step210 p h) (sat_cons (step159 p h) (sat_cons (step61 p h) (sat_cons (step156 p h) (sat_nil p)))))
def c577 : List Lit := [(1332, false), (1339, true)]
theorem step577 (p : Nat → Bool) (h : Constraints p) : clause p c577 = true :=
  Snake9.LocalRup.prove_clause [c179, c556, c302, c311, c305, c296, c554, c552, c1, c10] c577 (by decide) p (sat_cons (step179 p h) (sat_cons (step556 p h) (sat_cons (step302 p h) (sat_cons (step311 p h) (sat_cons (step305 p h) (sat_cons (step296 p h) (sat_cons (step554 p h) (sat_cons (step552 p h) (sat_cons (step1 p h) (sat_cons (step10 p h) (sat_nil p)))))))))))
def c578 : List Lit := [(1479, true), (75, true), (79, false), (78, false)]
theorem step578 (p : Nat → Bool) (h : Constraints p) : clause p c578 = true :=
  Snake9.LocalRup.prove_clause [c447, c454, c459, c462, c457, c444, c448, c155] c578 (by decide) p (sat_cons (step447 p h) (sat_cons (step454 p h) (sat_cons (step459 p h) (sat_cons (step462 p h) (sat_cons (step457 p h) (sat_cons (step444 p h) (sat_cons (step448 p h) (sat_cons (step155 p h) (sat_nil p)))))))))
def c579 : List Lit := [(1508, true), (81, false)]
theorem step579 (p : Nat → Bool) (h : Constraints p) : clause p c579 = true :=
  Snake9.LocalRup.prove_clause [c215, c492, c494, c489, c486, c176, c175] c579 (by decide) p (sat_cons (step215 p h) (sat_cons (step492 p h) (sat_cons (step494 p h) (sat_cons (step489 p h) (sat_cons (step486 p h) (sat_cons (step176 p h) (sat_cons (step175 p h) (sat_nil p))))))))
def c580 : List Lit := [(1558, true), (1479, false), (81, false)]
theorem step580 (p : Nat → Bool) (h : Constraints p) : clause p c580 = true :=
  Snake9.LocalRup.prove_clause [c574, c570, c558, c200, c579, c499, c514, c518, c515, c500, c521, c472, c437, c425, c129, c172, c173, c486, c489, c495] c580 (by decide) p (sat_cons (step574 p h) (sat_cons (step570 p h) (sat_cons (step558 p h) (sat_cons (step200 p h) (sat_cons (step579 p h) (sat_cons (step499 p h) (sat_cons (step514 p h) (sat_cons (step518 p h) (sat_cons (step515 p h) (sat_cons (step500 p h) (sat_cons (step521 p h) (sat_cons (step472 p h) (sat_cons (step437 p h) (sat_cons (step425 p h) (sat_cons (step129 p h) (sat_cons (step172 p h) (sat_cons (step173 p h) (sat_cons (step486 p h) (sat_cons (step489 p h) (sat_cons (step495 p h) (sat_nil p)))))))))))))))))))))
def c581 : List Lit := [(1339, true), (4, false), (8, false), (69, false), (64, false)]
theorem step581 (p : Nat → Bool) (h : Constraints p) : clause p c581 = true :=
  Snake9.LocalRup.prove_clause [c314, c577, c300, c6, c552, c296, c298, c311, c15, c304] c581 (by decide) p (sat_cons (step314 p h) (sat_cons (step577 p h) (sat_cons (step300 p h) (sat_cons (step6 p h) (sat_cons (step552 p h) (sat_cons (step296 p h) (sat_cons (step298 p h) (sat_cons (step311 p h) (sat_cons (step15 p h) (sat_cons (step304 p h) (sat_nil p)))))))))))
def c582 : List Lit := [(69, false), (181, true), (64, false), (66, false), (67, false), (1479, true)]
theorem step582 (p : Nat → Bool) (h : Constraints p) : clause p c582 = true :=
  Snake9.LocalRup.prove_clause [c206, c205, c207, c459, c141, c144, c140, c147, c148, c137, c447, c578, c455, c450] c582 (by decide) p (sat_cons (step206 p h) (sat_cons (step205 p h) (sat_cons (step207 p h) (sat_cons (step459 p h) (sat_cons (step141 p h) (sat_cons (step144 p h) (sat_cons (step140 p h) (sat_cons (step147 p h) (sat_cons (step148 p h) (sat_cons (step137 p h) (sat_cons (step447 p h) (sat_cons (step578 p h) (sat_cons (step455 p h) (sat_cons (step450 p h) (sat_nil p)))))))))))))))
def c583 : List Lit := [(57, true), (1487, true), (1479, true)]
theorem step583 (p : Nat → Bool) (h : Constraints p) : clause p c583 = true :=
  Snake9.LocalRup.prove_clause [c201, c545, c207, c477, c465, c425, c439, c432, c572, c475, c440, c438, c426, c431, c433, c424, c428, c429, c427, c131, c128, c258, c262, c263, c272, c270, c265, c264, c582, c444, c445, c462, c442, c454, c148, c447, c137] c583 (by decide) p (sat_cons (step201 p h) (sat_cons (step545 p h) (sat_cons (step207 p h) (sat_cons (step477 p h) (sat_cons (step465 p h) (sat_cons (step425 p h) (sat_cons (step439 p h) (sat_cons (step432 p h) (sat_cons (step572 p h) (sat_cons (step475 p h) (sat_cons (step440 p h) (sat_cons (step438 p h) (sat_cons (step426 p h) (sat_cons (step431 p h) (sat_cons (step433 p h) (sat_cons (step424 p h) (sat_cons (step428 p h) (sat_cons (step429 p h) (sat_cons (step427 p h) (sat_cons (step131 p h) (sat_cons (step128 p h) (sat_cons (step258 p h) (sat_cons (step262 p h) (sat_cons (step263 p h) (sat_cons (step272 p h) (sat_cons (step270 p h) (sat_cons (step265 p h) (sat_cons (step264 p h) (sat_cons (step582 p h) (sat_cons (step444 p h) (sat_cons (step445 p h) (sat_cons (step462 p h) (sat_cons (step442 p h) (sat_cons (step454 p h) (sat_cons (step148 p h) (sat_cons (step447 p h) (sat_cons (step137 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c584 : List Lit := [(57, false), (97, false), (81, false)]
theorem step584 (p : Nat → Bool) (h : Constraints p) : clause p c584 = true :=
  Snake9.LocalRup.prove_clause [c200, c129, c173] c584 (by decide) p (sat_cons (step200 p h) (sat_cons (step129 p h) (sat_cons (step173 p h) (sat_nil p))))
def c585 : List Lit := [(339, true), (57, true)]
theorem step585 (p : Nat → Bool) (h : Constraints p) : clause p c585 = true :=
  Snake9.LocalRup.prove_clause [c540, c201, c202, c261, c262, c260, c257, c258, c259, c256, c128, c130, c131, c133, c132] c585 (by decide) p (sat_cons (step540 p h) (sat_cons (step201 p h) (sat_cons (step202 p h) (sat_cons (step261 p h) (sat_cons (step262 p h) (sat_cons (step260 p h) (sat_cons (step257 p h) (sat_cons (step258 p h) (sat_cons (step259 p h) (sat_cons (step256 p h) (sat_cons (step128 p h) (sat_cons (step130 p h) (sat_cons (step131 p h) (sat_cons (step133 p h) (sat_cons (step132 p h) (sat_nil p))))))))))))))))
def c586 : List Lit := [(1, false), (114, true)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true :=
  Snake9.LocalRup.prove_clause [c179, c541, c1, c2, c529, c4] c586 (by decide) p (sat_cons (step179 p h) (sat_cons (step541 p h) (sat_cons (step1 p h) (sat_cons (step2 p h) (sat_cons (step529 p h) (sat_cons (step4 p h) (sat_nil p)))))))
def c587 : List Lit := [(71, false), (75, false), (66, false)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true :=
  Snake9.LocalRup.prove_clause [c207, c148, c137] c587 (by decide) p (sat_cons (step207 p h) (sat_cons (step148 p h) (sat_cons (step137 p h) (sat_nil p))))
def c588 : List Lit := [(1356, true)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true :=
  Snake9.LocalRup.prove_clause [c184, c335, c338, c331, c320, c322, c326, c317, c318, c55, c47, c40] c588 (by decide) p (sat_cons (step184 p h) (sat_cons (step335 p h) (sat_cons (step338 p h) (sat_cons (step331 p h) (sat_cons (step320 p h) (sat_cons (step322 p h) (sat_cons (step326 p h) (sat_cons (step317 p h) (sat_cons (step318 p h) (sat_cons (step55 p h) (sat_cons (step47 p h) (sat_cons (step40 p h) (sat_nil p)))))))))))))
def c589 : List Lit := [(6, false), (1332, true), (64, false)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true :=
  Snake9.LocalRup.prove_clause [c182, c300, c299, c35, c6, c33] c589 (by decide) p (sat_cons (step182 p h) (sat_cons (step300 p h) (sat_cons (step299 p h) (sat_cons (step35 p h) (sat_cons (step6 p h) (sat_cons (step33 p h) (sat_nil p)))))))
def c590 : List Lit := [(1508, true), (57, false)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true :=
  Snake9.LocalRup.prove_clause [c200, c129, c492, c494, c489, c486, c174] c590 (by decide) p (sat_cons (step200 p h) (sat_cons (step129 p h) (sat_cons (step492 p h) (sat_cons (step494 p h) (sat_cons (step489 p h) (sat_cons (step486 p h) (sat_cons (step174 p h) (sat_nil p))))))))
def c591 : List Lit := [(1420, true), (1384, false), (1398, false)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true :=
  Snake9.LocalRup.prove_clause [c560, c369, c375, c402, c417, c415, c376, c403, c372, c563, c364] c591 (by decide) p (sat_cons (step560 p h) (sat_cons (step369 p h) (sat_cons (step375 p h) (sat_cons (step402 p h) (sat_cons (step417 p h) (sat_cons (step415 p h) (sat_cons (step376 p h) (sat_cons (step403 p h) (sat_cons (step372 p h) (sat_cons (step563 p h) (sat_cons (step364 p h) (sat_nil p))))))))))))
def c592 : List Lit := [(1558, true), (1470, false), (1467, false), (1541, false)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true :=
  Snake9.LocalRup.prove_clause [c454, c462, c580, c521, c449, c469, c455, c463] c592 (by decide) p (sat_cons (step454 p h) (sat_cons (step462 p h) (sat_cons (step580 p h) (sat_cons (step521 p h) (sat_cons (step449 p h) (sat_cons (step469 p h) (sat_cons (step455 p h) (sat_cons (step463 p h) (sat_nil p)))))))))
def c593 : List Lit := [(78, false), (79, true), (13, false)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true :=
  Snake9.LocalRup.prove_clause [c209, c153, c152, c534] c593 (by decide) p (sat_cons (step209 p h) (sat_cons (step153 p h) (sat_cons (step152 p h) (sat_cons (step534 p h) (sat_nil p)))))
def c594 : List Lit := [(1419, true), (1398, false), (1383, false)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true :=
  Snake9.LocalRup.prove_clause [c560, c402, c368, c374, c414, c411, c375, c403, c371, c563, c364] c594 (by decide) p (sat_cons (step560 p h) (sat_cons (step402 p h) (sat_cons (step368 p h) (sat_cons (step374 p h) (sat_cons (step414 p h) (sat_cons (step411 p h) (sat_cons (step375 p h) (sat_cons (step403 p h) (sat_cons (step371 p h) (sat_cons (step563 p h) (sat_cons (step364 p h) (sat_nil p))))))))))))
def c595 : List Lit := [(1384, false), (1419, true)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true :=
  Snake9.LocalRup.prove_clause [c560, c416, c376, c369, c372, c375, c364, c414, c563, c399] c595 (by decide) p (sat_cons (step560 p h) (sat_cons (step416 p h) (sat_cons (step376 p h) (sat_cons (step369 p h) (sat_cons (step372 p h) (sat_cons (step375 p h) (sat_cons (step364 p h) (sat_cons (step414 p h) (sat_cons (step563 p h) (sat_cons (step399 p h) (sat_nil p)))))))))))
def c596 : List Lit := [(40, true), (1419, true)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true :=
  Snake9.LocalRup.prove_clause [c560, c196, c198, c595, c366, c367, c368, c594, c374, c382, c384, c411, c379, c380, c400, c116, c97, c387, c396, c390, c391, c126, c111, c121] c596 (by decide) p (sat_cons (step560 p h) (sat_cons (step196 p h) (sat_cons (step198 p h) (sat_cons (step595 p h) (sat_cons (step366 p h) (sat_cons (step367 p h) (sat_cons (step368 p h) (sat_cons (step594 p h) (sat_cons (step374 p h) (sat_cons (step382 p h) (sat_cons (step384 p h) (sat_cons (step411 p h) (sat_cons (step379 p h) (sat_cons (step380 p h) (sat_cons (step400 p h) (sat_cons (step116 p h) (sat_cons (step97 p h) (sat_cons (step387 p h) (sat_cons (step396 p h) (sat_cons (step390 p h) (sat_cons (step391 p h) (sat_cons (step126 p h) (sat_cons (step111 p h) (sat_cons (step121 p h) (sat_nil p)))))))))))))))))))))))))
def c597 : List Lit := [(1403, true), (54, false), (45, false)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true :=
  Snake9.LocalRup.prove_clause [c390, c391, c126] c597 (by decide) p (sat_cons (step390 p h) (sat_cons (step391 p h) (sat_cons (step126 p h) (sat_nil p))))
def c598 : List Lit := [(90, false), (36, false), (37, false), (55, false)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true :=
  Snake9.LocalRup.prove_clause [c191, c84, c85, c87] c598 (by decide) p (sat_cons (step191 p h) (sat_cons (step84 p h) (sat_cons (step85 p h) (sat_cons (step87 p h) (sat_nil p)))))
def c599 : List Lit := [(49, false), (36, false), (1406, true), (42, false)]
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true :=
  Snake9.LocalRup.prove_clause [c197, c117, c118, c119, c127, c387, c391, c396] c599 (by decide) p (sat_cons (step197 p h) (sat_cons (step117 p h) (sat_cons (step118 p h) (sat_cons (step119 p h) (sat_cons (step127 p h) (sat_cons (step387 p h) (sat_cons (step391 p h) (sat_cons (step396 p h) (sat_nil p)))))))))
def c600 : List Lit := [(45, false), (1403, true), (40, false)]
theorem step600 (p : Nat → Bool) (h : Constraints p) : clause p c600 = true :=
  Snake9.LocalRup.prove_clause [c195, c391, c110, c597, c112] c600 (by decide) p (sat_cons (step195 p h) (sat_cons (step391 p h) (sat_cons (step110 p h) (sat_cons (step597 p h) (sat_cons (step112 p h) (sat_nil p))))))
def c601 : List Lit := [(36, false), (1406, true), (42, false), (1419, true)]
theorem step601 (p : Nat → Bool) (h : Constraints p) : clause p c601 = true :=
  Snake9.LocalRup.prove_clause [c561, c196, c397, c596, c409, c563, c406, c383, c599, c388, c389, c396, c600, c381, c116, c97] c601 (by decide) p (sat_cons (step561 p h) (sat_cons (step196 p h) (sat_cons (step397 p h) (sat_cons (step596 p h) (sat_cons (step409 p h) (sat_cons (step563 p h) (sat_cons (step406 p h) (sat_cons (step383 p h) (sat_cons (step599 p h) (sat_cons (step388 p h) (sat_cons (step389 p h) (sat_cons (step396 p h) (sat_cons (step600 p h) (sat_cons (step381 p h) (sat_cons (step116 p h) (sat_cons (step97 p h) (sat_nil p)))))))))))))))))
def c602 : List Lit := [(389, false), (1357, false), (85, true), (82, true), (8, false), (45, false)]
theorem step602 (p : Nat → Bool) (h : Constraints p) : clause p c602 = true :=
  Snake9.LocalRup.prove_clause [c550, c213, c542, c292, c570, c574, c528, c564, c275, c277, c278, c273, c280, c168, c282, c164, c284, c287, c481, c290, c271, c485, c253, c263, c231, c585, c224, c590, c219, c505, c218, c516, c217, c519, c586, c525, c554, c420, c351, c314, c311, c298, c304, c552, c18] c602 (by decide) p (sat_cons (step550 p h) (sat_cons (step213 p h) (sat_cons (step542 p h) (sat_cons (step292 p h) (sat_cons (step570 p h) (sat_cons (step574 p h) (sat_cons (step528 p h) (sat_cons (step564 p h) (sat_cons (step275 p h) (sat_cons (step277 p h) (sat_cons (step278 p h) (sat_cons (step273 p h) (sat_cons (step280 p h) (sat_cons (step168 p h) (sat_cons (step282 p h) (sat_cons (step164 p h) (sat_cons (step284 p h) (sat_cons (step287 p h) (sat_cons (step481 p h) (sat_cons (step290 p h) (sat_cons (step271 p h) (sat_cons (step485 p h) (sat_cons (step253 p h) (sat_cons (step263 p h) (sat_cons (step231 p h) (sat_cons (step585 p h) (sat_cons (step224 p h) (sat_cons (step590 p h) (sat_cons (step219 p h) (sat_cons (step505 p h) (sat_cons (step218 p h) (sat_cons (step516 p h) (sat_cons (step217 p h) (sat_cons (step519 p h) (sat_cons (step586 p h) (sat_cons (step525 p h) (sat_cons (step554 p h) (sat_cons (step420 p h) (sat_cons (step351 p h) (sat_cons (step314 p h) (sat_cons (step311 p h) (sat_cons (step298 p h) (sat_cons (step304 p h) (sat_cons (step552 p h) (sat_cons (step18 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c603 : List Lit := [(1509, true), (57, false), (88, true)]
theorem step603 (p : Nat → Bool) (h : Constraints p) : clause p c603 = true :=
  Snake9.LocalRup.prove_clause [c200, c129, c487, c496, c495, c488, c489, c174] c603 (by decide) p (sat_cons (step200 p h) (sat_cons (step129 p h) (sat_cons (step487 p h) (sat_cons (step496 p h) (sat_cons (step495 p h) (sat_cons (step488 p h) (sat_cons (step489 p h) (sat_cons (step174 p h) (sat_nil p)))))))))
end B112E148
