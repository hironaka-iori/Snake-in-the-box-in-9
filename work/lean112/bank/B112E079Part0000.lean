import B112E079Inputs
namespace B112E079
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c548 : List Lit := [(96, true)]
theorem step548 (p : Nat → Bool) (h : Constraints p) : clause p c548 = true :=
  Snake9.LocalRup.prove_clause [c144, c143] c548 (by decide) p (sat_cons (step144 p h) (sat_cons (step143 p h) (sat_nil p)))
def c549 : List Lit := [(206, true), (102, true)]
theorem step549 (p : Nat → Bool) (h : Constraints p) : clause p c549 = true :=
  Snake9.LocalRup.prove_clause [c548, c145] c549 (by decide) p (sat_cons (step548 p h) (sat_cons (step145 p h) (sat_nil p)))
def c550 : List Lit := [(39, false)]
theorem step550 (p : Nat → Bool) (h : Constraints p) : clause p c550 = true :=
  Snake9.LocalRup.prove_clause [c184, c79] c550 (by decide) p (sat_cons (step184 p h) (sat_cons (step79 p h) (sat_nil p)))
def c551 : List Lit := [(43, false)]
theorem step551 (p : Nat → Bool) (h : Constraints p) : clause p c551 = true :=
  Snake9.LocalRup.prove_clause [c186, c86] c551 (by decide) p (sat_cons (step186 p h) (sat_cons (step86 p h) (sat_nil p)))
def c552 : List Lit := [(434, false)]
theorem step552 (p : Nat → Bool) (h : Constraints p) : clause p c552 = true :=
  Snake9.LocalRup.prove_clause [c344, c341] c552 (by decide) p (sat_cons (step344 p h) (sat_cons (step341 p h) (sat_nil p)))
def c553 : List Lit := [(326, false)]
theorem step553 (p : Nat → Bool) (h : Constraints p) : clause p c553 = true :=
  Snake9.LocalRup.prove_clause [c344, c343] c553 (by decide) p (sat_cons (step344 p h) (sat_cons (step343 p h) (sat_nil p)))
def c554 : List Lit := [(432, false)]
theorem step554 (p : Nat → Bool) (h : Constraints p) : clause p c554 = true :=
  Snake9.LocalRup.prove_clause [c552, c338] c554 (by decide) p (sat_cons (step552 p h) (sat_cons (step338 p h) (sat_nil p)))
def c555 : List Lit := [(378, false)]
theorem step555 (p : Nat → Bool) (h : Constraints p) : clause p c555 = true :=
  Snake9.LocalRup.prove_clause [c552, c340] c555 (by decide) p (sat_cons (step552 p h) (sat_cons (step340 p h) (sat_nil p)))
def c556 : List Lit := [(324, false)]
theorem step556 (p : Nat → Bool) (h : Constraints p) : clause p c556 = true :=
  Snake9.LocalRup.prove_clause [c553, c272] c556 (by decide) p (sat_cons (step553 p h) (sat_cons (step272 p h) (sat_nil p)))
def c557 : List Lit := [(272, false)]
theorem step557 (p : Nat → Bool) (h : Constraints p) : clause p c557 = true :=
  Snake9.LocalRup.prove_clause [c553, c275] c557 (by decide) p (sat_cons (step553 p h) (sat_cons (step275 p h) (sat_nil p)))
def c558 : List Lit := [(430, false)]
theorem step558 (p : Nat → Bool) (h : Constraints p) : clause p c558 = true :=
  Snake9.LocalRup.prove_clause [c554, c333] c558 (by decide) p (sat_cons (step554 p h) (sat_cons (step333 p h) (sat_nil p)))
def c559 : List Lit := [(404, false)]
theorem step559 (p : Nat → Bool) (h : Constraints p) : clause p c559 = true :=
  Snake9.LocalRup.prove_clause [c554, c336] c559 (by decide) p (sat_cons (step554 p h) (sat_cons (step336 p h) (sat_nil p)))
def c560 : List Lit := [(376, false)]
theorem step560 (p : Nat → Bool) (h : Constraints p) : clause p c560 = true :=
  Snake9.LocalRup.prove_clause [c555, c289] c560 (by decide) p (sat_cons (step555 p h) (sat_cons (step289 p h) (sat_nil p)))
def c561 : List Lit := [(350, false)]
theorem step561 (p : Nat → Bool) (h : Constraints p) : clause p c561 = true :=
  Snake9.LocalRup.prove_clause [c555, c290] c561 (by decide) p (sat_cons (step555 p h) (sat_cons (step290 p h) (sat_nil p)))
def c562 : List Lit := [(322, false)]
theorem step562 (p : Nat → Bool) (h : Constraints p) : clause p c562 = true :=
  Snake9.LocalRup.prove_clause [c556, c267] c562 (by decide) p (sat_cons (step556 p h) (sat_cons (step267 p h) (sat_nil p)))
def c563 : List Lit := [(296, false)]
theorem step563 (p : Nat → Bool) (h : Constraints p) : clause p c563 = true :=
  Snake9.LocalRup.prove_clause [c556, c270] c563 (by decide) p (sat_cons (step556 p h) (sat_cons (step270 p h) (sat_nil p)))
def c564 : List Lit := [(270, false)]
theorem step564 (p : Nat → Bool) (h : Constraints p) : clause p c564 = true :=
  Snake9.LocalRup.prove_clause [c557, c229] c564 (by decide) p (sat_cons (step557 p h) (sat_cons (step229 p h) (sat_nil p)))
def c565 : List Lit := [(428, false)]
theorem step565 (p : Nat → Bool) (h : Constraints p) : clause p c565 = true :=
  Snake9.LocalRup.prove_clause [c558, c329] c565 (by decide) p (sat_cons (step558 p h) (sat_cons (step329 p h) (sat_nil p)))
def c566 : List Lit := [(416, false)]
theorem step566 (p : Nat → Bool) (h : Constraints p) : clause p c566 = true :=
  Snake9.LocalRup.prove_clause [c558, c331] c566 (by decide) p (sat_cons (step558 p h) (sat_cons (step331 p h) (sat_nil p)))
def c567 : List Lit := [(402, false)]
theorem step567 (p : Nat → Bool) (h : Constraints p) : clause p c567 = true :=
  Snake9.LocalRup.prove_clause [c559, c309] c567 (by decide) p (sat_cons (step559 p h) (sat_cons (step309 p h) (sat_nil p)))
def c568 : List Lit := [(362, false)]
theorem step568 (p : Nat → Bool) (h : Constraints p) : clause p c568 = true :=
  Snake9.LocalRup.prove_clause [c560, c287] c568 (by decide) p (sat_cons (step560 p h) (sat_cons (step287 p h) (sat_nil p)))
def c569 : List Lit := [(348, false)]
theorem step569 (p : Nat → Bool) (h : Constraints p) : clause p c569 = true :=
  Snake9.LocalRup.prove_clause [c561, c279] c569 (by decide) p (sat_cons (step561 p h) (sat_cons (step279 p h) (sat_nil p)))
def c570 : List Lit := [(320, false)]
theorem step570 (p : Nat → Bool) (h : Constraints p) : clause p c570 = true :=
  Snake9.LocalRup.prove_clause [c562, c264] c570 (by decide) p (sat_cons (step562 p h) (sat_cons (step264 p h) (sat_nil p)))
def c571 : List Lit := [(294, false)]
theorem step571 (p : Nat → Bool) (h : Constraints p) : clause p c571 = true :=
  Snake9.LocalRup.prove_clause [c563, c248] c571 (by decide) p (sat_cons (step563 p h) (sat_cons (step248 p h) (sat_nil p)))
def c572 : List Lit := [(282, false)]
theorem step572 (p : Nat → Bool) (h : Constraints p) : clause p c572 = true :=
  Snake9.LocalRup.prove_clause [c563, c251] c572 (by decide) p (sat_cons (step563 p h) (sat_cons (step251 p h) (sat_nil p)))
def c573 : List Lit := [(268, false)]
theorem step573 (p : Nat → Bool) (h : Constraints p) : clause p c573 = true :=
  Snake9.LocalRup.prove_clause [c564, c225] c573 (by decide) p (sat_cons (step564 p h) (sat_cons (step225 p h) (sat_nil p)))
def c574 : List Lit := [(360, false)]
theorem step574 (p : Nat → Bool) (h : Constraints p) : clause p c574 = true :=
  Snake9.LocalRup.prove_clause [c568, c282] c574 (by decide) p (sat_cons (step568 p h) (sat_cons (step282 p h) (sat_nil p)))
def c575 : List Lit := [(340, false)]
theorem step575 (p : Nat → Bool) (h : Constraints p) : clause p c575 = true :=
  Snake9.LocalRup.prove_clause [c569, c278] c575 (by decide) p (sat_cons (step569 p h) (sat_cons (step278 p h) (sat_nil p)))
def c576 : List Lit := [(318, false)]
theorem step576 (p : Nat → Bool) (h : Constraints p) : clause p c576 = true :=
  Snake9.LocalRup.prove_clause [c570, c263] c576 (by decide) p (sat_cons (step570 p h) (sat_cons (step263 p h) (sat_nil p)))
def c577 : List Lit := [(276, false)]
theorem step577 (p : Nat → Bool) (h : Constraints p) : clause p c577 = true :=
  Snake9.LocalRup.prove_clause [c572, c237] c577 (by decide) p (sat_cons (step572 p h) (sat_cons (step237 p h) (sat_nil p)))
def c578 : List Lit := [(358, false)]
theorem step578 (p : Nat → Bool) (h : Constraints p) : clause p c578 = true :=
  Snake9.LocalRup.prove_clause [c574, c281] c578 (by decide) p (sat_cons (step574 p h) (sat_cons (step281 p h) (sat_nil p)))
def c579 : List Lit := [(1362, true)]
theorem step579 (p : Nat → Bool) (h : Constraints p) : clause p c579 = true :=
  Snake9.LocalRup.prove_clause [c377, c380, c371, c373, c363, c368, c369, c366, c360, c361, c42, c44, c26, c48] c579 (by decide) p (sat_cons (step377 p h) (sat_cons (step380 p h) (sat_cons (step371 p h) (sat_cons (step373 p h) (sat_cons (step363 p h) (sat_cons (step368 p h) (sat_cons (step369 p h) (sat_cons (step366 p h) (sat_cons (step360 p h) (sat_cons (step361 p h) (sat_cons (step42 p h) (sat_cons (step44 p h) (sat_cons (step26 p h) (sat_cons (step48 p h) (sat_nil p)))))))))))))))
def c580 : List Lit := [(1343, true)]
theorem step580 (p : Nat → Bool) (h : Constraints p) : clause p c580 = true :=
  Snake9.LocalRup.prove_clause [c356, c358, c352, c354, c348, c349, c350, c8, c7, c9] c580 (by decide) p (sat_cons (step356 p h) (sat_cons (step358 p h) (sat_cons (step352 p h) (sat_cons (step354 p h) (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step350 p h) (sat_cons (step8 p h) (sat_cons (step7 p h) (sat_cons (step9 p h) (sat_nil p)))))))))))
def c581 : List Lit := [(1370, true)]
theorem step581 (p : Nat → Bool) (h : Constraints p) : clause p c581 = true :=
  Snake9.LocalRup.prove_clause [c580, c579, c385] c581 (by decide) p (sat_cons (step580 p h) (sat_cons (step579 p h) (sat_cons (step385 p h) (sat_nil p))))
def c582 : List Lit := [(81, false), (1491, true)]
theorem step582 (p : Nat → Bool) (h : Constraints p) : clause p c582 = true :=
  Snake9.LocalRup.prove_clause [c559, c485, c483, c482, c487, c113, c127, c122, c132, c291, c300, c292, c306, c297, c311] c582 (by decide) p (sat_cons (step559 p h) (sat_cons (step485 p h) (sat_cons (step483 p h) (sat_cons (step482 p h) (sat_cons (step487 p h) (sat_cons (step113 p h) (sat_cons (step127 p h) (sat_cons (step122 p h) (sat_cons (step132 p h) (sat_cons (step291 p h) (sat_cons (step300 p h) (sat_cons (step292 p h) (sat_cons (step306 p h) (sat_cons (step297 p h) (sat_cons (step311 p h) (sat_nil p))))))))))))))))
def c583 : List Lit := [(1466, false), (1478, true)]
theorem step583 (p : Nat → Bool) (h : Constraints p) : clause p c583 = true :=
  Snake9.LocalRup.prove_clause [c473, c468, c471, c475, c459, c460, c452, c458, c450, c451, c448, c100, c104, c101] c583 (by decide) p (sat_cons (step473 p h) (sat_cons (step468 p h) (sat_cons (step471 p h) (sat_cons (step475 p h) (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step452 p h) (sat_cons (step458 p h) (sat_cons (step450 p h) (sat_cons (step451 p h) (sat_cons (step448 p h) (sat_cons (step100 p h) (sat_cons (step104 p h) (sat_cons (step101 p h) (sat_nil p)))))))))))))))
def c584 : List Lit := [(1451, true), (1462, true)]
theorem step584 (p : Nat → Bool) (h : Constraints p) : clause p c584 = true :=
  Snake9.LocalRup.prove_clause [c575, c462, c461, c452, c453, c450, c445, c449, c442, c443, c102, c97, c98, c99, c277, c276] c584 (by decide) p (sat_cons (step575 p h) (sat_cons (step462 p h) (sat_cons (step461 p h) (sat_cons (step452 p h) (sat_cons (step453 p h) (sat_cons (step450 p h) (sat_cons (step445 p h) (sat_cons (step449 p h) (sat_cons (step442 p h) (sat_cons (step443 p h) (sat_cons (step102 p h) (sat_cons (step97 p h) (sat_cons (step98 p h) (sat_cons (step99 p h) (sat_cons (step277 p h) (sat_cons (step276 p h) (sat_nil p)))))))))))))))))
def c585 : List Lit := [(1448, true), (1459, true)]
theorem step585 (p : Nat → Bool) (h : Constraints p) : clause p c585 = true :=
  Snake9.LocalRup.prove_clause [c459, c458, c460, c450, c451, c448, c100, c104, c101] c585 (by decide) p (sat_cons (step459 p h) (sat_cons (step458 p h) (sat_cons (step460 p h) (sat_cons (step450 p h) (sat_cons (step451 p h) (sat_cons (step448 p h) (sat_cons (step100 p h) (sat_cons (step104 p h) (sat_cons (step101 p h) (sat_nil p))))))))))
def c586 : List Lit := [(1478, true)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true :=
  Snake9.LocalRup.prove_clause [c578, c575, c477, c583, c466, c461, c462, c584, c475, c470, c459, c460, c457, c458, c585, c454, c445, c447, c442, c443, c103, c97, c106, c107, c98, c280, c277, c105, c276, c108, c99] c586 (by decide) p (sat_cons (step578 p h) (sat_cons (step575 p h) (sat_cons (step477 p h) (sat_cons (step583 p h) (sat_cons (step466 p h) (sat_cons (step461 p h) (sat_cons (step462 p h) (sat_cons (step584 p h) (sat_cons (step475 p h) (sat_cons (step470 p h) (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step457 p h) (sat_cons (step458 p h) (sat_cons (step585 p h) (sat_cons (step454 p h) (sat_cons (step445 p h) (sat_cons (step447 p h) (sat_cons (step442 p h) (sat_cons (step443 p h) (sat_cons (step103 p h) (sat_cons (step97 p h) (sat_cons (step106 p h) (sat_cons (step107 p h) (sat_cons (step98 p h) (sat_cons (step280 p h) (sat_cons (step277 p h) (sat_cons (step105 p h) (sat_cons (step276 p h) (sat_cons (step108 p h) (sat_cons (step99 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c587 : List Lit := [(1388, true), (105, true), (150, true)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true :=
  Snake9.LocalRup.prove_clause [c402, c404, c399, c400, c80, c69] c587 (by decide) p (sat_cons (step402 p h) (sat_cons (step404 p h) (sat_cons (step399 p h) (sat_cons (step400 p h) (sat_cons (step80 p h) (sat_cons (step69 p h) (sat_nil p)))))))
def c588 : List Lit := [(48, false), (53, false), (51, false)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true :=
  Snake9.LocalRup.prove_clause [c576, c93, c94, c92, c261, c260, c262] c588 (by decide) p (sat_cons (step576 p h) (sat_cons (step93 p h) (sat_cons (step94 p h) (sat_cons (step92 p h) (sat_cons (step261 p h) (sat_cons (step260 p h) (sat_cons (step262 p h) (sat_nil p))))))))
def c589 : List Lit := [(1406, true)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true :=
  Snake9.LocalRup.prove_clause [c420, c421, c419, c417, c418, c588] c589 (by decide) p (sat_cons (step420 p h) (sat_cons (step421 p h) (sat_cons (step419 p h) (sat_cons (step417 p h) (sat_cons (step418 p h) (sat_cons (step588 p h) (sat_nil p)))))))
def c590 : List Lit := [(1410, true)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true :=
  Snake9.LocalRup.prove_clause [c589, c422] c590 (by decide) p (sat_cons (step589 p h) (sat_cons (step422 p h) (sat_nil p)))
def c591 : List Lit := [(1505, true), (101, false), (98, false)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true :=
  Snake9.LocalRup.prove_clause [c500, c501, c151] c591 (by decide) p (sat_cons (step500 p h) (sat_cons (step501 p h) (sat_cons (step151 p h) (sat_nil p))))
def c592 : List Lit := [(1491, true), (105, false), (403, true)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true :=
  Snake9.LocalRup.prove_clause [c310, c297, c292, c291, c308, c306, c300, c485, c487, c482, c483, c122, c132, c125] c592 (by decide) p (sat_cons (step310 p h) (sat_cons (step297 p h) (sat_cons (step292 p h) (sat_cons (step291 p h) (sat_cons (step308 p h) (sat_cons (step306 p h) (sat_cons (step300 p h) (sat_cons (step485 p h) (sat_cons (step487 p h) (sat_cons (step482 p h) (sat_cons (step483 p h) (sat_cons (step122 p h) (sat_cons (step132 p h) (sat_cons (step125 p h) (sat_nil p)))))))))))))))
def c593 : List Lit := [(1507, false), (1510, false), (1528, true), (19, false), (40, false), (105, false), (403, true)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true :=
  Snake9.LocalRup.prove_clause [c190, c514, c592, c495, c526, c310, c297, c292, c291, c308, c306, c300, c517, c529, c498, c486, c518, c515, c509, c159, c483, c484, c488, c132, c122, c129, c114] c593 (by decide) p (sat_cons (step190 p h) (sat_cons (step514 p h) (sat_cons (step592 p h) (sat_cons (step495 p h) (sat_cons (step526 p h) (sat_cons (step310 p h) (sat_cons (step297 p h) (sat_cons (step292 p h) (sat_cons (step291 p h) (sat_cons (step308 p h) (sat_cons (step306 p h) (sat_cons (step300 p h) (sat_cons (step517 p h) (sat_cons (step529 p h) (sat_cons (step498 p h) (sat_cons (step486 p h) (sat_cons (step518 p h) (sat_cons (step515 p h) (sat_cons (step509 p h) (sat_cons (step159 p h) (sat_cons (step483 p h) (sat_cons (step484 p h) (sat_cons (step488 p h) (sat_cons (step132 p h) (sat_cons (step122 p h) (sat_cons (step129 p h) (sat_cons (step114 p h) (sat_nil p))))))))))))))))))))))))))))
def c594 : List Lit := [(1507, true), (208, true)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true :=
  Snake9.LocalRup.prove_clause [c503, c505, c591, c147] c594 (by decide) p (sat_cons (step503 p h) (sat_cons (step505 p h) (sat_cons (step591 p h) (sat_cons (step147 p h) (sat_nil p)))))
def c595 : List Lit := [(106, false), (40, false), (1521, true), (105, false), (431, true)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true :=
  Snake9.LocalRup.prove_clause [c194, c196, c332, c328, c326, c321, c334, c308, c305, c303, c302, c549, c153, c156, c330, c317, c313, c312, c316, c315, c314, c154, c160, c162, c171, c511, c148, c149, c513, c500, c520, c506] c595 (by decide) p (sat_cons (step194 p h) (sat_cons (step196 p h) (sat_cons (step332 p h) (sat_cons (step328 p h) (sat_cons (step326 p h) (sat_cons (step321 p h) (sat_cons (step334 p h) (sat_cons (step308 p h) (sat_cons (step305 p h) (sat_cons (step303 p h) (sat_cons (step302 p h) (sat_cons (step549 p h) (sat_cons (step153 p h) (sat_cons (step156 p h) (sat_cons (step330 p h) (sat_cons (step317 p h) (sat_cons (step313 p h) (sat_cons (step312 p h) (sat_cons (step316 p h) (sat_cons (step315 p h) (sat_cons (step314 p h) (sat_cons (step154 p h) (sat_cons (step160 p h) (sat_cons (step162 p h) (sat_cons (step171 p h) (sat_cons (step511 p h) (sat_cons (step148 p h) (sat_cons (step149 p h) (sat_cons (step513 p h) (sat_cons (step500 p h) (sat_cons (step520 p h) (sat_cons (step506 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c596 : List Lit := [(1340, true), (121, true)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true :=
  Snake9.LocalRup.prove_clause [c352, c354, c349, c350, c12, c8] c596 (by decide) p (sat_cons (step352 p h) (sat_cons (step354 p h) (sat_cons (step349 p h) (sat_cons (step350 p h) (sat_cons (step12 p h) (sat_cons (step8 p h) (sat_nil p)))))))
def c597 : List Lit := [(1338, true), (1335, true), (243, true)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true :=
  Snake9.LocalRup.prove_clause [c175, c174, c209, c200, c199, c347, c346, c4, c345, c348, c201, c198, c197, c208, c207, c206, c202, c205, c204, c349, c350, c12, c11, c8, c14, c1, c13, c3, c5] c597 (by decide) p (sat_cons (step175 p h) (sat_cons (step174 p h) (sat_cons (step209 p h) (sat_cons (step200 p h) (sat_cons (step199 p h) (sat_cons (step347 p h) (sat_cons (step346 p h) (sat_cons (step4 p h) (sat_cons (step345 p h) (sat_cons (step348 p h) (sat_cons (step201 p h) (sat_cons (step198 p h) (sat_cons (step197 p h) (sat_cons (step208 p h) (sat_cons (step207 p h) (sat_cons (step206 p h) (sat_cons (step202 p h) (sat_cons (step205 p h) (sat_cons (step204 p h) (sat_cons (step349 p h) (sat_cons (step350 p h) (sat_cons (step12 p h) (sat_cons (step11 p h) (sat_cons (step8 p h) (sat_cons (step14 p h) (sat_cons (step1 p h) (sat_cons (step13 p h) (sat_cons (step3 p h) (sat_cons (step5 p h) (sat_nil p))))))))))))))))))))))))))))))
def c598 : List Lit := [(11, false), (1344, true), (243, true)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true :=
  Snake9.LocalRup.prove_clause [c175, c357, c208, c207, c206, c202, c596, c359, c597, c355, c209, c200, c199, c347, c346, c4, c345, c348, c201, c198, c197, c205, c204, c12, c11, c14, c13, c5, c2, c3, c6] c598 (by decide) p (sat_cons (step175 p h) (sat_cons (step357 p h) (sat_cons (step208 p h) (sat_cons (step207 p h) (sat_cons (step206 p h) (sat_cons (step202 p h) (sat_cons (step596 p h) (sat_cons (step359 p h) (sat_cons (step597 p h) (sat_cons (step355 p h) (sat_cons (step209 p h) (sat_cons (step200 p h) (sat_cons (step199 p h) (sat_cons (step347 p h) (sat_cons (step346 p h) (sat_cons (step4 p h) (sat_cons (step345 p h) (sat_cons (step348 p h) (sat_cons (step201 p h) (sat_cons (step198 p h) (sat_cons (step197 p h) (sat_cons (step205 p h) (sat_cons (step204 p h) (sat_cons (step12 p h) (sat_cons (step11 p h) (sat_cons (step14 p h) (sat_cons (step13 p h) (sat_cons (step5 p h) (sat_cons (step2 p h) (sat_cons (step3 p h) (sat_cons (step6 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c599 : List Lit := [(1344, true), (243, true)]
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true :=
  Snake9.LocalRup.prove_clause [c208, c207, c206, c202, c596, c203, c357, c359, c353, c348, c597, c355, c598, c351, c10, c7] c599 (by decide) p (sat_cons (step208 p h) (sat_cons (step207 p h) (sat_cons (step206 p h) (sat_cons (step202 p h) (sat_cons (step596 p h) (sat_cons (step203 p h) (sat_cons (step357 p h) (sat_cons (step359 p h) (sat_cons (step353 p h) (sat_cons (step348 p h) (sat_cons (step597 p h) (sat_cons (step355 p h) (sat_cons (step598 p h) (sat_cons (step351 p h) (sat_cons (step10 p h) (sat_cons (step7 p h) (sat_nil p)))))))))))))))))
def c600 : List Lit := [(1514, true), (431, true)]
theorem step600 (p : Nat → Bool) (h : Constraints p) : clause p c600 = true :=
  Snake9.LocalRup.prove_clause [c194, c332, c328, c326, c321, c334, c308, c305, c303, c302, c549, c153, c156, c512, c514, c510, c507, c154] c600 (by decide) p (sat_cons (step194 p h) (sat_cons (step332 p h) (sat_cons (step328 p h) (sat_cons (step326 p h) (sat_cons (step321 p h) (sat_cons (step334 p h) (sat_cons (step308 p h) (sat_cons (step305 p h) (sat_cons (step303 p h) (sat_cons (step302 p h) (sat_cons (step549 p h) (sat_cons (step153 p h) (sat_cons (step156 p h) (sat_cons (step512 p h) (sat_cons (step514 p h) (sat_cons (step510 p h) (sat_cons (step507 p h) (sat_cons (step154 p h) (sat_nil p)))))))))))))))))))
def c601 : List Lit := [(17, false), (137, true), (1356, true), (21, false)]
theorem step601 (p : Nat → Bool) (h : Constraints p) : clause p c601 = true :=
  Snake9.LocalRup.prove_clause [c369, c368, c44, c27, c50] c601 (by decide) p (sat_cons (step369 p h) (sat_cons (step368 p h) (sat_cons (step44 p h) (sat_cons (step27 p h) (sat_cons (step50 p h) (sat_nil p))))))
def c602 : List Lit := [(137, true), (1356, true), (21, false), (1350, true)]
theorem step602 (p : Nat → Bool) (h : Constraints p) : clause p c602 = true :=
  Snake9.LocalRup.prove_clause [c369, c368, c601, c362, c26, c42, c51] c602 (by decide) p (sat_cons (step369 p h) (sat_cons (step368 p h) (sat_cons (step601 p h) (sat_cons (step362 p h) (sat_cons (step26 p h) (sat_cons (step42 p h) (sat_cons (step51 p h) (sat_nil p))))))))
def c603 : List Lit := [(42, false), (45, false), (33, false), (152, true)]
theorem step603 (p : Nat → Bool) (h : Constraints p) : clause p c603 = true :=
  Snake9.LocalRup.prove_clause [c84, c90] c603 (by decide) p (sat_cons (step84 p h) (sat_cons (step90 p h) (sat_nil p)))
def c604 : List Lit := [(1384, false), (1393, true), (19, false), (269, false)]
theorem step604 (p : Nat → Bool) (h : Constraints p) : clause p c604 = true :=
  Snake9.LocalRup.prove_clause [c557, c579, c553, c344, c590, c542, c586, c228, c273, c342, c337, c332, c330, c317, c313, c312, c594, c274, c268, c247, c244, c242, c241, c334, c231, c599, c388, c410, c427, c436, c539, c533, c523, c411, c402, c587, c399, c593, c595, c507] c604 (by decide) p (sat_cons (step557 p h) (sat_cons (step579 p h) (sat_cons (step553 p h) (sat_cons (step344 p h) (sat_cons (step590 p h) (sat_cons (step542 p h) (sat_cons (step586 p h) (sat_cons (step228 p h) (sat_cons (step273 p h) (sat_cons (step342 p h) (sat_cons (step337 p h) (sat_cons (step332 p h) (sat_cons (step330 p h) (sat_cons (step317 p h) (sat_cons (step313 p h) (sat_cons (step312 p h) (sat_cons (step594 p h) (sat_cons (step274 p h) (sat_cons (step268 p h) (sat_cons (step247 p h) (sat_cons (step244 p h) (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_cons (step334 p h) (sat_cons (step231 p h) (sat_cons (step599 p h) (sat_cons (step388 p h) (sat_cons (step410 p h) (sat_cons (step427 p h) (sat_cons (step436 p h) (sat_cons (step539 p h) (sat_cons (step533 p h) (sat_cons (step523 p h) (sat_cons (step411 p h) (sat_cons (step402 p h) (sat_cons (step587 p h) (sat_cons (step399 p h) (sat_cons (step593 p h) (sat_cons (step595 p h) (sat_cons (step507 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c605 : List Lit := [(33, false), (1356, true), (17, false), (1354, true)]
theorem step605 (p : Nat → Bool) (h : Constraints p) : clause p c605 = true :=
  Snake9.TreeRup.prove_clause [c573, c553, c194, c344, c557, c579, c183, c589, c542, c586, c551, c187, c190, c366, c601, c219, c220, c221, c224, c231, c599, c388, c228, c273, c342, c337, c600, c332, c330, c317, c313, c312, c594, c517, c521, c531, c541, c438, c328, c326, c321, c334, c308, c305, c303, c302, c549, c153, c156, c310, c296, c295, c294, c306, c300, c274, c266, c265, c259, c253, c252, c258, c257, c254, c268, c249, c236, c234, c223, c217, c216, c218, c368, c369, c44, c27, c365, c41, c34, c35, c39, c40, c546, c62, c78, c392, c394, c407, c603, c416, c423, c430, c604, c426, c409, c397, c436, c403, c53, c55, c539, c66, c67, c31, c533, c88, c131, c400, c401, c529, c87, c482, c405, c498, c154, c485, c30, c486, c507, c496, c128, c484, c593, c491, c126, c124] c605 (by decide) p (sat_cons (step573 p h) (sat_cons (step553 p h) (sat_cons (step194 p h) (sat_cons (step344 p h) (sat_cons (step557 p h) (sat_cons (step579 p h) (sat_cons (step183 p h) (sat_cons (step589 p h) (sat_cons (step542 p h) (sat_cons (step586 p h) (sat_cons (step551 p h) (sat_cons (step187 p h) (sat_cons (step190 p h) (sat_cons (step366 p h) (sat_cons (step601 p h) (sat_cons (step219 p h) (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step224 p h) (sat_cons (step231 p h) (sat_cons (step599 p h) (sat_cons (step388 p h) (sat_cons (step228 p h) (sat_cons (step273 p h) (sat_cons (step342 p h) (sat_cons (step337 p h) (sat_cons (step600 p h) (sat_cons (step332 p h) (sat_cons (step330 p h) (sat_cons (step317 p h) (sat_cons (step313 p h) (sat_cons (step312 p h) (sat_cons (step594 p h) (sat_cons (step517 p h) (sat_cons (step521 p h) (sat_cons (step531 p h) (sat_cons (step541 p h) (sat_cons (step438 p h) (sat_cons (step328 p h) (sat_cons (step326 p h) (sat_cons (step321 p h) (sat_cons (step334 p h) (sat_cons (step308 p h) (sat_cons (step305 p h) (sat_cons (step303 p h) (sat_cons (step302 p h) (sat_cons (step549 p h) (sat_cons (step153 p h) (sat_cons (step156 p h) (sat_cons (step310 p h) (sat_cons (step296 p h) (sat_cons (step295 p h) (sat_cons (step294 p h) (sat_cons (step306 p h) (sat_cons (step300 p h) (sat_cons (step274 p h) (sat_cons (step266 p h) (sat_cons (step265 p h) (sat_cons (step259 p h) (sat_cons (step253 p h) (sat_cons (step252 p h) (sat_cons (step258 p h) (sat_cons (step257 p h) (sat_cons (step254 p h) (sat_cons (step268 p h) (sat_cons (step249 p h) (sat_cons (step236 p h) (sat_cons (step234 p h) (sat_cons (step223 p h) (sat_cons (step217 p h) (sat_cons (step216 p h) (sat_cons (step218 p h) (sat_cons (step368 p h) (sat_cons (step369 p h) (sat_cons (step44 p h) (sat_cons (step27 p h) (sat_cons (step365 p h) (sat_cons (step41 p h) (sat_cons (step34 p h) (sat_cons (step35 p h) (sat_cons (step39 p h) (sat_cons (step40 p h) (sat_cons (step546 p h) (sat_cons (step62 p h) (sat_cons (step78 p h) (sat_cons (step392 p h) (sat_cons (step394 p h) (sat_cons (step407 p h) (sat_cons (step603 p h) (sat_cons (step416 p h) (sat_cons (step423 p h) (sat_cons (step430 p h) (sat_cons (step604 p h) (sat_cons (step426 p h) (sat_cons (step409 p h) (sat_cons (step397 p h) (sat_cons (step436 p h) (sat_cons (step403 p h) (sat_cons (step53 p h) (sat_cons (step55 p h) (sat_cons (step539 p h) (sat_cons (step66 p h) (sat_cons (step67 p h) (sat_cons (step31 p h) (sat_cons (step533 p h) (sat_cons (step88 p h) (sat_cons (step131 p h) (sat_cons (step400 p h) (sat_cons (step401 p h) (sat_cons (step529 p h) (sat_cons (step87 p h) (sat_cons (step482 p h) (sat_cons (step405 p h) (sat_cons (step498 p h) (sat_cons (step154 p h) (sat_cons (step485 p h) (sat_cons (step30 p h) (sat_cons (step486 p h) (sat_cons (step507 p h) (sat_cons (step496 p h) (sat_cons (step128 p h) (sat_cons (step484 p h) (sat_cons (step593 p h) (sat_cons (step491 p h) (sat_cons (step126 p h) (sat_cons (step124 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c606 : List Lit := [(1383, false), (271, false), (1371, false), (1392, true), (1411, false)]
theorem step606 (p : Nat → Bool) (h : Constraints p) : clause p c606 = true :=
  Snake9.LocalRup.prove_clause [c553, c344, c542, c586, c273, c342, c337, c332, c330, c317, c313, c312, c594, c274, c268, c247, c245, c239, c238, c244, c242, c241, c334, c424, c435, c538, c534, c407, c408, c426, c402, c404, c587, c436, c399, c400, c69, c592, c539, c72, c495, c533, c527, c593, c595, c507] c606 (by decide) p (sat_cons (step553 p h) (sat_cons (step344 p h) (sat_cons (step542 p h) (sat_cons (step586 p h) (sat_cons (step273 p h) (sat_cons (step342 p h) (sat_cons (step337 p h) (sat_cons (step332 p h) (sat_cons (step330 p h) (sat_cons (step317 p h) (sat_cons (step313 p h) (sat_cons (step312 p h) (sat_cons (step594 p h) (sat_cons (step274 p h) (sat_cons (step268 p h) (sat_cons (step247 p h) (sat_cons (step245 p h) (sat_cons (step239 p h) (sat_cons (step238 p h) (sat_cons (step244 p h) (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_cons (step334 p h) (sat_cons (step424 p h) (sat_cons (step435 p h) (sat_cons (step538 p h) (sat_cons (step534 p h) (sat_cons (step407 p h) (sat_cons (step408 p h) (sat_cons (step426 p h) (sat_cons (step402 p h) (sat_cons (step404 p h) (sat_cons (step587 p h) (sat_cons (step436 p h) (sat_cons (step399 p h) (sat_cons (step400 p h) (sat_cons (step69 p h) (sat_cons (step592 p h) (sat_cons (step539 p h) (sat_cons (step72 p h) (sat_cons (step495 p h) (sat_cons (step533 p h) (sat_cons (step527 p h) (sat_cons (step593 p h) (sat_cons (step595 p h) (sat_cons (step507 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c607 : List Lit := [(1388, true), (1528, true), (37, false), (146, true), (150, true), (431, true)]
theorem step607 (p : Nat → Bool) (h : Constraints p) : clause p c607 = true :=
  Snake9.LocalRup.prove_clause [c523, c332, c330, c317, c313, c312, c594, c334, c402, c404, c587, c399, c69, c595, c72, c507, c593] c607 (by decide) p (sat_cons (step523 p h) (sat_cons (step332 p h) (sat_cons (step330 p h) (sat_cons (step317 p h) (sat_cons (step313 p h) (sat_cons (step312 p h) (sat_cons (step594 p h) (sat_cons (step334 p h) (sat_cons (step402 p h) (sat_cons (step404 p h) (sat_cons (step587 p h) (sat_cons (step399 p h) (sat_cons (step69 p h) (sat_cons (step595 p h) (sat_cons (step72 p h) (sat_cons (step507 p h) (sat_cons (step593 p h) (sat_nil p))))))))))))))))))
def c608 : List Lit := [(271, false), (1359, false), (1392, true), (1411, false)]
theorem step608 (p : Nat → Bool) (h : Constraints p) : clause p c608 = true :=
  Snake9.TreeRup.prove_clause [c553, c344, c176, c580, c542, c586, c378, c386, c424, c273, c274, c342, c268, c337, c247, c249, c332, c334, c600, c244, c245, c236, c330, c308, c242, c239, c234, c317, c306, c241, c238, c313, c300, c312, c594, c517, c606, c394, c396, c391, c392, c64, c54, c53, c544, c360, c32, c363, c382, c387, c439, c539, c533, c607, c406, c426, c440, c540, c532, c525, c493, c495, c490, c485, c489, c482, c131, c141] c608 (by decide) p (sat_cons (step553 p h) (sat_cons (step344 p h) (sat_cons (step176 p h) (sat_cons (step580 p h) (sat_cons (step542 p h) (sat_cons (step586 p h) (sat_cons (step378 p h) (sat_cons (step386 p h) (sat_cons (step424 p h) (sat_cons (step273 p h) (sat_cons (step274 p h) (sat_cons (step342 p h) (sat_cons (step268 p h) (sat_cons (step337 p h) (sat_cons (step247 p h) (sat_cons (step249 p h) (sat_cons (step332 p h) (sat_cons (step334 p h) (sat_cons (step600 p h) (sat_cons (step244 p h) (sat_cons (step245 p h) (sat_cons (step236 p h) (sat_cons (step330 p h) (sat_cons (step308 p h) (sat_cons (step242 p h) (sat_cons (step239 p h) (sat_cons (step234 p h) (sat_cons (step317 p h) (sat_cons (step306 p h) (sat_cons (step241 p h) (sat_cons (step238 p h) (sat_cons (step313 p h) (sat_cons (step300 p h) (sat_cons (step312 p h) (sat_cons (step594 p h) (sat_cons (step517 p h) (sat_cons (step606 p h) (sat_cons (step394 p h) (sat_cons (step396 p h) (sat_cons (step391 p h) (sat_cons (step392 p h) (sat_cons (step64 p h) (sat_cons (step54 p h) (sat_cons (step53 p h) (sat_cons (step544 p h) (sat_cons (step360 p h) (sat_cons (step32 p h) (sat_cons (step363 p h) (sat_cons (step382 p h) (sat_cons (step387 p h) (sat_cons (step439 p h) (sat_cons (step539 p h) (sat_cons (step533 p h) (sat_cons (step607 p h) (sat_cons (step406 p h) (sat_cons (step426 p h) (sat_cons (step440 p h) (sat_cons (step540 p h) (sat_cons (step532 p h) (sat_cons (step525 p h) (sat_cons (step493 p h) (sat_cons (step495 p h) (sat_cons (step490 p h) (sat_cons (step485 p h) (sat_cons (step489 p h) (sat_cons (step482 p h) (sat_cons (step131 p h) (sat_cons (step141 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c609 : List Lit := [(1363, true), (28, false), (17, true)]
theorem step609 (p : Nat → Bool) (h : Constraints p) : clause p c609 = true :=
  Snake9.LocalRup.prove_clause [c360, c363, c383, c381, c364, c371, c373, c362, c368, c369, c366, c26, c47, c42, c48] c609 (by decide) p (sat_cons (step360 p h) (sat_cons (step363 p h) (sat_cons (step383 p h) (sat_cons (step381 p h) (sat_cons (step364 p h) (sat_cons (step371 p h) (sat_cons (step373 p h) (sat_cons (step362 p h) (sat_cons (step368 p h) (sat_cons (step369 p h) (sat_cons (step366 p h) (sat_cons (step26 p h) (sat_cons (step47 p h) (sat_cons (step42 p h) (sat_cons (step48 p h) (sat_nil p))))))))))))))))
def c610 : List Lit := [(1381, true), (32, false), (28, false)]
theorem step610 (p : Nat → Bool) (h : Constraints p) : clause p c610 = true :=
  Snake9.LocalRup.prove_clause [c391, c392, c64] c610 (by decide) p (sat_cons (step391 p h) (sat_cons (step392 p h) (sat_cons (step64 p h) (sat_nil p))))
def c611 : List Lit := [(1358, true), (137, true), (1350, true)]
theorem step611 (p : Nat → Bool) (h : Constraints p) : clause p c611 = true :=
  Snake9.LocalRup.prove_clause [c371, c373, c602, c366] c611 (by decide) p (sat_cons (step371 p h) (sat_cons (step373 p h) (sat_cons (step602 p h) (sat_cons (step366 p h) (sat_nil p)))))
end B112E079
