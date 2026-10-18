import B112E201Inputs
namespace B112E201
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c672 : List Lit := [(1, false)]
theorem step672 (p : Nat → Bool) (h : Constraints p) : clause p c672 = true :=
  Snake9.LocalRup.prove_clause [c174, c1] c672 (by decide) p (sat_cons (step174 p h) (sat_cons (step1 p h) (sat_nil p)))
def c673 : List Lit := [(41, false)]
theorem step673 (p : Nat → Bool) (h : Constraints p) : clause p c673 = true :=
  Snake9.LocalRup.prove_clause [c195, c91] c673 (by decide) p (sat_cons (step195 p h) (sat_cons (step91 p h) (sat_nil p)))
def c674 : List Lit := [(52, false)]
theorem step674 (p : Nat → Bool) (h : Constraints p) : clause p c674 = true :=
  Snake9.LocalRup.prove_clause [c201, c111] c674 (by decide) p (sat_cons (step201 p h) (sat_cons (step111 p h) (sat_nil p)))
def c675 : List Lit := [(55, false)]
theorem step675 (p : Nat → Bool) (h : Constraints p) : clause p c675 = true :=
  Snake9.LocalRup.prove_clause [c203, c116] c675 (by decide) p (sat_cons (step203 p h) (sat_cons (step116 p h) (sat_nil p)))
def c676 : List Lit := [(430, false)]
theorem step676 (p : Nat → Bool) (h : Constraints p) : clause p c676 = true :=
  Snake9.LocalRup.prove_clause [c415, c412] c676 (by decide) p (sat_cons (step415 p h) (sat_cons (step412 p h) (sat_nil p)))
def c677 : List Lit := [(324, false)]
theorem step677 (p : Nat → Bool) (h : Constraints p) : clause p c677 = true :=
  Snake9.LocalRup.prove_clause [c415, c414] c677 (by decide) p (sat_cons (step415 p h) (sat_cons (step414 p h) (sat_nil p)))
def c678 : List Lit := [(428, false)]
theorem step678 (p : Nat → Bool) (h : Constraints p) : clause p c678 = true :=
  Snake9.LocalRup.prove_clause [c676, c409] c678 (by decide) p (sat_cons (step676 p h) (sat_cons (step409 p h) (sat_nil p)))
def c679 : List Lit := [(376, false)]
theorem step679 (p : Nat → Bool) (h : Constraints p) : clause p c679 = true :=
  Snake9.LocalRup.prove_clause [c676, c411] c679 (by decide) p (sat_cons (step676 p h) (sat_cons (step411 p h) (sat_nil p)))
def c680 : List Lit := [(322, false)]
theorem step680 (p : Nat → Bool) (h : Constraints p) : clause p c680 = true :=
  Snake9.LocalRup.prove_clause [c677, c317] c680 (by decide) p (sat_cons (step677 p h) (sat_cons (step317 p h) (sat_nil p)))
def c681 : List Lit := [(270, false)]
theorem step681 (p : Nat → Bool) (h : Constraints p) : clause p c681 = true :=
  Snake9.LocalRup.prove_clause [c677, c320] c681 (by decide) p (sat_cons (step677 p h) (sat_cons (step320 p h) (sat_nil p)))
def c682 : List Lit := [(400, false)]
theorem step682 (p : Nat → Bool) (h : Constraints p) : clause p c682 = true :=
  Snake9.LocalRup.prove_clause [c678, c407] c682 (by decide) p (sat_cons (step678 p h) (sat_cons (step407 p h) (sat_nil p)))
def c683 : List Lit := [(374, false)]
theorem step683 (p : Nat → Bool) (h : Constraints p) : clause p c683 = true :=
  Snake9.LocalRup.prove_clause [c679, c367] c683 (by decide) p (sat_cons (step679 p h) (sat_cons (step367 p h) (sat_nil p)))
def c684 : List Lit := [(348, false)]
theorem step684 (p : Nat → Bool) (h : Constraints p) : clause p c684 = true :=
  Snake9.LocalRup.prove_clause [c679, c369] c684 (by decide) p (sat_cons (step679 p h) (sat_cons (step369 p h) (sat_nil p)))
def c685 : List Lit := [(294, false)]
theorem step685 (p : Nat → Bool) (h : Constraints p) : clause p c685 = true :=
  Snake9.LocalRup.prove_clause [c680, c315] c685 (by decide) p (sat_cons (step680 p h) (sat_cons (step315 p h) (sat_nil p)))
def c686 : List Lit := [(242, false)]
theorem step686 (p : Nat → Bool) (h : Constraints p) : clause p c686 = true :=
  Snake9.LocalRup.prove_clause [c681, c276] c686 (by decide) p (sat_cons (step681 p h) (sat_cons (step276 p h) (sat_nil p)))
def c687 : List Lit := [(386, false)]
theorem step687 (p : Nat → Bool) (h : Constraints p) : clause p c687 = true :=
  Snake9.LocalRup.prove_clause [c682, c386] c687 (by decide) p (sat_cons (step682 p h) (sat_cons (step386 p h) (sat_nil p)))
def c688 : List Lit := [(360, false)]
theorem step688 (p : Nat → Bool) (h : Constraints p) : clause p c688 = true :=
  Snake9.LocalRup.prove_clause [c683, c365] c688 (by decide) p (sat_cons (step683 p h) (sat_cons (step365 p h) (sat_nil p)))
def c689 : List Lit := [(346, false)]
theorem step689 (p : Nat → Bool) (h : Constraints p) : clause p c689 = true :=
  Snake9.LocalRup.prove_clause [c684, c340] c689 (by decide) p (sat_cons (step684 p h) (sat_cons (step340 p h) (sat_nil p)))
def c690 : List Lit := [(292, false)]
theorem step690 (p : Nat → Bool) (h : Constraints p) : clause p c690 = true :=
  Snake9.LocalRup.prove_clause [c685, c292] c690 (by decide) p (sat_cons (step685 p h) (sat_cons (step292 p h) (sat_nil p)))
def c691 : List Lit := [(240, false)]
theorem step691 (p : Nat → Bool) (h : Constraints p) : clause p c691 = true :=
  Snake9.LocalRup.prove_clause [c686, c252] c691 (by decide) p (sat_cons (step686 p h) (sat_cons (step252 p h) (sat_nil p)))
def c692 : List Lit := [(228, false)]
theorem step692 (p : Nat → Bool) (h : Constraints p) : clause p c692 = true :=
  Snake9.LocalRup.prove_clause [c686, c255] c692 (by decide) p (sat_cons (step686 p h) (sat_cons (step255 p h) (sat_nil p)))
def c693 : List Lit := [(358, false)]
theorem step693 (p : Nat → Bool) (h : Constraints p) : clause p c693 = true :=
  Snake9.LocalRup.prove_clause [c688, c353] c693 (by decide) p (sat_cons (step688 p h) (sat_cons (step353 p h) (sat_nil p)))
def c694 : List Lit := [(338, false)]
theorem step694 (p : Nat → Bool) (h : Constraints p) : clause p c694 = true :=
  Snake9.LocalRup.prove_clause [c689, c338] c694 (by decide) p (sat_cons (step689 p h) (sat_cons (step338 p h) (sat_nil p)))
def c695 : List Lit := [(232, false)]
theorem step695 (p : Nat → Bool) (h : Constraints p) : clause p c695 = true :=
  Snake9.LocalRup.prove_clause [c691, c250] c695 (by decide) p (sat_cons (step691 p h) (sat_cons (step250 p h) (sat_nil p)))
def c696 : List Lit := [(222, false)]
theorem step696 (p : Nat → Bool) (h : Constraints p) : clause p c696 = true :=
  Snake9.LocalRup.prove_clause [c692, c239] c696 (by decide) p (sat_cons (step692 p h) (sat_cons (step239 p h) (sat_nil p)))
def c697 : List Lit := [(354, false)]
theorem step697 (p : Nat → Bool) (h : Constraints p) : clause p c697 = true :=
  Snake9.LocalRup.prove_clause [c693, c351] c697 (by decide) p (sat_cons (step693 p h) (sat_cons (step351 p h) (sat_nil p)))
def c698 : List Lit := [(230, false)]
theorem step698 (p : Nat → Bool) (h : Constraints p) : clause p c698 = true :=
  Snake9.LocalRup.prove_clause [c695, c244] c698 (by decide) p (sat_cons (step695 p h) (sat_cons (step244 p h) (sat_nil p)))
def c699 : List Lit := [(220, false)]
theorem step699 (p : Nat → Bool) (h : Constraints p) : clause p c699 = true :=
  Snake9.LocalRup.prove_clause [c696, c234] c699 (by decide) p (sat_cons (step696 p h) (sat_cons (step234 p h) (sat_nil p)))
def c700 : List Lit := [(111, true), (112, true), (113, true), (117, true), (118, true), (119, true), (123, true), (124, true), (128, true), (129, true), (131, true), (134, true), (135, true), (137, true), (140, true), (143, true), (144, true), (147, true), (149, true), (152, true), (154, true), (155, true), (158, true), (160, true), (162, true), (166, true), (168, true), (170, true), (172, true), (173, true), (175, true), (178, true), (180, true), (181, true), (183, true), (186, true), (188, true), (189, true), (191, true), (194, true), (196, true), (197, true), (200, true), (203, true), (205, true), (206, true), (207, true), (209, true), (212, true), (214, true), (215, true), (216, true)]
theorem step700 (p : Nat → Bool) (h : Constraints p) : clause p c700 = true :=
  Snake9.LocalRup.prove_clause [c174, c175, c176, c177, c178, c179, c180, c181, c182, c183, c184, c185, c186, c187, c188, c189, c190, c191, c192, c193, c194, c195, c196, c197, c198, c199, c200, c201, c202, c203, c204, c205, c206, c207, c208, c209, c210, c211, c212, c213, c214, c215, c216, c217, c218, c219, c220, c221, c222, c223, c224, c225, c226, c227, c228, c229, c416] c700 (by decide) p (sat_cons (step174 p h) (sat_cons (step175 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_cons (step178 p h) (sat_cons (step179 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step182 p h) (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step186 p h) (sat_cons (step187 p h) (sat_cons (step188 p h) (sat_cons (step189 p h) (sat_cons (step190 p h) (sat_cons (step191 p h) (sat_cons (step192 p h) (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step195 p h) (sat_cons (step196 p h) (sat_cons (step197 p h) (sat_cons (step198 p h) (sat_cons (step199 p h) (sat_cons (step200 p h) (sat_cons (step201 p h) (sat_cons (step202 p h) (sat_cons (step203 p h) (sat_cons (step204 p h) (sat_cons (step205 p h) (sat_cons (step206 p h) (sat_cons (step207 p h) (sat_cons (step208 p h) (sat_cons (step209 p h) (sat_cons (step210 p h) (sat_cons (step211 p h) (sat_cons (step212 p h) (sat_cons (step213 p h) (sat_cons (step214 p h) (sat_cons (step215 p h) (sat_cons (step216 p h) (sat_cons (step217 p h) (sat_cons (step218 p h) (sat_cons (step219 p h) (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step222 p h) (sat_cons (step223 p h) (sat_cons (step224 p h) (sat_cons (step225 p h) (sat_cons (step226 p h) (sat_cons (step227 p h) (sat_cons (step228 p h) (sat_cons (step229 p h) (sat_cons (step416 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c701 : List Lit := [(1392, true)]
theorem step701 (p : Nat → Bool) (h : Constraints p) : clause p c701 = true :=
  Snake9.LocalRup.prove_clause [c507, c508, c503, c491, c496, c497, c489, c99, c106] c701 (by decide) p (sat_cons (step507 p h) (sat_cons (step508 p h) (sat_cons (step503 p h) (sat_cons (step491 p h) (sat_cons (step496 p h) (sat_cons (step497 p h) (sat_cons (step489 p h) (sat_cons (step99 p h) (sat_cons (step106 p h) (sat_nil p))))))))))
def c702 : List Lit := [(1448, true), (1473, true)]
theorem step702 (p : Nat → Bool) (h : Constraints p) : clause p c702 = true :=
  Snake9.LocalRup.prove_clause [c687, c596, c594, c597, c575, c576, c572, c569, c141, c151, c147, c153, c370, c371, c376, c372] c702 (by decide) p (sat_cons (step687 p h) (sat_cons (step596 p h) (sat_cons (step594 p h) (sat_cons (step597 p h) (sat_cons (step575 p h) (sat_cons (step576 p h) (sat_cons (step572 p h) (sat_cons (step569 p h) (sat_cons (step141 p h) (sat_cons (step151 p h) (sat_cons (step147 p h) (sat_cons (step153 p h) (sat_cons (step370 p h) (sat_cons (step371 p h) (sat_cons (step376 p h) (sat_cons (step372 p h) (sat_nil p)))))))))))))))))
def c703 : List Lit := [(1448, false), (1460, true)]
theorem step703 (p : Nat → Bool) (h : Constraints p) : clause p c703 = true :=
  Snake9.LocalRup.prove_clause [c586, c580, c584, c587, c568, c560, c562, c557, c551, c555, c556, c548, c125, c133, c126] c703 (by decide) p (sat_cons (step586 p h) (sat_cons (step580 p h) (sat_cons (step584 p h) (sat_cons (step587 p h) (sat_cons (step568 p h) (sat_cons (step560 p h) (sat_cons (step562 p h) (sat_cons (step557 p h) (sat_cons (step551 p h) (sat_cons (step555 p h) (sat_cons (step556 p h) (sat_cons (step548 p h) (sat_cons (step125 p h) (sat_cons (step133 p h) (sat_cons (step126 p h) (sat_nil p))))))))))))))))
def c704 : List Lit := [(63, false), (69, false), (66, false)]
theorem step704 (p : Nat → Bool) (h : Constraints p) : clause p c704 = true :=
  Snake9.LocalRup.prove_clause [c689, c125, c130, c128, c332, c327, c333, c328, c337] c704 (by decide) p (sat_cons (step689 p h) (sat_cons (step125 p h) (sat_cons (step130 p h) (sat_cons (step128 p h) (sat_cons (step332 p h) (sat_cons (step327 p h) (sat_cons (step333 p h) (sat_cons (step328 p h) (sat_cons (step337 p h) (sat_nil p))))))))))
def c705 : List Lit := [(1433, true)]
theorem step705 (p : Nat → Bool) (h : Constraints p) : clause p c705 = true :=
  Snake9.LocalRup.prove_clause [c560, c562, c557, c551, c555, c556, c548, c704] c705 (by decide) p (sat_cons (step560 p h) (sat_cons (step562 p h) (sat_cons (step557 p h) (sat_cons (step551 p h) (sat_cons (step555 p h) (sat_cons (step556 p h) (sat_cons (step548 p h) (sat_cons (step704 p h) (sat_nil p)))))))))
def c706 : List Lit := [(63, true), (1460, true)]
theorem step706 (p : Nat → Bool) (h : Constraints p) : clause p c706 = true :=
  Snake9.LocalRup.prove_clause [c705, c684, c587, c583, c567, c565, c703, c576, c570, c590, c564, c552, c548, c550, c551, c554, c118, c563, c123, c558, c323, c129, c324, c124, c325, c329, c342, c336] c706 (by decide) p (sat_cons (step705 p h) (sat_cons (step684 p h) (sat_cons (step587 p h) (sat_cons (step583 p h) (sat_cons (step567 p h) (sat_cons (step565 p h) (sat_cons (step703 p h) (sat_cons (step576 p h) (sat_cons (step570 p h) (sat_cons (step590 p h) (sat_cons (step564 p h) (sat_cons (step552 p h) (sat_cons (step548 p h) (sat_cons (step550 p h) (sat_cons (step551 p h) (sat_cons (step554 p h) (sat_cons (step118 p h) (sat_cons (step563 p h) (sat_cons (step123 p h) (sat_cons (step558 p h) (sat_cons (step323 p h) (sat_cons (step129 p h) (sat_cons (step324 p h) (sat_cons (step124 p h) (sat_cons (step325 p h) (sat_cons (step329 p h) (sat_cons (step342 p h) (sat_cons (step336 p h) (sat_nil p)))))))))))))))))))))))))))))
def c707 : List Lit := [(69, false), (1460, true)]
theorem step707 (p : Nat → Bool) (h : Constraints p) : clause p c707 = true :=
  Snake9.LocalRup.prove_clause [c705, c697, c694, c706, c587, c583, c567, c566, c565, c568, c703, c576, c570, c590, c704, c133, c556, c134, c135, c127, c557, c347, c327, c563, c136, c330, c551, c553, c138, c549, c124, c118] c707 (by decide) p (sat_cons (step705 p h) (sat_cons (step697 p h) (sat_cons (step694 p h) (sat_cons (step706 p h) (sat_cons (step587 p h) (sat_cons (step583 p h) (sat_cons (step567 p h) (sat_cons (step566 p h) (sat_cons (step565 p h) (sat_cons (step568 p h) (sat_cons (step703 p h) (sat_cons (step576 p h) (sat_cons (step570 p h) (sat_cons (step590 p h) (sat_cons (step704 p h) (sat_cons (step133 p h) (sat_cons (step556 p h) (sat_cons (step134 p h) (sat_cons (step135 p h) (sat_cons (step127 p h) (sat_cons (step557 p h) (sat_cons (step347 p h) (sat_cons (step327 p h) (sat_cons (step563 p h) (sat_cons (step136 p h) (sat_cons (step330 p h) (sat_cons (step551 p h) (sat_cons (step553 p h) (sat_cons (step138 p h) (sat_cons (step549 p h) (sat_cons (step124 p h) (sat_cons (step118 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c708 : List Lit := [(1460, true)]
theorem step708 (p : Nat → Bool) (h : Constraints p) : clause p c708 = true :=
  Snake9.LocalRup.prove_clause [c705, c684, c590, c561, c703, c576, c570, c587, c583, c567, c565, c707, c555, c557, c559, c563, c551, c553, c549, c118, c129, c123, c124, c323, c329, c324, c336, c325, c342] c708 (by decide) p (sat_cons (step705 p h) (sat_cons (step684 p h) (sat_cons (step590 p h) (sat_cons (step561 p h) (sat_cons (step703 p h) (sat_cons (step576 p h) (sat_cons (step570 p h) (sat_cons (step587 p h) (sat_cons (step583 p h) (sat_cons (step567 p h) (sat_cons (step565 p h) (sat_cons (step707 p h) (sat_cons (step555 p h) (sat_cons (step557 p h) (sat_cons (step559 p h) (sat_cons (step563 p h) (sat_cons (step551 p h) (sat_cons (step553 p h) (sat_cons (step549 p h) (sat_cons (step118 p h) (sat_cons (step129 p h) (sat_cons (step123 p h) (sat_cons (step124 p h) (sat_cons (step323 p h) (sat_cons (step329 p h) (sat_cons (step324 p h) (sat_cons (step336 p h) (sat_cons (step325 p h) (sat_cons (step342 p h) (sat_nil p))))))))))))))))))))))))))))))
def c709 : List Lit := [(1344, true)]
theorem step709 (p : Nat → Bool) (h : Constraints p) : clause p c709 = true :=
  Snake9.LocalRup.prove_clause [c451, c454, c445, c447, c435, c437, c442, c443, c439, c432, c433, c60, c57, c40, c62] c709 (by decide) p (sat_cons (step451 p h) (sat_cons (step454 p h) (sat_cons (step445 p h) (sat_cons (step447 p h) (sat_cons (step435 p h) (sat_cons (step437 p h) (sat_cons (step442 p h) (sat_cons (step443 p h) (sat_cons (step439 p h) (sat_cons (step432 p h) (sat_cons (step433 p h) (sat_cons (step60 p h) (sat_cons (step57 p h) (sat_cons (step40 p h) (sat_cons (step62 p h) (sat_nil p))))))))))))))))
def c710 : List Lit := [(1351, true)]
theorem step710 (p : Nat → Bool) (h : Constraints p) : clause p c710 = true :=
  Snake9.LocalRup.prove_clause [c709, c459] c710 (by decide) p (sat_cons (step709 p h) (sat_cons (step459 p h) (sat_nil p)))
def c711 : List Lit := [(34, false), (1370, true)]
theorem step711 (p : Nat → Bool) (h : Constraints p) : clause p c711 = true :=
  Snake9.LocalRup.prove_clause [c690, c478, c476, c475, c480, c82, c87, c83, c90, c283, c285, c290, c286] c711 (by decide) p (sat_cons (step690 p h) (sat_cons (step478 p h) (sat_cons (step476 p h) (sat_cons (step475 p h) (sat_cons (step480 p h) (sat_cons (step82 p h) (sat_cons (step87 p h) (sat_cons (step83 p h) (sat_cons (step90 p h) (sat_cons (step283 p h) (sat_cons (step285 p h) (sat_cons (step290 p h) (sat_cons (step286 p h) (sat_nil p))))))))))))))
def c712 : List Lit := [(43, true), (1393, true)]
theorem step712 (p : Nat → Bool) (h : Constraints p) : clause p c712 = true :=
  Snake9.LocalRup.prove_clause [c512, c493, c494, c509, c489, c503, c99, c496, c497, c106] c712 (by decide) p (sat_cons (step512 p h) (sat_cons (step493 p h) (sat_cons (step494 p h) (sat_cons (step509 p h) (sat_cons (step489 p h) (sat_cons (step503 p h) (sat_cons (step99 p h) (sat_cons (step496 p h) (sat_cons (step497 p h) (sat_cons (step106 p h) (sat_nil p)))))))))))
def c713 : List Lit := [(46, false), (1384, true)]
theorem step713 (p : Nat → Bool) (h : Constraints p) : clause p c713 = true :=
  Snake9.LocalRup.prove_clause [c497, c496, c99, c106] c713 (by decide) p (sat_cons (step497 p h) (sat_cons (step496 p h) (sat_cons (step99 p h) (sat_cons (step106 p h) (sat_nil p)))))
def c714 : List Lit := [(31, true), (1374, true)]
theorem step714 (p : Nat → Bool) (h : Constraints p) : clause p c714 = true :=
  Snake9.LocalRup.prove_clause [c486, c471, c468, c469, c470, c711, c485] c714 (by decide) p (sat_cons (step486 p h) (sat_cons (step471 p h) (sat_cons (step468 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step711 p h) (sat_cons (step485 p h) (sat_nil p))))))))
def c715 : List Lit := [(40, false), (1400, false), (1393, true), (31, false)]
theorem step715 (p : Nat → Bool) (h : Constraints p) : clause p c715 = true :=
  Snake9.TreeRup.prove_clause [c680, c677, c415, c673, c196, c672, c176, c177, c179, c175, c709, c667, c708, c712, c512, c492, c94, c89, c285, c286, c288, c291, c313, c314, c316, c319, c311, c413, c274, c300, c301, c408, c251, c253, c298, c299, c295, c405, c247, c248, c236, c237, c297, c296, c294, c403, c246, c243, c235, c233, c100, c93, c402, c245, c240, c241, c231, c489, c490, c92, c396, c4, c491, c97, c395, c15, c509, c20, c502, c17, c500, c23, c101, c30, c13, c25, c11, c424, c418, c426, c422, c431, c466, c547, c666, c650, c636, c639, c631, c610, c628, c629, c597, c626, c624, c625, c173, c171, c172, c166] c715 (by decide) p (sat_cons (step680 p h) (sat_cons (step677 p h) (sat_cons (step415 p h) (sat_cons (step673 p h) (sat_cons (step196 p h) (sat_cons (step672 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_cons (step179 p h) (sat_cons (step175 p h) (sat_cons (step709 p h) (sat_cons (step667 p h) (sat_cons (step708 p h) (sat_cons (step712 p h) (sat_cons (step512 p h) (sat_cons (step492 p h) (sat_cons (step94 p h) (sat_cons (step89 p h) (sat_cons (step285 p h) (sat_cons (step286 p h) (sat_cons (step288 p h) (sat_cons (step291 p h) (sat_cons (step313 p h) (sat_cons (step314 p h) (sat_cons (step316 p h) (sat_cons (step319 p h) (sat_cons (step311 p h) (sat_cons (step413 p h) (sat_cons (step274 p h) (sat_cons (step300 p h) (sat_cons (step301 p h) (sat_cons (step408 p h) (sat_cons (step251 p h) (sat_cons (step253 p h) (sat_cons (step298 p h) (sat_cons (step299 p h) (sat_cons (step295 p h) (sat_cons (step405 p h) (sat_cons (step247 p h) (sat_cons (step248 p h) (sat_cons (step236 p h) (sat_cons (step237 p h) (sat_cons (step297 p h) (sat_cons (step296 p h) (sat_cons (step294 p h) (sat_cons (step403 p h) (sat_cons (step246 p h) (sat_cons (step243 p h) (sat_cons (step235 p h) (sat_cons (step233 p h) (sat_cons (step100 p h) (sat_cons (step93 p h) (sat_cons (step402 p h) (sat_cons (step245 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step231 p h) (sat_cons (step489 p h) (sat_cons (step490 p h) (sat_cons (step92 p h) (sat_cons (step396 p h) (sat_cons (step4 p h) (sat_cons (step491 p h) (sat_cons (step97 p h) (sat_cons (step395 p h) (sat_cons (step15 p h) (sat_cons (step509 p h) (sat_cons (step20 p h) (sat_cons (step502 p h) (sat_cons (step17 p h) (sat_cons (step500 p h) (sat_cons (step23 p h) (sat_cons (step101 p h) (sat_cons (step30 p h) (sat_cons (step13 p h) (sat_cons (step25 p h) (sat_cons (step11 p h) (sat_cons (step424 p h) (sat_cons (step418 p h) (sat_cons (step426 p h) (sat_cons (step422 p h) (sat_cons (step431 p h) (sat_cons (step466 p h) (sat_cons (step547 p h) (sat_cons (step666 p h) (sat_cons (step650 p h) (sat_cons (step636 p h) (sat_cons (step639 p h) (sat_cons (step631 p h) (sat_cons (step610 p h) (sat_cons (step628 p h) (sat_cons (step629 p h) (sat_cons (step597 p h) (sat_cons (step626 p h) (sat_cons (step624 p h) (sat_cons (step625 p h) (sat_cons (step173 p h) (sat_cons (step171 p h) (sat_cons (step172 p h) (sat_cons (step166 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c716 : List Lit := [(1507, true)]
theorem step716 (p : Nat → Bool) (h : Constraints p) : clause p c716 = true :=
  Snake9.LocalRup.prove_clause [c162, c636, c639, c632, c608, c620, c603, c617, c601, c161] c716 (by decide) p (sat_cons (step162 p h) (sat_cons (step636 p h) (sat_cons (step639 p h) (sat_cons (step632 p h) (sat_cons (step608 p h) (sat_cons (step620 p h) (sat_cons (step603 p h) (sat_cons (step617 p h) (sat_cons (step601 p h) (sat_cons (step161 p h) (sat_nil p)))))))))))
def c717 : List Lit := [(1521, true)]
theorem step717 (p : Nat → Bool) (h : Constraints p) : clause p c717 = true :=
  Snake9.LocalRup.prove_clause [c716, c708, c650] c717 (by decide) p (sat_cons (step716 p h) (sat_cons (step708 p h) (sat_cons (step650 p h) (sat_nil p))))
def c718 : List Lit := [(1419, false)]
theorem step718 (p : Nat → Bool) (h : Constraints p) : clause p c718 = true :=
  Snake9.LocalRup.prove_clause [c717, c667, c666] c718 (by decide) p (sat_cons (step717 p h) (sat_cons (step667 p h) (sat_cons (step666 p h) (sat_nil p))))
def c719 : List Lit := [(241, true), (1330, true)]
theorem step719 (p : Nat → Bool) (h : Constraints p) : clause p c719 = true :=
  Snake9.LocalRup.prove_clause [c672, c176, c177, c179, c178, c175, c251, c253, c247, c248, c236, c237, c246, c243, c235, c233, c245, c240, c241, c230, c231, c4, c15, c20, c17, c23, c30, c25, c27, c424, c10, c426, c12, c431, c7, c422, c418] c719 (by decide) p (sat_cons (step672 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_cons (step179 p h) (sat_cons (step178 p h) (sat_cons (step175 p h) (sat_cons (step251 p h) (sat_cons (step253 p h) (sat_cons (step247 p h) (sat_cons (step248 p h) (sat_cons (step236 p h) (sat_cons (step237 p h) (sat_cons (step246 p h) (sat_cons (step243 p h) (sat_cons (step235 p h) (sat_cons (step233 p h) (sat_cons (step245 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step230 p h) (sat_cons (step231 p h) (sat_cons (step4 p h) (sat_cons (step15 p h) (sat_cons (step20 p h) (sat_cons (step17 p h) (sat_cons (step23 p h) (sat_cons (step30 p h) (sat_cons (step25 p h) (sat_cons (step27 p h) (sat_cons (step424 p h) (sat_cons (step10 p h) (sat_cons (step426 p h) (sat_cons (step12 p h) (sat_cons (step431 p h) (sat_cons (step7 p h) (sat_cons (step422 p h) (sat_cons (step418 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c720 : List Lit := [(111, true), (239, true), (5, true), (112, true), (155, true), (166, true), (168, true), (172, true), (173, true), (175, true), (178, true), (180, true), (181, true), (183, true), (186, true), (188, true), (189, true), (196, true), (200, true), (203, true), (206, true), (207, true), (209, true), (214, true), (215, true), (216, true), (170, true), (191, true), (194, true), (197, true), (205, true), (212, true), (144, true), (147, true), (152, true), (154, true), (158, true), (160, true), (162, true), (137, true), (140, true), (143, true), (124, true), (128, true), (129, true), (131, true), (134, true), (135, true), (123, true), (149, true)]
theorem step720 (p : Nat → Bool) (h : Constraints p) : clause p c720 = true :=
  Snake9.LocalRup.prove_clause [c672, c176, c177, c178, c179, c248, c243, c241, c240, c247, c246, c245, c4, c700, c15, c8, c20, c9, c17, c27, c23, c25, c30] c720 (by decide) p (sat_cons (step672 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_cons (step178 p h) (sat_cons (step179 p h) (sat_cons (step248 p h) (sat_cons (step243 p h) (sat_cons (step241 p h) (sat_cons (step240 p h) (sat_cons (step247 p h) (sat_cons (step246 p h) (sat_cons (step245 p h) (sat_cons (step4 p h) (sat_cons (step700 p h) (sat_cons (step15 p h) (sat_cons (step8 p h) (sat_cons (step20 p h) (sat_cons (step9 p h) (sat_cons (step17 p h) (sat_cons (step27 p h) (sat_cons (step23 p h) (sat_cons (step25 p h) (sat_cons (step30 p h) (sat_nil p))))))))))))))))))))))))
def c721 : List Lit := [(239, true), (5, true), (112, true), (155, true), (166, true), (168, true), (172, true), (173, true), (175, true), (178, true), (180, true), (181, true), (183, true), (186, true), (188, true), (189, true), (196, true), (200, true), (203, true), (206, true), (207, true), (209, true), (214, true), (215, true), (216, true), (170, true), (191, true), (194, true), (197, true), (205, true), (212, true), (144, true), (147, true), (152, true), (154, true), (158, true), (160, true), (162, true), (137, true), (140, true), (143, true), (124, true), (128, true), (129, true), (131, true), (134, true), (135, true), (123, true), (149, true)]
theorem step721 (p : Nat → Bool) (h : Constraints p) : clause p c721 = true :=
  Snake9.LocalRup.prove_clause [c672, c176, c692, c177, c178, c179, c247, c248, c246, c243, c245, c240, c241, c720, c2, c231, c3, c233, c14, c238, c19, c235, c16, c11, c22, c28, c29, c26] c721 (by decide) p (sat_cons (step672 p h) (sat_cons (step176 p h) (sat_cons (step692 p h) (sat_cons (step177 p h) (sat_cons (step178 p h) (sat_cons (step179 p h) (sat_cons (step247 p h) (sat_cons (step248 p h) (sat_cons (step246 p h) (sat_cons (step243 p h) (sat_cons (step245 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step720 p h) (sat_cons (step2 p h) (sat_cons (step231 p h) (sat_cons (step3 p h) (sat_cons (step233 p h) (sat_cons (step14 p h) (sat_cons (step238 p h) (sat_cons (step19 p h) (sat_cons (step235 p h) (sat_cons (step16 p h) (sat_cons (step11 p h) (sat_cons (step22 p h) (sat_cons (step28 p h) (sat_cons (step29 p h) (sat_cons (step26 p h) (sat_nil p)))))))))))))))))))))))))))))
def c722 : List Lit := [(10, true), (1321, true), (7, true)]
theorem step722 (p : Nat → Bool) (h : Constraints p) : clause p c722 = true :=
  Snake9.LocalRup.prove_clause [c179, c29, c424, c21] c722 (by decide) p (sat_cons (step179 p h) (sat_cons (step29 p h) (sat_cons (step424 p h) (sat_cons (step21 p h) (sat_nil p)))))
def c723 : List Lit := [(8, true), (1324, true), (11, true)]
theorem step723 (p : Nat → Bool) (h : Constraints p) : clause p c723 = true :=
  Snake9.LocalRup.prove_clause [c177, c179, c691, c17, c426, c722, c26, c24, c245, c30, c246, c23, c249, c240, c243] c723 (by decide) p (sat_cons (step177 p h) (sat_cons (step179 p h) (sat_cons (step691 p h) (sat_cons (step17 p h) (sat_cons (step426 p h) (sat_cons (step722 p h) (sat_cons (step26 p h) (sat_cons (step24 p h) (sat_cons (step245 p h) (sat_cons (step30 p h) (sat_cons (step246 p h) (sat_cons (step23 p h) (sat_cons (step249 p h) (sat_cons (step240 p h) (sat_cons (step243 p h) (sat_nil p))))))))))))))))
def c724 : List Lit := [(1388, true), (1330, true), (149, true), (1380, true)]
theorem step724 (p : Nat → Bool) (h : Constraints p) : clause p c724 = true :=
  Snake9.TreeRup.prove_clause [c681, c677, c415, c674, c175, c686, c178, c672, c176, c698, c177, c691, c179, c719, c274, c318, c413, c410, c368, c341, c326, c322, c321, c325, c324, c323, c339, c336, c328, c327, c335, c334, c331, c333, c332, c366, c364, c354, c344, c343, c352, c350, c346, c345, c349, c348, c363, c362, c356, c355, c361, c360, c357, c359, c358, c408, c406, c385, c374, c372, c371, c384, c382, c381, c378, c380, c379, c405, c404, c394, c389, c388, c387, c393, c392, c391, c403, c402, c396, c395, c401, c400, c399, c398, c329, c375, c370, c373, c383, c377, c390, c397, c319, c313, c291, c289, c282, c281, c288, c287, c284, c312, c311, c301, c295, c294, c300, c299, c296, c310, c309, c303, c302, c308, c307, c304, c306, c305, c293, c280, c277, c279, c278, c283, c275, c273, c263, c257, c256, c262, c261, c260, c259, c272, c271, c265, c264, c270, c269, c266, c268, c267, c258, c502, c503, c500, c713, c98, c490, c113, c101, c5, c13, c721, c254, c236, c237, c235, c233, c11, c231, c28, c418, c4, c422, c15, c431, c723, c20, c18, c241, c242, c16, c243, c22, c249, c29, c246, c26, c245] c724 (by decide) p (sat_cons (step681 p h) (sat_cons (step677 p h) (sat_cons (step415 p h) (sat_cons (step674 p h) (sat_cons (step175 p h) (sat_cons (step686 p h) (sat_cons (step178 p h) (sat_cons (step672 p h) (sat_cons (step176 p h) (sat_cons (step698 p h) (sat_cons (step177 p h) (sat_cons (step691 p h) (sat_cons (step179 p h) (sat_cons (step719 p h) (sat_cons (step274 p h) (sat_cons (step318 p h) (sat_cons (step413 p h) (sat_cons (step410 p h) (sat_cons (step368 p h) (sat_cons (step341 p h) (sat_cons (step326 p h) (sat_cons (step322 p h) (sat_cons (step321 p h) (sat_cons (step325 p h) (sat_cons (step324 p h) (sat_cons (step323 p h) (sat_cons (step339 p h) (sat_cons (step336 p h) (sat_cons (step328 p h) (sat_cons (step327 p h) (sat_cons (step335 p h) (sat_cons (step334 p h) (sat_cons (step331 p h) (sat_cons (step333 p h) (sat_cons (step332 p h) (sat_cons (step366 p h) (sat_cons (step364 p h) (sat_cons (step354 p h) (sat_cons (step344 p h) (sat_cons (step343 p h) (sat_cons (step352 p h) (sat_cons (step350 p h) (sat_cons (step346 p h) (sat_cons (step345 p h) (sat_cons (step349 p h) (sat_cons (step348 p h) (sat_cons (step363 p h) (sat_cons (step362 p h) (sat_cons (step356 p h) (sat_cons (step355 p h) (sat_cons (step361 p h) (sat_cons (step360 p h) (sat_cons (step357 p h) (sat_cons (step359 p h) (sat_cons (step358 p h) (sat_cons (step408 p h) (sat_cons (step406 p h) (sat_cons (step385 p h) (sat_cons (step374 p h) (sat_cons (step372 p h) (sat_cons (step371 p h) (sat_cons (step384 p h) (sat_cons (step382 p h) (sat_cons (step381 p h) (sat_cons (step378 p h) (sat_cons (step380 p h) (sat_cons (step379 p h) (sat_cons (step405 p h) (sat_cons (step404 p h) (sat_cons (step394 p h) (sat_cons (step389 p h) (sat_cons (step388 p h) (sat_cons (step387 p h) (sat_cons (step393 p h) (sat_cons (step392 p h) (sat_cons (step391 p h) (sat_cons (step403 p h) (sat_cons (step402 p h) (sat_cons (step396 p h) (sat_cons (step395 p h) (sat_cons (step401 p h) (sat_cons (step400 p h) (sat_cons (step399 p h) (sat_cons (step398 p h) (sat_cons (step329 p h) (sat_cons (step375 p h) (sat_cons (step370 p h) (sat_cons (step373 p h) (sat_cons (step383 p h) (sat_cons (step377 p h) (sat_cons (step390 p h) (sat_cons (step397 p h) (sat_cons (step319 p h) (sat_cons (step313 p h) (sat_cons (step291 p h) (sat_cons (step289 p h) (sat_cons (step282 p h) (sat_cons (step281 p h) (sat_cons (step288 p h) (sat_cons (step287 p h) (sat_cons (step284 p h) (sat_cons (step312 p h) (sat_cons (step311 p h) (sat_cons (step301 p h) (sat_cons (step295 p h) (sat_cons (step294 p h) (sat_cons (step300 p h) (sat_cons (step299 p h) (sat_cons (step296 p h) (sat_cons (step310 p h) (sat_cons (step309 p h) (sat_cons (step303 p h) (sat_cons (step302 p h) (sat_cons (step308 p h) (sat_cons (step307 p h) (sat_cons (step304 p h) (sat_cons (step306 p h) (sat_cons (step305 p h) (sat_cons (step293 p h) (sat_cons (step280 p h) (sat_cons (step277 p h) (sat_cons (step279 p h) (sat_cons (step278 p h) (sat_cons (step283 p h) (sat_cons (step275 p h) (sat_cons (step273 p h) (sat_cons (step263 p h) (sat_cons (step257 p h) (sat_cons (step256 p h) (sat_cons (step262 p h) (sat_cons (step261 p h) (sat_cons (step260 p h) (sat_cons (step259 p h) (sat_cons (step272 p h) (sat_cons (step271 p h) (sat_cons (step265 p h) (sat_cons (step264 p h) (sat_cons (step270 p h) (sat_cons (step269 p h) (sat_cons (step266 p h) (sat_cons (step268 p h) (sat_cons (step267 p h) (sat_cons (step258 p h) (sat_cons (step502 p h) (sat_cons (step503 p h) (sat_cons (step500 p h) (sat_cons (step713 p h) (sat_cons (step98 p h) (sat_cons (step490 p h) (sat_cons (step113 p h) (sat_cons (step101 p h) (sat_cons (step5 p h) (sat_cons (step13 p h) (sat_cons (step721 p h) (sat_cons (step254 p h) (sat_cons (step236 p h) (sat_cons (step237 p h) (sat_cons (step235 p h) (sat_cons (step233 p h) (sat_cons (step11 p h) (sat_cons (step231 p h) (sat_cons (step28 p h) (sat_cons (step418 p h) (sat_cons (step4 p h) (sat_cons (step422 p h) (sat_cons (step15 p h) (sat_cons (step431 p h) (sat_cons (step723 p h) (sat_cons (step20 p h) (sat_cons (step18 p h) (sat_cons (step241 p h) (sat_cons (step242 p h) (sat_cons (step16 p h) (sat_cons (step243 p h) (sat_cons (step22 p h) (sat_cons (step249 p h) (sat_cons (step29 p h) (sat_cons (step246 p h) (sat_cons (step26 p h) (sat_cons (step245 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c725 : List Lit := [(1400, false), (1393, true), (31, false)]
theorem step725 (p : Nat → Bool) (h : Constraints p) : clause p c725 = true :=
  Snake9.LocalRup.prove_clause [c718, c709, c677, c512, c492, c715, c88, c547, c466, c719, c274, c319, c312, c311, c300, c298, c724, c297, c509, c100, c491, c489] c725 (by decide) p (sat_cons (step718 p h) (sat_cons (step709 p h) (sat_cons (step677 p h) (sat_cons (step512 p h) (sat_cons (step492 p h) (sat_cons (step715 p h) (sat_cons (step88 p h) (sat_cons (step547 p h) (sat_cons (step466 p h) (sat_cons (step719 p h) (sat_cons (step274 p h) (sat_cons (step319 p h) (sat_cons (step312 p h) (sat_cons (step311 p h) (sat_cons (step300 p h) (sat_cons (step298 p h) (sat_cons (step724 p h) (sat_cons (step297 p h) (sat_cons (step509 p h) (sat_cons (step100 p h) (sat_cons (step491 p h) (sat_cons (step489 p h) (sat_nil p)))))))))))))))))))))))
def c726 : List Lit := [(1373, true)]
theorem step726 (p : Nat → Bool) (h : Constraints p) : clause p c726 = true :=
  Snake9.LocalRup.prove_clause [c482, c484, c711, c470, c467] c726 (by decide) p (sat_cons (step482 p h) (sat_cons (step484 p h) (sat_cons (step711 p h) (sat_cons (step470 p h) (sat_cons (step467 p h) (sat_nil p))))))
def c727 : List Lit := [(1400, true)]
theorem step727 (p : Nat → Bool) (h : Constraints p) : clause p c727 = true :=
  Snake9.LocalRup.prove_clause [c726, c701, c520] c727 (by decide) p (sat_cons (step726 p h) (sat_cons (step701 p h) (sat_cons (step520 p h) (sat_nil p))))
def c728 : List Lit := [(1401, true)]
theorem step728 (p : Nat → Bool) (h : Constraints p) : clause p c728 = true :=
  Snake9.LocalRup.prove_clause [c701, c726, c727, c526, c714, c521, c725] c728 (by decide) p (sat_cons (step701 p h) (sat_cons (step726 p h) (sat_cons (step727 p h) (sat_cons (step526 p h) (sat_cons (step714 p h) (sat_cons (step521 p h) (sat_cons (step725 p h) (sat_nil p))))))))
def c729 : List Lit := [(1357, false)]
theorem step729 (p : Nat → Bool) (h : Constraints p) : clause p c729 = true :=
  Snake9.LocalRup.prove_clause [c727, c718, c547] c729 (by decide) p (sat_cons (step727 p h) (sat_cons (step718 p h) (sat_cons (step547 p h) (sat_nil p))))
def c730 : List Lit := [(1414, true)]
theorem step730 (p : Nat → Bool) (h : Constraints p) : clause p c730 = true :=
  Snake9.LocalRup.prove_clause [c728, c710, c532] c730 (by decide) p (sat_cons (step728 p h) (sat_cons (step710 p h) (sat_cons (step532 p h) (sat_nil p))))
def c731 : List Lit := [(1330, false)]
theorem step731 (p : Nat → Bool) (h : Constraints p) : clause p c731 = true :=
  Snake9.LocalRup.prove_clause [c729, c709, c466] c731 (by decide) p (sat_cons (step729 p h) (sat_cons (step709 p h) (sat_cons (step466 p h) (sat_nil p))))
def c732 : List Lit := [(1526, false)]
theorem step732 (p : Nat → Bool) (h : Constraints p) : clause p c732 = true :=
  Snake9.LocalRup.prove_clause [c730, c667, c661] c732 (by decide) p (sat_cons (step730 p h) (sat_cons (step667 p h) (sat_cons (step661 p h) (sat_nil p))))
def c733 : List Lit := [(241, true)]
theorem step733 (p : Nat → Bool) (h : Constraints p) : clause p c733 = true :=
  Snake9.LocalRup.prove_clause [c731, c719] c733 (by decide) p (sat_cons (step731 p h) (sat_cons (step719 p h) (sat_nil p)))
def c734 : List Lit := [(269, true)]
theorem step734 (p : Nat → Bool) (h : Constraints p) : clause p c734 = true :=
  Snake9.LocalRup.prove_clause [c733, c274] c734 (by decide) p (sat_cons (step733 p h) (sat_cons (step274 p h) (sat_nil p)))
def c735 : List Lit := [(267, false)]
theorem step735 (p : Nat → Bool) (h : Constraints p) : clause p c735 = true :=
  Snake9.LocalRup.prove_clause [c733, c681, c275] c735 (by decide) p (sat_cons (step733 p h) (sat_cons (step681 p h) (sat_cons (step275 p h) (sat_nil p))))
end B112E201
