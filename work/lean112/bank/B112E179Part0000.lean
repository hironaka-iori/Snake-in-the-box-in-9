import B112E179Inputs
namespace B112E179
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c586 : List Lit := [(54, true)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true :=
  Snake9.LocalRup.prove_clause [c83, c82] c586 (by decide) p (sat_cons (step83 p h) (sat_cons (step82 p h) (sat_nil p)))
def c587 : List Lit := [(78, false)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true :=
  Snake9.LocalRup.prove_clause [c185, c121] c587 (by decide) p (sat_cons (step185 p h) (sat_cons (step121 p h) (sat_nil p)))
def c588 : List Lit := [(84, false)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true :=
  Snake9.LocalRup.prove_clause [c188, c125] c588 (by decide) p (sat_cons (step188 p h) (sat_cons (step125 p h) (sat_nil p)))
def c589 : List Lit := [(410, false)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true :=
  Snake9.LocalRup.prove_clause [c386, c383] c589 (by decide) p (sat_cons (step386 p h) (sat_cons (step383 p h) (sat_nil p)))
def c590 : List Lit := [(308, false)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true :=
  Snake9.LocalRup.prove_clause [c386, c385] c590 (by decide) p (sat_cons (step386 p h) (sat_cons (step385 p h) (sat_nil p)))
def c591 : List Lit := [(408, false)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true :=
  Snake9.LocalRup.prove_clause [c589, c379] c591 (by decide) p (sat_cons (step589 p h) (sat_cons (step379 p h) (sat_nil p)))
def c592 : List Lit := [(358, false)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true :=
  Snake9.LocalRup.prove_clause [c589, c382] c592 (by decide) p (sat_cons (step589 p h) (sat_cons (step382 p h) (sat_nil p)))
def c593 : List Lit := [(306, false)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true :=
  Snake9.LocalRup.prove_clause [c590, c287] c593 (by decide) p (sat_cons (step590 p h) (sat_cons (step287 p h) (sat_nil p)))
def c594 : List Lit := [(256, false)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true :=
  Snake9.LocalRup.prove_clause [c590, c290] c594 (by decide) p (sat_cons (step590 p h) (sat_cons (step290 p h) (sat_nil p)))
def c595 : List Lit := [(406, false)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true :=
  Snake9.LocalRup.prove_clause [c591, c374] c595 (by decide) p (sat_cons (step591 p h) (sat_cons (step374 p h) (sat_nil p)))
def c596 : List Lit := [(382, false)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true :=
  Snake9.LocalRup.prove_clause [c591, c377] c596 (by decide) p (sat_cons (step591 p h) (sat_cons (step377 p h) (sat_nil p)))
def c597 : List Lit := [(356, false)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true :=
  Snake9.LocalRup.prove_clause [c592, c333] c597 (by decide) p (sat_cons (step592 p h) (sat_cons (step333 p h) (sat_nil p)))
def c598 : List Lit := [(332, false)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true :=
  Snake9.LocalRup.prove_clause [c592, c336] c598 (by decide) p (sat_cons (step592 p h) (sat_cons (step336 p h) (sat_nil p)))
def c599 : List Lit := [(304, false)]
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true :=
  Snake9.LocalRup.prove_clause [c593, c282] c599 (by decide) p (sat_cons (step593 p h) (sat_cons (step282 p h) (sat_nil p)))
def c600 : List Lit := [(280, false)]
theorem step600 (p : Nat → Bool) (h : Constraints p) : clause p c600 = true :=
  Snake9.LocalRup.prove_clause [c593, c285] c600 (by decide) p (sat_cons (step593 p h) (sat_cons (step285 p h) (sat_nil p)))
def c601 : List Lit := [(254, false)]
theorem step601 (p : Nat → Bool) (h : Constraints p) : clause p c601 = true :=
  Snake9.LocalRup.prove_clause [c594, c241] c601 (by decide) p (sat_cons (step594 p h) (sat_cons (step241 p h) (sat_nil p)))
def c602 : List Lit := [(230, false)]
theorem step602 (p : Nat → Bool) (h : Constraints p) : clause p c602 = true :=
  Snake9.LocalRup.prove_clause [c594, c244] c602 (by decide) p (sat_cons (step594 p h) (sat_cons (step244 p h) (sat_nil p)))
def c603 : List Lit := [(392, false)]
theorem step603 (p : Nat → Bool) (h : Constraints p) : clause p c603 = true :=
  Snake9.LocalRup.prove_clause [c595, c372] c603 (by decide) p (sat_cons (step595 p h) (sat_cons (step372 p h) (sat_nil p)))
def c604 : List Lit := [(368, false)]
theorem step604 (p : Nat → Bool) (h : Constraints p) : clause p c604 = true :=
  Snake9.LocalRup.prove_clause [c596, c354] c604 (by decide) p (sat_cons (step596 p h) (sat_cons (step354 p h) (sat_nil p)))
def c605 : List Lit := [(342, false)]
theorem step605 (p : Nat → Bool) (h : Constraints p) : clause p c605 = true :=
  Snake9.LocalRup.prove_clause [c597, c331] c605 (by decide) p (sat_cons (step597 p h) (sat_cons (step331 p h) (sat_nil p)))
def c606 : List Lit := [(330, false)]
theorem step606 (p : Nat → Bool) (h : Constraints p) : clause p c606 = true :=
  Snake9.LocalRup.prove_clause [c598, c311] c606 (by decide) p (sat_cons (step598 p h) (sat_cons (step311 p h) (sat_nil p)))
def c607 : List Lit := [(318, false)]
theorem step607 (p : Nat → Bool) (h : Constraints p) : clause p c607 = true :=
  Snake9.LocalRup.prove_clause [c598, c314] c607 (by decide) p (sat_cons (step598 p h) (sat_cons (step314 p h) (sat_nil p)))
def c608 : List Lit := [(290, false)]
theorem step608 (p : Nat → Bool) (h : Constraints p) : clause p c608 = true :=
  Snake9.LocalRup.prove_clause [c599, c280] c608 (by decide) p (sat_cons (step599 p h) (sat_cons (step280 p h) (sat_nil p)))
def c609 : List Lit := [(278, false)]
theorem step609 (p : Nat → Bool) (h : Constraints p) : clause p c609 = true :=
  Snake9.LocalRup.prove_clause [c600, c260] c609 (by decide) p (sat_cons (step600 p h) (sat_cons (step260 p h) (sat_nil p)))
def c610 : List Lit := [(252, false)]
theorem step610 (p : Nat → Bool) (h : Constraints p) : clause p c610 = true :=
  Snake9.LocalRup.prove_clause [c601, c238] c610 (by decide) p (sat_cons (step601 p h) (sat_cons (step238 p h) (sat_nil p)))
def c611 : List Lit := [(228, false)]
theorem step611 (p : Nat → Bool) (h : Constraints p) : clause p c611 = true :=
  Snake9.LocalRup.prove_clause [c602, c216] c611 (by decide) p (sat_cons (step602 p h) (sat_cons (step216 p h) (sat_nil p)))
def c612 : List Lit := [(218, false)]
theorem step612 (p : Nat → Bool) (h : Constraints p) : clause p c612 = true :=
  Snake9.LocalRup.prove_clause [c602, c219] c612 (by decide) p (sat_cons (step602 p h) (sat_cons (step219 p h) (sat_nil p)))
def c613 : List Lit := [(386, false)]
theorem step613 (p : Nat → Bool) (h : Constraints p) : clause p c613 = true :=
  Snake9.LocalRup.prove_clause [c603, c362] c613 (by decide) p (sat_cons (step603 p h) (sat_cons (step362 p h) (sat_nil p)))
def c614 : List Lit := [(362, false)]
theorem step614 (p : Nat → Bool) (h : Constraints p) : clause p c614 = true :=
  Snake9.LocalRup.prove_clause [c604, c344] c614 (by decide) p (sat_cons (step604 p h) (sat_cons (step344 p h) (sat_nil p)))
def c615 : List Lit := [(322, false)]
theorem step615 (p : Nat → Bool) (h : Constraints p) : clause p c615 = true :=
  Snake9.LocalRup.prove_clause [c606, c309] c615 (by decide) p (sat_cons (step606 p h) (sat_cons (step309 p h) (sat_nil p)))
def c616 : List Lit := [(288, false)]
theorem step616 (p : Nat → Bool) (h : Constraints p) : clause p c616 = true :=
  Snake9.LocalRup.prove_clause [c608, c272] c616 (by decide) p (sat_cons (step608 p h) (sat_cons (step272 p h) (sat_nil p)))
def c617 : List Lit := [(250, false)]
theorem step617 (p : Nat → Bool) (h : Constraints p) : clause p c617 = true :=
  Snake9.LocalRup.prove_clause [c610, c235] c617 (by decide) p (sat_cons (step610 p h) (sat_cons (step235 p h) (sat_nil p)))
def c618 : List Lit := [(360, false)]
theorem step618 (p : Nat → Bool) (h : Constraints p) : clause p c618 = true :=
  Snake9.LocalRup.prove_clause [c614, c341] c618 (by decide) p (sat_cons (step614 p h) (sat_cons (step341 p h) (sat_nil p)))
def c619 : List Lit := [(320, false)]
theorem step619 (p : Nat → Bool) (h : Constraints p) : clause p c619 = true :=
  Snake9.LocalRup.prove_clause [c615, c304] c619 (by decide) p (sat_cons (step615 p h) (sat_cons (step304 p h) (sat_nil p)))
def c620 : List Lit := [(286, false)]
theorem step620 (p : Nat → Bool) (h : Constraints p) : clause p c620 = true :=
  Snake9.LocalRup.prove_clause [c616, c269] c620 (by decide) p (sat_cons (step616 p h) (sat_cons (step269 p h) (sat_nil p)))
def c621 : List Lit := [(106, true), (110, true), (111, true), (112, true), (114, true), (116, true), (118, true), (121, true), (124, true), (125, true), (126, true), (128, true), (130, true), (133, true), (136, true), (138, true), (139, true), (141, true), (145, true), (146, true), (147, true), (148, true), (152, true), (153, true), (156, true), (157, true), (158, true), (162, true), (164, true), (165, true), (167, true), (171, true), (173, true), (174, true), (175, true), (179, true), (181, true), (183, true), (184, true), (185, true), (189, true), (191, true), (194, true), (196, true), (197, true), (199, true), (203, true), (204, true), (205, true), (206, true)]
theorem step621 (p : Nat → Bool) (h : Constraints p) : clause p c621 = true :=
  Snake9.LocalRup.prove_clause [c146, c147, c148, c149, c150, c151, c152, c153, c154, c155, c156, c157, c158, c159, c160, c161, c162, c163, c164, c165, c166, c167, c168, c169, c170, c171, c172, c173, c174, c175, c176, c177, c178, c179, c180, c181, c182, c183, c184, c185, c186, c187, c188, c189, c190, c191, c192, c193, c194, c195, c196, c197, c198, c387] c621 (by decide) p (sat_cons (step146 p h) (sat_cons (step147 p h) (sat_cons (step148 p h) (sat_cons (step149 p h) (sat_cons (step150 p h) (sat_cons (step151 p h) (sat_cons (step152 p h) (sat_cons (step153 p h) (sat_cons (step154 p h) (sat_cons (step155 p h) (sat_cons (step156 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step159 p h) (sat_cons (step160 p h) (sat_cons (step161 p h) (sat_cons (step162 p h) (sat_cons (step163 p h) (sat_cons (step164 p h) (sat_cons (step165 p h) (sat_cons (step166 p h) (sat_cons (step167 p h) (sat_cons (step168 p h) (sat_cons (step169 p h) (sat_cons (step170 p h) (sat_cons (step171 p h) (sat_cons (step172 p h) (sat_cons (step173 p h) (sat_cons (step174 p h) (sat_cons (step175 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_cons (step178 p h) (sat_cons (step179 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step182 p h) (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step186 p h) (sat_cons (step187 p h) (sat_cons (step188 p h) (sat_cons (step189 p h) (sat_cons (step190 p h) (sat_cons (step191 p h) (sat_cons (step192 p h) (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step195 p h) (sat_cons (step196 p h) (sat_cons (step197 p h) (sat_cons (step198 p h) (sat_cons (step387 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c622 : List Lit := [(1267, true)]
theorem step622 (p : Nat → Bool) (h : Constraints p) : clause p c622 = true :=
  Snake9.LocalRup.prove_clause [c429, c431, c426, c428, c418, c420, c424, c415, c416, c34, c39, c44, c46] c622 (by decide) p (sat_cons (step429 p h) (sat_cons (step431 p h) (sat_cons (step426 p h) (sat_cons (step428 p h) (sat_cons (step418 p h) (sat_cons (step420 p h) (sat_cons (step424 p h) (sat_cons (step415 p h) (sat_cons (step416 p h) (sat_cons (step34 p h) (sat_cons (step39 p h) (sat_cons (step44 p h) (sat_cons (step46 p h) (sat_nil p))))))))))))))
def c623 : List Lit := [(1273, true)]
theorem step623 (p : Nat → Bool) (h : Constraints p) : clause p c623 = true :=
  Snake9.LocalRup.prove_clause [c622, c436] c623 (by decide) p (sat_cons (step622 p h) (sat_cons (step436 p h) (sat_nil p)))
def c624 : List Lit := [(1365, true)]
theorem step624 (p : Nat → Bool) (h : Constraints p) : clause p c624 = true :=
  Snake9.LocalRup.prove_clause [c519, c521, c517, c511, c512, c509, c510, c106, c118, c112] c624 (by decide) p (sat_cons (step519 p h) (sat_cons (step521 p h) (sat_cons (step517 p h) (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step509 p h) (sat_cons (step510 p h) (sat_cons (step106 p h) (sat_cons (step118 p h) (sat_cons (step112 p h) (sat_nil p)))))))))))
def c625 : List Lit := [(1371, true)]
theorem step625 (p : Nat → Bool) (h : Constraints p) : clause p c625 = true :=
  Snake9.LocalRup.prove_clause [c624, c525] c625 (by decide) p (sat_cons (step624 p h) (sat_cons (step525 p h) (sat_nil p)))
def c626 : List Lit := [(79, false), (81, false), (80, false)]
theorem step626 (p : Nat → Bool) (h : Constraints p) : clause p c626 = true :=
  Snake9.LocalRup.prove_clause [c618, c124, c123, c122, c339] c626 (by decide) p (sat_cons (step618 p h) (sat_cons (step124 p h) (sat_cons (step123 p h) (sat_cons (step122 p h) (sat_cons (step339 p h) (sat_nil p))))))
def c627 : List Lit := [(1383, true)]
theorem step627 (p : Nat → Bool) (h : Constraints p) : clause p c627 = true :=
  Snake9.LocalRup.prove_clause [c535, c536, c533, c534, c626] c627 (by decide) p (sat_cons (step535 p h) (sat_cons (step536 p h) (sat_cons (step533 p h) (sat_cons (step534 p h) (sat_cons (step626 p h) (sat_nil p))))))
def c628 : List Lit := [(1391, true)]
theorem step628 (p : Nat → Bool) (h : Constraints p) : clause p c628 = true :=
  Snake9.LocalRup.prove_clause [c627, c544] c628 (by decide) p (sat_cons (step627 p h) (sat_cons (step544 p h) (sat_nil p)))
def c629 : List Lit := [(1312, true)]
theorem step629 (p : Nat → Bool) (h : Constraints p) : clause p c629 = true :=
  Snake9.LocalRup.prove_clause [c620, c476, c478, c474, c468, c469, c471, c466, c467, c68, c72, c71, c70, c267] c629 (by decide) p (sat_cons (step620 p h) (sat_cons (step476 p h) (sat_cons (step478 p h) (sat_cons (step474 p h) (sat_cons (step468 p h) (sat_cons (step469 p h) (sat_cons (step471 p h) (sat_cons (step466 p h) (sat_cons (step467 p h) (sat_cons (step68 p h) (sat_cons (step72 p h) (sat_cons (step71 p h) (sat_cons (step70 p h) (sat_cons (step267 p h) (sat_nil p)))))))))))))))
def c630 : List Lit := [(1319, true)]
theorem step630 (p : Nat → Bool) (h : Constraints p) : clause p c630 = true :=
  Snake9.LocalRup.prove_clause [c629, c480] c630 (by decide) p (sat_cons (step629 p h) (sat_cons (step480 p h) (sat_nil p)))
def c631 : List Lit := [(1331, true)]
theorem step631 (p : Nat → Bool) (h : Constraints p) : clause p c631 = true :=
  Snake9.LocalRup.prove_clause [c623, c629, c630, c622, c609, c485, c482, c487, c460, c462, c439, c456, c450, c404, c453, c454, c448, c399, c401, c66, c396, c54, c24, c58, c63, c251, c252, c258, c255] c631 (by decide) p (sat_cons (step623 p h) (sat_cons (step629 p h) (sat_cons (step630 p h) (sat_cons (step622 p h) (sat_cons (step609 p h) (sat_cons (step485 p h) (sat_cons (step482 p h) (sat_cons (step487 p h) (sat_cons (step460 p h) (sat_cons (step462 p h) (sat_cons (step439 p h) (sat_cons (step456 p h) (sat_cons (step450 p h) (sat_cons (step404 p h) (sat_cons (step453 p h) (sat_cons (step454 p h) (sat_cons (step448 p h) (sat_cons (step399 p h) (sat_cons (step401 p h) (sat_cons (step66 p h) (sat_cons (step396 p h) (sat_cons (step54 p h) (sat_cons (step24 p h) (sat_cons (step58 p h) (sat_cons (step63 p h) (sat_cons (step251 p h) (sat_cons (step252 p h) (sat_cons (step258 p h) (sat_cons (step255 p h) (sat_nil p))))))))))))))))))))))))))))))
def c632 : List Lit := [(1433, false)]
theorem step632 (p : Nat → Bool) (h : Constraints p) : clause p c632 = true :=
  Snake9.LocalRup.prove_clause [c631, c583, c578] c632 (by decide) p (sat_cons (step631 p h) (sat_cons (step583 p h) (sat_cons (step578 p h) (sat_nil p))))
def c633 : List Lit := [(57, true), (58, false), (61, false), (62, true)]
theorem step633 (p : Nat → Bool) (h : Constraints p) : clause p c633 = true :=
  Snake9.LocalRup.prove_clause [c598, c97, c89, c300, c295, c303, c296, c308, c297, c313] c633 (by decide) p (sat_cons (step598 p h) (sat_cons (step97 p h) (sat_cons (step89 p h) (sat_cons (step300 p h) (sat_cons (step295 p h) (sat_cons (step303 p h) (sat_cons (step296 p h) (sat_cons (step308 p h) (sat_cons (step297 p h) (sat_cons (step313 p h) (sat_nil p)))))))))))
def c634 : List Lit := [(1410, true), (85, false), (196, true)]
theorem step634 (p : Nat → Bool) (h : Constraints p) : clause p c634 = true :=
  Snake9.LocalRup.prove_clause [c558, c559, c557, c550, c552, c136, c137] c634 (by decide) p (sat_cons (step558 p h) (sat_cons (step559 p h) (sat_cons (step557 p h) (sat_cons (step550 p h) (sat_cons (step552 p h) (sat_cons (step136 p h) (sat_cons (step137 p h) (sat_nil p))))))))
def c635 : List Lit := [(1419, true), (74, false), (85, false), (1410, false), (329, false)]
theorem step635 (p : Nat → Bool) (h : Constraints p) : clause p c635 = true :=
  Snake9.LocalRup.prove_clause [c589, c586, c173, c172, c598, c171, c170, c386, c628, c627, c310, c334, c380, c384, c286, c281, c278, c277, c276, c274, c313, c298, c294, c293, c292, c291, c81, c84, c80, c78, c79, c77, c275, c74, c73, c76, c381, c375, c352, c351, c346, c345, c373, c370, c360, c357, c563, c564, c561, c545, c540, c538, c132, c130, c126, c548, c137, c551] c635 (by decide) p (sat_cons (step589 p h) (sat_cons (step586 p h) (sat_cons (step173 p h) (sat_cons (step172 p h) (sat_cons (step598 p h) (sat_cons (step171 p h) (sat_cons (step170 p h) (sat_cons (step386 p h) (sat_cons (step628 p h) (sat_cons (step627 p h) (sat_cons (step310 p h) (sat_cons (step334 p h) (sat_cons (step380 p h) (sat_cons (step384 p h) (sat_cons (step286 p h) (sat_cons (step281 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step276 p h) (sat_cons (step274 p h) (sat_cons (step313 p h) (sat_cons (step298 p h) (sat_cons (step294 p h) (sat_cons (step293 p h) (sat_cons (step292 p h) (sat_cons (step291 p h) (sat_cons (step81 p h) (sat_cons (step84 p h) (sat_cons (step80 p h) (sat_cons (step78 p h) (sat_cons (step79 p h) (sat_cons (step77 p h) (sat_cons (step275 p h) (sat_cons (step74 p h) (sat_cons (step73 p h) (sat_cons (step76 p h) (sat_cons (step381 p h) (sat_cons (step375 p h) (sat_cons (step352 p h) (sat_cons (step351 p h) (sat_cons (step346 p h) (sat_cons (step345 p h) (sat_cons (step373 p h) (sat_cons (step370 p h) (sat_cons (step360 p h) (sat_cons (step357 p h) (sat_cons (step563 p h) (sat_cons (step564 p h) (sat_cons (step561 p h) (sat_cons (step545 p h) (sat_cons (step540 p h) (sat_cons (step538 p h) (sat_cons (step132 p h) (sat_cons (step130 p h) (sat_cons (step126 p h) (sat_cons (step548 p h) (sat_cons (step137 p h) (sat_cons (step551 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c636 : List Lit := [(1410, false), (1419, true), (329, false)]
theorem step636 (p : Nat → Bool) (h : Constraints p) : clause p c636 = true :=
  Snake9.LocalRup.prove_clause [c589, c586, c173, c172, c598, c171, c170, c386, c628, c627, c588, c563, c561, c310, c334, c380, c384, c286, c281, c278, c277, c276, c274, c313, c298, c294, c293, c292, c291, c81, c84, c80, c78, c79, c77, c275, c74, c73, c76, c381, c375, c352, c351, c347, c564, c545, c540, c542, c538, c635, c130, c127, c548, c549, c551, c560, c136, c557, c552] c636 (by decide) p (sat_cons (step589 p h) (sat_cons (step586 p h) (sat_cons (step173 p h) (sat_cons (step172 p h) (sat_cons (step598 p h) (sat_cons (step171 p h) (sat_cons (step170 p h) (sat_cons (step386 p h) (sat_cons (step628 p h) (sat_cons (step627 p h) (sat_cons (step588 p h) (sat_cons (step563 p h) (sat_cons (step561 p h) (sat_cons (step310 p h) (sat_cons (step334 p h) (sat_cons (step380 p h) (sat_cons (step384 p h) (sat_cons (step286 p h) (sat_cons (step281 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step276 p h) (sat_cons (step274 p h) (sat_cons (step313 p h) (sat_cons (step298 p h) (sat_cons (step294 p h) (sat_cons (step293 p h) (sat_cons (step292 p h) (sat_cons (step291 p h) (sat_cons (step81 p h) (sat_cons (step84 p h) (sat_cons (step80 p h) (sat_cons (step78 p h) (sat_cons (step79 p h) (sat_cons (step77 p h) (sat_cons (step275 p h) (sat_cons (step74 p h) (sat_cons (step73 p h) (sat_cons (step76 p h) (sat_cons (step381 p h) (sat_cons (step375 p h) (sat_cons (step352 p h) (sat_cons (step351 p h) (sat_cons (step347 p h) (sat_cons (step564 p h) (sat_cons (step545 p h) (sat_cons (step540 p h) (sat_cons (step542 p h) (sat_cons (step538 p h) (sat_cons (step635 p h) (sat_cons (step130 p h) (sat_cons (step127 p h) (sat_cons (step548 p h) (sat_cons (step549 p h) (sat_cons (step551 p h) (sat_cons (step560 p h) (sat_cons (step136 p h) (sat_cons (step557 p h) (sat_cons (step552 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c637 : List Lit := [(1419, true), (329, false)]
theorem step637 (p : Nat → Bool) (h : Constraints p) : clause p c637 = true :=
  Snake9.LocalRup.prove_clause [c589, c627, c190, c310, c334, c381, c375, c352, c351, c346, c345, c373, c370, c360, c357, c636, c566, c634, c546, c134, c543, c132, c538] c637 (by decide) p (sat_cons (step589 p h) (sat_cons (step627 p h) (sat_cons (step190 p h) (sat_cons (step310 p h) (sat_cons (step334 p h) (sat_cons (step381 p h) (sat_cons (step375 p h) (sat_cons (step352 p h) (sat_cons (step351 p h) (sat_cons (step346 p h) (sat_cons (step345 p h) (sat_cons (step373 p h) (sat_cons (step370 p h) (sat_cons (step360 p h) (sat_cons (step357 p h) (sat_cons (step636 p h) (sat_cons (step566 p h) (sat_cons (step634 p h) (sat_cons (step546 p h) (sat_cons (step134 p h) (sat_cons (step543 p h) (sat_cons (step132 p h) (sat_cons (step538 p h) (sat_nil p))))))))))))))))))))))))
def c638 : List Lit := [(1249, false), (1333, true), (106, true), (136, true), (8, true)]
theorem step638 (p : Nat → Bool) (h : Constraints p) : clause p c638 = true :=
  Snake9.LocalRup.prove_clause [c630, c622, c629, c146, c493, c444, c405, c442, c491, c482, c460, c462, c456, c450, c453, c448, c409, c393, c4, c454, c66, c2, c58, c55] c638 (by decide) p (sat_cons (step630 p h) (sat_cons (step622 p h) (sat_cons (step629 p h) (sat_cons (step146 p h) (sat_cons (step493 p h) (sat_cons (step444 p h) (sat_cons (step405 p h) (sat_cons (step442 p h) (sat_cons (step491 p h) (sat_cons (step482 p h) (sat_cons (step460 p h) (sat_cons (step462 p h) (sat_cons (step456 p h) (sat_cons (step450 p h) (sat_cons (step453 p h) (sat_cons (step448 p h) (sat_cons (step409 p h) (sat_cons (step393 p h) (sat_cons (step4 p h) (sat_cons (step454 p h) (sat_cons (step66 p h) (sat_cons (step2 p h) (sat_cons (step58 p h) (sat_cons (step55 p h) (sat_nil p)))))))))))))))))))))))))
def c639 : List Lit := [(329, false), (8, true), (61, false), (1372, false)]
theorem step639 (p : Nat → Bool) (h : Constraints p) : clause p c639 = true :=
  Snake9.TreeRup.prove_clause [c386, c583, c629, c622, c146, c401, c404, c439, c310, c334, c380, c384, c286, c288, c283, c240, c242, c259, c237, c215, c217, c257, c234, c212, c213, c204, c251, c231, c210, c208, c200, c230, c209, c199, c637, c572, c580, c638, c489, c402, c483, c396, c397, c461, c30, c457, c27, c454, c455, c456, c460, c463, c482, c450, c491, c448, c442, c440, c408, c433, c391, c393, c419, c388, c4, c14, c2, c5, c416, c417, c418, c64, c432, c58, c426, c33, c423, c48] c639 (by decide) p (sat_cons (step386 p h) (sat_cons (step583 p h) (sat_cons (step629 p h) (sat_cons (step622 p h) (sat_cons (step146 p h) (sat_cons (step401 p h) (sat_cons (step404 p h) (sat_cons (step439 p h) (sat_cons (step310 p h) (sat_cons (step334 p h) (sat_cons (step380 p h) (sat_cons (step384 p h) (sat_cons (step286 p h) (sat_cons (step288 p h) (sat_cons (step283 p h) (sat_cons (step240 p h) (sat_cons (step242 p h) (sat_cons (step259 p h) (sat_cons (step237 p h) (sat_cons (step215 p h) (sat_cons (step217 p h) (sat_cons (step257 p h) (sat_cons (step234 p h) (sat_cons (step212 p h) (sat_cons (step213 p h) (sat_cons (step204 p h) (sat_cons (step251 p h) (sat_cons (step231 p h) (sat_cons (step210 p h) (sat_cons (step208 p h) (sat_cons (step200 p h) (sat_cons (step230 p h) (sat_cons (step209 p h) (sat_cons (step199 p h) (sat_cons (step637 p h) (sat_cons (step572 p h) (sat_cons (step580 p h) (sat_cons (step638 p h) (sat_cons (step489 p h) (sat_cons (step402 p h) (sat_cons (step483 p h) (sat_cons (step396 p h) (sat_cons (step397 p h) (sat_cons (step461 p h) (sat_cons (step30 p h) (sat_cons (step457 p h) (sat_cons (step27 p h) (sat_cons (step454 p h) (sat_cons (step455 p h) (sat_cons (step456 p h) (sat_cons (step460 p h) (sat_cons (step463 p h) (sat_cons (step482 p h) (sat_cons (step450 p h) (sat_cons (step491 p h) (sat_cons (step448 p h) (sat_cons (step442 p h) (sat_cons (step440 p h) (sat_cons (step408 p h) (sat_cons (step433 p h) (sat_cons (step391 p h) (sat_cons (step393 p h) (sat_cons (step419 p h) (sat_cons (step388 p h) (sat_cons (step4 p h) (sat_cons (step14 p h) (sat_cons (step2 p h) (sat_cons (step5 p h) (sat_cons (step416 p h) (sat_cons (step417 p h) (sat_cons (step418 p h) (sat_cons (step64 p h) (sat_cons (step432 p h) (sat_cons (step58 p h) (sat_cons (step426 p h) (sat_cons (step33 p h) (sat_cons (step423 p h) (sat_cons (step48 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c640 : List Lit := [(1262, true), (16, true), (19, true)]
theorem step640 (p : Nat → Bool) (h : Constraints p) : clause p c640 = true :=
  Snake9.LocalRup.prove_clause [c617, c423, c424, c48, c45, c230, c229, c233] c640 (by decide) p (sat_cons (step617 p h) (sat_cons (step423 p h) (sat_cons (step424 p h) (sat_cons (step48 p h) (sat_cons (step45 p h) (sat_cons (step230 p h) (sat_cons (step229 p h) (sat_cons (step233 p h) (sat_nil p)))))))))
def c641 : List Lit := [(17, false), (138, true), (26, false), (34, false), (10, false)]
theorem step641 (p : Nat → Bool) (h : Constraints p) : clause p c641 = true :=
  Snake9.LocalRup.prove_clause [c38, c59, c61] c641 (by decide) p (sat_cons (step38 p h) (sat_cons (step59 p h) (sat_cons (step61 p h) (sat_nil p))))
def c642 : List Lit := [(1257, false), (1268, true)]
theorem step642 (p : Nat → Bool) (h : Constraints p) : clause p c642 = true :=
  Snake9.LocalRup.prove_clause [c433, c418, c432, c426, c428, c423, c424, c421, c41, c36, c640] c642 (by decide) p (sat_cons (step433 p h) (sat_cons (step418 p h) (sat_cons (step432 p h) (sat_cons (step426 p h) (sat_cons (step428 p h) (sat_cons (step423 p h) (sat_cons (step424 p h) (sat_cons (step421 p h) (sat_cons (step41 p h) (sat_cons (step36 p h) (sat_cons (step640 p h) (sat_nil p))))))))))))
def c643 : List Lit := [(1333, true), (1288, false), (7, false), (10, false), (1251, false)]
theorem step643 (p : Nat → Bool) (h : Constraints p) : clause p c643 = true :=
  Snake9.LocalRup.prove_clause [c622, c629, c590, c456, c460, c482, c439, c489, c491, c483, c440, c461, c463, c459, c451, c642, c416, c5, c641, c14, c249, c208, c250, c213, c257, c215, c259, c242, c283, c289] c643 (by decide) p (sat_cons (step622 p h) (sat_cons (step629 p h) (sat_cons (step590 p h) (sat_cons (step456 p h) (sat_cons (step460 p h) (sat_cons (step482 p h) (sat_cons (step439 p h) (sat_cons (step489 p h) (sat_cons (step491 p h) (sat_cons (step483 p h) (sat_cons (step440 p h) (sat_cons (step461 p h) (sat_cons (step463 p h) (sat_cons (step459 p h) (sat_cons (step451 p h) (sat_cons (step642 p h) (sat_cons (step416 p h) (sat_cons (step5 p h) (sat_cons (step641 p h) (sat_cons (step14 p h) (sat_cons (step249 p h) (sat_cons (step208 p h) (sat_cons (step250 p h) (sat_cons (step213 p h) (sat_cons (step257 p h) (sat_cons (step215 p h) (sat_cons (step259 p h) (sat_cons (step242 p h) (sat_cons (step283 p h) (sat_cons (step289 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c644 : List Lit := [(24, false), (14, false), (128, true), (17, false)]
theorem step644 (p : Nat → Bool) (h : Constraints p) : clause p c644 = true :=
  Snake9.LocalRup.prove_clause [c35, c48] c644 (by decide) p (sat_cons (step35 p h) (sat_cons (step48 p h) (sat_nil p)))
def c645 : List Lit := [(22, false), (20, false), (14, false), (126, true), (17, false)]
theorem step645 (p : Nat → Bool) (h : Constraints p) : clause p c645 = true :=
  Snake9.LocalRup.prove_clause [c40, c34, c45] c645 (by decide) p (sat_cons (step40 p h) (sat_cons (step34 p h) (sat_cons (step45 p h) (sat_nil p))))
def c646 : List Lit := [(85, true), (191, true), (1389, true)]
theorem step646 (p : Nat → Bool) (h : Constraints p) : clause p c646 = true :=
  Snake9.LocalRup.prove_clause [c190, c134, c543, c132, c538] c646 (by decide) p (sat_cons (step190 p h) (sat_cons (step134 p h) (sat_cons (step543 p h) (sat_cons (step132 p h) (sat_cons (step538 p h) (sat_nil p))))))
def c647 : List Lit := [(255, false), (1419, true)]
theorem step647 (p : Nat → Bool) (h : Constraints p) : clause p c647 = true :=
  Snake9.TreeRup.prove_clause [c628, c590, c386, c586, c173, c172, c171, c170, c627, c563, c561, c566, c546, c288, c289, c384, c281, c378, c380, c278, c373, c375, c334, c277, c370, c352, c312, c276, c360, c351, c298, c274, c275, c357, c346, c293, c294, c345, c291, c292, c81, c84, c80, c78, c79, c77, c74, c73, c76, c646, c634, c564, c545, c540, c538, c130, c548, c549, c551, c560, c137, c557, c136, c552] c647 (by decide) p (sat_cons (step628 p h) (sat_cons (step590 p h) (sat_cons (step386 p h) (sat_cons (step586 p h) (sat_cons (step173 p h) (sat_cons (step172 p h) (sat_cons (step171 p h) (sat_cons (step170 p h) (sat_cons (step627 p h) (sat_cons (step563 p h) (sat_cons (step561 p h) (sat_cons (step566 p h) (sat_cons (step546 p h) (sat_cons (step288 p h) (sat_cons (step289 p h) (sat_cons (step384 p h) (sat_cons (step281 p h) (sat_cons (step378 p h) (sat_cons (step380 p h) (sat_cons (step278 p h) (sat_cons (step373 p h) (sat_cons (step375 p h) (sat_cons (step334 p h) (sat_cons (step277 p h) (sat_cons (step370 p h) (sat_cons (step352 p h) (sat_cons (step312 p h) (sat_cons (step276 p h) (sat_cons (step360 p h) (sat_cons (step351 p h) (sat_cons (step298 p h) (sat_cons (step274 p h) (sat_cons (step275 p h) (sat_cons (step357 p h) (sat_cons (step346 p h) (sat_cons (step293 p h) (sat_cons (step294 p h) (sat_cons (step345 p h) (sat_cons (step291 p h) (sat_cons (step292 p h) (sat_cons (step81 p h) (sat_cons (step84 p h) (sat_cons (step80 p h) (sat_cons (step78 p h) (sat_cons (step79 p h) (sat_cons (step77 p h) (sat_cons (step74 p h) (sat_cons (step73 p h) (sat_cons (step76 p h) (sat_cons (step646 p h) (sat_cons (step634 p h) (sat_cons (step564 p h) (sat_cons (step545 p h) (sat_cons (step540 p h) (sat_cons (step538 p h) (sat_cons (step130 p h) (sat_cons (step548 p h) (sat_cons (step549 p h) (sat_cons (step551 p h) (sat_cons (step560 p h) (sat_cons (step137 p h) (sat_cons (step557 p h) (sat_cons (step136 p h) (sat_cons (step552 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c648 : List Lit := [(1406, true)]
theorem step648 (p : Nat → Bool) (h : Constraints p) : clause p c648 = true :=
  Snake9.LocalRup.prove_clause [c556, c557, c554, c555, c552, c553, c145, c142, c144] c648 (by decide) p (sat_cons (step556 p h) (sat_cons (step557 p h) (sat_cons (step554 p h) (sat_cons (step555 p h) (sat_cons (step552 p h) (sat_cons (step553 p h) (sat_cons (step145 p h) (sat_cons (step142 p h) (sat_cons (step144 p h) (sat_nil p))))))))))
def c649 : List Lit := [(1410, true)]
theorem step649 (p : Nat → Bool) (h : Constraints p) : clause p c649 = true :=
  Snake9.LocalRup.prove_clause [c648, c558] c649 (by decide) p (sat_cons (step648 p h) (sat_cons (step558 p h) (sat_nil p)))
end B112E179
