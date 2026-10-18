import B112E205Inputs
namespace B112E205
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c587 : List Lit := [(101, false), (68, false), (102, false)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true :=
  Snake9.LocalRup.prove_clause [c124, c139] c587 (by decide) p (sat_cons (step124 p h) (sat_cons (step139 p h) (sat_nil p)))
def c588 : List Lit := [(1, false)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true :=
  Snake9.LocalRup.prove_clause [c157, c1] c588 (by decide) p (sat_cons (step157 p h) (sat_cons (step1 p h) (sat_nil p)))
def c589 : List Lit := [(41, false)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true :=
  Snake9.LocalRup.prove_clause [c163, c32] c589 (by decide) p (sat_cons (step163 p h) (sat_cons (step32 p h) (sat_nil p)))
def c590 : List Lit := [(52, false)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true :=
  Snake9.LocalRup.prove_clause [c167, c46] c590 (by decide) p (sat_cons (step167 p h) (sat_cons (step46 p h) (sat_nil p)))
def c591 : List Lit := [(430, false)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true :=
  Snake9.LocalRup.prove_clause [c337, c334] c591 (by decide) p (sat_cons (step337 p h) (sat_cons (step334 p h) (sat_nil p)))
def c592 : List Lit := [(324, false)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true :=
  Snake9.LocalRup.prove_clause [c337, c336] c592 (by decide) p (sat_cons (step337 p h) (sat_cons (step336 p h) (sat_nil p)))
def c593 : List Lit := [(428, false)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true :=
  Snake9.LocalRup.prove_clause [c591, c330] c593 (by decide) p (sat_cons (step591 p h) (sat_cons (step330 p h) (sat_nil p)))
def c594 : List Lit := [(376, false)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true :=
  Snake9.LocalRup.prove_clause [c591, c333] c594 (by decide) p (sat_cons (step591 p h) (sat_cons (step333 p h) (sat_nil p)))
def c595 : List Lit := [(270, false)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true :=
  Snake9.LocalRup.prove_clause [c592, c237] c595 (by decide) p (sat_cons (step592 p h) (sat_cons (step237 p h) (sat_nil p)))
def c596 : List Lit := [(426, false)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true :=
  Snake9.LocalRup.prove_clause [c593, c325] c596 (by decide) p (sat_cons (step593 p h) (sat_cons (step325 p h) (sat_nil p)))
def c597 : List Lit := [(400, false)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true :=
  Snake9.LocalRup.prove_clause [c593, c328] c597 (by decide) p (sat_cons (step593 p h) (sat_cons (step328 p h) (sat_nil p)))
def c598 : List Lit := [(374, false)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true :=
  Snake9.LocalRup.prove_clause [c594, c270] c598 (by decide) p (sat_cons (step594 p h) (sat_cons (step270 p h) (sat_nil p)))
def c599 : List Lit := [(348, false)]
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true :=
  Snake9.LocalRup.prove_clause [c594, c272] c599 (by decide) p (sat_cons (step594 p h) (sat_cons (step272 p h) (sat_nil p)))
def c600 : List Lit := [(242, false)]
theorem step600 (p : Nat → Bool) (h : Constraints p) : clause p c600 = true :=
  Snake9.LocalRup.prove_clause [c595, c208] c600 (by decide) p (sat_cons (step595 p h) (sat_cons (step208 p h) (sat_nil p)))
def c601 : List Lit := [(424, false)]
theorem step601 (p : Nat → Bool) (h : Constraints p) : clause p c601 = true :=
  Snake9.LocalRup.prove_clause [c596, c320] c601 (by decide) p (sat_cons (step596 p h) (sat_cons (step320 p h) (sat_nil p)))
def c602 : List Lit := [(412, false)]
theorem step602 (p : Nat → Bool) (h : Constraints p) : clause p c602 = true :=
  Snake9.LocalRup.prove_clause [c596, c323] c602 (by decide) p (sat_cons (step596 p h) (sat_cons (step323 p h) (sat_nil p)))
def c603 : List Lit := [(386, false)]
theorem step603 (p : Nat → Bool) (h : Constraints p) : clause p c603 = true :=
  Snake9.LocalRup.prove_clause [c597, c292] c603 (by decide) p (sat_cons (step597 p h) (sat_cons (step292 p h) (sat_nil p)))
def c604 : List Lit := [(360, false)]
theorem step604 (p : Nat → Bool) (h : Constraints p) : clause p c604 = true :=
  Snake9.LocalRup.prove_clause [c598, c268] c604 (by decide) p (sat_cons (step598 p h) (sat_cons (step268 p h) (sat_nil p)))
def c605 : List Lit := [(228, false)]
theorem step605 (p : Nat → Bool) (h : Constraints p) : clause p c605 = true :=
  Snake9.LocalRup.prove_clause [c600, c198] c605 (by decide) p (sat_cons (step600 p h) (sat_cons (step198 p h) (sat_nil p)))
def c606 : List Lit := [(422, false)]
theorem step606 (p : Nat → Bool) (h : Constraints p) : clause p c606 = true :=
  Snake9.LocalRup.prove_clause [c601, c315] c606 (by decide) p (sat_cons (step601 p h) (sat_cons (step315 p h) (sat_nil p)))
def c607 : List Lit := [(416, false)]
theorem step607 (p : Nat → Bool) (h : Constraints p) : clause p c607 = true :=
  Snake9.LocalRup.prove_clause [c601, c318] c607 (by decide) p (sat_cons (step601 p h) (sat_cons (step318 p h) (sat_nil p)))
def c608 : List Lit := [(404, false)]
theorem step608 (p : Nat → Bool) (h : Constraints p) : clause p c608 = true :=
  Snake9.LocalRup.prove_clause [c602, c303] c608 (by decide) p (sat_cons (step602 p h) (sat_cons (step303 p h) (sat_nil p)))
def c609 : List Lit := [(384, false)]
theorem step609 (p : Nat → Bool) (h : Constraints p) : clause p c609 = true :=
  Snake9.LocalRup.prove_clause [c603, c279] c609 (by decide) p (sat_cons (step603 p h) (sat_cons (step279 p h) (sat_nil p)))
def c610 : List Lit := [(222, false)]
theorem step610 (p : Nat → Bool) (h : Constraints p) : clause p c610 = true :=
  Snake9.LocalRup.prove_clause [c605, c188] c610 (by decide) p (sat_cons (step605 p h) (sat_cons (step188 p h) (sat_nil p)))
def c611 : List Lit := [(418, false)]
theorem step611 (p : Nat → Bool) (h : Constraints p) : clause p c611 = true :=
  Snake9.LocalRup.prove_clause [c606, c313] c611 (by decide) p (sat_cons (step606 p h) (sat_cons (step313 p h) (sat_nil p)))
def c612 : List Lit := [(414, false)]
theorem step612 (p : Nat → Bool) (h : Constraints p) : clause p c612 = true :=
  Snake9.LocalRup.prove_clause [c607, c308] c612 (by decide) p (sat_cons (step607 p h) (sat_cons (step308 p h) (sat_nil p)))
def c613 : List Lit := [(402, false)]
theorem step613 (p : Nat → Bool) (h : Constraints p) : clause p c613 = true :=
  Snake9.LocalRup.prove_clause [c608, c297] c613 (by decide) p (sat_cons (step608 p h) (sat_cons (step297 p h) (sat_nil p)))
def c614 : List Lit := [(220, false)]
theorem step614 (p : Nat → Bool) (h : Constraints p) : clause p c614 = true :=
  Snake9.LocalRup.prove_clause [c610, c183] c614 (by decide) p (sat_cons (step610 p h) (sat_cons (step183 p h) (sat_nil p)))
def c615 : List Lit := [(1392, true)]
theorem step615 (p : Nat → Bool) (h : Constraints p) : clause p c615 = true :=
  Snake9.LocalRup.prove_clause [c411, c412, c406, c397, c400, c401, c395, c37, c42] c615 (by decide) p (sat_cons (step411 p h) (sat_cons (step412 p h) (sat_cons (step406 p h) (sat_cons (step397 p h) (sat_cons (step400 p h) (sat_cons (step401 p h) (sat_cons (step395 p h) (sat_cons (step37 p h) (sat_cons (step42 p h) (sat_nil p))))))))))
def c616 : List Lit := [(1373, true)]
theorem step616 (p : Nat → Bool) (h : Constraints p) : clause p c616 = true :=
  Snake9.LocalRup.prove_clause [c390, c392, c386, c388, c381, c383, c384, c378, c26, c29, c27] c616 (by decide) p (sat_cons (step390 p h) (sat_cons (step392 p h) (sat_cons (step386 p h) (sat_cons (step388 p h) (sat_cons (step381 p h) (sat_cons (step383 p h) (sat_cons (step384 p h) (sat_cons (step378 p h) (sat_cons (step26 p h) (sat_cons (step29 p h) (sat_cons (step27 p h) (sat_nil p))))))))))))
def c617 : List Lit := [(1400, true)]
theorem step617 (p : Nat → Bool) (h : Constraints p) : clause p c617 = true :=
  Snake9.LocalRup.prove_clause [c616, c615, c420] c617 (by decide) p (sat_cons (step616 p h) (sat_cons (step615 p h) (sat_cons (step420 p h) (sat_nil p))))
def c618 : List Lit := [(1344, true)]
theorem step618 (p : Nat → Bool) (h : Constraints p) : clause p c618 = true :=
  Snake9.LocalRup.prove_clause [c365, c367, c362, c363, c355, c356, c360, c361, c358, c353, c354, c22, c21, c18, c23] c618 (by decide) p (sat_cons (step365 p h) (sat_cons (step367 p h) (sat_cons (step362 p h) (sat_cons (step363 p h) (sat_cons (step355 p h) (sat_cons (step356 p h) (sat_cons (step360 p h) (sat_cons (step361 p h) (sat_cons (step358 p h) (sat_cons (step353 p h) (sat_cons (step354 p h) (sat_cons (step22 p h) (sat_cons (step21 p h) (sat_cons (step18 p h) (sat_cons (step23 p h) (sat_nil p))))))))))))))))
def c619 : List Lit := [(1351, true)]
theorem step619 (p : Nat → Bool) (h : Constraints p) : clause p c619 = true :=
  Snake9.LocalRup.prove_clause [c618, c370] c619 (by decide) p (sat_cons (step618 p h) (sat_cons (step370 p h) (sat_nil p)))
def c620 : List Lit := [(1414, true)]
theorem step620 (p : Nat → Bool) (h : Constraints p) : clause p c620 = true :=
  Snake9.LocalRup.prove_clause [c619, c617, c616, c618, c588, c614, c592, c427, c431, c421, c372, c416, c348, c398, c340, c342, c338, c2, c180, c181, c182, c3, c186, c197, c206, c236, c233, c232, c221, c219, c218, c38, c395, c396, c397, c39, c413, c403, c405] c620 (by decide) p (sat_cons (step619 p h) (sat_cons (step617 p h) (sat_cons (step616 p h) (sat_cons (step618 p h) (sat_cons (step588 p h) (sat_cons (step614 p h) (sat_cons (step592 p h) (sat_cons (step427 p h) (sat_cons (step431 p h) (sat_cons (step421 p h) (sat_cons (step372 p h) (sat_cons (step416 p h) (sat_cons (step348 p h) (sat_cons (step398 p h) (sat_cons (step340 p h) (sat_cons (step342 p h) (sat_cons (step338 p h) (sat_cons (step2 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step182 p h) (sat_cons (step3 p h) (sat_cons (step186 p h) (sat_cons (step197 p h) (sat_cons (step206 p h) (sat_cons (step236 p h) (sat_cons (step233 p h) (sat_cons (step232 p h) (sat_cons (step221 p h) (sat_cons (step219 p h) (sat_cons (step218 p h) (sat_cons (step38 p h) (sat_cons (step395 p h) (sat_cons (step396 p h) (sat_cons (step397 p h) (sat_cons (step39 p h) (sat_cons (step413 p h) (sat_cons (step403 p h) (sat_cons (step405 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c621 : List Lit := [(1526, false)]
theorem step621 (p : Nat → Bool) (h : Constraints p) : clause p c621 = true :=
  Snake9.LocalRup.prove_clause [c620, c584, c579] c621 (by decide) p (sat_cons (step620 p h) (sat_cons (step584 p h) (sat_cons (step579 p h) (sat_nil p))))
def c622 : List Lit := [(1448, true), (1473, true)]
theorem step622 (p : Nat → Bool) (h : Constraints p) : clause p c622 = true :=
  Snake9.LocalRup.prove_clause [c609, c503, c501, c505, c471, c473, c468, c465, c93, c109, c107, c112, c277, c274] c622 (by decide) p (sat_cons (step609 p h) (sat_cons (step503 p h) (sat_cons (step501 p h) (sat_cons (step505 p h) (sat_cons (step471 p h) (sat_cons (step473 p h) (sat_cons (step468 p h) (sat_cons (step465 p h) (sat_cons (step93 p h) (sat_cons (step109 p h) (sat_cons (step107 p h) (sat_cons (step112 p h) (sat_cons (step277 p h) (sat_cons (step274 p h) (sat_nil p)))))))))))))))
def c623 : List Lit := [(1448, false), (1460, true)]
theorem step623 (p : Nat → Bool) (h : Constraints p) : clause p c623 = true :=
  Snake9.LocalRup.prove_clause [c604, c488, c477, c480, c489, c462, c450, c452, c447, c441, c445, c446, c438, c64, c79, c78, c82, c251, c254, c252, c257, c260] c623 (by decide) p (sat_cons (step604 p h) (sat_cons (step488 p h) (sat_cons (step477 p h) (sat_cons (step480 p h) (sat_cons (step489 p h) (sat_cons (step462 p h) (sat_cons (step450 p h) (sat_cons (step452 p h) (sat_cons (step447 p h) (sat_cons (step441 p h) (sat_cons (step445 p h) (sat_cons (step446 p h) (sat_cons (step438 p h) (sat_cons (step64 p h) (sat_cons (step79 p h) (sat_cons (step78 p h) (sat_cons (step82 p h) (sat_cons (step251 p h) (sat_cons (step254 p h) (sat_cons (step252 p h) (sat_cons (step257 p h) (sat_cons (step260 p h) (sat_nil p)))))))))))))))))))))))
def c624 : List Lit := [(1433, true), (77, false)]
theorem step624 (p : Nat → Bool) (h : Constraints p) : clause p c624 = true :=
  Snake9.LocalRup.prove_clause [c599, c450, c452, c447, c441, c443, c445, c446, c438, c439, c64, c54, c70, c59, c243, c238, c244, c239, c246, c240, c250] c624 (by decide) p (sat_cons (step599 p h) (sat_cons (step450 p h) (sat_cons (step452 p h) (sat_cons (step447 p h) (sat_cons (step441 p h) (sat_cons (step443 p h) (sat_cons (step445 p h) (sat_cons (step446 p h) (sat_cons (step438 p h) (sat_cons (step439 p h) (sat_cons (step64 p h) (sat_cons (step54 p h) (sat_cons (step70 p h) (sat_cons (step59 p h) (sat_cons (step243 p h) (sat_cons (step238 p h) (sat_cons (step244 p h) (sat_cons (step239 p h) (sat_cons (step246 p h) (sat_cons (step240 p h) (sat_cons (step250 p h) (sat_nil p))))))))))))))))))))))
def c625 : List Lit := [(1425, true), (1428, true), (1460, true)]
theorem step625 (p : Nat → Bool) (h : Constraints p) : clause p c625 = true :=
  Snake9.LocalRup.prove_clause [c169, c446, c445, c623, c473, c466, c624, c489, c479, c460, c458, c462, c441, c443, c438, c439, c64, c79, c54, c75, c57, c71, c56] c625 (by decide) p (sat_cons (step169 p h) (sat_cons (step446 p h) (sat_cons (step445 p h) (sat_cons (step623 p h) (sat_cons (step473 p h) (sat_cons (step466 p h) (sat_cons (step624 p h) (sat_cons (step489 p h) (sat_cons (step479 p h) (sat_cons (step460 p h) (sat_cons (step458 p h) (sat_cons (step462 p h) (sat_cons (step441 p h) (sat_cons (step443 p h) (sat_cons (step438 p h) (sat_cons (step439 p h) (sat_cons (step64 p h) (sat_cons (step79 p h) (sat_cons (step54 p h) (sat_cons (step75 p h) (sat_cons (step57 p h) (sat_cons (step71 p h) (sat_cons (step56 p h) (sat_nil p))))))))))))))))))))))))
def c626 : List Lit := [(63, false), (1428, true), (1460, true)]
theorem step626 (p : Nat → Bool) (h : Constraints p) : clause p c626 = true :=
  Snake9.LocalRup.prove_clause [c124, c446, c445, c623, c473, c466, c624, c489, c479, c460, c458, c462, c465, c64, c79, c65, c75, c127, c74, c122] c626 (by decide) p (sat_cons (step124 p h) (sat_cons (step446 p h) (sat_cons (step445 p h) (sat_cons (step623 p h) (sat_cons (step473 p h) (sat_cons (step466 p h) (sat_cons (step624 p h) (sat_cons (step489 p h) (sat_cons (step479 p h) (sat_cons (step460 p h) (sat_cons (step458 p h) (sat_cons (step462 p h) (sat_cons (step465 p h) (sat_cons (step64 p h) (sat_cons (step79 p h) (sat_cons (step65 p h) (sat_cons (step75 p h) (sat_cons (step127 p h) (sat_cons (step74 p h) (sat_cons (step122 p h) (sat_nil p)))))))))))))))))))))
def c627 : List Lit := [(1430, true), (1460, true)]
theorem step627 (p : Nat → Bool) (h : Constraints p) : clause p c627 = true :=
  Snake9.LocalRup.prove_clause [c599, c623, c473, c466, c624, c489, c479, c460, c457, c493, c455, c442, c447, c448, c626, c438, c440, c444, c67, c54, c59, c62, c238, c241, c239, c247, c240, c250] c627 (by decide) p (sat_cons (step599 p h) (sat_cons (step623 p h) (sat_cons (step473 p h) (sat_cons (step466 p h) (sat_cons (step624 p h) (sat_cons (step489 p h) (sat_cons (step479 p h) (sat_cons (step460 p h) (sat_cons (step457 p h) (sat_cons (step493 p h) (sat_cons (step455 p h) (sat_cons (step442 p h) (sat_cons (step447 p h) (sat_cons (step448 p h) (sat_cons (step626 p h) (sat_cons (step438 p h) (sat_cons (step440 p h) (sat_cons (step444 p h) (sat_cons (step67 p h) (sat_cons (step54 p h) (sat_cons (step59 p h) (sat_cons (step62 p h) (sat_cons (step238 p h) (sat_cons (step241 p h) (sat_cons (step239 p h) (sat_cons (step247 p h) (sat_cons (step240 p h) (sat_cons (step250 p h) (sat_nil p)))))))))))))))))))))))))))))
def c628 : List Lit := [(1460, true)]
theorem step628 (p : Nat → Bool) (h : Constraints p) : clause p c628 = true :=
  Snake9.LocalRup.prove_clause [c599, c493, c451, c623, c473, c466, c624, c489, c479, c460, c457, c627, c453, c441, c443, c625, c439, c54, c449, c67, c59, c62, c238, c241, c239, c247, c240, c250] c628 (by decide) p (sat_cons (step599 p h) (sat_cons (step493 p h) (sat_cons (step451 p h) (sat_cons (step623 p h) (sat_cons (step473 p h) (sat_cons (step466 p h) (sat_cons (step624 p h) (sat_cons (step489 p h) (sat_cons (step479 p h) (sat_cons (step460 p h) (sat_cons (step457 p h) (sat_cons (step627 p h) (sat_cons (step453 p h) (sat_cons (step441 p h) (sat_cons (step443 p h) (sat_cons (step625 p h) (sat_cons (step439 p h) (sat_cons (step54 p h) (sat_cons (step449 p h) (sat_cons (step67 p h) (sat_cons (step59 p h) (sat_cons (step62 p h) (sat_cons (step238 p h) (sat_cons (step241 p h) (sat_cons (step239 p h) (sat_cons (step247 p h) (sat_cons (step240 p h) (sat_cons (step250 p h) (sat_nil p)))))))))))))))))))))))))))))
def c629 : List Lit := [(170, true), (56, true), (61, false)]
theorem step629 (p : Nat → Bool) (h : Constraints p) : clause p c629 = true :=
  Snake9.LocalRup.prove_clause [c170, c62, c63, c60, c586] c629 (by decide) p (sat_cons (step170 p h) (sat_cons (step62 p h) (sat_cons (step63 p h) (sat_cons (step60 p h) (sat_cons (step586 p h) (sat_nil p))))))
def c630 : List Lit := [(59, false), (77, false), (61, false)]
theorem step630 (p : Nat → Bool) (h : Constraints p) : clause p c630 = true :=
  Snake9.LocalRup.prove_clause [c599, c54, c59, c238, c239, c240, c250, c247, c241, c629] c630 (by decide) p (sat_cons (step599 p h) (sat_cons (step54 p h) (sat_cons (step59 p h) (sat_cons (step238 p h) (sat_cons (step239 p h) (sat_cons (step240 p h) (sat_cons (step250 p h) (sat_cons (step247 p h) (sat_cons (step241 p h) (sat_cons (step629 p h) (sat_nil p)))))))))))
def c631 : List Lit := [(241, true), (1326, true)]
theorem step631 (p : Nat → Bool) (h : Constraints p) : clause p c631 = true :=
  Snake9.LocalRup.prove_clause [c588, c159, c196, c197, c195, c186, c191, c182, c190, c180, c2, c9, c342, c11, c349, c346] c631 (by decide) p (sat_cons (step588 p h) (sat_cons (step159 p h) (sat_cons (step196 p h) (sat_cons (step197 p h) (sat_cons (step195 p h) (sat_cons (step186 p h) (sat_cons (step191 p h) (sat_cons (step182 p h) (sat_cons (step190 p h) (sat_cons (step180 p h) (sat_cons (step2 p h) (sat_cons (step9 p h) (sat_cons (step342 p h) (sat_cons (step11 p h) (sat_cons (step349 p h) (sat_cons (step346 p h) (sat_nil p)))))))))))))))))
def c632 : List Lit := [(1442, false), (79, true), (61, false), (1448, false), (1430, false), (1463, true)]
theorem step632 (p : Nat → Bool) (h : Constraints p) : clause p c632 = true :=
  Snake9.LocalRup.prove_clause [c450, c492, c484, c485, c496, c475, c453, c467, c443, c630] c632 (by decide) p (sat_cons (step450 p h) (sat_cons (step492 p h) (sat_cons (step484 p h) (sat_cons (step485 p h) (sat_cons (step496 p h) (sat_cons (step475 p h) (sat_cons (step453 p h) (sat_cons (step467 p h) (sat_cons (step443 p h) (sat_cons (step630 p h) (sat_nil p)))))))))))
def c633 : List Lit := [(71, true), (72, true), (183, true), (1443, true)]
theorem step633 (p : Nat → Bool) (h : Constraints p) : clause p c633 = true :=
  Snake9.LocalRup.prove_clause [c172, c173, c85, c90, c464, c87, c459] c633 (by decide) p (sat_cons (step172 p h) (sat_cons (step173 p h) (sat_cons (step85 p h) (sat_cons (step90 p h) (sat_cons (step464 p h) (sat_cons (step87 p h) (sat_cons (step459 p h) (sat_nil p))))))))
def c634 : List Lit := [(427, false), (1510, false), (1434, false), (65, false), (71, false), (74, false)]
theorem step634 (p : Nat → Bool) (h : Constraints p) : clause p c634 = true :=
  Snake9.LocalRup.prove_clause [c591, c337, c618, c617, c584, c329, c332, c335, c269, c235, c267, c206, c258, c631, c257, c373, c253, c254, c433, c81, c580, c86, c573, c83, c494, c458, c479, c460] c634 (by decide) p (sat_cons (step591 p h) (sat_cons (step337 p h) (sat_cons (step618 p h) (sat_cons (step617 p h) (sat_cons (step584 p h) (sat_cons (step329 p h) (sat_cons (step332 p h) (sat_cons (step335 p h) (sat_cons (step269 p h) (sat_cons (step235 p h) (sat_cons (step267 p h) (sat_cons (step206 p h) (sat_cons (step258 p h) (sat_cons (step631 p h) (sat_cons (step257 p h) (sat_cons (step373 p h) (sat_cons (step253 p h) (sat_cons (step254 p h) (sat_cons (step433 p h) (sat_cons (step81 p h) (sat_cons (step580 p h) (sat_cons (step86 p h) (sat_cons (step573 p h) (sat_cons (step83 p h) (sat_cons (step494 p h) (sat_cons (step458 p h) (sat_cons (step479 p h) (sat_cons (step460 p h) (sat_nil p)))))))))))))))))))))))))))))
def c635 : List Lit := [(1441, false), (1502, false), (1434, false), (1478, false)]
theorem step635 (p : Nat → Bool) (h : Constraints p) : clause p c635 = true :=
  Snake9.LocalRup.prove_clause [c621, c516, c559, c577, c495, c479, c480, c494, c622, c574, c520, c563] c635 (by decide) p (sat_cons (step621 p h) (sat_cons (step516 p h) (sat_cons (step559 p h) (sat_cons (step577 p h) (sat_cons (step495 p h) (sat_cons (step479 p h) (sat_cons (step480 p h) (sat_cons (step494 p h) (sat_cons (step622 p h) (sat_cons (step574 p h) (sat_cons (step520 p h) (sat_cons (step563 p h) (sat_nil p)))))))))))))
def c636 : List Lit := [(1490, true), (100, false), (101, true), (97, false)]
theorem step636 (p : Nat → Bool) (h : Constraints p) : clause p c636 = true :=
  Snake9.LocalRup.prove_clause [c527, c531, c533, c529, c138] c636 (by decide) p (sat_cons (step527 p h) (sat_cons (step531 p h) (sat_cons (step533 p h) (sat_cons (step529 p h) (sat_cons (step138 p h) (sat_nil p))))))
def c637 : List Lit := [(107, true), (1497, true), (103, false), (104, false)]
theorem step637 (p : Nat → Bool) (h : Constraints p) : clause p c637 = true :=
  Snake9.LocalRup.prove_clause [c542, c538, c540, c544, c144, c535] c637 (by decide) p (sat_cons (step542 p h) (sat_cons (step538 p h) (sat_cons (step540 p h) (sat_cons (step544 p h) (sat_cons (step144 p h) (sat_cons (step535 p h) (sat_nil p)))))))
def c638 : List Lit := [(1380, false), (42, true), (31, true), (149, true), (152, true), (1402, true)]
theorem step638 (p : Nat → Bool) (h : Constraints p) : clause p c638 = true :=
  Snake9.LocalRup.prove_clause [c616, c589, c164, c379, c381, c422, c419, c398, c399, c416, c33, c426, c35, c394, c393, c31, c382, c386, c380, c384, c29] c638 (by decide) p (sat_cons (step616 p h) (sat_cons (step589 p h) (sat_cons (step164 p h) (sat_cons (step379 p h) (sat_cons (step381 p h) (sat_cons (step422 p h) (sat_cons (step419 p h) (sat_cons (step398 p h) (sat_cons (step399 p h) (sat_cons (step416 p h) (sat_cons (step33 p h) (sat_cons (step426 p h) (sat_cons (step35 p h) (sat_cons (step394 p h) (sat_cons (step393 p h) (sat_cons (step31 p h) (sat_cons (step382 p h) (sat_cons (step386 p h) (sat_cons (step380 p h) (sat_cons (step384 p h) (sat_cons (step29 p h) (sat_nil p))))))))))))))))))))))
def c639 : List Lit := [(1448, true), (1502, false), (1461, false), (1452, false), (1430, false)]
theorem step639 (p : Nat → Bool) (h : Constraints p) : clause p c639 = true :=
  Snake9.TreeRup.prove_clause [c621, c584, c125, c619, c617, c618, c592, c337, c176, c178, c574, c563, c523, c471, c473, c622, c468, c465, c466, c519, c520, c560, c559, c511, c513, c577, c573, c508, c509, c498, c580, c123, c129, c456, c428, c433, c373, c631, c206, c235, c236, c335, c233, c234, c329, c232, c214, c324, c326, c221, c222, c213, c319, c321, c289, c290, c219, c220, c216, c211, c314, c316, c301, c287, c278, c280, c218, c217, c215, c210, c312, c307, c296, c285, c275, c273, c38, c309, c305, c294, c284, c274, c100, c133, c134, c126, c93, c140, c506, c146, c501, c111, c121, c636, c552, c637, c151, c147, c156, c149, c638, c396, c36, c52, c53, c444, c439] c639 (by decide) p (sat_cons (step621 p h) (sat_cons (step584 p h) (sat_cons (step125 p h) (sat_cons (step619 p h) (sat_cons (step617 p h) (sat_cons (step618 p h) (sat_cons (step592 p h) (sat_cons (step337 p h) (sat_cons (step176 p h) (sat_cons (step178 p h) (sat_cons (step574 p h) (sat_cons (step563 p h) (sat_cons (step523 p h) (sat_cons (step471 p h) (sat_cons (step473 p h) (sat_cons (step622 p h) (sat_cons (step468 p h) (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step519 p h) (sat_cons (step520 p h) (sat_cons (step560 p h) (sat_cons (step559 p h) (sat_cons (step511 p h) (sat_cons (step513 p h) (sat_cons (step577 p h) (sat_cons (step573 p h) (sat_cons (step508 p h) (sat_cons (step509 p h) (sat_cons (step498 p h) (sat_cons (step580 p h) (sat_cons (step123 p h) (sat_cons (step129 p h) (sat_cons (step456 p h) (sat_cons (step428 p h) (sat_cons (step433 p h) (sat_cons (step373 p h) (sat_cons (step631 p h) (sat_cons (step206 p h) (sat_cons (step235 p h) (sat_cons (step236 p h) (sat_cons (step335 p h) (sat_cons (step233 p h) (sat_cons (step234 p h) (sat_cons (step329 p h) (sat_cons (step232 p h) (sat_cons (step214 p h) (sat_cons (step324 p h) (sat_cons (step326 p h) (sat_cons (step221 p h) (sat_cons (step222 p h) (sat_cons (step213 p h) (sat_cons (step319 p h) (sat_cons (step321 p h) (sat_cons (step289 p h) (sat_cons (step290 p h) (sat_cons (step219 p h) (sat_cons (step220 p h) (sat_cons (step216 p h) (sat_cons (step211 p h) (sat_cons (step314 p h) (sat_cons (step316 p h) (sat_cons (step301 p h) (sat_cons (step287 p h) (sat_cons (step278 p h) (sat_cons (step280 p h) (sat_cons (step218 p h) (sat_cons (step217 p h) (sat_cons (step215 p h) (sat_cons (step210 p h) (sat_cons (step312 p h) (sat_cons (step307 p h) (sat_cons (step296 p h) (sat_cons (step285 p h) (sat_cons (step275 p h) (sat_cons (step273 p h) (sat_cons (step38 p h) (sat_cons (step309 p h) (sat_cons (step305 p h) (sat_cons (step294 p h) (sat_cons (step284 p h) (sat_cons (step274 p h) (sat_cons (step100 p h) (sat_cons (step133 p h) (sat_cons (step134 p h) (sat_cons (step126 p h) (sat_cons (step93 p h) (sat_cons (step140 p h) (sat_cons (step506 p h) (sat_cons (step146 p h) (sat_cons (step501 p h) (sat_cons (step111 p h) (sat_cons (step121 p h) (sat_cons (step636 p h) (sat_cons (step552 p h) (sat_cons (step637 p h) (sat_cons (step151 p h) (sat_cons (step147 p h) (sat_cons (step156 p h) (sat_cons (step149 p h) (sat_cons (step638 p h) (sat_cons (step396 p h) (sat_cons (step36 p h) (sat_cons (step52 p h) (sat_cons (step53 p h) (sat_cons (step444 p h) (sat_cons (step439 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c640 : List Lit := [(61, true), (1424, true), (1431, true), (65, true), (70, false), (173, true), (71, false)]
theorem step640 (p : Nat → Bool) (h : Constraints p) : clause p c640 = true :=
  Snake9.LocalRup.prove_clause [c170, c61, c440, c66, c79, c449, c445] c640 (by decide) p (sat_cons (step170 p h) (sat_cons (step61 p h) (sat_cons (step440 p h) (sat_cons (step66 p h) (sat_cons (step79 p h) (sat_cons (step449 p h) (sat_cons (step445 p h) (sat_nil p))))))))
def c641 : List Lit := [(1374, true), (39, false), (40, false), (31, true)]
theorem step641 (p : Nat → Bool) (h : Constraints p) : clause p c641 = true :=
  Snake9.LocalRup.prove_clause [c379, c381, c394, c393, c382, c386, c380, c384, c29] c641 (by decide) p (sat_cons (step379 p h) (sat_cons (step381 p h) (sat_cons (step394 p h) (sat_cons (step393 p h) (sat_cons (step382 p h) (sat_cons (step386 p h) (sat_cons (step380 p h) (sat_cons (step384 p h) (sat_cons (step29 p h) (sat_nil p))))))))))
def c642 : List Lit := [(3, true), (1318, true)]
theorem step642 (p : Nat → Bool) (h : Constraints p) : clause p c642 = true :=
  Snake9.LocalRup.prove_clause [c158, c588, c605, c341, c8, c338, c339, c343, c6, c2, c184, c180, c187, c182] c642 (by decide) p (sat_cons (step158 p h) (sat_cons (step588 p h) (sat_cons (step605 p h) (sat_cons (step341 p h) (sat_cons (step8 p h) (sat_cons (step338 p h) (sat_cons (step339 p h) (sat_cons (step343 p h) (sat_cons (step6 p h) (sat_cons (step2 p h) (sat_cons (step184 p h) (sat_cons (step180 p h) (sat_cons (step187 p h) (sat_cons (step182 p h) (sat_nil p)))))))))))))))
def c643 : List Lit := [(53, true), (1415, true)]
theorem step643 (p : Nat → Bool) (h : Constraints p) : clause p c643 = true :=
  Snake9.LocalRup.prove_clause [c617, c618, c592, c619, c616, c168, c428, c422, c433, c373, c631, c206, c236, c233, c232, c221, c219, c218, c38, c395, c397, c414, c231, c229, c228, c225, c49, c403, c44, c407, c400] c643 (by decide) p (sat_cons (step617 p h) (sat_cons (step618 p h) (sat_cons (step592 p h) (sat_cons (step619 p h) (sat_cons (step616 p h) (sat_cons (step168 p h) (sat_cons (step428 p h) (sat_cons (step422 p h) (sat_cons (step433 p h) (sat_cons (step373 p h) (sat_cons (step631 p h) (sat_cons (step206 p h) (sat_cons (step236 p h) (sat_cons (step233 p h) (sat_cons (step232 p h) (sat_cons (step221 p h) (sat_cons (step219 p h) (sat_cons (step218 p h) (sat_cons (step38 p h) (sat_cons (step395 p h) (sat_cons (step397 p h) (sat_cons (step414 p h) (sat_cons (step231 p h) (sat_cons (step229 p h) (sat_cons (step228 p h) (sat_cons (step225 p h) (sat_cons (step49 p h) (sat_cons (step403 p h) (sat_cons (step44 p h) (sat_cons (step407 p h) (sat_cons (step400 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c644 : List Lit := [(40, true), (1415, true)]
theorem step644 (p : Nat → Bool) (h : Constraints p) : clause p c644 = true :=
  Snake9.LocalRup.prove_clause [c590, c617, c618, c592, c619, c428, c433, c373, c631, c206, c236, c233, c232, c221, c219, c218, c38, c643, c351, c642, c231, c229, c227, c226, c48, c39, c396, c398, c416, c426, c391, c387, c234, c214, c213, c212, c209, c383, c386, c389, c393, c385, c381, c28, c378, c26] c644 (by decide) p (sat_cons (step590 p h) (sat_cons (step617 p h) (sat_cons (step618 p h) (sat_cons (step592 p h) (sat_cons (step619 p h) (sat_cons (step428 p h) (sat_cons (step433 p h) (sat_cons (step373 p h) (sat_cons (step631 p h) (sat_cons (step206 p h) (sat_cons (step236 p h) (sat_cons (step233 p h) (sat_cons (step232 p h) (sat_cons (step221 p h) (sat_cons (step219 p h) (sat_cons (step218 p h) (sat_cons (step38 p h) (sat_cons (step643 p h) (sat_cons (step351 p h) (sat_cons (step642 p h) (sat_cons (step231 p h) (sat_cons (step229 p h) (sat_cons (step227 p h) (sat_cons (step226 p h) (sat_cons (step48 p h) (sat_cons (step39 p h) (sat_cons (step396 p h) (sat_cons (step398 p h) (sat_cons (step416 p h) (sat_cons (step426 p h) (sat_cons (step391 p h) (sat_cons (step387 p h) (sat_cons (step234 p h) (sat_cons (step214 p h) (sat_cons (step213 p h) (sat_cons (step212 p h) (sat_cons (step209 p h) (sat_cons (step383 p h) (sat_cons (step386 p h) (sat_cons (step389 p h) (sat_cons (step393 p h) (sat_cons (step385 p h) (sat_cons (step381 p h) (sat_cons (step28 p h) (sat_cons (step378 p h) (sat_cons (step26 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c645 : List Lit := [(1415, true)]
theorem step645 (p : Nat → Bool) (h : Constraints p) : clause p c645 = true :=
  Snake9.LocalRup.prove_clause [c619, c617, c616, c618, c592, c590, c428, c433, c422, c373, c419, c351, c631, c206, c236, c233, c234, c231, c232, c214, c229, c221, c213, c227, c219, c211, c226, c218, c210, c38, c642, c643, c48, c39, c396, c398, c399, c416, c426, c644, c30, c31, c34, c641] c645 (by decide) p (sat_cons (step619 p h) (sat_cons (step617 p h) (sat_cons (step616 p h) (sat_cons (step618 p h) (sat_cons (step592 p h) (sat_cons (step590 p h) (sat_cons (step428 p h) (sat_cons (step433 p h) (sat_cons (step422 p h) (sat_cons (step373 p h) (sat_cons (step419 p h) (sat_cons (step351 p h) (sat_cons (step631 p h) (sat_cons (step206 p h) (sat_cons (step236 p h) (sat_cons (step233 p h) (sat_cons (step234 p h) (sat_cons (step231 p h) (sat_cons (step232 p h) (sat_cons (step214 p h) (sat_cons (step229 p h) (sat_cons (step221 p h) (sat_cons (step213 p h) (sat_cons (step227 p h) (sat_cons (step219 p h) (sat_cons (step211 p h) (sat_cons (step226 p h) (sat_cons (step218 p h) (sat_cons (step210 p h) (sat_cons (step38 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step48 p h) (sat_cons (step39 p h) (sat_cons (step396 p h) (sat_cons (step398 p h) (sat_cons (step399 p h) (sat_cons (step416 p h) (sat_cons (step426 p h) (sat_cons (step644 p h) (sat_cons (step30 p h) (sat_cons (step31 p h) (sat_cons (step34 p h) (sat_cons (step641 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c646 : List Lit := [(1525, false)]
theorem step646 (p : Nat → Bool) (h : Constraints p) : clause p c646 = true :=
  Snake9.LocalRup.prove_clause [c645, c584, c580] c646 (by decide) p (sat_cons (step645 p h) (sat_cons (step584 p h) (sat_cons (step580 p h) (sat_nil p))))
def c647 : List Lit := [(1374, true), (31, true)]
theorem step647 (p : Nat → Bool) (h : Constraints p) : clause p c647 = true :=
  Snake9.LocalRup.prove_clause [c379, c381, c394, c393, c382, c386, c388, c380, c383, c384, c26, c641, c27] c647 (by decide) p (sat_cons (step379 p h) (sat_cons (step381 p h) (sat_cons (step394 p h) (sat_cons (step393 p h) (sat_cons (step382 p h) (sat_cons (step386 p h) (sat_cons (step388 p h) (sat_cons (step380 p h) (sat_cons (step383 p h) (sat_cons (step384 p h) (sat_cons (step26 p h) (sat_cons (step641 p h) (sat_cons (step27 p h) (sat_nil p))))))))))))))
def c648 : List Lit := [(1374, false), (90, true), (87, false), (88, false), (85, false), (91, false), (1424, true), (1431, true), (1449, true), (1416, true), (1441, true)]
theorem step648 (p : Nat → Bool) (h : Constraints p) : clause p c648 = true :=
  Snake9.TreeRup.prove_clause [c615, c618, c595, c592, c337, c475, c460, c458, c457, c462, c425, c434, c373, c631, c206, c207, c235, c236, c204, c335, c233, c203, c329, c331, c232, c202, c326, c269, c271, c221, c201, c289, c290, c266, c267, c248, c219, c288, c278, c280, c265, c258, c246, c247, c218, c282, c275, c273, c263, c257, c245, c241, c38, c274, c262, c253, c254, c242, c112, c83, c81, c82, c109, c86, c465, c467, c640, c474, c629, c468, c469, c53, c100, c97, c396, c105, c96, c398, c113, c91, c92, c416, c354, c426, c355, c432, c371, c368, c362, c363, c361, c358, c24, c25, c20] c648 (by decide) p (sat_cons (step615 p h) (sat_cons (step618 p h) (sat_cons (step595 p h) (sat_cons (step592 p h) (sat_cons (step337 p h) (sat_cons (step475 p h) (sat_cons (step460 p h) (sat_cons (step458 p h) (sat_cons (step457 p h) (sat_cons (step462 p h) (sat_cons (step425 p h) (sat_cons (step434 p h) (sat_cons (step373 p h) (sat_cons (step631 p h) (sat_cons (step206 p h) (sat_cons (step207 p h) (sat_cons (step235 p h) (sat_cons (step236 p h) (sat_cons (step204 p h) (sat_cons (step335 p h) (sat_cons (step233 p h) (sat_cons (step203 p h) (sat_cons (step329 p h) (sat_cons (step331 p h) (sat_cons (step232 p h) (sat_cons (step202 p h) (sat_cons (step326 p h) (sat_cons (step269 p h) (sat_cons (step271 p h) (sat_cons (step221 p h) (sat_cons (step201 p h) (sat_cons (step289 p h) (sat_cons (step290 p h) (sat_cons (step266 p h) (sat_cons (step267 p h) (sat_cons (step248 p h) (sat_cons (step219 p h) (sat_cons (step288 p h) (sat_cons (step278 p h) (sat_cons (step280 p h) (sat_cons (step265 p h) (sat_cons (step258 p h) (sat_cons (step246 p h) (sat_cons (step247 p h) (sat_cons (step218 p h) (sat_cons (step282 p h) (sat_cons (step275 p h) (sat_cons (step273 p h) (sat_cons (step263 p h) (sat_cons (step257 p h) (sat_cons (step245 p h) (sat_cons (step241 p h) (sat_cons (step38 p h) (sat_cons (step274 p h) (sat_cons (step262 p h) (sat_cons (step253 p h) (sat_cons (step254 p h) (sat_cons (step242 p h) (sat_cons (step112 p h) (sat_cons (step83 p h) (sat_cons (step81 p h) (sat_cons (step82 p h) (sat_cons (step109 p h) (sat_cons (step86 p h) (sat_cons (step465 p h) (sat_cons (step467 p h) (sat_cons (step640 p h) (sat_cons (step474 p h) (sat_cons (step629 p h) (sat_cons (step468 p h) (sat_cons (step469 p h) (sat_cons (step53 p h) (sat_cons (step100 p h) (sat_cons (step97 p h) (sat_cons (step396 p h) (sat_cons (step105 p h) (sat_cons (step96 p h) (sat_cons (step398 p h) (sat_cons (step113 p h) (sat_cons (step91 p h) (sat_cons (step92 p h) (sat_cons (step416 p h) (sat_cons (step354 p h) (sat_cons (step426 p h) (sat_cons (step355 p h) (sat_cons (step432 p h) (sat_cons (step371 p h) (sat_cons (step368 p h) (sat_cons (step362 p h) (sat_cons (step363 p h) (sat_cons (step361 p h) (sat_cons (step358 p h) (sat_cons (step24 p h) (sat_cons (step25 p h) (sat_cons (step20 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c649 : List Lit := [(90, true), (87, false), (88, false), (85, false), (91, false), (1424, true), (1431, true), (1449, true), (1416, true), (1441, true)]
theorem step649 (p : Nat → Bool) (h : Constraints p) : clause p c649 = true :=
  Snake9.LocalRup.prove_clause [c597, c475, c648, c647, c121, c111, c110, c274, c109, c275, c465, c467, c278, c474, c291, c469, c287, c97, c286, c119, c283] c649 (by decide) p (sat_cons (step597 p h) (sat_cons (step475 p h) (sat_cons (step648 p h) (sat_cons (step647 p h) (sat_cons (step121 p h) (sat_cons (step111 p h) (sat_cons (step110 p h) (sat_cons (step274 p h) (sat_cons (step109 p h) (sat_cons (step275 p h) (sat_cons (step465 p h) (sat_cons (step467 p h) (sat_cons (step278 p h) (sat_cons (step474 p h) (sat_cons (step291 p h) (sat_cons (step469 p h) (sat_cons (step287 p h) (sat_cons (step97 p h) (sat_cons (step286 p h) (sat_cons (step119 p h) (sat_cons (step283 p h) (sat_nil p))))))))))))))))))))))
def c650 : List Lit := [(1502, false), (1452, false), (1441, true), (1425, false), (1430, false)]
theorem step650 (p : Nat → Bool) (h : Constraints p) : clause p c650 = true :=
  Snake9.LocalRup.prove_clause [c584, c646, c174, c453, c494, c573, c556, c572, c581, c576, c495, c498, c559, c478, c456, c454, c516, c519, c472, c442, c513, c503, c505, c500, c501, c649, c115, c101, c469, c470, c99, c474, c93, c465] c650 (by decide) p (sat_cons (step584 p h) (sat_cons (step646 p h) (sat_cons (step174 p h) (sat_cons (step453 p h) (sat_cons (step494 p h) (sat_cons (step573 p h) (sat_cons (step556 p h) (sat_cons (step572 p h) (sat_cons (step581 p h) (sat_cons (step576 p h) (sat_cons (step495 p h) (sat_cons (step498 p h) (sat_cons (step559 p h) (sat_cons (step478 p h) (sat_cons (step456 p h) (sat_cons (step454 p h) (sat_cons (step516 p h) (sat_cons (step519 p h) (sat_cons (step472 p h) (sat_cons (step442 p h) (sat_cons (step513 p h) (sat_cons (step503 p h) (sat_cons (step505 p h) (sat_cons (step500 p h) (sat_cons (step501 p h) (sat_cons (step649 p h) (sat_cons (step115 p h) (sat_cons (step101 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step99 p h) (sat_cons (step474 p h) (sat_cons (step93 p h) (sat_cons (step465 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
end B112E205
