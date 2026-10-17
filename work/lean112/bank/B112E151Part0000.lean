import B112E151Inputs
namespace B112E151
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c581 : List Lit := [(6, true)]
theorem step581 (p : Nat → Bool) (h : Constraints p) : clause p c581 = true :=
  Snake9.LocalRup.prove_clause [c11, c10] c581 (by decide) p (sat_cons (step11 p h) (sat_cons (step10 p h) (sat_nil p)))
def c582 : List Lit := [(1, false)]
theorem step582 (p : Nat → Bool) (h : Constraints p) : clause p c582 = true :=
  Snake9.LocalRup.prove_clause [c186, c1] c582 (by decide) p (sat_cons (step186 p h) (sat_cons (step1 p h) (sat_nil p)))
def c583 : List Lit := [(96, false)]
theorem step583 (p : Nat → Bool) (h : Constraints p) : clause p c583 = true :=
  Snake9.LocalRup.prove_clause [c218, c167] c583 (by decide) p (sat_cons (step218 p h) (sat_cons (step167 p h) (sat_nil p)))
def c584 : List Lit := [(98, false)]
theorem step584 (p : Nat → Bool) (h : Constraints p) : clause p c584 = true :=
  Snake9.LocalRup.prove_clause [c220, c171] c584 (by decide) p (sat_cons (step220 p h) (sat_cons (step171 p h) (sat_nil p)))
def c585 : List Lit := [(422, false)]
theorem step585 (p : Nat → Bool) (h : Constraints p) : clause p c585 = true :=
  Snake9.LocalRup.prove_clause [c315, c312] c585 (by decide) p (sat_cons (step315 p h) (sat_cons (step312 p h) (sat_nil p)))
def c586 : List Lit := [(318, false)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true :=
  Snake9.LocalRup.prove_clause [c315, c314] c586 (by decide) p (sat_cons (step315 p h) (sat_cons (step314 p h) (sat_nil p)))
def c587 : List Lit := [(420, false)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true :=
  Snake9.LocalRup.prove_clause [c585, c310] c587 (by decide) p (sat_cons (step585 p h) (sat_cons (step310 p h) (sat_nil p)))
def c588 : List Lit := [(264, false)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true :=
  Snake9.LocalRup.prove_clause [c586, c264] c588 (by decide) p (sat_cons (step586 p h) (sat_cons (step264 p h) (sat_nil p)))
def c589 : List Lit := [(392, false)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true :=
  Snake9.LocalRup.prove_clause [c587, c308] c589 (by decide) p (sat_cons (step587 p h) (sat_cons (step308 p h) (sat_nil p)))
def c590 : List Lit := [(238, false)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true :=
  Snake9.LocalRup.prove_clause [c588, c255] c590 (by decide) p (sat_cons (step588 p h) (sat_cons (step255 p h) (sat_nil p)))
def c591 : List Lit := [(378, false)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true :=
  Snake9.LocalRup.prove_clause [c589, c290] c591 (by decide) p (sat_cons (step589 p h) (sat_cons (step290 p h) (sat_nil p)))
def c592 : List Lit := [(224, false)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true :=
  Snake9.LocalRup.prove_clause [c590, c240] c592 (by decide) p (sat_cons (step590 p h) (sat_cons (step240 p h) (sat_nil p)))
def c593 : List Lit := [(729, true)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true :=
  Snake9.LocalRup.prove_clause [c582, c319] c593 (by decide) p (sat_cons (step582 p h) (sat_cons (step319 p h) (sat_nil p)))
def c594 : List Lit := [(727, false), (730, true)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true :=
  Snake9.LocalRup.prove_clause [c582, c320] c594 (by decide) p (sat_cons (step582 p h) (sat_cons (step320 p h) (sat_nil p)))
def c595 : List Lit := [(728, false), (731, true)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true :=
  Snake9.LocalRup.prove_clause [c582, c321] c595 (by decide) p (sat_cons (step582 p h) (sat_cons (step321 p h) (sat_nil p)))
def c596 : List Lit := [(737, true)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true :=
  Snake9.LocalRup.prove_clause [c593, c325] c596 (by decide) p (sat_cons (step593 p h) (sat_cons (step325 p h) (sat_nil p)))
def c597 : List Lit := [(734, false), (738, true)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true :=
  Snake9.LocalRup.prove_clause [c593, c326] c597 (by decide) p (sat_cons (step593 p h) (sat_cons (step326 p h) (sat_nil p)))
def c598 : List Lit := [(756, false), (764, true)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true :=
  Snake9.LocalRup.prove_clause [c596, c355] c598 (by decide) p (sat_cons (step596 p h) (sat_cons (step355 p h) (sat_nil p)))
def c599 : List Lit := [(757, false), (765, true)]
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true :=
  Snake9.LocalRup.prove_clause [c596, c356] c599 (by decide) p (sat_cons (step596 p h) (sat_cons (step356 p h) (sat_nil p)))
def c600 : List Lit := [(758, false), (766, true)]
theorem step600 (p : Nat → Bool) (h : Constraints p) : clause p c600 = true :=
  Snake9.LocalRup.prove_clause [c596, c357] c600 (by decide) p (sat_cons (step596 p h) (sat_cons (step357 p h) (sat_nil p)))
def c601 : List Lit := [(759, false), (767, true)]
theorem step601 (p : Nat → Bool) (h : Constraints p) : clause p c601 = true :=
  Snake9.LocalRup.prove_clause [c596, c358] c601 (by decide) p (sat_cons (step596 p h) (sat_cons (step358 p h) (sat_nil p)))
def c602 : List Lit := [(913, true)]
theorem step602 (p : Nat → Bool) (h : Constraints p) : clause p c602 = true :=
  Snake9.LocalRup.prove_clause [c584, c506] c602 (by decide) p (sat_cons (step584 p h) (sat_cons (step506 p h) (sat_nil p)))
def c603 : List Lit := [(97, true), (914, true)]
theorem step603 (p : Nat → Bool) (h : Constraints p) : clause p c603 = true :=
  Snake9.LocalRup.prove_clause [c584, c507] c603 (by decide) p (sat_cons (step584 p h) (sat_cons (step507 p h) (sat_nil p)))
def c604 : List Lit := [(916, true)]
theorem step604 (p : Nat → Bool) (h : Constraints p) : clause p c604 = true :=
  Snake9.LocalRup.prove_clause [c583, c602, c508] c604 (by decide) p (sat_cons (step583 p h) (sat_cons (step602 p h) (sat_cons (step508 p h) (sat_nil p))))
def c605 : List Lit := [(914, false), (917, true)]
theorem step605 (p : Nat → Bool) (h : Constraints p) : clause p c605 = true :=
  Snake9.LocalRup.prove_clause [c583, c509] c605 (by decide) p (sat_cons (step583 p h) (sat_cons (step509 p h) (sat_nil p)))
def c606 : List Lit := [(927, true)]
theorem step606 (p : Nat → Bool) (h : Constraints p) : clause p c606 = true :=
  Snake9.LocalRup.prove_clause [c604, c522] c606 (by decide) p (sat_cons (step604 p h) (sat_cons (step522 p h) (sat_nil p)))
def c607 : List Lit := [(922, false), (928, true)]
theorem step607 (p : Nat → Bool) (h : Constraints p) : clause p c607 = true :=
  Snake9.LocalRup.prove_clause [c604, c523] c607 (by decide) p (sat_cons (step604 p h) (sat_cons (step523 p h) (sat_nil p)))
def c608 : List Lit := [(923, false), (929, true)]
theorem step608 (p : Nat → Bool) (h : Constraints p) : clause p c608 = true :=
  Snake9.LocalRup.prove_clause [c604, c524] c608 (by decide) p (sat_cons (step604 p h) (sat_cons (step524 p h) (sat_nil p)))
def c609 : List Lit := [(924, false), (930, true)]
theorem step609 (p : Nat → Bool) (h : Constraints p) : clause p c609 = true :=
  Snake9.LocalRup.prove_clause [c604, c525] c609 (by decide) p (sat_cons (step604 p h) (sat_cons (step525 p h) (sat_nil p)))
def c610 : List Lit := [(925, false), (931, true)]
theorem step610 (p : Nat → Bool) (h : Constraints p) : clause p c610 = true :=
  Snake9.LocalRup.prove_clause [c604, c526] c610 (by decide) p (sat_cons (step604 p h) (sat_cons (step526 p h) (sat_nil p)))
def c611 : List Lit := [(907, false), (936, true)]
theorem step611 (p : Nat → Bool) (h : Constraints p) : clause p c611 = true :=
  Snake9.LocalRup.prove_clause [c606, c533] c611 (by decide) p (sat_cons (step606 p h) (sat_cons (step533 p h) (sat_nil p)))
def c612 : List Lit := [(908, false), (937, true)]
theorem step612 (p : Nat → Bool) (h : Constraints p) : clause p c612 = true :=
  Snake9.LocalRup.prove_clause [c606, c537] c612 (by decide) p (sat_cons (step606 p h) (sat_cons (step537 p h) (sat_nil p)))
def c613 : List Lit := [(909, false), (938, true)]
theorem step613 (p : Nat → Bool) (h : Constraints p) : clause p c613 = true :=
  Snake9.LocalRup.prove_clause [c606, c542] c613 (by decide) p (sat_cons (step606 p h) (sat_cons (step542 p h) (sat_nil p)))
def c614 : List Lit := [(910, false), (939, true)]
theorem step614 (p : Nat → Bool) (h : Constraints p) : clause p c614 = true :=
  Snake9.LocalRup.prove_clause [c606, c546] c614 (by decide) p (sat_cons (step606 p h) (sat_cons (step546 p h) (sat_nil p)))
def c615 : List Lit := [(756, true)]
theorem step615 (p : Nat → Bool) (h : Constraints p) : clause p c615 = true :=
  Snake9.LocalRup.prove_clause [c192, c347, c349, c343, c333, c337, c338, c330, c27, c24] c615 (by decide) p (sat_cons (step192 p h) (sat_cons (step347 p h) (sat_cons (step349 p h) (sat_cons (step343 p h) (sat_cons (step333 p h) (sat_cons (step337 p h) (sat_cons (step338 p h) (sat_cons (step330 p h) (sat_cons (step27 p h) (sat_cons (step24 p h) (sat_nil p)))))))))))
def c616 : List Lit := [(764, true)]
theorem step616 (p : Nat → Bool) (h : Constraints p) : clause p c616 = true :=
  Snake9.LocalRup.prove_clause [c615, c598] c616 (by decide) p (sat_cons (step615 p h) (sat_cons (step598 p h) (sat_nil p)))
def c617 : List Lit := [(785, true)]
theorem step617 (p : Nat → Bool) (h : Constraints p) : clause p c617 = true :=
  Snake9.LocalRup.prove_clause [c198, c370, c371, c369, c367, c44, c45, c573] c617 (by decide) p (sat_cons (step198 p h) (sat_cons (step370 p h) (sat_cons (step371 p h) (sat_cons (step369 p h) (sat_cons (step367 p h) (sat_cons (step44 p h) (sat_cons (step45 p h) (sat_cons (step573 p h) (sat_nil p)))))))))
def c618 : List Lit := [(789, true)]
theorem step618 (p : Nat → Bool) (h : Constraints p) : clause p c618 = true :=
  Snake9.LocalRup.prove_clause [c617, c373] c618 (by decide) p (sat_cons (step617 p h) (sat_cons (step373 p h) (sat_nil p)))
def c619 : List Lit := [(816, true)]
theorem step619 (p : Nat → Bool) (h : Constraints p) : clause p c619 = true :=
  Snake9.LocalRup.prove_clause [c618, c400] c619 (by decide) p (sat_cons (step618 p h) (sat_cons (step400 p h) (sat_nil p)))
def c620 : List Lit := [(862, true)]
theorem step620 (p : Nat → Bool) (h : Constraints p) : clause p c620 = true :=
  Snake9.LocalRup.prove_clause [c208, c437, c438, c435, c436, c90, c88] c620 (by decide) p (sat_cons (step208 p h) (sat_cons (step437 p h) (sat_cons (step438 p h) (sat_cons (step435 p h) (sat_cons (step436 p h) (sat_cons (step90 p h) (sat_cons (step88 p h) (sat_nil p))))))))
def c621 : List Lit := [(873, true)]
theorem step621 (p : Nat → Bool) (h : Constraints p) : clause p c621 = true :=
  Snake9.LocalRup.prove_clause [c620, c452] c621 (by decide) p (sat_cons (step620 p h) (sat_cons (step452 p h) (sat_nil p)))
def c622 : List Lit := [(880, true)]
theorem step622 (p : Nat → Bool) (h : Constraints p) : clause p c622 = true :=
  Snake9.LocalRup.prove_clause [c621, c459] c622 (by decide) p (sat_cons (step621 p h) (sat_cons (step459 p h) (sat_nil p)))
def c623 : List Lit := [(937, true), (869, true)]
theorem step623 (p : Nat → Bool) (h : Constraints p) : clause p c623 = true :=
  Snake9.LocalRup.prove_clause [c211, c212, c446, c444, c443, c448, c440, c100, c99, c105, c511, c517, c607, c104, c471, c474, c495, c97, c531, c534, c608, c499, c519, c475, c477, c512, c473, c121] c623 (by decide) p (sat_cons (step211 p h) (sat_cons (step212 p h) (sat_cons (step446 p h) (sat_cons (step444 p h) (sat_cons (step443 p h) (sat_cons (step448 p h) (sat_cons (step440 p h) (sat_cons (step100 p h) (sat_cons (step99 p h) (sat_cons (step105 p h) (sat_cons (step511 p h) (sat_cons (step517 p h) (sat_cons (step607 p h) (sat_cons (step104 p h) (sat_cons (step471 p h) (sat_cons (step474 p h) (sat_cons (step495 p h) (sat_cons (step97 p h) (sat_cons (step531 p h) (sat_cons (step534 p h) (sat_cons (step608 p h) (sat_cons (step499 p h) (sat_cons (step519 p h) (sat_cons (step475 p h) (sat_cons (step477 p h) (sat_cons (step512 p h) (sat_cons (step473 p h) (sat_cons (step121 p h) (sat_nil p)))))))))))))))))))))))))))))
def c624 : List Lit := [(101, false), (846, false), (869, true), (956, true)]
theorem step624 (p : Nat → Bool) (h : Constraints p) : clause p c624 = true :=
  Snake9.LocalRup.prove_clause [c211, c212, c217, c621, c446, c444, c443, c448, c440, c100, c99, c105, c511, c517, c607, c430, c463, c553, c547, c104, c97, c116, c118, c119, c473, c480, c478, c487, c505, c504, c488, c543, c482, c557, c160, c466, c164, c431, c423, c425] c624 (by decide) p (sat_cons (step211 p h) (sat_cons (step212 p h) (sat_cons (step217 p h) (sat_cons (step621 p h) (sat_cons (step446 p h) (sat_cons (step444 p h) (sat_cons (step443 p h) (sat_cons (step448 p h) (sat_cons (step440 p h) (sat_cons (step100 p h) (sat_cons (step99 p h) (sat_cons (step105 p h) (sat_cons (step511 p h) (sat_cons (step517 p h) (sat_cons (step607 p h) (sat_cons (step430 p h) (sat_cons (step463 p h) (sat_cons (step553 p h) (sat_cons (step547 p h) (sat_cons (step104 p h) (sat_cons (step97 p h) (sat_cons (step116 p h) (sat_cons (step118 p h) (sat_cons (step119 p h) (sat_cons (step473 p h) (sat_cons (step480 p h) (sat_cons (step478 p h) (sat_cons (step487 p h) (sat_cons (step505 p h) (sat_cons (step504 p h) (sat_cons (step488 p h) (sat_cons (step543 p h) (sat_cons (step482 p h) (sat_cons (step557 p h) (sat_cons (step160 p h) (sat_cons (step466 p h) (sat_cons (step164 p h) (sat_cons (step431 p h) (sat_cons (step423 p h) (sat_cons (step425 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c625 : List Lit := [(897, false), (929, false), (881, false), (745, false), (738, false)]
theorem step625 (p : Nat → Bool) (h : Constraints p) : clause p c625 = true :=
  Snake9.LocalRup.prove_clause [c615, c569, c619, c216, c359, c409, c564, c553, c544, c503, c504, c539, c485, c487, c552, c483, c479, c480, c565, c143, c413, c144, c360, c154, c350, c337, c343] c625 (by decide) p (sat_cons (step615 p h) (sat_cons (step569 p h) (sat_cons (step619 p h) (sat_cons (step216 p h) (sat_cons (step359 p h) (sat_cons (step409 p h) (sat_cons (step564 p h) (sat_cons (step553 p h) (sat_cons (step544 p h) (sat_cons (step503 p h) (sat_cons (step504 p h) (sat_cons (step539 p h) (sat_cons (step485 p h) (sat_cons (step487 p h) (sat_cons (step552 p h) (sat_cons (step483 p h) (sat_cons (step479 p h) (sat_cons (step480 p h) (sat_cons (step565 p h) (sat_cons (step143 p h) (sat_cons (step413 p h) (sat_cons (step144 p h) (sat_cons (step360 p h) (sat_cons (step154 p h) (sat_cons (step350 p h) (sat_cons (step337 p h) (sat_cons (step343 p h) (sat_nil p))))))))))))))))))))))))))))
def c626 : List Lit := [(80, true), (846, false), (869, true), (738, false)]
theorem step626 (p : Nat → Bool) (h : Constraints p) : clause p c626 = true :=
  Snake9.LocalRup.prove_clause [c211, c615, c621, c212, c569, c619, c224, c446, c443, c444, c448, c440, c100, c99, c101, c335, c430, c463, c105, c359, c409, c564, c624, c512, c519, c608, c625, c553, c544, c104, c471, c97, c477, c501, c490, c478, c473, c117, c480, c481, c487, c500, c540, c539, c609, c529, c552, c520, c605, c565, c513, c603, c413, c185, c360, c183, c353, c133, c336, c330] c626 (by decide) p (sat_cons (step211 p h) (sat_cons (step615 p h) (sat_cons (step621 p h) (sat_cons (step212 p h) (sat_cons (step569 p h) (sat_cons (step619 p h) (sat_cons (step224 p h) (sat_cons (step446 p h) (sat_cons (step443 p h) (sat_cons (step444 p h) (sat_cons (step448 p h) (sat_cons (step440 p h) (sat_cons (step100 p h) (sat_cons (step99 p h) (sat_cons (step101 p h) (sat_cons (step335 p h) (sat_cons (step430 p h) (sat_cons (step463 p h) (sat_cons (step105 p h) (sat_cons (step359 p h) (sat_cons (step409 p h) (sat_cons (step564 p h) (sat_cons (step624 p h) (sat_cons (step512 p h) (sat_cons (step519 p h) (sat_cons (step608 p h) (sat_cons (step625 p h) (sat_cons (step553 p h) (sat_cons (step544 p h) (sat_cons (step104 p h) (sat_cons (step471 p h) (sat_cons (step97 p h) (sat_cons (step477 p h) (sat_cons (step501 p h) (sat_cons (step490 p h) (sat_cons (step478 p h) (sat_cons (step473 p h) (sat_cons (step117 p h) (sat_cons (step480 p h) (sat_cons (step481 p h) (sat_cons (step487 p h) (sat_cons (step500 p h) (sat_cons (step540 p h) (sat_cons (step539 p h) (sat_cons (step609 p h) (sat_cons (step529 p h) (sat_cons (step552 p h) (sat_cons (step520 p h) (sat_cons (step605 p h) (sat_cons (step565 p h) (sat_cons (step513 p h) (sat_cons (step603 p h) (sat_cons (step413 p h) (sat_cons (step185 p h) (sat_cons (step360 p h) (sat_cons (step183 p h) (sat_cons (step353 p h) (sat_cons (step133 p h) (sat_cons (step336 p h) (sat_cons (step330 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c627 : List Lit := [(846, false), (869, true), (738, false)]
theorem step627 (p : Nat → Bool) (h : Constraints p) : clause p c627 = true :=
  Snake9.TreeRup.prove_clause [c615, c619, c569, c211, c213, c212, c621, c587, c224, c584, c446, c444, c443, c448, c440, c100, c99, c105, c104, c109, c97, c359, c409, c564, c430, c463, c553, c624, c512, c519, c608, c544, c626, c114, c115, c130, c473, c480, c281, c475, c487, c282, c501, c500, c288, c490, c540, c307, c481, c609, c529, c304, c520, c605, c295, c513, c603, c294, c185, c293, c182, c173] c627 (by decide) p (sat_cons (step615 p h) (sat_cons (step619 p h) (sat_cons (step569 p h) (sat_cons (step211 p h) (sat_cons (step213 p h) (sat_cons (step212 p h) (sat_cons (step621 p h) (sat_cons (step587 p h) (sat_cons (step224 p h) (sat_cons (step584 p h) (sat_cons (step446 p h) (sat_cons (step444 p h) (sat_cons (step443 p h) (sat_cons (step448 p h) (sat_cons (step440 p h) (sat_cons (step100 p h) (sat_cons (step99 p h) (sat_cons (step105 p h) (sat_cons (step104 p h) (sat_cons (step109 p h) (sat_cons (step97 p h) (sat_cons (step359 p h) (sat_cons (step409 p h) (sat_cons (step564 p h) (sat_cons (step430 p h) (sat_cons (step463 p h) (sat_cons (step553 p h) (sat_cons (step624 p h) (sat_cons (step512 p h) (sat_cons (step519 p h) (sat_cons (step608 p h) (sat_cons (step544 p h) (sat_cons (step626 p h) (sat_cons (step114 p h) (sat_cons (step115 p h) (sat_cons (step130 p h) (sat_cons (step473 p h) (sat_cons (step480 p h) (sat_cons (step281 p h) (sat_cons (step475 p h) (sat_cons (step487 p h) (sat_cons (step282 p h) (sat_cons (step501 p h) (sat_cons (step500 p h) (sat_cons (step288 p h) (sat_cons (step490 p h) (sat_cons (step540 p h) (sat_cons (step307 p h) (sat_cons (step481 p h) (sat_cons (step609 p h) (sat_cons (step529 p h) (sat_cons (step304 p h) (sat_cons (step520 p h) (sat_cons (step605 p h) (sat_cons (step295 p h) (sat_cons (step513 p h) (sat_cons (step603 p h) (sat_cons (step294 p h) (sat_cons (step185 p h) (sat_cons (step293 p h) (sat_cons (step182 p h) (sat_cons (step173 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c628 : List Lit := [(80, false), (869, true), (941, true)]
theorem step628 (p : Nat → Bool) (h : Constraints p) : clause p c628 = true :=
  Snake9.TreeRup.prove_clause [c211, c213, c212, c587, c584, c223, c224, c446, c444, c443, c448, c440, c100, c99, c105, c104, c109, c97, c114, c115, c116, c130, c473, c480, c512, c281, c475, c487, c282, c500, c288, c541, c307, c610, c303, c304, c521, c301, c302, c295, c300, c298, c294, c299, c297, c293, c180, c179, c173, c178, c514, c515, c520, c182, c184, c609, c579, c545, c481, c501, c490] c628 (by decide) p (sat_cons (step211 p h) (sat_cons (step213 p h) (sat_cons (step212 p h) (sat_cons (step587 p h) (sat_cons (step584 p h) (sat_cons (step223 p h) (sat_cons (step224 p h) (sat_cons (step446 p h) (sat_cons (step444 p h) (sat_cons (step443 p h) (sat_cons (step448 p h) (sat_cons (step440 p h) (sat_cons (step100 p h) (sat_cons (step99 p h) (sat_cons (step105 p h) (sat_cons (step104 p h) (sat_cons (step109 p h) (sat_cons (step97 p h) (sat_cons (step114 p h) (sat_cons (step115 p h) (sat_cons (step116 p h) (sat_cons (step130 p h) (sat_cons (step473 p h) (sat_cons (step480 p h) (sat_cons (step512 p h) (sat_cons (step281 p h) (sat_cons (step475 p h) (sat_cons (step487 p h) (sat_cons (step282 p h) (sat_cons (step500 p h) (sat_cons (step288 p h) (sat_cons (step541 p h) (sat_cons (step307 p h) (sat_cons (step610 p h) (sat_cons (step303 p h) (sat_cons (step304 p h) (sat_cons (step521 p h) (sat_cons (step301 p h) (sat_cons (step302 p h) (sat_cons (step295 p h) (sat_cons (step300 p h) (sat_cons (step298 p h) (sat_cons (step294 p h) (sat_cons (step299 p h) (sat_cons (step297 p h) (sat_cons (step293 p h) (sat_cons (step180 p h) (sat_cons (step179 p h) (sat_cons (step173 p h) (sat_cons (step178 p h) (sat_cons (step514 p h) (sat_cons (step515 p h) (sat_cons (step520 p h) (sat_cons (step182 p h) (sat_cons (step184 p h) (sat_cons (step609 p h) (sat_cons (step579 p h) (sat_cons (step545 p h) (sat_cons (step481 p h) (sat_cons (step501 p h) (sat_cons (step490 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c629 : List Lit := [(929, true), (899, true), (869, true)]
theorem step629 (p : Nat → Bool) (h : Constraints p) : clause p c629 = true :=
  Snake9.LocalRup.prove_clause [c211, c213, c212, c587, c224, c584, c446, c444, c443, c448, c440, c100, c99, c105, c511, c517, c109, c97, c608, c528, c519, c518, c605, c512, c513, c603, c118, c130, c281, c282, c288, c307, c304, c119, c295, c481, c294, c185, c293, c182, c173] c629 (by decide) p (sat_cons (step211 p h) (sat_cons (step213 p h) (sat_cons (step212 p h) (sat_cons (step587 p h) (sat_cons (step224 p h) (sat_cons (step584 p h) (sat_cons (step446 p h) (sat_cons (step444 p h) (sat_cons (step443 p h) (sat_cons (step448 p h) (sat_cons (step440 p h) (sat_cons (step100 p h) (sat_cons (step99 p h) (sat_cons (step105 p h) (sat_cons (step511 p h) (sat_cons (step517 p h) (sat_cons (step109 p h) (sat_cons (step97 p h) (sat_cons (step608 p h) (sat_cons (step528 p h) (sat_cons (step519 p h) (sat_cons (step518 p h) (sat_cons (step605 p h) (sat_cons (step512 p h) (sat_cons (step513 p h) (sat_cons (step603 p h) (sat_cons (step118 p h) (sat_cons (step130 p h) (sat_cons (step281 p h) (sat_cons (step282 p h) (sat_cons (step288 p h) (sat_cons (step307 p h) (sat_cons (step304 p h) (sat_cons (step119 p h) (sat_cons (step295 p h) (sat_cons (step481 p h) (sat_cons (step294 p h) (sat_cons (step185 p h) (sat_cons (step293 p h) (sat_cons (step182 p h) (sat_cons (step173 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c630 : List Lit := [(849, true), (58, false), (74, false)]
theorem step630 (p : Nat → Bool) (h : Constraints p) : clause p c630 = true :=
  Snake9.LocalRup.prove_clause [c207, c422, c423, c95, c87, c86] c630 (by decide) p (sat_cons (step207 p h) (sat_cons (step422 p h) (sat_cons (step423 p h) (sat_cons (step95 p h) (sat_cons (step87 p h) (sat_cons (step86 p h) (sat_nil p)))))))
def c631 : List Lit := [(939, true), (869, true), (738, false)]
theorem step631 (p : Nat → Bool) (h : Constraints p) : clause p c631 = true :=
  Snake9.LocalRup.prove_clause [c211, c615, c619, c569, c622, c212, c621, c448, c441, c627, c419, c418, c630, c425, c428, c463, c446, c444, c443, c440, c100, c99, c104, c471, c359, c409, c564, c549, c628, c477, c105, c511, c517, c607, c101, c335, c97, c543, c501, c490, c629, c625, c539, c478, c500, c473, c487, c117, c480] c631 (by decide) p (sat_cons (step211 p h) (sat_cons (step615 p h) (sat_cons (step619 p h) (sat_cons (step569 p h) (sat_cons (step622 p h) (sat_cons (step212 p h) (sat_cons (step621 p h) (sat_cons (step448 p h) (sat_cons (step441 p h) (sat_cons (step627 p h) (sat_cons (step419 p h) (sat_cons (step418 p h) (sat_cons (step630 p h) (sat_cons (step425 p h) (sat_cons (step428 p h) (sat_cons (step463 p h) (sat_cons (step446 p h) (sat_cons (step444 p h) (sat_cons (step443 p h) (sat_cons (step440 p h) (sat_cons (step100 p h) (sat_cons (step99 p h) (sat_cons (step104 p h) (sat_cons (step471 p h) (sat_cons (step359 p h) (sat_cons (step409 p h) (sat_cons (step564 p h) (sat_cons (step549 p h) (sat_cons (step628 p h) (sat_cons (step477 p h) (sat_cons (step105 p h) (sat_cons (step511 p h) (sat_cons (step517 p h) (sat_cons (step607 p h) (sat_cons (step101 p h) (sat_cons (step335 p h) (sat_cons (step97 p h) (sat_cons (step543 p h) (sat_cons (step501 p h) (sat_cons (step490 p h) (sat_cons (step629 p h) (sat_cons (step625 p h) (sat_cons (step539 p h) (sat_cons (step478 p h) (sat_cons (step500 p h) (sat_cons (step473 p h) (sat_cons (step487 p h) (sat_cons (step117 p h) (sat_cons (step480 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))
def c632 : List Lit := [(17, false), (20, false), (22, false)]
theorem step632 (p : Nat → Bool) (h : Constraints p) : clause p c632 = true :=
  Snake9.LocalRup.prove_clause [c192, c24, c27] c632 (by decide) p (sat_cons (step192 p h) (sat_cons (step24 p h) (sat_cons (step27 p h) (sat_nil p))))
def c633 : List Lit := [(869, true), (738, false)]
theorem step633 (p : Nat → Bool) (h : Constraints p) : clause p c633 = true :=
  Snake9.LocalRup.prove_clause [c212, c621, c569, c619, c446, c448, c443, c444, c440, c441, c100, c99, c101, c335, c627, c419, c418, c630, c425, c428, c463, c631, c552, c565, c413, c360, c353, c350, c336, c343, c330, c337, c338, c632] c633 (by decide) p (sat_cons (step212 p h) (sat_cons (step621 p h) (sat_cons (step569 p h) (sat_cons (step619 p h) (sat_cons (step446 p h) (sat_cons (step448 p h) (sat_cons (step443 p h) (sat_cons (step444 p h) (sat_cons (step440 p h) (sat_cons (step441 p h) (sat_cons (step100 p h) (sat_cons (step99 p h) (sat_cons (step101 p h) (sat_cons (step335 p h) (sat_cons (step627 p h) (sat_cons (step419 p h) (sat_cons (step418 p h) (sat_cons (step630 p h) (sat_cons (step425 p h) (sat_cons (step428 p h) (sat_cons (step463 p h) (sat_cons (step631 p h) (sat_cons (step552 p h) (sat_cons (step565 p h) (sat_cons (step413 p h) (sat_cons (step360 p h) (sat_cons (step353 p h) (sat_cons (step350 p h) (sat_cons (step336 p h) (sat_cons (step343 p h) (sat_cons (step330 p h) (sat_cons (step337 p h) (sat_cons (step338 p h) (sat_cons (step632 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c634 : List Lit := [(809, true)]
theorem step634 (p : Nat → Bool) (h : Constraints p) : clause p c634 = true :=
  Snake9.LocalRup.prove_clause [c200, c395, c397, c390, c381, c383, c388, c378, c379, c50, c49, c48] c634 (by decide) p (sat_cons (step200 p h) (sat_cons (step395 p h) (sat_cons (step397 p h) (sat_cons (step390 p h) (sat_cons (step381 p h) (sat_cons (step383 p h) (sat_cons (step388 p h) (sat_cons (step378 p h) (sat_cons (step379 p h) (sat_cons (step50 p h) (sat_cons (step49 p h) (sat_cons (step48 p h) (sat_nil p)))))))))))))
def c635 : List Lit := [(817, true)]
theorem step635 (p : Nat → Bool) (h : Constraints p) : clause p c635 = true :=
  Snake9.LocalRup.prove_clause [c634, c618, c401] c635 (by decide) p (sat_cons (step634 p h) (sat_cons (step618 p h) (sat_cons (step401 p h) (sat_nil p))))
def c636 : List Lit := [(76, false), (79, false), (13, false), (75, false)]
theorem step636 (p : Nat → Bool) (h : Constraints p) : clause p c636 = true :=
  Snake9.LocalRup.prove_clause [c212, c100, c101, c99] c636 (by decide) p (sat_cons (step212 p h) (sat_cons (step100 p h) (sat_cons (step101 p h) (sat_cons (step99 p h) (sat_nil p)))))
def c637 : List Lit := [(727, true), (56, false), (22, false), (17, false)]
theorem step637 (p : Nat → Bool) (h : Constraints p) : clause p c637 = true :=
  Snake9.LocalRup.prove_clause [c188, c316, c317, c6, c28, c8] c637 (by decide) p (sat_cons (step188 p h) (sat_cons (step316 p h) (sat_cons (step317 p h) (sat_cons (step6 p h) (sat_cons (step28 p h) (sat_cons (step8 p h) (sat_nil p)))))))
def c638 : List Lit := [(4, true), (3, false), (22, false), (17, false)]
theorem step638 (p : Nat → Bool) (h : Constraints p) : clause p c638 = true :=
  Snake9.LocalRup.prove_clause [c187, c582, c592, c590, c581, c189, c188, c5, c2, c225, c226, c229, c230, c239, c228, c236, c227, c231, c9, c13, c12, c28, c8] c638 (by decide) p (sat_cons (step187 p h) (sat_cons (step582 p h) (sat_cons (step592 p h) (sat_cons (step590 p h) (sat_cons (step581 p h) (sat_cons (step189 p h) (sat_cons (step188 p h) (sat_cons (step5 p h) (sat_cons (step2 p h) (sat_cons (step225 p h) (sat_cons (step226 p h) (sat_cons (step229 p h) (sat_cons (step230 p h) (sat_cons (step239 p h) (sat_cons (step228 p h) (sat_cons (step236 p h) (sat_cons (step227 p h) (sat_cons (step231 p h) (sat_cons (step9 p h) (sat_cons (step13 p h) (sat_cons (step12 p h) (sat_cons (step28 p h) (sat_cons (step8 p h) (sat_nil p))))))))))))))))))))))))
def c639 : List Lit := [(4, false), (3, false), (56, false)]
theorem step639 (p : Nat → Bool) (h : Constraints p) : clause p c639 = true :=
  Snake9.LocalRup.prove_clause [c189, c581, c590, c592, c582, c187, c570, c6, c4, c2, c225, c226, c229, c230, c239, c228, c236, c227, c231, c9, c12, c13] c639 (by decide) p (sat_cons (step189 p h) (sat_cons (step581 p h) (sat_cons (step590 p h) (sat_cons (step592 p h) (sat_cons (step582 p h) (sat_cons (step187 p h) (sat_cons (step570 p h) (sat_cons (step6 p h) (sat_cons (step4 p h) (sat_cons (step2 p h) (sat_cons (step225 p h) (sat_cons (step226 p h) (sat_cons (step229 p h) (sat_cons (step230 p h) (sat_cons (step239 p h) (sat_cons (step228 p h) (sat_cons (step236 p h) (sat_cons (step227 p h) (sat_cons (step231 p h) (sat_cons (step9 p h) (sat_cons (step12 p h) (sat_cons (step13 p h) (sat_nil p)))))))))))))))))))))))
def c640 : List Lit := [(91, true), (22, false), (17, false)]
theorem step640 (p : Nat → Bool) (h : Constraints p) : clause p c640 = true :=
  Snake9.LocalRup.prove_clause [c193, c32, c33, c572] c640 (by decide) p (sat_cons (step193 p h) (sat_cons (step32 p h) (sat_cons (step33 p h) (sat_cons (step572 p h) (sat_nil p)))))
def c641 : List Lit := [(81, false), (90, true), (908, true), (84, false), (75, false), (91, false)]
theorem step641 (p : Nat → Bool) (h : Constraints p) : clause p c641 = true :=
  Snake9.LocalRup.prove_clause [c479, c487, c500, c127, c472, c474, c477, c497, c115, c490, c481] c641 (by decide) p (sat_cons (step479 p h) (sat_cons (step487 p h) (sat_cons (step500 p h) (sat_cons (step127 p h) (sat_cons (step472 p h) (sat_cons (step474 p h) (sat_cons (step477 p h) (sat_cons (step497 p h) (sat_cons (step115 p h) (sat_cons (step490 p h) (sat_cons (step481 p h) (sat_nil p))))))))))))
def c642 : List Lit := [(83, true), (81, true), (896, true), (90, true), (84, false)]
theorem step642 (p : Nat → Bool) (h : Constraints p) : clause p c642 = true :=
  Snake9.LocalRup.prove_clause [c214, c591, c472, c130, c477, c281, c113, c284, c125, c278, c277] c642 (by decide) p (sat_cons (step214 p h) (sat_cons (step591 p h) (sat_cons (step472 p h) (sat_cons (step130 p h) (sat_cons (step477 p h) (sat_cons (step281 p h) (sat_cons (step113 p h) (sat_cons (step284 p h) (sat_cons (step125 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_nil p))))))))))))
def c643 : List Lit := [(90, true), (908, true), (84, false), (75, false), (91, false), (22, false)]
theorem step643 (p : Nat → Bool) (h : Constraints p) : clause p c643 = true :=
  Snake9.LocalRup.prove_clause [c214, c479, c487, c500, c641, c642, c128, c152, c113, c481, c476, c490, c497] c643 (by decide) p (sat_cons (step214 p h) (sat_cons (step479 p h) (sat_cons (step487 p h) (sat_cons (step500 p h) (sat_cons (step641 p h) (sat_cons (step642 p h) (sat_cons (step128 p h) (sat_cons (step152 p h) (sat_cons (step113 p h) (sat_cons (step481 p h) (sat_cons (step476 p h) (sat_cons (step490 p h) (sat_cons (step497 p h) (sat_nil p))))))))))))))
def c644 : List Lit := [(908, true), (84, false), (75, false), (22, false), (17, false), (939, true)]
theorem step644 (p : Nat → Bool) (h : Constraints p) : clause p c644 = true :=
  Snake9.LocalRup.prove_clause [c215, c214, c224, c640, c643, c154, c153, c480, c472, c129, c487, c474, c500, c497, c496, c475, c477, c488, c536, c473, c483, c609, c131, c142, c139, c112, c111, c107, c116, c150, c512, c183, c520, c513] c644 (by decide) p (sat_cons (step215 p h) (sat_cons (step214 p h) (sat_cons (step224 p h) (sat_cons (step640 p h) (sat_cons (step643 p h) (sat_cons (step154 p h) (sat_cons (step153 p h) (sat_cons (step480 p h) (sat_cons (step472 p h) (sat_cons (step129 p h) (sat_cons (step487 p h) (sat_cons (step474 p h) (sat_cons (step500 p h) (sat_cons (step497 p h) (sat_cons (step496 p h) (sat_cons (step475 p h) (sat_cons (step477 p h) (sat_cons (step488 p h) (sat_cons (step536 p h) (sat_cons (step473 p h) (sat_cons (step483 p h) (sat_cons (step609 p h) (sat_cons (step131 p h) (sat_cons (step142 p h) (sat_cons (step139 p h) (sat_cons (step112 p h) (sat_cons (step111 p h) (sat_cons (step107 p h) (sat_cons (step116 p h) (sat_cons (step150 p h) (sat_cons (step512 p h) (sat_cons (step183 p h) (sat_cons (step520 p h) (sat_cons (step513 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
end B112E151
