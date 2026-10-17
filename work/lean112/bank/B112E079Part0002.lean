import B112E079Part0001
namespace B112E079
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c676 : List Lit := [(1491, false), (1542, true), (21, false), (1399, true)]
theorem step676 (p : Nat → Bool) (h : Constraints p) : clause p c676 = true :=
  Snake9.LocalRup.prove_clause [c586, c344, c620, c188, c662, c599, c230, c273, c342, c337, c600, c517, c533, c529, c672, c334, c310, c297, c293, c495, c496, c525, c490, c491, c536, c489, c619, c673, c674, c446, c675, c461, c110, c467, c463, c136, c117] c676 (by decide) p (sat_cons (step586 p h) (sat_cons (step344 p h) (sat_cons (step620 p h) (sat_cons (step188 p h) (sat_cons (step662 p h) (sat_cons (step599 p h) (sat_cons (step230 p h) (sat_cons (step273 p h) (sat_cons (step342 p h) (sat_cons (step337 p h) (sat_cons (step600 p h) (sat_cons (step517 p h) (sat_cons (step533 p h) (sat_cons (step529 p h) (sat_cons (step672 p h) (sat_cons (step334 p h) (sat_cons (step310 p h) (sat_cons (step297 p h) (sat_cons (step293 p h) (sat_cons (step495 p h) (sat_cons (step496 p h) (sat_cons (step525 p h) (sat_cons (step490 p h) (sat_cons (step491 p h) (sat_cons (step536 p h) (sat_cons (step489 p h) (sat_cons (step619 p h) (sat_cons (step673 p h) (sat_cons (step674 p h) (sat_cons (step446 p h) (sat_cons (step675 p h) (sat_cons (step461 p h) (sat_cons (step110 p h) (sat_cons (step467 p h) (sat_cons (step463 p h) (sat_cons (step136 p h) (sat_cons (step117 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c677 : List Lit := [(1542, true), (21, false), (1399, true)]
theorem step677 (p : Nat → Bool) (h : Constraints p) : clause p c677 = true :=
  Snake9.LocalRup.prove_clause [c620, c344, c622, c189, c192, c188, c672, c662, c599, c230, c273, c342, c337, c334, c310, c297, c292, c291, c293, c308, c306, c300, c600, c517, c416, c415, c414, c660, c265, c259, c253, c252, c603, c537, c676, c485, c487, c582, c482, c121, c464, c131, c123, c465, c668, c142, c655, c446, c675, c461, c110, c467, c117, c619, c136, c536, c491, c525, c493] c677 (by decide) p (sat_cons (step620 p h) (sat_cons (step344 p h) (sat_cons (step622 p h) (sat_cons (step189 p h) (sat_cons (step192 p h) (sat_cons (step188 p h) (sat_cons (step672 p h) (sat_cons (step662 p h) (sat_cons (step599 p h) (sat_cons (step230 p h) (sat_cons (step273 p h) (sat_cons (step342 p h) (sat_cons (step337 p h) (sat_cons (step334 p h) (sat_cons (step310 p h) (sat_cons (step297 p h) (sat_cons (step292 p h) (sat_cons (step291 p h) (sat_cons (step293 p h) (sat_cons (step308 p h) (sat_cons (step306 p h) (sat_cons (step300 p h) (sat_cons (step600 p h) (sat_cons (step517 p h) (sat_cons (step416 p h) (sat_cons (step415 p h) (sat_cons (step414 p h) (sat_cons (step660 p h) (sat_cons (step265 p h) (sat_cons (step259 p h) (sat_cons (step253 p h) (sat_cons (step252 p h) (sat_cons (step603 p h) (sat_cons (step537 p h) (sat_cons (step676 p h) (sat_cons (step485 p h) (sat_cons (step487 p h) (sat_cons (step582 p h) (sat_cons (step482 p h) (sat_cons (step121 p h) (sat_cons (step464 p h) (sat_cons (step131 p h) (sat_cons (step123 p h) (sat_cons (step465 p h) (sat_cons (step668 p h) (sat_cons (step142 p h) (sat_cons (step655 p h) (sat_cons (step446 p h) (sat_cons (step675 p h) (sat_cons (step461 p h) (sat_cons (step110 p h) (sat_cons (step467 p h) (sat_cons (step117 p h) (sat_cons (step619 p h) (sat_cons (step136 p h) (sat_cons (step536 p h) (sat_cons (step491 p h) (sat_cons (step525 p h) (sat_cons (step493 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c678 : List Lit := [(1434, true), (1399, true)]
theorem step678 (p : Nat → Bool) (h : Constraints p) : clause p c678 = true :=
  Snake9.LocalRup.prove_clause [c581, c580, c672, c660, c265, c259, c253, c252, c658, c656, c416, c657, c433, c436, c616, c386, c609] c678 (by decide) p (sat_cons (step581 p h) (sat_cons (step580 p h) (sat_cons (step672 p h) (sat_cons (step660 p h) (sat_cons (step265 p h) (sat_cons (step259 p h) (sat_cons (step253 p h) (sat_cons (step252 p h) (sat_cons (step658 p h) (sat_cons (step656 p h) (sat_cons (step416 p h) (sat_cons (step657 p h) (sat_cons (step433 p h) (sat_cons (step436 p h) (sat_cons (step616 p h) (sat_cons (step386 p h) (sat_cons (step609 p h) (sat_nil p))))))))))))))))))
def c679 : List Lit := [(1399, true)]
theorem step679 (p : Nat → Bool) (h : Constraints p) : clause p c679 = true :=
  Snake9.LocalRup.prove_clause [c542, c580, c625, c416, c657, c660, c265, c259, c253, c252, c662, c599, c678, c539, c677, c366, c614, c652, c386, c616, c437] c679 (by decide) p (sat_cons (step542 p h) (sat_cons (step580 p h) (sat_cons (step625 p h) (sat_cons (step416 p h) (sat_cons (step657 p h) (sat_cons (step660 p h) (sat_cons (step265 p h) (sat_cons (step259 p h) (sat_cons (step253 p h) (sat_cons (step252 p h) (sat_cons (step662 p h) (sat_cons (step599 p h) (sat_cons (step678 p h) (sat_cons (step539 p h) (sat_cons (step677 p h) (sat_cons (step366 p h) (sat_cons (step614 p h) (sat_cons (step652 p h) (sat_cons (step386 p h) (sat_cons (step616 p h) (sat_cons (step437 p h) (sat_nil p))))))))))))))))))))))
def c680 : List Lit := [(1411, true)]
theorem step680 (p : Nat → Bool) (h : Constraints p) : clause p c680 = true :=
  Snake9.LocalRup.prove_clause [c679, c589, c423] c680 (by decide) p (sat_cons (step679 p h) (sat_cons (step589 p h) (sat_cons (step423 p h) (sat_nil p))))
def c681 : List Lit := [(1393, false)]
theorem step681 (p : Nat → Bool) (h : Constraints p) : clause p c681 = true :=
  Snake9.LocalRup.prove_clause [c680, c626, c430] c681 (by decide) p (sat_cons (step680 p h) (sat_cons (step626 p h) (sat_cons (step430 p h) (sat_nil p))))
def c682 : List Lit := [(1383, false), (1363, false)]
theorem step682 (p : Nat → Bool) (h : Constraints p) : clause p c682 = true :=
  Snake9.LocalRup.prove_clause [c580, c680, c625, c386, c437, c428, c656, c408, c440, c647, c389, c599] c682 (by decide) p (sat_cons (step580 p h) (sat_cons (step680 p h) (sat_cons (step625 p h) (sat_cons (step386 p h) (sat_cons (step437 p h) (sat_cons (step428 p h) (sat_cons (step656 p h) (sat_cons (step408 p h) (sat_cons (step440 p h) (sat_cons (step647 p h) (sat_cons (step389 p h) (sat_cons (step599 p h) (sat_nil p)))))))))))))
def c683 : List Lit := [(1527, true), (1363, false)]
theorem step683 (p : Nat → Bool) (h : Constraints p) : clause p c683 = true :=
  Snake9.LocalRup.prove_clause [c646, c625, c680, c621, c620, c645, c682, c394, c396, c649, c599, c389, c440, c426, c406, c402, c400, c399, c639, c404, c547, c390, c640, c243, c240, c615, c242, c241, c587, c522, c528, c518, c641, c513, c509, c511, c512, c515, c517, c507, c508, c158, c164, c483, c629] c683 (by decide) p (sat_cons (step646 p h) (sat_cons (step625 p h) (sat_cons (step680 p h) (sat_cons (step621 p h) (sat_cons (step620 p h) (sat_cons (step645 p h) (sat_cons (step682 p h) (sat_cons (step394 p h) (sat_cons (step396 p h) (sat_cons (step649 p h) (sat_cons (step599 p h) (sat_cons (step389 p h) (sat_cons (step440 p h) (sat_cons (step426 p h) (sat_cons (step406 p h) (sat_cons (step402 p h) (sat_cons (step400 p h) (sat_cons (step399 p h) (sat_cons (step639 p h) (sat_cons (step404 p h) (sat_cons (step547 p h) (sat_cons (step390 p h) (sat_cons (step640 p h) (sat_cons (step243 p h) (sat_cons (step240 p h) (sat_cons (step615 p h) (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_cons (step587 p h) (sat_cons (step522 p h) (sat_cons (step528 p h) (sat_cons (step518 p h) (sat_cons (step641 p h) (sat_cons (step513 p h) (sat_cons (step509 p h) (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step515 p h) (sat_cons (step517 p h) (sat_cons (step507 p h) (sat_cons (step508 p h) (sat_cons (step158 p h) (sat_cons (step164 p h) (sat_cons (step483 p h) (sat_cons (step629 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c684 : List Lit := [(1489, false), (1519, false), (1363, false), (1528, true)]
theorem step684 (p : Nat → Bool) (h : Constraints p) : clause p c684 = true :=
  Snake9.LocalRup.prove_clause [c646, c625, c680, c620, c645, c682, c394, c396, c649, c599, c389, c440, c426, c406, c390, c642, c644, c402, c400, c399, c639, c404, c547, c640, c243, c240, c615, c242, c241, c587, c485, c495, c526, c518, c513, c515, c511, c507, c508, c629, c164] c684 (by decide) p (sat_cons (step646 p h) (sat_cons (step625 p h) (sat_cons (step680 p h) (sat_cons (step620 p h) (sat_cons (step645 p h) (sat_cons (step682 p h) (sat_cons (step394 p h) (sat_cons (step396 p h) (sat_cons (step649 p h) (sat_cons (step599 p h) (sat_cons (step389 p h) (sat_cons (step440 p h) (sat_cons (step426 p h) (sat_cons (step406 p h) (sat_cons (step390 p h) (sat_cons (step642 p h) (sat_cons (step644 p h) (sat_cons (step402 p h) (sat_cons (step400 p h) (sat_cons (step399 p h) (sat_cons (step639 p h) (sat_cons (step404 p h) (sat_cons (step547 p h) (sat_cons (step640 p h) (sat_cons (step243 p h) (sat_cons (step240 p h) (sat_cons (step615 p h) (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_cons (step587 p h) (sat_cons (step485 p h) (sat_cons (step495 p h) (sat_cons (step526 p h) (sat_cons (step518 p h) (sat_cons (step513 p h) (sat_cons (step515 p h) (sat_cons (step511 p h) (sat_cons (step507 p h) (sat_cons (step508 p h) (sat_cons (step629 p h) (sat_cons (step164 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c685 : List Lit := [(1519, false), (1479, true), (1363, false), (1528, true)]
theorem step685 (p : Nat → Bool) (h : Constraints p) : clause p c685 = true :=
  Snake9.LocalRup.prove_clause [c646, c625, c680, c645, c620, c619, c682, c394, c396, c649, c599, c389, c440, c426, c406, c390, c404, c402, c400, c399, c639, c547, c640, c242, c241, c587, c644, c684, c483, c158, c157, c507, c460, c515, c518, c526, c495, c582, c464, c465, c467, c471, c584, c476] c685 (by decide) p (sat_cons (step646 p h) (sat_cons (step625 p h) (sat_cons (step680 p h) (sat_cons (step645 p h) (sat_cons (step620 p h) (sat_cons (step619 p h) (sat_cons (step682 p h) (sat_cons (step394 p h) (sat_cons (step396 p h) (sat_cons (step649 p h) (sat_cons (step599 p h) (sat_cons (step389 p h) (sat_cons (step440 p h) (sat_cons (step426 p h) (sat_cons (step406 p h) (sat_cons (step390 p h) (sat_cons (step404 p h) (sat_cons (step402 p h) (sat_cons (step400 p h) (sat_cons (step399 p h) (sat_cons (step639 p h) (sat_cons (step547 p h) (sat_cons (step640 p h) (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_cons (step587 p h) (sat_cons (step644 p h) (sat_cons (step684 p h) (sat_cons (step483 p h) (sat_cons (step158 p h) (sat_cons (step157 p h) (sat_cons (step507 p h) (sat_cons (step460 p h) (sat_cons (step515 p h) (sat_cons (step518 p h) (sat_cons (step526 p h) (sat_cons (step495 p h) (sat_cons (step582 p h) (sat_cons (step464 p h) (sat_cons (step465 p h) (sat_cons (step467 p h) (sat_cons (step471 p h) (sat_cons (step584 p h) (sat_cons (step476 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c686 : List Lit := [(1363, false), (1542, true)]
theorem step686 (p : Nat → Bool) (h : Constraints p) : clause p c686 = true :=
  Snake9.LocalRup.prove_clause [c586, c646, c625, c680, c620, c533, c682, c394, c396, c649, c599, c390, c389, c440, c426, c406, c402, c404, c639, c399, c400, c547, c640, c242, c241, c587, c683, c536, c685, c517, c512, c514, c509, c507, c160] c686 (by decide) p (sat_cons (step586 p h) (sat_cons (step646 p h) (sat_cons (step625 p h) (sat_cons (step680 p h) (sat_cons (step620 p h) (sat_cons (step533 p h) (sat_cons (step682 p h) (sat_cons (step394 p h) (sat_cons (step396 p h) (sat_cons (step649 p h) (sat_cons (step599 p h) (sat_cons (step390 p h) (sat_cons (step389 p h) (sat_cons (step440 p h) (sat_cons (step426 p h) (sat_cons (step406 p h) (sat_cons (step402 p h) (sat_cons (step404 p h) (sat_cons (step639 p h) (sat_cons (step399 p h) (sat_cons (step400 p h) (sat_cons (step547 p h) (sat_cons (step640 p h) (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_cons (step587 p h) (sat_cons (step683 p h) (sat_cons (step536 p h) (sat_cons (step685 p h) (sat_cons (step517 p h) (sat_cons (step512 p h) (sat_cons (step514 p h) (sat_cons (step509 p h) (sat_cons (step507 p h) (sat_cons (step160 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c687 : List Lit := [(1363, true), (17, true)]
theorem step687 (p : Nat → Bool) (h : Constraints p) : clause p c687 = true :=
  Snake9.LocalRup.prove_clause [c573, c564, c681, c360, c363, c383, c614, c609, c381, c364, c366, c371, c611, c362, c368, c369, c219, c26, c42, c220, c221, c223, c224, c227, c217, c215, c216, c211, c612, c210, c397, c16, c604] c687 (by decide) p (sat_cons (step573 p h) (sat_cons (step564 p h) (sat_cons (step681 p h) (sat_cons (step360 p h) (sat_cons (step363 p h) (sat_cons (step383 p h) (sat_cons (step614 p h) (sat_cons (step609 p h) (sat_cons (step381 p h) (sat_cons (step364 p h) (sat_cons (step366 p h) (sat_cons (step371 p h) (sat_cons (step611 p h) (sat_cons (step362 p h) (sat_cons (step368 p h) (sat_cons (step369 p h) (sat_cons (step219 p h) (sat_cons (step26 p h) (sat_cons (step42 p h) (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step223 p h) (sat_cons (step224 p h) (sat_cons (step227 p h) (sat_cons (step217 p h) (sat_cons (step215 p h) (sat_cons (step216 p h) (sat_cons (step211 p h) (sat_cons (step612 p h) (sat_cons (step210 p h) (sat_cons (step397 p h) (sat_cons (step16 p h) (sat_cons (step604 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c688 : List Lit := [(1363, false)]
theorem step688 (p : Nat → Bool) (h : Constraints p) : clause p c688 = true :=
  Snake9.LocalRup.prove_clause [c542, c645, c682, c686, c394, c396, c539, c649, c439, c599, c389] c688 (by decide) p (sat_cons (step542 p h) (sat_cons (step645 p h) (sat_cons (step682 p h) (sat_cons (step686 p h) (sat_cons (step394 p h) (sat_cons (step396 p h) (sat_cons (step539 p h) (sat_cons (step649 p h) (sat_cons (step439 p h) (sat_cons (step599 p h) (sat_cons (step389 p h) (sat_nil p))))))))))))
def c689 : List Lit := [(1359, false)]
theorem step689 (p : Nat → Bool) (h : Constraints p) : clause p c689 = true :=
  Snake9.LocalRup.prove_clause [c688, c378] c689 (by decide) p (sat_cons (step688 p h) (sat_cons (step378 p h) (sat_nil p)))
def c690 : List Lit := [(1354, false)]
theorem step690 (p : Nat → Bool) (h : Constraints p) : clause p c690 = true :=
  Snake9.LocalRup.prove_clause [c688, c614] c690 (by decide) p (sat_cons (step688 p h) (sat_cons (step614 p h) (sat_nil p)))
def c691 : List Lit := [(17, true)]
theorem step691 (p : Nat → Bool) (h : Constraints p) : clause p c691 = true :=
  Snake9.LocalRup.prove_clause [c688, c687] c691 (by decide) p (sat_cons (step688 p h) (sat_cons (step687 p h) (sat_nil p)))
def c692 : List Lit := [(1357, false)]
theorem step692 (p : Nat → Bool) (h : Constraints p) : clause p c692 = true :=
  Snake9.LocalRup.prove_clause [c689, c372] c692 (by decide) p (sat_cons (step689 p h) (sat_cons (step372 p h) (sat_nil p)))
def c693 : List Lit := [(22, true)]
theorem step693 (p : Nat → Bool) (h : Constraints p) : clause p c693 = true :=
  Snake9.LocalRup.prove_clause [c690, c365] c693 (by decide) p (sat_cons (step690 p h) (sat_cons (step365 p h) (sat_nil p)))
def c694 : List Lit := [(21, true)]
theorem step694 (p : Nat → Bool) (h : Constraints p) : clause p c694 = true :=
  Snake9.LocalRup.prove_clause [c690, c366] c694 (by decide) p (sat_cons (step690 p h) (sat_cons (step366 p h) (sat_nil p)))
def c695 : List Lit := [(1381, true)]
theorem step695 (p : Nat → Bool) (h : Constraints p) : clause p c695 = true :=
  Snake9.LocalRup.prove_clause [c691, c694, c688, c557, c693, c579, c690, c625, c391, c392, c612, c605, c41, c62, c216, c371, c36, c217, c381, c222, c363, c224, c361, c231, c28, c599, c404, c388, c637, c437] c695 (by decide) p (sat_cons (step691 p h) (sat_cons (step694 p h) (sat_cons (step688 p h) (sat_cons (step557 p h) (sat_cons (step693 p h) (sat_cons (step579 p h) (sat_cons (step690 p h) (sat_cons (step625 p h) (sat_cons (step391 p h) (sat_cons (step392 p h) (sat_cons (step612 p h) (sat_cons (step605 p h) (sat_cons (step41 p h) (sat_cons (step62 p h) (sat_cons (step216 p h) (sat_cons (step371 p h) (sat_cons (step36 p h) (sat_cons (step217 p h) (sat_cons (step381 p h) (sat_cons (step222 p h) (sat_cons (step363 p h) (sat_cons (step224 p h) (sat_cons (step361 p h) (sat_cons (step231 p h) (sat_cons (step28 p h) (sat_cons (step599 p h) (sat_cons (step404 p h) (sat_cons (step388 p h) (sat_cons (step637 p h) (sat_cons (step437 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c696 : List Lit := [(1383, true)]
theorem step696 (p : Nat → Bool) (h : Constraints p) : clause p c696 = true :=
  Snake9.LocalRup.prove_clause [c695, c394] c696 (by decide) p (sat_cons (step695 p h) (sat_cons (step394 p h) (sat_nil p)))
def c697 : List Lit := [(1389, false)]
theorem step697 (p : Nat → Bool) (h : Constraints p) : clause p c697 = true :=
  Snake9.LocalRup.prove_clause [c696, c681, c409] c697 (by decide) p (sat_cons (step696 p h) (sat_cons (step681 p h) (sat_cons (step409 p h) (sat_nil p))))
def c698 : List Lit := [(1371, false)]
theorem step698 (p : Nat → Bool) (h : Constraints p) : clause p c698 = true :=
  Snake9.LocalRup.prove_clause [c625, c680, c696, c695, c688, c437, c428, c410, c408, c397, c643] c698 (by decide) p (sat_cons (step625 p h) (sat_cons (step680 p h) (sat_cons (step696 p h) (sat_cons (step695 p h) (sat_cons (step688 p h) (sat_cons (step437 p h) (sat_cons (step428 p h) (sat_cons (step410 p h) (sat_cons (step408 p h) (sat_cons (step397 p h) (sat_cons (step643 p h) (sat_nil p))))))))))))
def c699 : List Lit := [(1344, false)]
theorem step699 (p : Nat → Bool) (h : Constraints p) : clause p c699 = true :=
  Snake9.LocalRup.prove_clause [c698, c579, c388] c699 (by decide) p (sat_cons (step698 p h) (sat_cons (step579 p h) (sat_cons (step388 p h) (sat_nil p))))
def c700 : List Lit := [(243, true)]
theorem step700 (p : Nat → Bool) (h : Constraints p) : clause p c700 = true :=
  Snake9.LocalRup.prove_clause [c699, c599] c700 (by decide) p (sat_cons (step699 p h) (sat_cons (step599 p h) (sat_nil p)))
def c701 : List Lit := [(271, true)]
theorem step701 (p : Nat → Bool) (h : Constraints p) : clause p c701 = true :=
  Snake9.LocalRup.prove_clause [c700, c230] c701 (by decide) p (sat_cons (step700 p h) (sat_cons (step230 p h) (sat_nil p)))
def c702 : List Lit := [(269, false)]
theorem step702 (p : Nat → Bool) (h : Constraints p) : clause p c702 = true :=
  Snake9.LocalRup.prove_clause [c700, c557, c231] c702 (by decide) p (sat_cons (step700 p h) (sat_cons (step557 p h) (sat_cons (step231 p h) (sat_nil p))))
def c703 : List Lit := [(1388, true)]
theorem step703 (p : Nat → Bool) (h : Constraints p) : clause p c703 = true :=
  Snake9.LocalRup.prove_clause [c700, c647] c703 (by decide) p (sat_cons (step700 p h) (sat_cons (step647 p h) (sat_nil p)))
def c704 : List Lit := [(323, false)]
theorem step704 (p : Nat → Bool) (h : Constraints p) : clause p c704 = true :=
  Snake9.LocalRup.prove_clause [c701, c553, c274] c704 (by decide) p (sat_cons (step701 p h) (sat_cons (step553 p h) (sat_cons (step274 p h) (sat_nil p))))
def c705 : List Lit := [(267, false)]
theorem step705 (p : Nat → Bool) (h : Constraints p) : clause p c705 = true :=
  Snake9.LocalRup.prove_clause [c702, c224] c705 (by decide) p (sat_cons (step702 p h) (sat_cons (step224 p h) (sat_nil p)))
def c706 : List Lit := [(1384, false)]
theorem step706 (p : Nat → Bool) (h : Constraints p) : clause p c706 = true :=
  Snake9.LocalRup.prove_clause [c703, c681, c411] c706 (by decide) p (sat_cons (step703 p h) (sat_cons (step681 p h) (sat_cons (step411 p h) (sat_nil p))))
def c707 : List Lit := [(295, false)]
theorem step707 (p : Nat → Bool) (h : Constraints p) : clause p c707 = true :=
  Snake9.LocalRup.prove_clause [c704, c268] c707 (by decide) p (sat_cons (step704 p h) (sat_cons (step268 p h) (sat_nil p)))
def c708 : List Lit := [(265, false)]
theorem step708 (p : Nat → Bool) (h : Constraints p) : clause p c708 = true :=
  Snake9.LocalRup.prove_clause [c705, c221] c708 (by decide) p (sat_cons (step705 p h) (sat_cons (step221 p h) (sat_nil p)))
def c709 : List Lit := [(28, true)]
theorem step709 (p : Nat → Bool) (h : Constraints p) : clause p c709 = true :=
  Snake9.LocalRup.prove_clause [c706, c695, c397] c709 (by decide) p (sat_cons (step706 p h) (sat_cons (step695 p h) (sat_cons (step397 p h) (sat_nil p))))
def c710 : List Lit := [(281, false)]
theorem step710 (p : Nat → Bool) (h : Constraints p) : clause p c710 = true :=
  Snake9.LocalRup.prove_clause [c707, c249] c710 (by decide) p (sat_cons (step707 p h) (sat_cons (step249 p h) (sat_nil p)))
def c711 : List Lit := [(263, false)]
theorem step711 (p : Nat → Bool) (h : Constraints p) : clause p c711 = true :=
  Snake9.LocalRup.prove_clause [c708, c220] c711 (by decide) p (sat_cons (step708 p h) (sat_cons (step220 p h) (sat_nil p)))
def c712 : List Lit := [(26, false)]
theorem step712 (p : Nat → Bool) (h : Constraints p) : clause p c712 = true :=
  Snake9.LocalRup.prove_clause [c709, c691, c692, c633] c712 (by decide) p (sat_cons (step709 p h) (sat_cons (step691 p h) (sat_cons (step692 p h) (sat_cons (step633 p h) (sat_nil p)))))
def c713 : List Lit := [(19, true)]
theorem step713 (p : Nat → Bool) (h : Constraints p) : clause p c713 = true :=
  Snake9.LocalRup.prove_clause [c709, c688, c694, c691, c702, c665] c713 (by decide) p (sat_cons (step709 p h) (sat_cons (step688 p h) (sat_cons (step694 p h) (sat_cons (step691 p h) (sat_cons (step702 p h) (sat_cons (step665 p h) (sat_nil p)))))))
def c714 : List Lit := [(275, false)]
theorem step714 (p : Nat → Bool) (h : Constraints p) : clause p c714 = true :=
  Snake9.LocalRup.prove_clause [c710, c236] c714 (by decide) p (sat_cons (step710 p h) (sat_cons (step236 p h) (sat_nil p)))
def c715 : List Lit := [(137, false)]
theorem step715 (p : Nat → Bool) (h : Constraints p) : clause p c715 = true :=
  Snake9.LocalRup.prove_clause [c711, c219] c715 (by decide) p (sat_cons (step711 p h) (sat_cons (step219 p h) (sat_nil p)))
def c716 : List Lit := [(138, false)]
theorem step716 (p : Nat → Bool) (h : Constraints p) : clause p c716 = true :=
  Snake9.LocalRup.prove_clause [c714, c234] c716 (by decide) p (sat_cons (step714 p h) (sat_cons (step234 p h) (sat_nil p)))
def c717 : List Lit := [(36, false)]
theorem step717 (p : Nat → Bool) (h : Constraints p) : clause p c717 = true :=
  Snake9.LocalRup.prove_clause [c715, c688, c713, c617] c717 (by decide) p (sat_cons (step715 p h) (sat_cons (step688 p h) (sat_cons (step713 p h) (sat_cons (step617 p h) (sat_nil p)))))
def c718 : List Lit := [(20, true)]
theorem step718 (p : Nat → Bool) (h : Constraints p) : clause p c718 = true :=
  Snake9.LocalRup.prove_clause [c716, c712, c709, c55] c718 (by decide) p (sat_cons (step716 p h) (sat_cons (step712 p h) (sat_cons (step709 p h) (sat_cons (step55 p h) (sat_nil p)))))
def c719 : List Lit := [(1386, false)]
theorem step719 (p : Nat → Bool) (h : Constraints p) : clause p c719 = true :=
  Snake9.LocalRup.prove_clause [c717, c697, c405] c719 (by decide) p (sat_cons (step717 p h) (sat_cons (step697 p h) (sat_cons (step405 p h) (sat_nil p))))
def c720 : List Lit := [(37, false)]
theorem step720 (p : Nat → Bool) (h : Constraints p) : clause p c720 = true :=
  Snake9.LocalRup.prove_clause [c718, c709, c691, c31] c720 (by decide) p (sat_cons (step718 p h) (sat_cons (step709 p h) (sat_cons (step691 p h) (sat_cons (step31 p h) (sat_nil p)))))
def c721 : List Lit := []
theorem step721 (p : Nat → Bool) (h : Constraints p) : clause p c721 = true :=
  Snake9.LocalRup.prove_clause [c720, c719, c400] c721 (by decide) p (sat_cons (step720 p h) (sat_cons (step719 p h) (sat_cons (step400 p h) (sat_nil p))))
end B112E079
