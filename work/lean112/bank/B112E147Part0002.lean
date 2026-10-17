import B112E147Part0001
namespace B112E147
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c640 : List Lit := [(720, true), (744, false), (704, true)]
theorem step640 (p : Nat → Bool) (h : Constraints p) : clause p c640 = true :=
  Snake9.LocalRup.prove_clause [c159, c161, c163, c160, c165, c530, c367, c369, c363, c365, c357, c358, c360, c361, c355, c356, c39, c40, c45, c42, c50, c54, c43, c47, c325, c338, c638, c232, c221, c222, c220, c219, c218, c639, c62, c61, c32, c334, c328, c329, c36] c640 (by decide) p (sat_cons (step159 p h) (sat_cons (step161 p h) (sat_cons (step163 p h) (sat_cons (step160 p h) (sat_cons (step165 p h) (sat_cons (step530 p h) (sat_cons (step367 p h) (sat_cons (step369 p h) (sat_cons (step363 p h) (sat_cons (step365 p h) (sat_cons (step357 p h) (sat_cons (step358 p h) (sat_cons (step360 p h) (sat_cons (step361 p h) (sat_cons (step355 p h) (sat_cons (step356 p h) (sat_cons (step39 p h) (sat_cons (step40 p h) (sat_cons (step45 p h) (sat_cons (step42 p h) (sat_cons (step50 p h) (sat_cons (step54 p h) (sat_cons (step43 p h) (sat_cons (step47 p h) (sat_cons (step325 p h) (sat_cons (step338 p h) (sat_cons (step638 p h) (sat_cons (step232 p h) (sat_cons (step221 p h) (sat_cons (step222 p h) (sat_cons (step220 p h) (sat_cons (step219 p h) (sat_cons (step218 p h) (sat_cons (step639 p h) (sat_cons (step62 p h) (sat_cons (step61 p h) (sat_cons (step32 p h) (sat_cons (step334 p h) (sat_cons (step328 p h) (sat_cons (step329 p h) (sat_cons (step36 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c641 : List Lit := [(391, false), (720, false), (728, false), (42, false)]
theorem step641 (p : Nat → Bool) (h : Constraints p) : clause p c641 = true :=
  Snake9.LocalRup.prove_clause [c538, c539, c533, c537] c641 (by decide) p (sat_cons (step538 p h) (sat_cons (step539 p h) (sat_cons (step533 p h) (sat_cons (step537 p h) (sat_nil p)))))
def c642 : List Lit := [(744, false), (728, false), (704, true), (42, false)]
theorem step642 (p : Nat → Bool) (h : Constraints p) : clause p c642 = true :=
  Snake9.LocalRup.prove_clause [c539, c507, c622, c634, c185, c588, c403, c503, c640, c641, c293, c612, c484, c485, c499, c475, c477, c439, c473, c466, c467, c434, c469, c465, c138, c433, c140, c432, c113] c642 (by decide) p (sat_cons (step539 p h) (sat_cons (step507 p h) (sat_cons (step622 p h) (sat_cons (step634 p h) (sat_cons (step185 p h) (sat_cons (step588 p h) (sat_cons (step403 p h) (sat_cons (step503 p h) (sat_cons (step640 p h) (sat_cons (step641 p h) (sat_cons (step293 p h) (sat_cons (step612 p h) (sat_cons (step484 p h) (sat_cons (step485 p h) (sat_cons (step499 p h) (sat_cons (step475 p h) (sat_cons (step477 p h) (sat_cons (step439 p h) (sat_cons (step473 p h) (sat_cons (step466 p h) (sat_cons (step467 p h) (sat_cons (step434 p h) (sat_cons (step469 p h) (sat_cons (step465 p h) (sat_cons (step138 p h) (sat_cons (step433 p h) (sat_cons (step140 p h) (sat_cons (step432 p h) (sat_cons (step113 p h) (sat_nil p))))))))))))))))))))))))))))))
def c643 : List Lit := [(728, false), (704, true), (42, false)]
theorem step643 (p : Nat → Bool) (h : Constraints p) : clause p c643 = true :=
  Snake9.LocalRup.prove_clause [c625, c161, c160, c162, c163, c530, c387, c642, c393, c396, c390, c367, c369, c377, c363, c365, c357, c360, c361, c355, c356, c45, c579, c42, c43, c50, c49, c54, c47, c375, c639, c65] c643 (by decide) p (sat_cons (step625 p h) (sat_cons (step161 p h) (sat_cons (step160 p h) (sat_cons (step162 p h) (sat_cons (step163 p h) (sat_cons (step530 p h) (sat_cons (step387 p h) (sat_cons (step642 p h) (sat_cons (step393 p h) (sat_cons (step396 p h) (sat_cons (step390 p h) (sat_cons (step367 p h) (sat_cons (step369 p h) (sat_cons (step377 p h) (sat_cons (step363 p h) (sat_cons (step365 p h) (sat_cons (step357 p h) (sat_cons (step360 p h) (sat_cons (step361 p h) (sat_cons (step355 p h) (sat_cons (step356 p h) (sat_cons (step45 p h) (sat_cons (step579 p h) (sat_cons (step42 p h) (sat_cons (step43 p h) (sat_cons (step50 p h) (sat_cons (step49 p h) (sat_cons (step54 p h) (sat_cons (step47 p h) (sat_cons (step375 p h) (sat_cons (step639 p h) (sat_cons (step65 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c644 : List Lit := [(721, true), (33, true), (688, true), (36, false), (39, false)]
theorem step644 (p : Nat → Bool) (h : Constraints p) : clause p c644 = true :=
  Snake9.LocalRup.prove_clause [c165, c160, c361, c363, c63, c368, c370, c364, c366, c357, c362, c356, c60, c53, c43, c320, c47, c326] c644 (by decide) p (sat_cons (step165 p h) (sat_cons (step160 p h) (sat_cons (step361 p h) (sat_cons (step363 p h) (sat_cons (step63 p h) (sat_cons (step368 p h) (sat_cons (step370 p h) (sat_cons (step364 p h) (sat_cons (step366 p h) (sat_cons (step357 p h) (sat_cons (step362 p h) (sat_cons (step356 p h) (sat_cons (step60 p h) (sat_cons (step53 p h) (sat_cons (step43 p h) (sat_cons (step320 p h) (sat_cons (step47 p h) (sat_cons (step326 p h) (sat_nil p)))))))))))))))))))
def c645 : List Lit := [(703, false), (704, true), (42, false)]
theorem step645 (p : Nat → Bool) (h : Constraints p) : clause p c645 = true :=
  Snake9.LocalRup.prove_clause [c166, c164, c626, c637, c507, c635, c643, c376, c374, c378, c58, c530, c534, c340, c373, c67, c64, c644, c399, c361, c68, c408, c407, c560, c504, c293, c494, c612, c484] c645 (by decide) p (sat_cons (step166 p h) (sat_cons (step164 p h) (sat_cons (step626 p h) (sat_cons (step637 p h) (sat_cons (step507 p h) (sat_cons (step635 p h) (sat_cons (step643 p h) (sat_cons (step376 p h) (sat_cons (step374 p h) (sat_cons (step378 p h) (sat_cons (step58 p h) (sat_cons (step530 p h) (sat_cons (step534 p h) (sat_cons (step340 p h) (sat_cons (step373 p h) (sat_cons (step67 p h) (sat_cons (step64 p h) (sat_cons (step644 p h) (sat_cons (step399 p h) (sat_cons (step361 p h) (sat_cons (step68 p h) (sat_cons (step408 p h) (sat_cons (step407 p h) (sat_cons (step560 p h) (sat_cons (step504 p h) (sat_cons (step293 p h) (sat_cons (step494 p h) (sat_cons (step612 p h) (sat_cons (step484 p h) (sat_nil p))))))))))))))))))))))))))))))
def c646 : List Lit := [(704, true), (42, false)]
theorem step646 (p : Nat → Bool) (h : Constraints p) : clause p c646 = true :=
  Snake9.LocalRup.prove_clause [c165, c538, c156, c182, c623, c530, c643, c376, c378, c374, c534, c63, c645, c529, c345, c337, c312, c323, c523, c320, c321, c305, c306, c10, c616, c13, c12, c26, c31, c442, c132, c445, c451, c461, c456] c646 (by decide) p (sat_cons (step165 p h) (sat_cons (step538 p h) (sat_cons (step156 p h) (sat_cons (step182 p h) (sat_cons (step623 p h) (sat_cons (step530 p h) (sat_cons (step643 p h) (sat_cons (step376 p h) (sat_cons (step378 p h) (sat_cons (step374 p h) (sat_cons (step534 p h) (sat_cons (step63 p h) (sat_cons (step645 p h) (sat_cons (step529 p h) (sat_cons (step345 p h) (sat_cons (step337 p h) (sat_cons (step312 p h) (sat_cons (step323 p h) (sat_cons (step523 p h) (sat_cons (step320 p h) (sat_cons (step321 p h) (sat_cons (step305 p h) (sat_cons (step306 p h) (sat_cons (step10 p h) (sat_cons (step616 p h) (sat_cons (step13 p h) (sat_cons (step12 p h) (sat_cons (step26 p h) (sat_cons (step31 p h) (sat_cons (step442 p h) (sat_cons (step132 p h) (sat_cons (step445 p h) (sat_cons (step451 p h) (sat_cons (step461 p h) (sat_cons (step456 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c647 : List Lit := [(1, false)]
theorem step647 (p : Nat → Bool) (h : Constraints p) : clause p c647 = true :=
  Snake9.LocalRup.prove_clause [c151, c594, c637, c507, c595, c635, c592, c187, c1, c646, c410, c411, c504, c633, c498, c494, c556, c484, c482, c590, c475, c564, c472, c147, c471] c647 (by decide) p (sat_cons (step151 p h) (sat_cons (step594 p h) (sat_cons (step637 p h) (sat_cons (step507 p h) (sat_cons (step595 p h) (sat_cons (step635 p h) (sat_cons (step592 p h) (sat_cons (step187 p h) (sat_cons (step1 p h) (sat_cons (step646 p h) (sat_cons (step410 p h) (sat_cons (step411 p h) (sat_cons (step504 p h) (sat_cons (step633 p h) (sat_cons (step498 p h) (sat_cons (step494 p h) (sat_cons (step556 p h) (sat_cons (step484 p h) (sat_cons (step482 p h) (sat_cons (step590 p h) (sat_cons (step475 p h) (sat_cons (step564 p h) (sat_cons (step472 p h) (sat_cons (step147 p h) (sat_cons (step471 p h) (sat_nil p))))))))))))))))))))))))))
def c648 : List Lit := [(671, true)]
theorem step648 (p : Nat → Bool) (h : Constraints p) : clause p c648 = true :=
  Snake9.LocalRup.prove_clause [c647, c303] c648 (by decide) p (sat_cons (step647 p h) (sat_cons (step303 p h) (sat_nil p)))
def c649 : List Lit := [(209, true)]
theorem step649 (p : Nat → Bool) (h : Constraints p) : clause p c649 = true :=
  Snake9.LocalRup.prove_clause [c647, c631, c536] c649 (by decide) p (sat_cons (step647 p h) (sat_cons (step631 p h) (sat_cons (step536 p h) (sat_nil p))))
def c650 : List Lit := [(680, true)]
theorem step650 (p : Nat → Bool) (h : Constraints p) : clause p c650 = true :=
  Snake9.LocalRup.prove_clause [c648, c526] c650 (by decide) p (sat_cons (step648 p h) (sat_cons (step526 p h) (sat_nil p)))
def c651 : List Lit := [(221, true)]
theorem step651 (p : Nat → Bool) (h : Constraints p) : clause p c651 = true :=
  Snake9.LocalRup.prove_clause [c649, c200] c651 (by decide) p (sat_cons (step649 p h) (sat_cons (step200 p h) (sat_nil p)))
def c652 : List Lit := [(703, true)]
theorem step652 (p : Nat → Bool) (h : Constraints p) : clause p c652 = true :=
  Snake9.LocalRup.prove_clause [c650, c538, c345] c652 (by decide) p (sat_cons (step650 p h) (sat_cons (step538 p h) (sat_cons (step345 p h) (sat_nil p))))
def c653 : List Lit := [(245, true)]
theorem step653 (p : Nat → Bool) (h : Constraints p) : clause p c653 = true :=
  Snake9.LocalRup.prove_clause [c651, c207] c653 (by decide) p (sat_cons (step651 p h) (sat_cons (step207 p h) (sat_nil p)))
def c654 : List Lit := [(755, true)]
theorem step654 (p : Nat → Bool) (h : Constraints p) : clause p c654 = true :=
  Snake9.LocalRup.prove_clause [c652, c594, c406] c654 (by decide) p (sat_cons (step652 p h) (sat_cons (step594 p h) (sat_cons (step406 p h) (sat_nil p))))
def c655 : List Lit := [(295, true)]
theorem step655 (p : Nat → Bool) (h : Constraints p) : clause p c655 = true :=
  Snake9.LocalRup.prove_clause [c653, c238] c655 (by decide) p (sat_cons (step653 p h) (sat_cons (step238 p h) (sat_nil p)))
def c656 : List Lit := [(849, false)]
theorem step656 (p : Nat → Bool) (h : Constraints p) : clause p c656 = true :=
  Snake9.LocalRup.prove_clause [c654, c507, c503] c656 (by decide) p (sat_cons (step654 p h) (sat_cons (step507 p h) (sat_cons (step503 p h) (sat_nil p))))
def c657 : List Lit := [(393, false)]
theorem step657 (p : Nat → Bool) (h : Constraints p) : clause p c657 = true :=
  Snake9.LocalRup.prove_clause [c655, c301, c299] c657 (by decide) p (sat_cons (step655 p h) (sat_cons (step301 p h) (sat_cons (step299 p h) (sat_nil p))))
def c658 : List Lit := [(391, false)]
theorem step658 (p : Nat → Bool) (h : Constraints p) : clause p c658 = true :=
  Snake9.LocalRup.prove_clause [c657, c294] c658 (by decide) p (sat_cons (step657 p h) (sat_cons (step294 p h) (sat_nil p)))
def c659 : List Lit := [(389, false)]
theorem step659 (p : Nat → Bool) (h : Constraints p) : clause p c659 = true :=
  Snake9.LocalRup.prove_clause [c658, c292] c659 (by decide) p (sat_cons (step658 p h) (sat_cons (step292 p h) (sat_nil p)))
def c660 : List Lit := [(365, false)]
theorem step660 (p : Nat → Bool) (h : Constraints p) : clause p c660 = true :=
  Snake9.LocalRup.prove_clause [c658, c293] c660 (by decide) p (sat_cons (step658 p h) (sat_cons (step293 p h) (sat_nil p)))
def c661 : List Lit := [(387, false)]
theorem step661 (p : Nat → Bool) (h : Constraints p) : clause p c661 = true :=
  Snake9.LocalRup.prove_clause [c659, c290] c661 (by decide) p (sat_cons (step659 p h) (sat_cons (step290 p h) (sat_nil p)))
def c662 : List Lit := [(379, false)]
theorem step662 (p : Nat → Bool) (h : Constraints p) : clause p c662 = true :=
  Snake9.LocalRup.prove_clause [c661, c289] c662 (by decide) p (sat_cons (step661 p h) (sat_cons (step289 p h) (sat_nil p)))
def c663 : List Lit := [(377, false)]
theorem step663 (p : Nat → Bool) (h : Constraints p) : clause p c663 = true :=
  Snake9.LocalRup.prove_clause [c662, c285] c663 (by decide) p (sat_cons (step662 p h) (sat_cons (step285 p h) (sat_nil p)))
def c664 : List Lit := [(195, false)]
theorem step664 (p : Nat → Bool) (h : Constraints p) : clause p c664 = true :=
  Snake9.LocalRup.prove_clause [c663, c284] c664 (by decide) p (sat_cons (step663 p h) (sat_cons (step284 p h) (sat_nil p)))
def c665 : List Lit := [(96, true)]
theorem step665 (p : Nat → Bool) (h : Constraints p) : clause p c665 = true :=
  Snake9.LocalRup.prove_clause [c664, c624, c558] c665 (by decide) p (sat_cons (step664 p h) (sat_cons (step624 p h) (sat_cons (step558 p h) (sat_nil p))))
def c666 : List Lit := [(95, true)]
theorem step666 (p : Nat → Bool) (h : Constraints p) : clause p c666 = true :=
  Snake9.LocalRup.prove_clause [c665, c187, c148] c666 (by decide) p (sat_cons (step665 p h) (sat_cons (step187 p h) (sat_cons (step148 p h) (sat_nil p))))
def c667 : List Lit := [(90, true)]
theorem step667 (p : Nat → Bool) (h : Constraints p) : clause p c667 = true :=
  Snake9.LocalRup.prove_clause [c666, c659, c624, c572] c667 (by decide) p (sat_cons (step666 p h) (sat_cons (step659 p h) (sat_cons (step624 p h) (sat_cons (step572 p h) (sat_nil p)))))
def c668 : List Lit := [(73, false)]
theorem step668 (p : Nat → Bool) (h : Constraints p) : clause p c668 = true :=
  Snake9.LocalRup.prove_clause [c178, c588, c667, c115, c113] c668 (by decide) p (sat_cons (step178 p h) (sat_cons (step588 p h) (sat_cons (step667 p h) (sat_cons (step115 p h) (sat_cons (step113 p h) (sat_nil p))))))
def c669 : List Lit := [(781, true)]
theorem step669 (p : Nat → Bool) (h : Constraints p) : clause p c669 = true :=
  Snake9.LocalRup.prove_clause [c668, c432] c669 (by decide) p (sat_cons (step668 p h) (sat_cons (step432 p h) (sat_nil p)))
def c670 : List Lit := [(783, true)]
theorem step670 (p : Nat → Bool) (h : Constraints p) : clause p c670 = true :=
  Snake9.LocalRup.prove_clause [c669, c433] c670 (by decide) p (sat_cons (step669 p h) (sat_cons (step433 p h) (sat_nil p)))
def c671 : List Lit := [(786, true)]
theorem step671 (p : Nat → Bool) (h : Constraints p) : clause p c671 = true :=
  Snake9.LocalRup.prove_clause [c670, c434] c671 (by decide) p (sat_cons (step670 p h) (sat_cons (step434 p h) (sat_nil p)))
def c672 : List Lit := [(793, true)]
theorem step672 (p : Nat → Bool) (h : Constraints p) : clause p c672 = true :=
  Snake9.LocalRup.prove_clause [c671, c634, c439] c672 (by decide) p (sat_cons (step671 p h) (sat_cons (step634 p h) (sat_cons (step439 p h) (sat_nil p))))
def c673 : List Lit := [(838, false)]
theorem step673 (p : Nat → Bool) (h : Constraints p) : clause p c673 = true :=
  Snake9.LocalRup.prove_clause [c672, c656, c499] c673 (by decide) p (sat_cons (step672 p h) (sat_cons (step656 p h) (sat_cons (step499 p h) (sat_nil p))))
def c674 : List Lit := [(848, true)]
theorem step674 (p : Nat → Bool) (h : Constraints p) : clause p c674 = true :=
  Snake9.LocalRup.prove_clause [c672, c595, c498] c674 (by decide) p (sat_cons (step672 p h) (sat_cons (step595 p h) (sat_cons (step498 p h) (sat_nil p))))
def c675 : List Lit := [(812, false)]
theorem step675 (p : Nat → Bool) (h : Constraints p) : clause p c675 = true :=
  Snake9.LocalRup.prove_clause [c673, c484] c675 (by decide) p (sat_cons (step673 p h) (sat_cons (step484 p h) (sat_nil p)))
def c676 : List Lit := [(756, false)]
theorem step676 (p : Nat → Bool) (h : Constraints p) : clause p c676 = true :=
  Snake9.LocalRup.prove_clause [c674, c507, c504] c676 (by decide) p (sat_cons (step674 p h) (sat_cons (step507 p h) (sat_cons (step504 p h) (sat_nil p))))
def c677 : List Lit := []
theorem step677 (p : Nat → Bool) (h : Constraints p) : clause p c677 = true :=
  Snake9.LocalRup.prove_clause [c676, c675, c648, c660, c610] c677 (by decide) p (sat_cons (step676 p h) (sat_cons (step675 p h) (sat_cons (step648 p h) (sat_cons (step660 p h) (sat_cons (step610 p h) (sat_nil p))))))
end B112E147
