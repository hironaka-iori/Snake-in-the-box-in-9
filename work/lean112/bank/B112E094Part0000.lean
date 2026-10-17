import B112E094Inputs
namespace B112E094
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c631 : List Lit := [(56, true)]
theorem step631 (p : Nat → Bool) (h : Constraints p) : clause p c631 = true :=
  Snake9.LocalRup.prove_clause [c75, c74] c631 (by decide) p (sat_cons (step75 p h) (sat_cons (step74 p h) (sat_nil p)))
def c632 : List Lit := [(160, true), (57, true)]
theorem step632 (p : Nat → Bool) (h : Constraints p) : clause p c632 = true :=
  Snake9.LocalRup.prove_clause [c631, c76] c632 (by decide) p (sat_cons (step631 p h) (sat_cons (step76 p h) (sat_nil p)))
def c633 : List Lit := [(97, false)]
theorem step633 (p : Nat → Bool) (h : Constraints p) : clause p c633 = true :=
  Snake9.LocalRup.prove_clause [c208, c154] c633 (by decide) p (sat_cons (step208 p h) (sat_cons (step154 p h) (sat_nil p)))
def c634 : List Lit := [(101, false)]
theorem step634 (p : Nat → Bool) (h : Constraints p) : clause p c634 = true :=
  Snake9.LocalRup.prove_clause [c210, c164] c634 (by decide) p (sat_cons (step210 p h) (sat_cons (step164 p h) (sat_nil p)))
def c635 : List Lit := [(410, false)]
theorem step635 (p : Nat → Bool) (h : Constraints p) : clause p c635 = true :=
  Snake9.LocalRup.prove_clause [c305, c302] c635 (by decide) p (sat_cons (step305 p h) (sat_cons (step302 p h) (sat_nil p)))
def c636 : List Lit := [(308, false)]
theorem step636 (p : Nat → Bool) (h : Constraints p) : clause p c636 = true :=
  Snake9.LocalRup.prove_clause [c305, c304] c636 (by decide) p (sat_cons (step305 p h) (sat_cons (step304 p h) (sat_nil p)))
def c637 : List Lit := [(306, false)]
theorem step637 (p : Nat → Bool) (h : Constraints p) : clause p c637 = true :=
  Snake9.LocalRup.prove_clause [c636, c253] c637 (by decide) p (sat_cons (step636 p h) (sat_cons (step253 p h) (sat_nil p)))
def c638 : List Lit := [(304, false)]
theorem step638 (p : Nat → Bool) (h : Constraints p) : clause p c638 = true :=
  Snake9.LocalRup.prove_clause [c637, c248] c638 (by decide) p (sat_cons (step637 p h) (sat_cons (step248 p h) (sat_nil p)))
def c639 : List Lit := [(280, false)]
theorem step639 (p : Nat → Bool) (h : Constraints p) : clause p c639 = true :=
  Snake9.LocalRup.prove_clause [c637, c251] c639 (by decide) p (sat_cons (step637 p h) (sat_cons (step251 p h) (sat_nil p)))
def c640 : List Lit := [(302, false)]
theorem step640 (p : Nat → Bool) (h : Constraints p) : clause p c640 = true :=
  Snake9.LocalRup.prove_clause [c638, c246] c640 (by decide) p (sat_cons (step638 p h) (sat_cons (step246 p h) (sat_nil p)))
def c641 : List Lit := [(266, false)]
theorem step641 (p : Nat → Bool) (h : Constraints p) : clause p c641 = true :=
  Snake9.LocalRup.prove_clause [c639, c236] c641 (by decide) p (sat_cons (step639 p h) (sat_cons (step236 p h) (sat_nil p)))
def c642 : List Lit := [(300, false)]
theorem step642 (p : Nat → Bool) (h : Constraints p) : clause p c642 = true :=
  Snake9.LocalRup.prove_clause [c640, c244] c642 (by decide) p (sat_cons (step640 p h) (sat_cons (step244 p h) (sat_nil p)))
def c643 : List Lit := [(260, false)]
theorem step643 (p : Nat → Bool) (h : Constraints p) : clause p c643 = true :=
  Snake9.LocalRup.prove_clause [c641, c230] c643 (by decide) p (sat_cons (step641 p h) (sat_cons (step230 p h) (sat_nil p)))
def c644 : List Lit := [(1390, true)]
theorem step644 (p : Nat → Bool) (h : Constraints p) : clause p c644 = true :=
  Snake9.LocalRup.prove_clause [c633, c561] c644 (by decide) p (sat_cons (step633 p h) (sat_cons (step561 p h) (sat_nil p)))
def c645 : List Lit := [(95, true), (1391, true)]
theorem step645 (p : Nat → Bool) (h : Constraints p) : clause p c645 = true :=
  Snake9.LocalRup.prove_clause [c633, c562] c645 (by decide) p (sat_cons (step633 p h) (sat_cons (step562 p h) (sat_nil p)))
def c646 : List Lit := [(1392, true)]
theorem step646 (p : Nat → Bool) (h : Constraints p) : clause p c646 = true :=
  Snake9.LocalRup.prove_clause [c644, c563] c646 (by decide) p (sat_cons (step644 p h) (sat_cons (step563 p h) (sat_nil p)))
def c647 : List Lit := [(93, true), (1393, true)]
theorem step647 (p : Nat → Bool) (h : Constraints p) : clause p c647 = true :=
  Snake9.LocalRup.prove_clause [c644, c565] c647 (by decide) p (sat_cons (step644 p h) (sat_cons (step565 p h) (sat_nil p)))
def c648 : List Lit := [(1395, true)]
theorem step648 (p : Nat → Bool) (h : Constraints p) : clause p c648 = true :=
  Snake9.LocalRup.prove_clause [c634, c567] c648 (by decide) p (sat_cons (step634 p h) (sat_cons (step567 p h) (sat_nil p)))
def c649 : List Lit := [(99, true), (1396, true)]
theorem step649 (p : Nat → Bool) (h : Constraints p) : clause p c649 = true :=
  Snake9.LocalRup.prove_clause [c634, c568] c649 (by decide) p (sat_cons (step634 p h) (sat_cons (step568 p h) (sat_nil p)))
def c650 : List Lit := [(1399, true)]
theorem step650 (p : Nat → Bool) (h : Constraints p) : clause p c650 = true :=
  Snake9.LocalRup.prove_clause [c648, c572] c650 (by decide) p (sat_cons (step648 p h) (sat_cons (step572 p h) (sat_nil p)))
def c651 : List Lit := [(1397, false), (1400, true)]
theorem step651 (p : Nat → Bool) (h : Constraints p) : clause p c651 = true :=
  Snake9.LocalRup.prove_clause [c648, c573] c651 (by decide) p (sat_cons (step648 p h) (sat_cons (step573 p h) (sat_nil p)))
def c652 : List Lit := [(1398, false), (1401, true)]
theorem step652 (p : Nat → Bool) (h : Constraints p) : clause p c652 = true :=
  Snake9.LocalRup.prove_clause [c648, c574] c652 (by decide) p (sat_cons (step648 p h) (sat_cons (step574 p h) (sat_nil p)))
def c653 : List Lit := [(1404, true)]
theorem step653 (p : Nat → Bool) (h : Constraints p) : clause p c653 = true :=
  Snake9.LocalRup.prove_clause [c646, c650, c577] c653 (by decide) p (sat_cons (step646 p h) (sat_cons (step650 p h) (sat_cons (step577 p h) (sat_nil p))))
def c654 : List Lit := [(1400, false), (1405, true)]
theorem step654 (p : Nat → Bool) (h : Constraints p) : clause p c654 = true :=
  Snake9.LocalRup.prove_clause [c646, c578] c654 (by decide) p (sat_cons (step646 p h) (sat_cons (step578 p h) (sat_nil p)))
def c655 : List Lit := [(1401, false), (1406, true)]
theorem step655 (p : Nat → Bool) (h : Constraints p) : clause p c655 = true :=
  Snake9.LocalRup.prove_clause [c646, c579] c655 (by decide) p (sat_cons (step646 p h) (sat_cons (step579 p h) (sat_nil p)))
def c656 : List Lit := [(1393, false), (1405, true)]
theorem step656 (p : Nat → Bool) (h : Constraints p) : clause p c656 = true :=
  Snake9.LocalRup.prove_clause [c650, c580] c656 (by decide) p (sat_cons (step650 p h) (sat_cons (step580 p h) (sat_nil p)))
def c657 : List Lit := [(1394, false), (1406, true)]
theorem step657 (p : Nat → Bool) (h : Constraints p) : clause p c657 = true :=
  Snake9.LocalRup.prove_clause [c650, c583] c657 (by decide) p (sat_cons (step650 p h) (sat_cons (step583 p h) (sat_nil p)))
def c658 : List Lit := [(1383, false), (1412, true)]
theorem step658 (p : Nat → Bool) (h : Constraints p) : clause p c658 = true :=
  Snake9.LocalRup.prove_clause [c653, c585] c658 (by decide) p (sat_cons (step653 p h) (sat_cons (step585 p h) (sat_nil p)))
def c659 : List Lit := [(1384, false), (1413, true)]
theorem step659 (p : Nat → Bool) (h : Constraints p) : clause p c659 = true :=
  Snake9.LocalRup.prove_clause [c653, c588] c659 (by decide) p (sat_cons (step653 p h) (sat_cons (step588 p h) (sat_nil p)))
def c660 : List Lit := [(1385, false), (1414, true)]
theorem step660 (p : Nat → Bool) (h : Constraints p) : clause p c660 = true :=
  Snake9.LocalRup.prove_clause [c653, c592] c660 (by decide) p (sat_cons (step653 p h) (sat_cons (step592 p h) (sat_nil p)))
def c661 : List Lit := [(1386, false), (1415, true)]
theorem step661 (p : Nat → Bool) (h : Constraints p) : clause p c661 = true :=
  Snake9.LocalRup.prove_clause [c653, c595] c661 (by decide) p (sat_cons (step653 p h) (sat_cons (step595 p h) (sat_nil p)))
def c662 : List Lit := [(1387, false), (1416, true)]
theorem step662 (p : Nat → Bool) (h : Constraints p) : clause p c662 = true :=
  Snake9.LocalRup.prove_clause [c653, c597] c662 (by decide) p (sat_cons (step653 p h) (sat_cons (step597 p h) (sat_nil p)))
def c663 : List Lit := [(28, false), (38, false), (36, false)]
theorem step663 (p : Nat → Bool) (h : Constraints p) : clause p c663 = true :=
  Snake9.LocalRup.prove_clause [c184, c52, c53] c663 (by decide) p (sat_cons (step184 p h) (sat_cons (step52 p h) (sat_cons (step53 p h) (sat_nil p))))
def c664 : List Lit := [(1269, true)]
theorem step664 (p : Nat → Bool) (h : Constraints p) : clause p c664 = true :=
  Snake9.LocalRup.prove_clause [c426, c428, c422, c416, c419, c420, c663] c664 (by decide) p (sat_cons (step426 p h) (sat_cons (step428 p h) (sat_cons (step422 p h) (sat_cons (step416 p h) (sat_cons (step419 p h) (sat_cons (step420 p h) (sat_cons (step663 p h) (sat_nil p))))))))
def c665 : List Lit := [(1295, true)]
theorem step665 (p : Nat → Bool) (h : Constraints p) : clause p c665 = true :=
  Snake9.LocalRup.prove_clause [c664, c455] c665 (by decide) p (sat_cons (step664 p h) (sat_cons (step455 p h) (sat_nil p)))
def c666 : List Lit := [(1358, true), (54, true)]
theorem step666 (p : Nat → Bool) (h : Constraints p) : clause p c666 = true :=
  Snake9.LocalRup.prove_clause [c191, c485, c495, c525, c522, c498, c513, c515, c486, c511, c501, c483, c505, c499, c77, c83] c666 (by decide) p (sat_cons (step191 p h) (sat_cons (step485 p h) (sat_cons (step495 p h) (sat_cons (step525 p h) (sat_cons (step522 p h) (sat_cons (step498 p h) (sat_cons (step513 p h) (sat_cons (step515 p h) (sat_cons (step486 p h) (sat_cons (step511 p h) (sat_cons (step501 p h) (sat_cons (step483 p h) (sat_cons (step505 p h) (sat_cons (step499 p h) (sat_cons (step77 p h) (sat_cons (step83 p h) (sat_nil p)))))))))))))))))
def c667 : List Lit := [(1344, true), (78, false), (88, true)]
theorem step667 (p : Nat → Bool) (h : Constraints p) : clause p c667 = true :=
  Snake9.LocalRup.prove_clause [c198, c506, c507, c95, c102] c667 (by decide) p (sat_cons (step198 p h) (sat_cons (step506 p h) (sat_cons (step507 p h) (sat_cons (step95 p h) (sat_cons (step102 p h) (sat_nil p))))))
def c668 : List Lit := [(91, true), (865, true), (94, true), (194, true)]
theorem step668 (p : Nat → Bool) (h : Constraints p) : clause p c668 = true :=
  Snake9.LocalRup.prove_clause [c206, c147, c338, c140, c339] c668 (by decide) p (sat_cons (step206 p h) (sat_cons (step147 p h) (sat_cons (step338 p h) (sat_cons (step140 p h) (sat_cons (step339 p h) (sat_nil p))))))
def c669 : List Lit := [(47, true), (1285, true), (152, true)]
theorem step669 (p : Nat → Bool) (h : Constraints p) : clause p c669 = true :=
  Snake9.LocalRup.prove_clause [c190, c439, c65, c447, c73, c441] c669 (by decide) p (sat_cons (step190 p h) (sat_cons (step439 p h) (sat_cons (step65 p h) (sat_cons (step447 p h) (sat_cons (step73 p h) (sat_cons (step441 p h) (sat_nil p)))))))
def c670 : List Lit := [(95, false), (47, false), (1385, false), (1346, false), (1430, true), (81, true)]
theorem step670 (p : Nat → Bool) (h : Constraints p) : clause p c670 = true :=
  Snake9.LocalRup.prove_clause [c207, c150, c161, c159, c570, c499, c651, c501, c654, c516, c593, c520, c607] c670 (by decide) p (sat_cons (step207 p h) (sat_cons (step150 p h) (sat_cons (step161 p h) (sat_cons (step159 p h) (sat_cons (step570 p h) (sat_cons (step499 p h) (sat_cons (step651 p h) (sat_cons (step501 p h) (sat_cons (step654 p h) (sat_cons (step516 p h) (sat_cons (step593 p h) (sat_cons (step520 p h) (sat_cons (step607 p h) (sat_nil p))))))))))))))
def c671 : List Lit := [(79, false), (1357, false), (1346, false), (1248, false), (81, true), (78, false), (30, false), (1372, false), (279, false), (1270, false)]
theorem step671 (p : Nat → Bool) (h : Constraints p) : clause p c671 = true :=
  Snake9.LocalRup.prove_clause [c637, c305, c202, c203, c622, c206, c459, c476, c618, c603, c249, c252, c303, c299, c298, c280, c278, c277, c276, c250, c245, c243, c241, c237, c98, c99, c121, c126, c539, c546, c553, c660, c594, c601, c657, c620, c478, c461, c450, c669, c670, c645, c139, c566, c148] c671 (by decide) p (sat_cons (step637 p h) (sat_cons (step305 p h) (sat_cons (step202 p h) (sat_cons (step203 p h) (sat_cons (step622 p h) (sat_cons (step206 p h) (sat_cons (step459 p h) (sat_cons (step476 p h) (sat_cons (step618 p h) (sat_cons (step603 p h) (sat_cons (step249 p h) (sat_cons (step252 p h) (sat_cons (step303 p h) (sat_cons (step299 p h) (sat_cons (step298 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step276 p h) (sat_cons (step250 p h) (sat_cons (step245 p h) (sat_cons (step243 p h) (sat_cons (step241 p h) (sat_cons (step237 p h) (sat_cons (step98 p h) (sat_cons (step99 p h) (sat_cons (step121 p h) (sat_cons (step126 p h) (sat_cons (step539 p h) (sat_cons (step546 p h) (sat_cons (step553 p h) (sat_cons (step660 p h) (sat_cons (step594 p h) (sat_cons (step601 p h) (sat_cons (step657 p h) (sat_cons (step620 p h) (sat_cons (step478 p h) (sat_cons (step461 p h) (sat_cons (step450 p h) (sat_cons (step669 p h) (sat_cons (step670 p h) (sat_cons (step645 p h) (sat_cons (step139 p h) (sat_cons (step566 p h) (sat_cons (step148 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c672 : List Lit := [(1385, false), (1393, false), (47, false), (1416, true), (1346, false), (1430, true)]
theorem step672 (p : Nat → Bool) (h : Constraints p) : clause p c672 = true :=
  Snake9.LocalRup.prove_clause [c211, c656, c594, c593, c581, c607, c651, c520, c570, c516, c168, c160, c501, c499] c672 (by decide) p (sat_cons (step211 p h) (sat_cons (step656 p h) (sat_cons (step594 p h) (sat_cons (step593 p h) (sat_cons (step581 p h) (sat_cons (step607 p h) (sat_cons (step651 p h) (sat_cons (step520 p h) (sat_cons (step570 p h) (sat_cons (step516 p h) (sat_cons (step168 p h) (sat_cons (step160 p h) (sat_cons (step501 p h) (sat_cons (step499 p h) (sat_nil p)))))))))))))))
def c673 : List Lit := [(89, true), (1376, true), (81, true)]
theorem step673 (p : Nat → Bool) (h : Constraints p) : clause p c673 = true :=
  Snake9.LocalRup.prove_clause [c202, c203, c121, c126, c539] c673 (by decide) p (sat_cons (step202 p h) (sat_cons (step203 p h) (sat_cons (step121 p h) (sat_cons (step126 p h) (sat_cons (step539 p h) (sat_nil p))))))
def c674 : List Lit := [(95, true), (47, false), (877, true), (1416, true), (1346, false), (1430, true), (81, true), (78, false), (30, false), (1372, false), (407, true)]
theorem step674 (p : Nat → Bool) (h : Constraints p) : clause p c674 = true :=
  Snake9.LocalRup.prove_clause [c206, c195, c551, c298, c280, c278, c277, c276, c275, c297, c295, c293, c292, c291, c645, c139, c564, c672, c553, c546, c673, c100, c148, c566, c141, c657, c668, c587, c348, c611, c344, c345, c521, c342, c343, c340, c518, c165, c166, c172, c502, c160, c84, c500] c674 (by decide) p (sat_cons (step206 p h) (sat_cons (step195 p h) (sat_cons (step551 p h) (sat_cons (step298 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step276 p h) (sat_cons (step275 p h) (sat_cons (step297 p h) (sat_cons (step295 p h) (sat_cons (step293 p h) (sat_cons (step292 p h) (sat_cons (step291 p h) (sat_cons (step645 p h) (sat_cons (step139 p h) (sat_cons (step564 p h) (sat_cons (step672 p h) (sat_cons (step553 p h) (sat_cons (step546 p h) (sat_cons (step673 p h) (sat_cons (step100 p h) (sat_cons (step148 p h) (sat_cons (step566 p h) (sat_cons (step141 p h) (sat_cons (step657 p h) (sat_cons (step668 p h) (sat_cons (step587 p h) (sat_cons (step348 p h) (sat_cons (step611 p h) (sat_cons (step344 p h) (sat_cons (step345 p h) (sat_cons (step521 p h) (sat_cons (step342 p h) (sat_cons (step343 p h) (sat_cons (step340 p h) (sat_cons (step518 p h) (sat_cons (step165 p h) (sat_cons (step166 p h) (sat_cons (step172 p h) (sat_cons (step502 p h) (sat_cons (step160 p h) (sat_cons (step84 p h) (sat_cons (step500 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c675 : List Lit := [(1379, true), (89, false), (78, false)]
theorem step675 (p : Nat → Bool) (h : Constraints p) : clause p c675 = true :=
  Snake9.LocalRup.prove_clause [c542, c543, c540, c538, c136] c675 (by decide) p (sat_cons (step542 p h) (sat_cons (step543 p h) (sat_cons (step540 p h) (sat_cons (step538 p h) (sat_cons (step136 p h) (sat_nil p))))))
def c676 : List Lit := [(47, false), (877, true), (79, true), (1416, true), (1430, true), (81, true), (78, false), (30, false), (1372, false), (407, true), (88, true)]
theorem step676 (p : Nat → Bool) (h : Constraints p) : clause p c676 = true :=
  Snake9.LocalRup.prove_clause [c198, c207, c206, c209, c197, c95, c667, c509, c298, c280, c278, c277, c276, c275, c674, c150, c151, c670, c161, c159, c140, c553, c570, c499, c546, c651, c501, c673, c654, c516, c100, c520, c147, c607, c142, c675, c552, c589, c590, c611, c655, c521, c576, c517, c649, c510, c158, c508, c143, c92] c676 (by decide) p (sat_cons (step198 p h) (sat_cons (step207 p h) (sat_cons (step206 p h) (sat_cons (step209 p h) (sat_cons (step197 p h) (sat_cons (step95 p h) (sat_cons (step667 p h) (sat_cons (step509 p h) (sat_cons (step298 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step276 p h) (sat_cons (step275 p h) (sat_cons (step674 p h) (sat_cons (step150 p h) (sat_cons (step151 p h) (sat_cons (step670 p h) (sat_cons (step161 p h) (sat_cons (step159 p h) (sat_cons (step140 p h) (sat_cons (step553 p h) (sat_cons (step570 p h) (sat_cons (step499 p h) (sat_cons (step546 p h) (sat_cons (step651 p h) (sat_cons (step501 p h) (sat_cons (step673 p h) (sat_cons (step654 p h) (sat_cons (step516 p h) (sat_cons (step100 p h) (sat_cons (step520 p h) (sat_cons (step147 p h) (sat_cons (step607 p h) (sat_cons (step142 p h) (sat_cons (step675 p h) (sat_cons (step552 p h) (sat_cons (step589 p h) (sat_cons (step590 p h) (sat_cons (step611 p h) (sat_cons (step655 p h) (sat_cons (step521 p h) (sat_cons (step576 p h) (sat_cons (step517 p h) (sat_cons (step649 p h) (sat_cons (step510 p h) (sat_cons (step158 p h) (sat_cons (step508 p h) (sat_cons (step143 p h) (sat_cons (step92 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c677 : List Lit := [(1357, false), (730, false), (1248, false), (81, true), (78, false), (30, false), (1372, false), (279, false), (750, false), (1270, false), (758, false), (88, true)]
theorem step677 (p : Nat → Bool) (h : Constraints p) : clause p c677 = true :=
  Snake9.TreeRup.prove_clause [c637, c305, c622, c359, c206, c207, c667, c509, c325, c327, c331, c356, c355, c459, c476, c618, c333, c249, c252, c303, c299, c298, c280, c278, c277, c276, c275, c250, c245, c243, c241, c237, c335, c336, c603, c671, c334, c337, c352, c676, c65, c669, c323, c450, c324, c461, c326, c478, c328, c620, c332, c601, c357, c660, c354, c553, c351, c546, c347, c673, c100, c675, c668, c552, c141, c659, c589, c148, c605, c654, c139, c520, c651, c150, c516, c570, c501, c162, c499] c677 (by decide) p (sat_cons (step637 p h) (sat_cons (step305 p h) (sat_cons (step622 p h) (sat_cons (step359 p h) (sat_cons (step206 p h) (sat_cons (step207 p h) (sat_cons (step667 p h) (sat_cons (step509 p h) (sat_cons (step325 p h) (sat_cons (step327 p h) (sat_cons (step331 p h) (sat_cons (step356 p h) (sat_cons (step355 p h) (sat_cons (step459 p h) (sat_cons (step476 p h) (sat_cons (step618 p h) (sat_cons (step333 p h) (sat_cons (step249 p h) (sat_cons (step252 p h) (sat_cons (step303 p h) (sat_cons (step299 p h) (sat_cons (step298 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step276 p h) (sat_cons (step275 p h) (sat_cons (step250 p h) (sat_cons (step245 p h) (sat_cons (step243 p h) (sat_cons (step241 p h) (sat_cons (step237 p h) (sat_cons (step335 p h) (sat_cons (step336 p h) (sat_cons (step603 p h) (sat_cons (step671 p h) (sat_cons (step334 p h) (sat_cons (step337 p h) (sat_cons (step352 p h) (sat_cons (step676 p h) (sat_cons (step65 p h) (sat_cons (step669 p h) (sat_cons (step323 p h) (sat_cons (step450 p h) (sat_cons (step324 p h) (sat_cons (step461 p h) (sat_cons (step326 p h) (sat_cons (step478 p h) (sat_cons (step328 p h) (sat_cons (step620 p h) (sat_cons (step332 p h) (sat_cons (step601 p h) (sat_cons (step357 p h) (sat_cons (step660 p h) (sat_cons (step354 p h) (sat_cons (step553 p h) (sat_cons (step351 p h) (sat_cons (step546 p h) (sat_cons (step347 p h) (sat_cons (step673 p h) (sat_cons (step100 p h) (sat_cons (step675 p h) (sat_cons (step668 p h) (sat_cons (step552 p h) (sat_cons (step141 p h) (sat_cons (step659 p h) (sat_cons (step589 p h) (sat_cons (step148 p h) (sat_cons (step605 p h) (sat_cons (step654 p h) (sat_cons (step139 p h) (sat_cons (step520 p h) (sat_cons (step651 p h) (sat_cons (step150 p h) (sat_cons (step516 p h) (sat_cons (step570 p h) (sat_cons (step501 p h) (sat_cons (step162 p h) (sat_cons (step499 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c678 : List Lit := [(29, false), (1372, false), (31, false), (134, true), (279, false), (25, true), (27, true), (1270, false), (758, false), (88, true), (32, false)]
theorem step678 (p : Nat → Bool) (h : Constraints p) : clause p c678 = true :=
  Snake9.LocalRup.prove_clause [c636, c181, c173, c174, c249, c255, c220, c214, c213, c212, c385, c388, c393, c314, c316, c320, c33, c35, c38, c42, c40, c8, c11, c361, c9, c366, c306, c376, c307, c407, c308, c313, c667, c509, c677, c513, c519] c678 (by decide) p (sat_cons (step636 p h) (sat_cons (step181 p h) (sat_cons (step173 p h) (sat_cons (step174 p h) (sat_cons (step249 p h) (sat_cons (step255 p h) (sat_cons (step220 p h) (sat_cons (step214 p h) (sat_cons (step213 p h) (sat_cons (step212 p h) (sat_cons (step385 p h) (sat_cons (step388 p h) (sat_cons (step393 p h) (sat_cons (step314 p h) (sat_cons (step316 p h) (sat_cons (step320 p h) (sat_cons (step33 p h) (sat_cons (step35 p h) (sat_cons (step38 p h) (sat_cons (step42 p h) (sat_cons (step40 p h) (sat_cons (step8 p h) (sat_cons (step11 p h) (sat_cons (step361 p h) (sat_cons (step9 p h) (sat_cons (step366 p h) (sat_cons (step306 p h) (sat_cons (step376 p h) (sat_cons (step307 p h) (sat_cons (step407 p h) (sat_cons (step308 p h) (sat_cons (step313 p h) (sat_cons (step667 p h) (sat_cons (step509 p h) (sat_cons (step677 p h) (sat_cons (step513 p h) (sat_cons (step519 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c679 : List Lit := [(95, false), (47, false), (1384, false), (1429, true), (1346, false), (81, true)]
theorem step679 (p : Nat → Bool) (h : Constraints p) : clause p c679 = true :=
  Snake9.LocalRup.prove_clause [c207, c150, c161, c159, c570, c499, c651, c501, c654, c516, c589, c520, c606] c679 (by decide) p (sat_cons (step207 p h) (sat_cons (step150 p h) (sat_cons (step161 p h) (sat_cons (step159 p h) (sat_cons (step570 p h) (sat_cons (step499 p h) (sat_cons (step651 p h) (sat_cons (step501 p h) (sat_cons (step654 p h) (sat_cons (step516 p h) (sat_cons (step589 p h) (sat_cons (step520 p h) (sat_cons (step606 p h) (sat_nil p))))))))))))))
def c680 : List Lit := [(1384, true), (78, false), (81, true), (1372, false)]
theorem step680 (p : Nat → Bool) (h : Constraints p) : clause p c680 = true :=
  Snake9.LocalRup.prove_clause [c549, c552, c546, c675, c673] c680 (by decide) p (sat_cons (step549 p h) (sat_cons (step552 p h) (sat_cons (step546 p h) (sat_cons (step675 p h) (sat_cons (step673 p h) (sat_nil p))))))
def c681 : List Lit := [(1379, true), (78, false), (81, true)]
theorem step681 (p : Nat → Bool) (h : Constraints p) : clause p c681 = true :=
  Snake9.LocalRup.prove_clause [c202, c543, c675, c538, c121] c681 (by decide) p (sat_cons (step202 p h) (sat_cons (step543 p h) (sat_cons (step675 p h) (sat_cons (step538 p h) (sat_cons (step121 p h) (sat_nil p))))))
def c682 : List Lit := [(47, true), (1290, true), (299, true)]
theorem step682 (p : Nat → Bool) (h : Constraints p) : clause p c682 = true :=
  Snake9.LocalRup.prove_clause [c190, c189, c187, c451, c241, c237, c240, c238, c439, c65, c669, c448, c73, c454, c443, c437, c438, c67, c435, c68, c63, c71] c682 (by decide) p (sat_cons (step190 p h) (sat_cons (step189 p h) (sat_cons (step187 p h) (sat_cons (step451 p h) (sat_cons (step241 p h) (sat_cons (step237 p h) (sat_cons (step240 p h) (sat_cons (step238 p h) (sat_cons (step439 p h) (sat_cons (step65 p h) (sat_cons (step669 p h) (sat_cons (step448 p h) (sat_cons (step73 p h) (sat_cons (step454 p h) (sat_cons (step443 p h) (sat_cons (step437 p h) (sat_cons (step438 p h) (sat_cons (step67 p h) (sat_cons (step435 p h) (sat_cons (step68 p h) (sat_cons (step63 p h) (sat_cons (step71 p h) (sat_nil p)))))))))))))))))))))))
def c683 : List Lit := [(1405, true), (47, false)]
theorem step683 (p : Nat → Bool) (h : Constraints p) : clause p c683 = true :=
  Snake9.LocalRup.prove_clause [c211, c654, c656, c651, c564, c570, c645, c168, c161] c683 (by decide) p (sat_cons (step211 p h) (sat_cons (step654 p h) (sat_cons (step656 p h) (sat_cons (step651 p h) (sat_cons (step564 p h) (sat_cons (step570 p h) (sat_cons (step645 p h) (sat_cons (step168 p h) (sat_cons (step161 p h) (sat_nil p))))))))))
def c684 : List Lit := [(1323, false), (1359, true), (1346, false)]
theorem step684 (p : Nat → Bool) (h : Constraints p) : clause p c684 = true :=
  Snake9.LocalRup.prove_clause [c193, c513, c526, c495, c496, c523, c490, c516, c488, c501, c503, c80, c499, c78] c684 (by decide) p (sat_cons (step193 p h) (sat_cons (step513 p h) (sat_cons (step526 p h) (sat_cons (step495 p h) (sat_cons (step496 p h) (sat_cons (step523 p h) (sat_cons (step490 p h) (sat_cons (step516 p h) (sat_cons (step488 p h) (sat_cons (step501 p h) (sat_cons (step503 p h) (sat_cons (step80 p h) (sat_cons (step499 p h) (sat_cons (step78 p h) (sat_nil p)))))))))))))))
def c685 : List Lit := [(65, false), (100, false), (1327, true), (357, true)]
theorem step685 (p : Nat → Bool) (h : Constraints p) : clause p c685 = true :=
  Snake9.LocalRup.prove_clause [c191, c193, c194, c271, c258, c257, c256, c632, c77, c270, c269, c264, c263, c82, c83, c80, c86, c489, c81] c685 (by decide) p (sat_cons (step191 p h) (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step271 p h) (sat_cons (step258 p h) (sat_cons (step257 p h) (sat_cons (step256 p h) (sat_cons (step632 p h) (sat_cons (step77 p h) (sat_cons (step270 p h) (sat_cons (step269 p h) (sat_cons (step264 p h) (sat_cons (step263 p h) (sat_cons (step82 p h) (sat_cons (step83 p h) (sat_cons (step80 p h) (sat_cons (step86 p h) (sat_cons (step489 p h) (sat_cons (step81 p h) (sat_nil p))))))))))))))))))))
def c686 : List Lit := [(95, true), (104, false), (71, false), (65, true), (1407, true), (100, false), (94, true), (407, true), (88, true)]
theorem step686 (p : Nat → Bool) (h : Constraints p) : clause p c686 = true :=
  Snake9.LocalRup.prove_clause [c634, c206, c211, c209, c298, c280, c278, c277, c276, c297, c295, c294, c289, c288, c645, c139, c163, c148, c167, c566, c172, c584, c157, c575, c649] c686 (by decide) p (sat_cons (step634 p h) (sat_cons (step206 p h) (sat_cons (step211 p h) (sat_cons (step209 p h) (sat_cons (step298 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step276 p h) (sat_cons (step297 p h) (sat_cons (step295 p h) (sat_cons (step294 p h) (sat_cons (step289 p h) (sat_cons (step288 p h) (sat_cons (step645 p h) (sat_cons (step139 p h) (sat_cons (step163 p h) (sat_cons (step148 p h) (sat_cons (step167 p h) (sat_cons (step566 p h) (sat_cons (step172 p h) (sat_cons (step584 p h) (sat_cons (step157 p h) (sat_cons (step575 p h) (sat_cons (step649 p h) (sat_nil p))))))))))))))))))))))))))
def c687 : List Lit := [(95, false), (1376, true), (81, false), (31, false)]
theorem step687 (p : Nat → Bool) (h : Constraints p) : clause p c687 = true :=
  Snake9.LocalRup.prove_clause [c109, c110, c539] c687 (by decide) p (sat_cons (step109 p h) (sat_cons (step110 p h) (sat_cons (step539 p h) (sat_nil p))))
def c688 : List Lit := [(1370, true), (95, false), (81, false)]
theorem step688 (p : Nat → Bool) (h : Constraints p) : clause p c688 = true :=
  Snake9.LocalRup.prove_clause [c529, c530, c112] c688 (by decide) p (sat_cons (step529 p h) (sat_cons (step530 p h) (sat_cons (step112 p h) (sat_nil p))))
def c689 : List Lit := [(1259, true), (1372, false), (134, true), (279, false), (25, true), (27, true), (1270, false), (758, false), (88, true), (32, false)]
theorem step689 (p : Nat → Bool) (h : Constraints p) : clause p c689 = true :=
  Snake9.LocalRup.prove_clause [c411, c412, c678] c689 (by decide) p (sat_cons (step411 p h) (sat_cons (step412 p h) (sat_cons (step678 p h) (sat_nil p))))
def c690 : List Lit := [(1346, true), (88, true)]
theorem step690 (p : Nat → Bool) (h : Constraints p) : clause p c690 = true :=
  Snake9.LocalRup.prove_clause [c198, c509, c511, c506, c507, c504, c96, c91] c690 (by decide) p (sat_cons (step198 p h) (sat_cons (step509 p h) (sat_cons (step511 p h) (sat_cons (step506 p h) (sat_cons (step507 p h) (sat_cons (step504 p h) (sat_cons (step96 p h) (sat_cons (step91 p h) (sat_nil p)))))))))
def c691 : List Lit := [(1375, true), (81, false), (136, true), (32, false)]
theorem step691 (p : Nat → Bool) (h : Constraints p) : clause p c691 = true :=
  Snake9.LocalRup.prove_clause [c537, c538, c108, c114, c48] c691 (by decide) p (sat_cons (step537 p h) (sat_cons (step538 p h) (sat_cons (step108 p h) (sat_cons (step114 p h) (sat_cons (step48 p h) (sat_nil p))))))
def c692 : List Lit := [(1379, true), (89, false)]
theorem step692 (p : Nat → Bool) (h : Constraints p) : clause p c692 = true :=
  Snake9.LocalRup.prove_clause [c542, c543, c540, c537, c538, c138] c692 (by decide) p (sat_cons (step542 p h) (sat_cons (step543 p h) (sat_cons (step540 p h) (sat_cons (step537 p h) (sat_cons (step538 p h) (sat_cons (step138 p h) (sat_nil p)))))))
def c693 : List Lit := [(29, false), (25, false), (27, true)]
theorem step693 (p : Nat → Bool) (h : Constraints p) : clause p c693 = true :=
  Snake9.LocalRup.prove_clause [c181, c33, c35, c623] c693 (by decide) p (sat_cons (step181 p h) (sat_cons (step33 p h) (sat_cons (step35 p h) (sat_cons (step623 p h) (sat_nil p)))))
def c694 : List Lit := [(1, true), (1213, true)]
theorem step694 (p : Nat → Bool) (h : Constraints p) : clause p c694 = true :=
  Snake9.LocalRup.prove_clause [c173, c174, c8, c11, c366, c361] c694 (by decide) p (sat_cons (step173 p h) (sat_cons (step174 p h) (sat_cons (step8 p h) (sat_cons (step11 p h) (sat_cons (step366 p h) (sat_cons (step361 p h) (sat_nil p)))))))
end B112E094
