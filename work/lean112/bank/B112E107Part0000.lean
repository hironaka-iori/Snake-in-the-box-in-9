import B112E107Inputs
namespace B112E107
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c756 : List Lit := [(2, false)]
theorem step756 (p : Nat → Bool) (h : Constraints p) : clause p c756 = true :=
  Snake9.LocalRup.prove_clause [c224, c2] c756 (by decide) p (sat_cons (step224 p h) (sat_cons (step2 p h) (sat_nil p)))
def c757 : List Lit := [(5, false)]
theorem step757 (p : Nat → Bool) (h : Constraints p) : clause p c757 = true :=
  Snake9.LocalRup.prove_clause [c226, c7] c757 (by decide) p (sat_cons (step226 p h) (sat_cons (step7 p h) (sat_nil p)))
def c758 : List Lit := [(7, false)]
theorem step758 (p : Nat → Bool) (h : Constraints p) : clause p c758 = true :=
  Snake9.LocalRup.prove_clause [c227, c11] c758 (by decide) p (sat_cons (step227 p h) (sat_cons (step11 p h) (sat_nil p)))
def c759 : List Lit := [(434, false)]
theorem step759 (p : Nat → Bool) (h : Constraints p) : clause p c759 = true :=
  Snake9.LocalRup.prove_clause [c425, c422] c759 (by decide) p (sat_cons (step425 p h) (sat_cons (step422 p h) (sat_nil p)))
def c760 : List Lit := [(326, false)]
theorem step760 (p : Nat → Bool) (h : Constraints p) : clause p c760 = true :=
  Snake9.LocalRup.prove_clause [c425, c424] c760 (by decide) p (sat_cons (step425 p h) (sat_cons (step424 p h) (sat_nil p)))
def c761 : List Lit := [(432, false)]
theorem step761 (p : Nat → Bool) (h : Constraints p) : clause p c761 = true :=
  Snake9.LocalRup.prove_clause [c759, c418] c761 (by decide) p (sat_cons (step759 p h) (sat_cons (step418 p h) (sat_nil p)))
def c762 : List Lit := [(378, false)]
theorem step762 (p : Nat → Bool) (h : Constraints p) : clause p c762 = true :=
  Snake9.LocalRup.prove_clause [c759, c421] c762 (by decide) p (sat_cons (step759 p h) (sat_cons (step421 p h) (sat_nil p)))
def c763 : List Lit := [(324, false)]
theorem step763 (p : Nat → Bool) (h : Constraints p) : clause p c763 = true :=
  Snake9.LocalRup.prove_clause [c760, c328] c763 (by decide) p (sat_cons (step760 p h) (sat_cons (step328 p h) (sat_nil p)))
def c764 : List Lit := [(272, false)]
theorem step764 (p : Nat → Bool) (h : Constraints p) : clause p c764 = true :=
  Snake9.LocalRup.prove_clause [c760, c331] c764 (by decide) p (sat_cons (step760 p h) (sat_cons (step331 p h) (sat_nil p)))
def c765 : List Lit := [(430, false)]
theorem step765 (p : Nat → Bool) (h : Constraints p) : clause p c765 = true :=
  Snake9.LocalRup.prove_clause [c761, c414] c765 (by decide) p (sat_cons (step761 p h) (sat_cons (step414 p h) (sat_nil p)))
def c766 : List Lit := [(404, false)]
theorem step766 (p : Nat → Bool) (h : Constraints p) : clause p c766 = true :=
  Snake9.LocalRup.prove_clause [c761, c416] c766 (by decide) p (sat_cons (step761 p h) (sat_cons (step416 p h) (sat_nil p)))
def c767 : List Lit := [(376, false)]
theorem step767 (p : Nat → Bool) (h : Constraints p) : clause p c767 = true :=
  Snake9.LocalRup.prove_clause [c762, c371] c767 (by decide) p (sat_cons (step762 p h) (sat_cons (step371 p h) (sat_nil p)))
def c768 : List Lit := [(350, false)]
theorem step768 (p : Nat → Bool) (h : Constraints p) : clause p c768 = true :=
  Snake9.LocalRup.prove_clause [c762, c374] c768 (by decide) p (sat_cons (step762 p h) (sat_cons (step374 p h) (sat_nil p)))
def c769 : List Lit := [(322, false)]
theorem step769 (p : Nat → Bool) (h : Constraints p) : clause p c769 = true :=
  Snake9.LocalRup.prove_clause [c763, c323] c769 (by decide) p (sat_cons (step763 p h) (sat_cons (step323 p h) (sat_nil p)))
def c770 : List Lit := [(296, false)]
theorem step770 (p : Nat → Bool) (h : Constraints p) : clause p c770 = true :=
  Snake9.LocalRup.prove_clause [c763, c326] c770 (by decide) p (sat_cons (step763 p h) (sat_cons (step326 p h) (sat_nil p)))
def c771 : List Lit := [(270, false)]
theorem step771 (p : Nat → Bool) (h : Constraints p) : clause p c771 = true :=
  Snake9.LocalRup.prove_clause [c764, c290] c771 (by decide) p (sat_cons (step764 p h) (sat_cons (step290 p h) (sat_nil p)))
def c772 : List Lit := [(244, false)]
theorem step772 (p : Nat → Bool) (h : Constraints p) : clause p c772 = true :=
  Snake9.LocalRup.prove_clause [c764, c293] c772 (by decide) p (sat_cons (step764 p h) (sat_cons (step293 p h) (sat_nil p)))
def c773 : List Lit := [(428, false)]
theorem step773 (p : Nat → Bool) (h : Constraints p) : clause p c773 = true :=
  Snake9.LocalRup.prove_clause [c765, c410] c773 (by decide) p (sat_cons (step765 p h) (sat_cons (step410 p h) (sat_nil p)))
def c774 : List Lit := [(416, false)]
theorem step774 (p : Nat → Bool) (h : Constraints p) : clause p c774 = true :=
  Snake9.LocalRup.prove_clause [c765, c412] c774 (by decide) p (sat_cons (step765 p h) (sat_cons (step412 p h) (sat_nil p)))
def c775 : List Lit := [(390, false)]
theorem step775 (p : Nat → Bool) (h : Constraints p) : clause p c775 = true :=
  Snake9.LocalRup.prove_clause [c766, c392] c775 (by decide) p (sat_cons (step766 p h) (sat_cons (step392 p h) (sat_nil p)))
def c776 : List Lit := [(362, false)]
theorem step776 (p : Nat → Bool) (h : Constraints p) : clause p c776 = true :=
  Snake9.LocalRup.prove_clause [c767, c369] c776 (by decide) p (sat_cons (step767 p h) (sat_cons (step369 p h) (sat_nil p)))
def c777 : List Lit := [(348, false)]
theorem step777 (p : Nat → Bool) (h : Constraints p) : clause p c777 = true :=
  Snake9.LocalRup.prove_clause [c768, c349] c777 (by decide) p (sat_cons (step768 p h) (sat_cons (step349 p h) (sat_nil p)))
def c778 : List Lit := [(336, false)]
theorem step778 (p : Nat → Bool) (h : Constraints p) : clause p c778 = true :=
  Snake9.LocalRup.prove_clause [c768, c352] c778 (by decide) p (sat_cons (step768 p h) (sat_cons (step352 p h) (sat_nil p)))
def c779 : List Lit := [(320, false)]
theorem step779 (p : Nat → Bool) (h : Constraints p) : clause p c779 = true :=
  Snake9.LocalRup.prove_clause [c769, c321] c779 (by decide) p (sat_cons (step769 p h) (sat_cons (step321 p h) (sat_nil p)))
def c780 : List Lit := [(294, false)]
theorem step780 (p : Nat → Bool) (h : Constraints p) : clause p c780 = true :=
  Snake9.LocalRup.prove_clause [c770, c307] c780 (by decide) p (sat_cons (step770 p h) (sat_cons (step307 p h) (sat_nil p)))
def c781 : List Lit := [(268, false)]
theorem step781 (p : Nat → Bool) (h : Constraints p) : clause p c781 = true :=
  Snake9.LocalRup.prove_clause [c771, c285] c781 (by decide) p (sat_cons (step771 p h) (sat_cons (step285 p h) (sat_nil p)))
def c782 : List Lit := [(256, false)]
theorem step782 (p : Nat → Bool) (h : Constraints p) : clause p c782 = true :=
  Snake9.LocalRup.prove_clause [c771, c288] c782 (by decide) p (sat_cons (step771 p h) (sat_cons (step288 p h) (sat_nil p)))
def c783 : List Lit := [(426, false)]
theorem step783 (p : Nat → Bool) (h : Constraints p) : clause p c783 = true :=
  Snake9.LocalRup.prove_clause [c773, c407] c783 (by decide) p (sat_cons (step773 p h) (sat_cons (step407 p h) (sat_nil p)))
def c784 : List Lit := [(388, false)]
theorem step784 (p : Nat → Bool) (h : Constraints p) : clause p c784 = true :=
  Snake9.LocalRup.prove_clause [c775, c384] c784 (by decide) p (sat_cons (step775 p h) (sat_cons (step384 p h) (sat_nil p)))
def c785 : List Lit := [(360, false)]
theorem step785 (p : Nat → Bool) (h : Constraints p) : clause p c785 = true :=
  Snake9.LocalRup.prove_clause [c776, c361] c785 (by decide) p (sat_cons (step776 p h) (sat_cons (step361 p h) (sat_nil p)))
def c786 : List Lit := [(346, false)]
theorem step786 (p : Nat → Bool) (h : Constraints p) : clause p c786 = true :=
  Snake9.LocalRup.prove_clause [c777, c345] c786 (by decide) p (sat_cons (step777 p h) (sat_cons (step345 p h) (sat_nil p)))
def c787 : List Lit := [(312, false)]
theorem step787 (p : Nat → Bool) (h : Constraints p) : clause p c787 = true :=
  Snake9.LocalRup.prove_clause [c779, c319] c787 (by decide) p (sat_cons (step779 p h) (sat_cons (step319 p h) (sat_nil p)))
def c788 : List Lit := [(260, false)]
theorem step788 (p : Nat → Bool) (h : Constraints p) : clause p c788 = true :=
  Snake9.LocalRup.prove_clause [c781, c283] c788 (by decide) p (sat_cons (step781 p h) (sat_cons (step283 p h) (sat_nil p)))
def c789 : List Lit := [(422, false)]
theorem step789 (p : Nat → Bool) (h : Constraints p) : clause p c789 = true :=
  Snake9.LocalRup.prove_clause [c783, c405] c789 (by decide) p (sat_cons (step783 p h) (sat_cons (step405 p h) (sat_nil p)))
def c790 : List Lit := [(1335, true)]
theorem step790 (p : Nat → Bool) (h : Constraints p) : clause p c790 = true :=
  Snake9.LocalRup.prove_clause [c442, c444, c437, c439, c429, c435, c426, c427, c12, c27, c17] c790 (by decide) p (sat_cons (step442 p h) (sat_cons (step444 p h) (sat_cons (step437 p h) (sat_cons (step439 p h) (sat_cons (step429 p h) (sat_cons (step435 p h) (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_cons (step12 p h) (sat_cons (step27 p h) (sat_cons (step17 p h) (sat_nil p))))))))))))
def c791 : List Lit := [(1361, true)]
theorem step791 (p : Nat → Bool) (h : Constraints p) : clause p c791 = true :=
  Snake9.LocalRup.prove_clause [c790, c484] c791 (by decide) p (sat_cons (step790 p h) (sat_cons (step484 p h) (sat_nil p)))
def c792 : List Lit := [(1354, true)]
theorem step792 (p : Nat → Bool) (h : Constraints p) : clause p c792 = true :=
  Snake9.LocalRup.prove_clause [c472, c475, c467, c469, c456, c465, c461, c462, c453, c51, c39, c43] c792 (by decide) p (sat_cons (step472 p h) (sat_cons (step475 p h) (sat_cons (step467 p h) (sat_cons (step469 p h) (sat_cons (step456 p h) (sat_cons (step465 p h) (sat_cons (step461 p h) (sat_cons (step462 p h) (sat_cons (step453 p h) (sat_cons (step51 p h) (sat_cons (step39 p h) (sat_cons (step43 p h) (sat_nil p)))))))))))))
def c793 : List Lit := [(1362, true)]
theorem step793 (p : Nat → Bool) (h : Constraints p) : clause p c793 = true :=
  Snake9.LocalRup.prove_clause [c792, c790, c485] c793 (by decide) p (sat_cons (step792 p h) (sat_cons (step790 p h) (sat_cons (step485 p h) (sat_nil p))))
def c794 : List Lit := [(1403, true)]
theorem step794 (p : Nat → Bool) (h : Constraints p) : clause p c794 = true :=
  Snake9.LocalRup.prove_clause [c532, c536, c525, c527, c514, c522, c523, c519, c520, c511, c512, c72, c75, c89, c87] c794 (by decide) p (sat_cons (step532 p h) (sat_cons (step536 p h) (sat_cons (step525 p h) (sat_cons (step527 p h) (sat_cons (step514 p h) (sat_cons (step522 p h) (sat_cons (step523 p h) (sat_cons (step519 p h) (sat_cons (step520 p h) (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step72 p h) (sat_cons (step75 p h) (sat_cons (step89 p h) (sat_cons (step87 p h) (sat_nil p))))))))))))))))
def c795 : List Lit := [(1410, true)]
theorem step795 (p : Nat → Bool) (h : Constraints p) : clause p c795 = true :=
  Snake9.LocalRup.prove_clause [c794, c544] c795 (by decide) p (sat_cons (step794 p h) (sat_cons (step544 p h) (sat_nil p)))
def c796 : List Lit := [(38, false), (39, false), (37, false)]
theorem step796 (p : Nat → Bool) (h : Constraints p) : clause p c796 = true :=
  Snake9.LocalRup.prove_clause [c780, c63, c64, c65, c298, c300, c299, c303, c305] c796 (by decide) p (sat_cons (step780 p h) (sat_cons (step63 p h) (sat_cons (step64 p h) (sat_cons (step65 p h) (sat_cons (step298 p h) (sat_cons (step300 p h) (sat_cons (step299 p h) (sat_cons (step303 p h) (sat_cons (step305 p h) (sat_nil p))))))))))
def c797 : List Lit := [(1381, true)]
theorem step797 (p : Nat → Bool) (h : Constraints p) : clause p c797 = true :=
  Snake9.LocalRup.prove_clause [c506, c507, c504, c505, c796] c797 (by decide) p (sat_cons (step506 p h) (sat_cons (step507 p h) (sat_cons (step504 p h) (sat_cons (step505 p h) (sat_cons (step796 p h) (sat_nil p))))))
def c798 : List Lit := [(1384, true)]
theorem step798 (p : Nat → Bool) (h : Constraints p) : clause p c798 = true :=
  Snake9.LocalRup.prove_clause [c797, c508] c798 (by decide) p (sat_cons (step797 p h) (sat_cons (step508 p h) (sat_nil p)))
def c799 : List Lit := [(1411, true)]
theorem step799 (p : Nat → Bool) (h : Constraints p) : clause p c799 = true :=
  Snake9.LocalRup.prove_clause [c798, c794, c546] c799 (by decide) p (sat_cons (step798 p h) (sat_cons (step794 p h) (sat_cons (step546 p h) (sat_nil p))))
def c800 : List Lit := [(1426, true)]
theorem step800 (p : Nat → Bool) (h : Constraints p) : clause p c800 = true :=
  Snake9.LocalRup.prove_clause [c799, c793, c556] c800 (by decide) p (sat_cons (step799 p h) (sat_cons (step793 p h) (sat_cons (step556 p h) (sat_nil p))))
def c801 : List Lit := [(1546, false)]
theorem step801 (p : Nat → Bool) (h : Constraints p) : clause p c801 = true :=
  Snake9.LocalRup.prove_clause [c800, c743, c736] c801 (by decide) p (sat_cons (step800 p h) (sat_cons (step743 p h) (sat_cons (step736 p h) (sat_nil p))))
def c802 : List Lit := [(1404, true), (40, true), (161, true)]
theorem step802 (p : Nat → Bool) (h : Constraints p) : clause p c802 = true :=
  Snake9.LocalRup.prove_clause [c516, c540, c537, c517, c525, c527, c511, c512, c522, c523, c520, c73, c75, c88] c802 (by decide) p (sat_cons (step516 p h) (sat_cons (step540 p h) (sat_cons (step537 p h) (sat_cons (step517 p h) (sat_cons (step525 p h) (sat_cons (step527 p h) (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step522 p h) (sat_cons (step523 p h) (sat_cons (step520 p h) (sat_cons (step73 p h) (sat_cons (step75 p h) (sat_cons (step88 p h) (sat_nil p)))))))))))))))
def c803 : List Lit := [(1351, true), (28, true), (134, true)]
theorem step803 (p : Nat → Bool) (h : Constraints p) : clause p c803 = true :=
  Snake9.LocalRup.prove_clause [c464, c468, c470, c466, c461, c462, c48, c51] c803 (by decide) p (sat_cons (step464 p h) (sat_cons (step468 p h) (sat_cons (step470 p h) (sat_cons (step466 p h) (sat_cons (step461 p h) (sat_cons (step462 p h) (sat_cons (step48 p h) (sat_cons (step51 p h) (sat_nil p)))))))))
def c804 : List Lit := [(1346, true), (26, false), (24, false)]
theorem step804 (p : Nat → Bool) (h : Constraints p) : clause p c804 = true :=
  Snake9.LocalRup.prove_clause [c461, c462, c51] c804 (by decide) p (sat_cons (step461 p h) (sat_cons (step462 p h) (sat_cons (step51 p h) (sat_nil p))))
def c805 : List Lit := [(1514, true), (218, true)]
theorem step805 (p : Nat → Bool) (h : Constraints p) : clause p c805 = true :=
  Snake9.LocalRup.prove_clause [c691, c692, c689, c690, c686, c219, c222] c805 (by decide) p (sat_cons (step691 p h) (sat_cons (step692 p h) (sat_cons (step689 p h) (sat_cons (step690 p h) (sat_cons (step686 p h) (sat_cons (step219 p h) (sat_cons (step222 p h) (sat_nil p))))))))
def c806 : List Lit := [(1498, true), (194, true)]
theorem step806 (p : Nat → Bool) (h : Constraints p) : clause p c806 = true :=
  Snake9.LocalRup.prove_clause [c669, c672, c663, c655, c660, c661, c200, c184] c806 (by decide) p (sat_cons (step669 p h) (sat_cons (step672 p h) (sat_cons (step663 p h) (sat_cons (step655 p h) (sat_cons (step660 p h) (sat_cons (step661 p h) (sat_cons (step200 p h) (sat_cons (step184 p h) (sat_nil p)))))))))
def c807 : List Lit := [(1465, true), (186, true)]
theorem step807 (p : Nat → Bool) (h : Constraints p) : clause p c807 = true :=
  Snake9.LocalRup.prove_clause [c619, c623, c613, c600, c605, c606, c597, c169, c174] c807 (by decide) p (sat_cons (step619 p h) (sat_cons (step623 p h) (sat_cons (step613 p h) (sat_cons (step600 p h) (sat_cons (step605 p h) (sat_cons (step606 p h) (sat_cons (step597 p h) (sat_cons (step169 p h) (sat_cons (step174 p h) (sat_nil p))))))))))
def c808 : List Lit := [(1505, true), (98, false), (67, false)]
theorem step808 (p : Nat → Bool) (h : Constraints p) : clause p c808 = true :=
  Snake9.LocalRup.prove_clause [c678, c679, c209] c808 (by decide) p (sat_cons (step678 p h) (sat_cons (step679 p h) (sat_cons (step209 p h) (sat_nil p))))
def c809 : List Lit := [(31, true), (28, false), (1414, true), (138, true), (140, true), (150, true), (1391, false)]
theorem step809 (p : Nat → Bool) (h : Constraints p) : clause p c809 = true :=
  Snake9.LocalRup.prove_clause [c235, c797, c515, c540, c554, c510, c501, c54, c498, c499, c56, c500, c503, c509, c57, c552, c62, c543, c66, c518] c809 (by decide) p (sat_cons (step235 p h) (sat_cons (step797 p h) (sat_cons (step515 p h) (sat_cons (step540 p h) (sat_cons (step554 p h) (sat_cons (step510 p h) (sat_cons (step501 p h) (sat_cons (step54 p h) (sat_cons (step498 p h) (sat_cons (step499 p h) (sat_cons (step56 p h) (sat_cons (step500 p h) (sat_cons (step503 p h) (sat_cons (step509 p h) (sat_cons (step57 p h) (sat_cons (step552 p h) (sat_cons (step62 p h) (sat_cons (step543 p h) (sat_cons (step66 p h) (sat_cons (step518 p h) (sat_nil p)))))))))))))))))))))
def c810 : List Lit := [(1444, true), (67, true), (57, true), (1399, true), (69, false)]
theorem step810 (p : Nat → Bool) (h : Constraints p) : clause p c810 = true :=
  Snake9.LocalRup.prove_clause [c787, c241, c425, c582, c525, c523, c527, c520, c519, c79, c522, c586, c584, c588, c124, c140, c83, c312, c313, c317, c309, c320, c88, c322, c72, c327, c119, c423, c123, c419, c337, c372, c338, c348, c346] c810 (by decide) p (sat_cons (step787 p h) (sat_cons (step241 p h) (sat_cons (step425 p h) (sat_cons (step582 p h) (sat_cons (step525 p h) (sat_cons (step523 p h) (sat_cons (step527 p h) (sat_cons (step520 p h) (sat_cons (step519 p h) (sat_cons (step79 p h) (sat_cons (step522 p h) (sat_cons (step586 p h) (sat_cons (step584 p h) (sat_cons (step588 p h) (sat_cons (step124 p h) (sat_cons (step140 p h) (sat_cons (step83 p h) (sat_cons (step312 p h) (sat_cons (step313 p h) (sat_cons (step317 p h) (sat_cons (step309 p h) (sat_cons (step320 p h) (sat_cons (step88 p h) (sat_cons (step322 p h) (sat_cons (step72 p h) (sat_cons (step327 p h) (sat_cons (step119 p h) (sat_cons (step423 p h) (sat_cons (step123 p h) (sat_cons (step419 p h) (sat_cons (step337 p h) (sat_cons (step372 p h) (sat_cons (step338 p h) (sat_cons (step348 p h) (sat_cons (step346 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c811 : List Lit := [(1429, true), (31, true), (134, true), (138, true), (140, true), (150, true), (1391, false)]
theorem step811 (p : Nat → Bool) (h : Constraints p) : clause p c811 = true :=
  Snake9.LocalRup.prove_clause [c797, c793, c790, c515, c540, c498, c500, c509, c551, c559, c562, c809, c486, c803, c473] c811 (by decide) p (sat_cons (step797 p h) (sat_cons (step793 p h) (sat_cons (step790 p h) (sat_cons (step515 p h) (sat_cons (step540 p h) (sat_cons (step498 p h) (sat_cons (step500 p h) (sat_cons (step509 p h) (sat_cons (step551 p h) (sat_cons (step559 p h) (sat_cons (step562 p h) (sat_cons (step809 p h) (sat_cons (step486 p h) (sat_cons (step803 p h) (sat_cons (step473 p h) (sat_nil p))))))))))))))))
def c812 : List Lit := [(1438, true), (169, true), (57, true)]
theorem step812 (p : Nat → Bool) (h : Constraints p) : clause p c812 = true :=
  Snake9.LocalRup.prove_clause [c577, c579, c574, c575, c116, c109] c812 (by decide) p (sat_cons (step577 p h) (sat_cons (step579 p h) (sat_cons (step574 p h) (sat_cons (step575 p h) (sat_cons (step116 p h) (sat_cons (step109 p h) (sat_nil p)))))))
def c813 : List Lit := [(77, true), (179, true), (69, false), (68, true)]
theorem step813 (p : Nat → Bool) (h : Constraints p) : clause p c813 = true :=
  Snake9.LocalRup.prove_clause [c243, c148, c150, c152, c753] c813 (by decide) p (sat_cons (step243 p h) (sat_cons (step148 p h) (sat_cons (step150 p h) (sat_cons (step152 p h) (sat_cons (step753 p h) (sat_nil p))))))
def c814 : List Lit := [(1336, true), (4, true)]
theorem step814 (p : Nat → Bool) (h : Constraints p) : clause p c814 = true :=
  Snake9.LocalRup.prove_clause [c431, c448, c445, c432, c437, c439, c426, c427, c435, c12, c27, c17] c814 (by decide) p (sat_cons (step431 p h) (sat_cons (step448 p h) (sat_cons (step445 p h) (sat_cons (step432 p h) (sat_cons (step437 p h) (sat_cons (step439 p h) (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_cons (step435 p h) (sat_cons (step12 p h) (sat_cons (step27 p h) (sat_cons (step17 p h) (sat_nil p)))))))))))))
def c815 : List Lit := [(6, false), (116, true), (8, true)]
theorem step815 (p : Nat → Bool) (h : Constraints p) : clause p c815 = true :=
  Snake9.LocalRup.prove_clause [c223, c758, c8, c10, c1, c744] c815 (by decide) p (sat_cons (step223 p h) (sat_cons (step758 p h) (sat_cons (step8 p h) (sat_cons (step10 p h) (sat_cons (step1 p h) (sat_cons (step744 p h) (sat_nil p)))))))
def c816 : List Lit := [(1463, false), (1475, true), (77, true), (179, true)]
theorem step816 (p : Nat → Bool) (h : Constraints p) : clause p c816 = true :=
  Snake9.LocalRup.prove_clause [c636, c621, c626, c640, c602, c589, c813, c585, c587, c142, c582] c816 (by decide) p (sat_cons (step636 p h) (sat_cons (step621 p h) (sat_cons (step626 p h) (sat_cons (step640 p h) (sat_cons (step602 p h) (sat_cons (step589 p h) (sat_cons (step813 p h) (sat_cons (step585 p h) (sat_cons (step587 p h) (sat_cons (step142 p h) (sat_cons (step582 p h) (sat_nil p))))))))))))
def c817 : List Lit := [(1475, false), (1364, false), (1498, false), (1514, false), (212, true)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true :=
  Snake9.LocalRup.prove_clause [c799, c743, c794, c797, c564, c738, c695, c701, c728, c729, c739, c702, c565, c697, c550, c681, c509, c678, c679, c500, c215, c208, c498] c817 (by decide) p (sat_cons (step799 p h) (sat_cons (step743 p h) (sat_cons (step794 p h) (sat_cons (step797 p h) (sat_cons (step564 p h) (sat_cons (step738 p h) (sat_cons (step695 p h) (sat_cons (step701 p h) (sat_cons (step728 p h) (sat_cons (step729 p h) (sat_cons (step739 p h) (sat_cons (step702 p h) (sat_cons (step565 p h) (sat_cons (step697 p h) (sat_cons (step550 p h) (sat_cons (step681 p h) (sat_cons (step509 p h) (sat_cons (step678 p h) (sat_cons (step679 p h) (sat_cons (step500 p h) (sat_cons (step215 p h) (sat_cons (step208 p h) (sat_cons (step498 p h) (sat_nil p))))))))))))))))))))))))
def c818 : List Lit := [(1438, false), (1462, false), (179, true), (1475, true), (77, true)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true :=
  Snake9.LocalRup.prove_clause [c620, c644, c591, c592, c640, c585, c587, c625, c582, c602, c142, c813] c818 (by decide) p (sat_cons (step620 p h) (sat_cons (step644 p h) (sat_cons (step591 p h) (sat_cons (step592 p h) (sat_cons (step640 p h) (sat_cons (step585 p h) (sat_cons (step587 p h) (sat_cons (step625 p h) (sat_cons (step582 p h) (sat_cons (step602 p h) (sat_cons (step142 p h) (sat_cons (step813 p h) (sat_nil p)))))))))))))
def c819 : List Lit := [(1438, true), (1436, true), (12, false), (166, true), (169, true)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true :=
  Snake9.LocalRup.prove_clause [c575, c574, c579, c812, c116, c111, c98] c819 (by decide) p (sat_cons (step575 p h) (sat_cons (step574 p h) (sat_cons (step579 p h) (sat_cons (step812 p h) (sat_cons (step116 p h) (sat_cons (step111 p h) (sat_cons (step98 p h) (sat_nil p))))))))
end B112E107
