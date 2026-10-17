import B112E123Part0000
namespace B112E123
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c775 : List Lit := [(89, false), (91, false), (86, false)]
theorem step775 (p : Nat → Bool) (h : Constraints p) : clause p c775 = true :=
  Snake9.LocalRup.prove_clause [c732, c206, c205, c203, c339, c338, c340] c775 (by decide) p (sat_cons (step732 p h) (sat_cons (step206 p h) (sat_cons (step205 p h) (sat_cons (step203 p h) (sat_cons (step339 p h) (sat_cons (step338 p h) (sat_cons (step340 p h) (sat_nil p))))))))
def c776 : List Lit := [(1490, true), (86, false)]
theorem step776 (p : Nat → Bool) (h : Constraints p) : clause p c776 = true :=
  Snake9.LocalRup.prove_clause [c676, c677, c775] c776 (by decide) p (sat_cons (step676 p h) (sat_cons (step677 p h) (sat_cons (step775 p h) (sat_nil p))))
def c777 : List Lit := [(1381, false), (1411, true)]
theorem step777 (p : Nat → Bool) (h : Constraints p) : clause p c777 = true :=
  Snake9.LocalRup.prove_clause [c150, c642, c626, c628, c641, c622, c637, c620, c634, c148, c633] c777 (by decide) p (sat_cons (step150 p h) (sat_cons (step642 p h) (sat_cons (step626 p h) (sat_cons (step628 p h) (sat_cons (step641 p h) (sat_cons (step622 p h) (sat_cons (step637 p h) (sat_cons (step620 p h) (sat_cons (step634 p h) (sat_cons (step148 p h) (sat_cons (step633 p h) (sat_nil p))))))))))))
def c778 : List Lit := [(1395, false), (1411, true)]
theorem step778 (p : Nat → Bool) (h : Constraints p) : clause p c778 = true :=
  Snake9.LocalRup.prove_clause [c150, c640, c638, c635, c636, c637, c633, c641, c148, c627, c620, c622] c778 (by decide) p (sat_cons (step150 p h) (sat_cons (step640 p h) (sat_cons (step638 p h) (sat_cons (step635 p h) (sat_cons (step636 p h) (sat_cons (step637 p h) (sat_cons (step633 p h) (sat_cons (step641 p h) (sat_cons (step148 p h) (sat_cons (step627 p h) (sat_cons (step620 p h) (sat_cons (step622 p h) (sat_nil p)))))))))))))
def c779 : List Lit := [(1411, true)]
theorem step779 (p : Nat → Bool) (h : Constraints p) : clause p c779 = true :=
  Snake9.LocalRup.prove_clause [c738, c777, c624, c625, c623, c778, c631, c632, c137, c134, c301, c136, c135, c133, c147, c621, c629, c622, c630, c627, c639, c641] c779 (by decide) p (sat_cons (step738 p h) (sat_cons (step777 p h) (sat_cons (step624 p h) (sat_cons (step625 p h) (sat_cons (step623 p h) (sat_cons (step778 p h) (sat_cons (step631 p h) (sat_cons (step632 p h) (sat_cons (step137 p h) (sat_cons (step134 p h) (sat_cons (step301 p h) (sat_cons (step136 p h) (sat_cons (step135 p h) (sat_cons (step133 p h) (sat_cons (step147 p h) (sat_cons (step621 p h) (sat_cons (step629 p h) (sat_cons (step622 p h) (sat_cons (step630 p h) (sat_cons (step627 p h) (sat_cons (step639 p h) (sat_cons (step641 p h) (sat_nil p)))))))))))))))))))))))
def c780 : List Lit := [(96, false), (84, false), (85, false)]
theorem step780 (p : Nat → Bool) (h : Constraints p) : clause p c780 = true :=
  Snake9.LocalRup.prove_clause [c737, c196, c201, c202, c336] c780 (by decide) p (sat_cons (step737 p h) (sat_cons (step196 p h) (sat_cons (step201 p h) (sat_cons (step202 p h) (sat_cons (step336 p h) (sat_nil p))))))
def c781 : List Lit := [(1499, true), (1490, false), (85, false)]
theorem step781 (p : Nat → Bool) (h : Constraints p) : clause p c781 = true :=
  Snake9.LocalRup.prove_clause [c680, c682, c683, c681, c674, c678, c780] c781 (by decide) p (sat_cons (step680 p h) (sat_cons (step682 p h) (sat_cons (step683 p h) (sat_cons (step681 p h) (sat_cons (step674 p h) (sat_cons (step678 p h) (sat_cons (step780 p h) (sat_nil p))))))))
def c782 : List Lit := [(1499, true), (1485, false), (85, false)]
theorem step782 (p : Nat → Bool) (h : Constraints p) : clause p c782 = true :=
  Snake9.LocalRup.prove_clause [c672, c684, c683, c675, c679, c780, c678] c782 (by decide) p (sat_cons (step672 p h) (sat_cons (step684 p h) (sat_cons (step683 p h) (sat_cons (step675 p h) (sat_cons (step679 p h) (sat_cons (step780 p h) (sat_cons (step678 p h) (sat_nil p))))))))
def c783 : List Lit := [(1499, true), (86, true)]
theorem step783 (p : Nat → Bool) (h : Constraints p) : clause p c783 = true :=
  Snake9.LocalRup.prove_clause [c669, c684, c782, c673, c671] c783 (by decide) p (sat_cons (step669 p h) (sat_cons (step684 p h) (sat_cons (step782 p h) (sat_cons (step673 p h) (sat_cons (step671 p h) (sat_nil p))))))
def c784 : List Lit := [(1518, true)]
theorem step784 (p : Nat → Bool) (h : Constraints p) : clause p c784 = true :=
  Snake9.LocalRup.prove_clause [c691, c692, c690, c686, c687, c688, c689, c685, c211, c209, c210] c784 (by decide) p (sat_cons (step691 p h) (sat_cons (step692 p h) (sat_cons (step690 p h) (sat_cons (step686 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step689 p h) (sat_cons (step685 p h) (sat_cons (step211 p h) (sat_cons (step209 p h) (sat_cons (step210 p h) (sat_nil p))))))))))))
def c785 : List Lit := [(1499, true), (1490, false)]
theorem step785 (p : Nat → Bool) (h : Constraints p) : clause p c785 = true :=
  Snake9.LocalRup.prove_clause [c680, c683, c781, c672, c670] c785 (by decide) p (sat_cons (step680 p h) (sat_cons (step683 p h) (sat_cons (step781 p h) (sat_cons (step672 p h) (sat_cons (step670 p h) (sat_nil p))))))
def c786 : List Lit := [(1452, true), (66, false), (179, true)]
theorem step786 (p : Nat → Bool) (h : Constraints p) : clause p c786 = true :=
  Snake9.LocalRup.prove_clause [c651, c652, c174, c162] c786 (by decide) p (sat_cons (step651 p h) (sat_cons (step652 p h) (sat_cons (step174 p h) (sat_cons (step162 p h) (sat_nil p)))))
def c787 : List Lit := [(1350, true), (21, false), (23, false)]
theorem step787 (p : Nat → Bool) (h : Constraints p) : clause p c787 = true :=
  Snake9.LocalRup.prove_clause [c615, c616, c614, c613, c105] c787 (by decide) p (sat_cons (step615 p h) (sat_cons (step616 p h) (sat_cons (step614 p h) (sat_cons (step613 p h) (sat_cons (step105 p h) (sat_nil p))))))
def c788 : List Lit := [(1499, true)]
theorem step788 (p : Nat → Bool) (h : Constraints p) : clause p c788 = true :=
  Snake9.LocalRup.prove_clause [c783, c785, c776] c788 (by decide) p (sat_cons (step783 p h) (sat_cons (step785 p h) (sat_cons (step776 p h) (sat_nil p))))
def c789 : List Lit := [(1527, true)]
theorem step789 (p : Nat → Bool) (h : Constraints p) : clause p c789 = true :=
  Snake9.LocalRup.prove_clause [c788, c784, c693] c789 (by decide) p (sat_cons (step788 p h) (sat_cons (step784 p h) (sat_cons (step693 p h) (sat_nil p))))
def c790 : List Lit := [(118, true), (19, false), (5, true), (8, false)]
theorem step790 (p : Nat → Bool) (h : Constraints p) : clause p c790 = true :=
  Snake9.LocalRup.prove_clause [c51, c52, c703] c790 (by decide) p (sat_cons (step51 p h) (sat_cons (step52 p h) (sat_cons (step703 p h) (sat_nil p))))
def c791 : List Lit := [(64, true), (1474, true), (1461, false), (179, true)]
theorem step791 (p : Nat → Bool) (h : Constraints p) : clause p c791 = true :=
  Snake9.LocalRup.prove_clause [c662, c668, c650, c648, c645, c646, c647, c786, c649, c654, c666, c664] c791 (by decide) p (sat_cons (step662 p h) (sat_cons (step668 p h) (sat_cons (step650 p h) (sat_cons (step648 p h) (sat_cons (step645 p h) (sat_cons (step646 p h) (sat_cons (step647 p h) (sat_cons (step786 p h) (sat_cons (step649 p h) (sat_cons (step654 p h) (sat_cons (step666 p h) (sat_cons (step664 p h) (sat_nil p)))))))))))))
def c792 : List Lit := [(67, true), (920, true), (902, false), (75, true), (68, true), (19, true), (188, true)]
theorem step792 (p : Nat → Bool) (h : Constraints p) : clause p c792 = true :=
  Snake9.LocalRup.prove_clause [c243, c241, c244, c245, c189, c176, c190, c518, c192, c521, c537, c193, c528, c762] c792 (by decide) p (sat_cons (step243 p h) (sat_cons (step241 p h) (sat_cons (step244 p h) (sat_cons (step245 p h) (sat_cons (step189 p h) (sat_cons (step176 p h) (sat_cons (step190 p h) (sat_cons (step518 p h) (sat_cons (step192 p h) (sat_cons (step521 p h) (sat_cons (step537 p h) (sat_cons (step193 p h) (sat_cons (step528 p h) (sat_cons (step762 p h) (sat_nil p)))))))))))))))
def c793 : List Lit := [(69, true), (1453, true), (71, true), (182, true)]
theorem step793 (p : Nat → Bool) (h : Constraints p) : clause p c793 = true :=
  Snake9.LocalRup.prove_clause [c240, c653, c180, c181, c165, c710] c793 (by decide) p (sat_cons (step240 p h) (sat_cons (step653 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step165 p h) (sat_cons (step710 p h) (sat_nil p)))))))
def c794 : List Lit := [(19, true), (3, false), (20, true), (14, true), (113, true), (32, false), (1350, false), (182, true), (184, true), (188, true), (179, true), (141, true), (126, true), (5, true), (1332, true), (1335, false)]
theorem step794 (p : Nat → Bool) (h : Constraints p) : clause p c794 = true :=
  Snake9.TreeRup.prove_clause [c225, c233, c713, c712, c228, c779, c698, c789, c730, c224, c243, c602, c245, c606, c604, c605, c72, c369, c372, c406, c743, c607, c610, c94, c127, c612, c397, c125, c617, c400, c115, c618, c420, c31, c643, c78, c80, c360, c696, c264, c695, c265, c269, c261, c260, c51, c52, c91, c48, c89, c500, c83, c65, c58, c503, c189, c656, c513, c27, c365, c508, c660, c394, c441, c760, c597, c774, c546, c792, c155, c645, c647, c649, c667, c663, c665, c655, c793, c173, c170, c192, c659, c193, c661, c184, c658] c794 (by decide) p (sat_cons (step225 p h) (sat_cons (step233 p h) (sat_cons (step713 p h) (sat_cons (step712 p h) (sat_cons (step228 p h) (sat_cons (step779 p h) (sat_cons (step698 p h) (sat_cons (step789 p h) (sat_cons (step730 p h) (sat_cons (step224 p h) (sat_cons (step243 p h) (sat_cons (step602 p h) (sat_cons (step245 p h) (sat_cons (step606 p h) (sat_cons (step604 p h) (sat_cons (step605 p h) (sat_cons (step72 p h) (sat_cons (step369 p h) (sat_cons (step372 p h) (sat_cons (step406 p h) (sat_cons (step743 p h) (sat_cons (step607 p h) (sat_cons (step610 p h) (sat_cons (step94 p h) (sat_cons (step127 p h) (sat_cons (step612 p h) (sat_cons (step397 p h) (sat_cons (step125 p h) (sat_cons (step617 p h) (sat_cons (step400 p h) (sat_cons (step115 p h) (sat_cons (step618 p h) (sat_cons (step420 p h) (sat_cons (step31 p h) (sat_cons (step643 p h) (sat_cons (step78 p h) (sat_cons (step80 p h) (sat_cons (step360 p h) (sat_cons (step696 p h) (sat_cons (step264 p h) (sat_cons (step695 p h) (sat_cons (step265 p h) (sat_cons (step269 p h) (sat_cons (step261 p h) (sat_cons (step260 p h) (sat_cons (step51 p h) (sat_cons (step52 p h) (sat_cons (step91 p h) (sat_cons (step48 p h) (sat_cons (step89 p h) (sat_cons (step500 p h) (sat_cons (step83 p h) (sat_cons (step65 p h) (sat_cons (step58 p h) (sat_cons (step503 p h) (sat_cons (step189 p h) (sat_cons (step656 p h) (sat_cons (step513 p h) (sat_cons (step27 p h) (sat_cons (step365 p h) (sat_cons (step508 p h) (sat_cons (step660 p h) (sat_cons (step394 p h) (sat_cons (step441 p h) (sat_cons (step760 p h) (sat_cons (step597 p h) (sat_cons (step774 p h) (sat_cons (step546 p h) (sat_cons (step792 p h) (sat_cons (step155 p h) (sat_cons (step645 p h) (sat_cons (step647 p h) (sat_cons (step649 p h) (sat_cons (step667 p h) (sat_cons (step663 p h) (sat_cons (step665 p h) (sat_cons (step655 p h) (sat_cons (step793 p h) (sat_cons (step173 p h) (sat_cons (step170 p h) (sat_cons (step192 p h) (sat_cons (step659 p h) (sat_cons (step193 p h) (sat_cons (step661 p h) (sat_cons (step184 p h) (sat_cons (step658 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c795 : List Lit := [(9, false), (1336, false), (64, true), (19, false), (14, true), (32, false), (1350, false), (184, true), (179, true), (126, true)]
theorem step795 (p : Nat → Bool) (h : Constraints p) : clause p c795 = true :=
  Snake9.LocalRup.prove_clause [c789, c779, c698, c97, c100, c99, c88, c184, c611, c657, c612, c660, c617, c791, c619, c694, c644, c697] c795 (by decide) p (sat_cons (step789 p h) (sat_cons (step779 p h) (sat_cons (step698 p h) (sat_cons (step97 p h) (sat_cons (step100 p h) (sat_cons (step99 p h) (sat_cons (step88 p h) (sat_cons (step184 p h) (sat_cons (step611 p h) (sat_cons (step657 p h) (sat_cons (step612 p h) (sat_cons (step660 p h) (sat_cons (step617 p h) (sat_cons (step791 p h) (sat_cons (step619 p h) (sat_cons (step694 p h) (sat_cons (step644 p h) (sat_cons (step697 p h) (sat_nil p)))))))))))))))))))
def c796 : List Lit := [(844, true)]
theorem step796 (p : Nat → Bool) (h : Constraints p) : clause p c796 = true :=
  Snake9.LocalRup.prove_clause [c236, c475, c476, c474, c468, c470, c472, c473, c465, c466, c146, c145, c143] c796 (by decide) p (sat_cons (step236 p h) (sat_cons (step475 p h) (sat_cons (step476 p h) (sat_cons (step474 p h) (sat_cons (step468 p h) (sat_cons (step470 p h) (sat_cons (step472 p h) (sat_cons (step473 p h) (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step146 p h) (sat_cons (step145 p h) (sat_cons (step143 p h) (sat_nil p))))))))))))))
def c797 : List Lit := [(853, true)]
theorem step797 (p : Nat → Bool) (h : Constraints p) : clause p c797 = true :=
  Snake9.LocalRup.prove_clause [c796, c758] c797 (by decide) p (sat_cons (step796 p h) (sat_cons (step758 p h) (sat_nil p)))
def c798 : List Lit := [(918, true), (902, false), (76, true), (67, false), (63, false)]
theorem step798 (p : Nat → Bool) (h : Constraints p) : clause p c798 = true :=
  Snake9.LocalRup.prove_clause [c515, c520, c763, c533, c535, c764, c518, c521, c170] c798 (by decide) p (sat_cons (step515 p h) (sat_cons (step520 p h) (sat_cons (step763 p h) (sat_cons (step533 p h) (sat_cons (step535 p h) (sat_cons (step764 p h) (sat_cons (step518 p h) (sat_cons (step521 p h) (sat_cons (step170 p h) (sat_nil p))))))))))
def c799 : List Lit := [(972, true)]
theorem step799 (p : Nat → Bool) (h : Constraints p) : clause p c799 = true :=
  Snake9.LocalRup.prove_clause [c252, c574, c576, c571, c566, c569, c570, c565, c215, c214] c799 (by decide) p (sat_cons (step252 p h) (sat_cons (step574 p h) (sat_cons (step576 p h) (sat_cons (step571 p h) (sat_cons (step566 p h) (sat_cons (step569 p h) (sat_cons (step570 p h) (sat_cons (step565 p h) (sat_cons (step215 p h) (sat_cons (step214 p h) (sat_nil p)))))))))))
def c800 : List Lit := [(981, true)]
theorem step800 (p : Nat → Bool) (h : Constraints p) : clause p c800 = true :=
  Snake9.LocalRup.prove_clause [c799, c772] c800 (by decide) p (sat_cons (step799 p h) (sat_cons (step772 p h) (sat_nil p)))
def c801 : List Lit := [(14, false), (12, true), (3, false), (23, false), (124, true)]
theorem step801 (p : Nat → Bool) (h : Constraints p) : clause p c801 = true :=
  Snake9.LocalRup.prove_clause [c42, c82] c801 (by decide) p (sat_cons (step42 p h) (sat_cons (step82 p h) (sat_nil p)))
def c802 : List Lit := [(760, false), (804, true), (787, false), (764, false), (18, true), (6, true), (5, false), (8, false)]
theorem step802 (p : Nat → Bool) (h : Constraints p) : clause p c802 = true :=
  Snake9.LocalRup.prove_clause [c397, c400, c420, c444, c367, c375, c390, c391, c442, c378, c424, c368, c401, c50, c399] c802 (by decide) p (sat_cons (step397 p h) (sat_cons (step400 p h) (sat_cons (step420 p h) (sat_cons (step444 p h) (sat_cons (step367 p h) (sat_cons (step375 p h) (sat_cons (step390 p h) (sat_cons (step391 p h) (sat_cons (step442 p h) (sat_cons (step378 p h) (sat_cons (step424 p h) (sat_cons (step368 p h) (sat_cons (step401 p h) (sat_cons (step50 p h) (sat_cons (step399 p h) (sat_nil p))))))))))))))))
def c803 : List Lit := [(895, false), (1000, true), (912, false)]
theorem step803 (p : Nat → Bool) (h : Constraints p) : clause p c803 = true :=
  Snake9.LocalRup.prove_clause [c800, c799, c247, c588, c529, c542, c586, c581, c543, c560, c769, c532, c767, c552, c515, c555, c551, c513, c200, c197] c803 (by decide) p (sat_cons (step800 p h) (sat_cons (step799 p h) (sat_cons (step247 p h) (sat_cons (step588 p h) (sat_cons (step529 p h) (sat_cons (step542 p h) (sat_cons (step586 p h) (sat_cons (step581 p h) (sat_cons (step543 p h) (sat_cons (step560 p h) (sat_cons (step769 p h) (sat_cons (step532 p h) (sat_cons (step767 p h) (sat_cons (step552 p h) (sat_cons (step515 p h) (sat_cons (step555 p h) (sat_cons (step551 p h) (sat_cons (step513 p h) (sat_cons (step200 p h) (sat_cons (step197 p h) (sat_nil p)))))))))))))))))))))
def c804 : List Lit := [(3, true), (891, true)]
theorem step804 (p : Nat → Bool) (h : Constraints p) : clause p c804 = true :=
  Snake9.LocalRup.prove_clause [c239, c505, c499, c503, c500, c157, c158, c709] c804 (by decide) p (sat_cons (step239 p h) (sat_cons (step505 p h) (sat_cons (step499 p h) (sat_cons (step503 p h) (sat_cons (step500 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step709 p h) (sat_nil p)))))))))
def c805 : List Lit := [(64, false), (72, false), (63, false), (68, false), (905, true), (939, true), (10, false)]
theorem step805 (p : Nat → Bool) (h : Constraints p) : clause p c805 = true :=
  Snake9.LocalRup.prove_clause [c241, c247, c161, c709, c554, c176, c551, c518, c200, c513, c177] c805 (by decide) p (sat_cons (step241 p h) (sat_cons (step247 p h) (sat_cons (step161 p h) (sat_cons (step709 p h) (sat_cons (step554 p h) (sat_cons (step176 p h) (sat_cons (step551 p h) (sat_cons (step518 p h) (sat_cons (step200 p h) (sat_cons (step513 p h) (sat_cons (step177 p h) (sat_nil p))))))))))))
def c806 : List Lit := [(1000, true), (912, false), (66, true), (10, false)]
theorem step806 (p : Nat → Bool) (h : Constraints p) : clause p c806 = true :=
  Snake9.LocalRup.prove_clause [c800, c799, c240, c239, c529, c538, c584, c588, c803, c582, c540, c508, c770, c535, c503, c505, c500, c501, c499, c164, c805, c156, c169, c518, c512, c513, c179] c806 (by decide) p (sat_cons (step800 p h) (sat_cons (step799 p h) (sat_cons (step240 p h) (sat_cons (step239 p h) (sat_cons (step529 p h) (sat_cons (step538 p h) (sat_cons (step584 p h) (sat_cons (step588 p h) (sat_cons (step803 p h) (sat_cons (step582 p h) (sat_cons (step540 p h) (sat_cons (step508 p h) (sat_cons (step770 p h) (sat_cons (step535 p h) (sat_cons (step503 p h) (sat_cons (step505 p h) (sat_cons (step500 p h) (sat_cons (step501 p h) (sat_cons (step499 p h) (sat_cons (step164 p h) (sat_cons (step805 p h) (sat_cons (step156 p h) (sat_cons (step169 p h) (sat_cons (step518 p h) (sat_cons (step512 p h) (sat_cons (step513 p h) (sat_cons (step179 p h) (sat_nil p))))))))))))))))))))))))))))
def c807 : List Lit := [(779, true), (19, true)]
theorem step807 (p : Nat → Bool) (h : Constraints p) : clause p c807 = true :=
  Snake9.LocalRup.prove_clause [c225, c400, c402, c397, c398, c93, c87] c807 (by decide) p (sat_cons (step225 p h) (sat_cons (step400 p h) (sat_cons (step402 p h) (sat_cons (step397 p h) (sat_cons (step398 p h) (sat_cons (step93 p h) (sat_cons (step87 p h) (sat_nil p))))))))
def c808 : List Lit := [(767, false), (803, true), (782, false), (64, false), (1, true), (779, false), (13, false)]
theorem step808 (p : Nat → Bool) (h : Constraints p) : clause p c808 = true :=
  Snake9.LocalRup.prove_clause [c228, c743, c420, c441, c363, c385, c390, c437, c364, c421, c359, c413, c32, c741, c115] c808 (by decide) p (sat_cons (step228 p h) (sat_cons (step743 p h) (sat_cons (step420 p h) (sat_cons (step441 p h) (sat_cons (step363 p h) (sat_cons (step385 p h) (sat_cons (step390 p h) (sat_cons (step437 p h) (sat_cons (step364 p h) (sat_cons (step421 p h) (sat_cons (step359 p h) (sat_cons (step413 p h) (sat_cons (step32 p h) (sat_cons (step741 p h) (sat_cons (step115 p h) (sat_nil p))))))))))))))))
def c809 : List Lit := [(20, false), (9, true), (4, false), (3, false), (773, true), (764, false)]
theorem step809 (p : Nat → Bool) (h : Constraints p) : clause p c809 = true :=
  Snake9.LocalRup.prove_clause [c226, c103, c702, c12, c368, c363, c378, c386] c809 (by decide) p (sat_cons (step226 p h) (sat_cons (step103 p h) (sat_cons (step702 p h) (sat_cons (step12 p h) (sat_cons (step368 p h) (sat_cons (step363 p h) (sat_cons (step378 p h) (sat_cons (step386 p h) (sat_nil p)))))))))
def c810 : List Lit := [(20, false), (126, true), (124, true), (113, true), (11, false), (4, true), (3, false), (781, true), (63, true), (12, true), (19, true), (10, false)]
theorem step810 (p : Nat → Bool) (h : Constraints p) : clause p c810 = true :=
  Snake9.LocalRup.prove_clause [c226, c225, c224, c103, c702, c801, c28, c94, c58, c89, c404, c91, c399] c810 (by decide) p (sat_cons (step226 p h) (sat_cons (step225 p h) (sat_cons (step224 p h) (sat_cons (step103 p h) (sat_cons (step702 p h) (sat_cons (step801 p h) (sat_cons (step28 p h) (sat_cons (step94 p h) (sat_cons (step58 p h) (sat_cons (step89 p h) (sat_cons (step404 p h) (sat_cons (step91 p h) (sat_cons (step399 p h) (sat_nil p))))))))))))))
def c811 : List Lit := [(826, true), (785, false), (17, true), (9, false), (795, true), (20, true), (19, false), (5, false), (22, false)]
theorem step811 (p : Nat → Bool) (h : Constraints p) : clause p c811 = true :=
  Snake9.LocalRup.prove_clause [c755, c463, c457, c753, c453, c109, c99, c407, c399, c415, c401, c426] c811 (by decide) p (sat_cons (step755 p h) (sat_cons (step463 p h) (sat_cons (step457 p h) (sat_cons (step753 p h) (sat_cons (step453 p h) (sat_cons (step109 p h) (sat_cons (step99 p h) (sat_cons (step407 p h) (sat_cons (step399 p h) (sat_cons (step415 p h) (sat_cons (step401 p h) (sat_cons (step426 p h) (sat_nil p)))))))))))))
def c812 : List Lit := [(1, false), (10, true), (3, true)]
theorem step812 (p : Nat → Bool) (h : Constraints p) : clause p c812 = true :=
  Snake9.LocalRup.prove_clause [c216, c2] c812 (by decide) p (sat_cons (step216 p h) (sat_cons (step2 p h) (sat_nil p)))
def c813 : List Lit := [(2, true), (1, false), (10, true)]
theorem step813 (p : Nat → Bool) (h : Constraints p) : clause p c813 = true :=
  Snake9.LocalRup.prove_clause [c216, c3] c813 (by decide) p (sat_cons (step216 p h) (sat_cons (step3 p h) (sat_nil p)))
def c814 : List Lit := [(1, false), (3, true), (2, true)]
theorem step814 (p : Nat → Bool) (h : Constraints p) : clause p c814 = true :=
  Snake9.LocalRup.prove_clause [c216, c4] c814 (by decide) p (sat_cons (step216 p h) (sat_cons (step4 p h) (sat_nil p)))
def c815 : List Lit := [(4, false), (7, true), (3, true), (13, true), (64, true)]
theorem step815 (p : Nat → Bool) (h : Constraints p) : clause p c815 = true :=
  Snake9.LocalRup.prove_clause [c217, c33] c815 (by decide) p (sat_cons (step217 p h) (sat_cons (step33 p h) (sat_nil p)))
def c816 : List Lit := [(64, true), (4, false), (2, true), (3, true), (7, true)]
theorem step816 (p : Nat → Bool) (h : Constraints p) : clause p c816 = true :=
  Snake9.LocalRup.prove_clause [c217, c34] c816 (by decide) p (sat_cons (step217 p h) (sat_cons (step34 p h) (sat_nil p)))
def c817 : List Lit := [(8, true), (22, true), (5, false), (66, true)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true :=
  Snake9.LocalRup.prove_clause [c218, c38] c817 (by decide) p (sat_cons (step218 p h) (sat_cons (step38 p h) (sat_nil p)))
def c818 : List Lit := [(5, false), (22, true), (2, true), (66, true)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true :=
  Snake9.LocalRup.prove_clause [c218, c39] c818 (by decide) p (sat_cons (step218 p h) (sat_cons (step39 p h) (sat_nil p)))
def c819 : List Lit := [(5, false), (8, true), (2, true), (66, true)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true :=
  Snake9.LocalRup.prove_clause [c218, c40] c819 (by decide) p (sat_cons (step218 p h) (sat_cons (step40 p h) (sat_nil p)))
def c820 : List Lit := [(5, false), (8, true), (2, true), (22, true)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true :=
  Snake9.LocalRup.prove_clause [c218, c41] c820 (by decide) p (sat_cons (step218 p h) (sat_cons (step41 p h) (sat_nil p)))
def c821 : List Lit := [(6, false), (23, true), (3, true)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true :=
  Snake9.LocalRup.prove_clause [c219, c43] c821 (by decide) p (sat_cons (step219 p h) (sat_cons (step43 p h) (sat_nil p)))
def c822 : List Lit := [(6, false), (14, true), (3, true)]
theorem step822 (p : Nat → Bool) (h : Constraints p) : clause p c822 = true :=
  Snake9.LocalRup.prove_clause [c219, c44] c822 (by decide) p (sat_cons (step219 p h) (sat_cons (step44 p h) (sat_nil p)))
def c823 : List Lit := [(9, false), (8, true), (19, true)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true :=
  Snake9.LocalRup.prove_clause [c220, c54] c823 (by decide) p (sat_cons (step220 p h) (sat_cons (step54 p h) (sat_nil p)))
def c824 : List Lit := [(7, true), (9, false), (19, true)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true :=
  Snake9.LocalRup.prove_clause [c220, c55] c824 (by decide) p (sat_cons (step220 p h) (sat_cons (step55 p h) (sat_nil p)))
def c825 : List Lit := [(9, false), (8, true), (7, true)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true :=
  Snake9.LocalRup.prove_clause [c220, c56] c825 (by decide) p (sat_cons (step220 p h) (sat_cons (step56 p h) (sat_nil p)))
def c826 : List Lit := [(11, false), (13, true), (10, true)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true :=
  Snake9.LocalRup.prove_clause [c221, c69] c826 (by decide) p (sat_cons (step221 p h) (sat_cons (step69 p h) (sat_nil p)))
def c827 : List Lit := [(11, false), (13, true), (2, true)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true :=
  Snake9.LocalRup.prove_clause [c221, c70] c827 (by decide) p (sat_cons (step221 p h) (sat_cons (step70 p h) (sat_nil p)))
def c828 : List Lit := [(11, false), (2, true), (10, true)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true :=
  Snake9.LocalRup.prove_clause [c221, c71] c828 (by decide) p (sat_cons (step221 p h) (sat_cons (step71 p h) (sat_nil p)))
def c829 : List Lit := [(12, false), (14, true), (3, true), (10, true)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true :=
  Snake9.LocalRup.prove_clause [c222, c76] c829 (by decide) p (sat_cons (step222 p h) (sat_cons (step76 p h) (sat_nil p)))
def c830 : List Lit := [(12, false), (13, true), (3, true), (10, true)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true :=
  Snake9.LocalRup.prove_clause [c222, c77] c830 (by decide) p (sat_cons (step222 p h) (sat_cons (step77 p h) (sat_nil p)))
def c831 : List Lit := [(75, true), (15, false), (16, true)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true :=
  Snake9.LocalRup.prove_clause [c223, c84] c831 (by decide) p (sat_cons (step223 p h) (sat_cons (step84 p h) (sat_nil p)))
def c832 : List Lit := [(75, true), (10, true), (15, false)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true :=
  Snake9.LocalRup.prove_clause [c223, c85] c832 (by decide) p (sat_cons (step223 p h) (sat_cons (step85 p h) (sat_nil p)))
def c833 : List Lit := [(15, false), (16, true), (10, true)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true :=
  Snake9.LocalRup.prove_clause [c223, c86] c833 (by decide) p (sat_cons (step223 p h) (sat_cons (step86 p h) (sat_nil p)))
def c834 : List Lit := [(16, true), (17, false), (19, true)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true :=
  Snake9.LocalRup.prove_clause [c224, c91] c834 (by decide) p (sat_cons (step224 p h) (sat_cons (step91 p h) (sat_nil p)))
def c835 : List Lit := [(17, false), (8, true), (19, true)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true :=
  Snake9.LocalRup.prove_clause [c224, c92] c835 (by decide) p (sat_cons (step224 p h) (sat_cons (step92 p h) (sat_nil p)))
def c836 : List Lit := [(16, true), (18, false), (19, true)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true :=
  Snake9.LocalRup.prove_clause [c225, c93] c836 (by decide) p (sat_cons (step225 p h) (sat_cons (step93 p h) (sat_nil p)))
def c837 : List Lit := [(18, false), (14, true), (19, true)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.LocalRup.prove_clause [c225, c94] c837 (by decide) p (sat_cons (step225 p h) (sat_cons (step94 p h) (sat_nil p)))
def c838 : List Lit := [(18, false), (14, true), (16, true)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c225, c95] c838 (by decide) p (sat_cons (step225 p h) (sat_cons (step95 p h) (sat_nil p)))
end B112E123
