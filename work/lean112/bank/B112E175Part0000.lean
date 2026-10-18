import B112E175Inputs
namespace B112E175
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c781 : List Lit := [(55, true)]
theorem step781 (p : Nat → Bool) (h : Constraints p) : clause p c781 = true :=
  Snake9.LocalRup.prove_clause [c138, c137] c781 (by decide) p (sat_cons (step138 p h) (sat_cons (step137 p h) (sat_nil p)))
def c782 : List Lit := [(78, false)]
theorem step782 (p : Nat → Bool) (h : Constraints p) : clause p c782 = true :=
  Snake9.LocalRup.prove_clause [c261, c181] c782 (by decide) p (sat_cons (step261 p h) (sat_cons (step181 p h) (sat_nil p)))
def c783 : List Lit := [(84, false)]
theorem step783 (p : Nat → Bool) (h : Constraints p) : clause p c783 = true :=
  Snake9.LocalRup.prove_clause [c264, c196] c783 (by decide) p (sat_cons (step264 p h) (sat_cons (step196 p h) (sat_nil p)))
def c784 : List Lit := [(410, false)]
theorem step784 (p : Nat → Bool) (h : Constraints p) : clause p c784 = true :=
  Snake9.LocalRup.prove_clause [c450, c447] c784 (by decide) p (sat_cons (step450 p h) (sat_cons (step447 p h) (sat_nil p)))
def c785 : List Lit := [(308, false)]
theorem step785 (p : Nat → Bool) (h : Constraints p) : clause p c785 = true :=
  Snake9.LocalRup.prove_clause [c450, c449] c785 (by decide) p (sat_cons (step450 p h) (sat_cons (step449 p h) (sat_nil p)))
def c786 : List Lit := [(408, false)]
theorem step786 (p : Nat → Bool) (h : Constraints p) : clause p c786 = true :=
  Snake9.LocalRup.prove_clause [c784, c443] c786 (by decide) p (sat_cons (step784 p h) (sat_cons (step443 p h) (sat_nil p)))
def c787 : List Lit := [(358, false)]
theorem step787 (p : Nat → Bool) (h : Constraints p) : clause p c787 = true :=
  Snake9.LocalRup.prove_clause [c784, c446] c787 (by decide) p (sat_cons (step784 p h) (sat_cons (step446 p h) (sat_nil p)))
def c788 : List Lit := [(306, false)]
theorem step788 (p : Nat → Bool) (h : Constraints p) : clause p c788 = true :=
  Snake9.LocalRup.prove_clause [c785, c356] c788 (by decide) p (sat_cons (step785 p h) (sat_cons (step356 p h) (sat_nil p)))
def c789 : List Lit := [(256, false)]
theorem step789 (p : Nat → Bool) (h : Constraints p) : clause p c789 = true :=
  Snake9.LocalRup.prove_clause [c785, c359] c789 (by decide) p (sat_cons (step785 p h) (sat_cons (step359 p h) (sat_nil p)))
def c790 : List Lit := [(406, false)]
theorem step790 (p : Nat → Bool) (h : Constraints p) : clause p c790 = true :=
  Snake9.LocalRup.prove_clause [c786, c438] c790 (by decide) p (sat_cons (step786 p h) (sat_cons (step438 p h) (sat_nil p)))
def c791 : List Lit := [(382, false)]
theorem step791 (p : Nat → Bool) (h : Constraints p) : clause p c791 = true :=
  Snake9.LocalRup.prove_clause [c786, c441] c791 (by decide) p (sat_cons (step786 p h) (sat_cons (step441 p h) (sat_nil p)))
def c792 : List Lit := [(356, false)]
theorem step792 (p : Nat → Bool) (h : Constraints p) : clause p c792 = true :=
  Snake9.LocalRup.prove_clause [c787, c400] c792 (by decide) p (sat_cons (step787 p h) (sat_cons (step400 p h) (sat_nil p)))
def c793 : List Lit := [(332, false)]
theorem step793 (p : Nat → Bool) (h : Constraints p) : clause p c793 = true :=
  Snake9.LocalRup.prove_clause [c787, c402] c793 (by decide) p (sat_cons (step787 p h) (sat_cons (step402 p h) (sat_nil p)))
def c794 : List Lit := [(304, false)]
theorem step794 (p : Nat → Bool) (h : Constraints p) : clause p c794 = true :=
  Snake9.LocalRup.prove_clause [c788, c351] c794 (by decide) p (sat_cons (step788 p h) (sat_cons (step351 p h) (sat_nil p)))
def c795 : List Lit := [(280, false)]
theorem step795 (p : Nat → Bool) (h : Constraints p) : clause p c795 = true :=
  Snake9.LocalRup.prove_clause [c788, c354] c795 (by decide) p (sat_cons (step788 p h) (sat_cons (step354 p h) (sat_nil p)))
def c796 : List Lit := [(254, false)]
theorem step796 (p : Nat → Bool) (h : Constraints p) : clause p c796 = true :=
  Snake9.LocalRup.prove_clause [c789, c302] c796 (by decide) p (sat_cons (step789 p h) (sat_cons (step302 p h) (sat_nil p)))
def c797 : List Lit := [(230, false)]
theorem step797 (p : Nat → Bool) (h : Constraints p) : clause p c797 = true :=
  Snake9.LocalRup.prove_clause [c789, c305] c797 (by decide) p (sat_cons (step789 p h) (sat_cons (step305 p h) (sat_nil p)))
def c798 : List Lit := [(404, false)]
theorem step798 (p : Nat → Bool) (h : Constraints p) : clause p c798 = true :=
  Snake9.LocalRup.prove_clause [c790, c434] c798 (by decide) p (sat_cons (step790 p h) (sat_cons (step434 p h) (sat_nil p)))
def c799 : List Lit := [(368, false)]
theorem step799 (p : Nat → Bool) (h : Constraints p) : clause p c799 = true :=
  Snake9.LocalRup.prove_clause [c791, c420] c799 (by decide) p (sat_cons (step791 p h) (sat_cons (step420 p h) (sat_nil p)))
def c800 : List Lit := [(354, false)]
theorem step800 (p : Nat → Bool) (h : Constraints p) : clause p c800 = true :=
  Snake9.LocalRup.prove_clause [c792, c396] c800 (by decide) p (sat_cons (step792 p h) (sat_cons (step396 p h) (sat_nil p)))
def c801 : List Lit := [(342, false)]
theorem step801 (p : Nat → Bool) (h : Constraints p) : clause p c801 = true :=
  Snake9.LocalRup.prove_clause [c792, c398] c801 (by decide) p (sat_cons (step792 p h) (sat_cons (step398 p h) (sat_nil p)))
def c802 : List Lit := [(330, false)]
theorem step802 (p : Nat → Bool) (h : Constraints p) : clause p c802 = true :=
  Snake9.LocalRup.prove_clause [c793, c377] c802 (by decide) p (sat_cons (step793 p h) (sat_cons (step377 p h) (sat_nil p)))
def c803 : List Lit := [(302, false)]
theorem step803 (p : Nat → Bool) (h : Constraints p) : clause p c803 = true :=
  Snake9.LocalRup.prove_clause [c794, c346] c803 (by decide) p (sat_cons (step794 p h) (sat_cons (step346 p h) (sat_nil p)))
def c804 : List Lit := [(290, false)]
theorem step804 (p : Nat → Bool) (h : Constraints p) : clause p c804 = true :=
  Snake9.LocalRup.prove_clause [c794, c349] c804 (by decide) p (sat_cons (step794 p h) (sat_cons (step349 p h) (sat_nil p)))
def c805 : List Lit := [(278, false)]
theorem step805 (p : Nat → Bool) (h : Constraints p) : clause p c805 = true :=
  Snake9.LocalRup.prove_clause [c795, c327] c805 (by decide) p (sat_cons (step795 p h) (sat_cons (step327 p h) (sat_nil p)))
def c806 : List Lit := [(252, false)]
theorem step806 (p : Nat → Bool) (h : Constraints p) : clause p c806 = true :=
  Snake9.LocalRup.prove_clause [c796, c298] c806 (by decide) p (sat_cons (step796 p h) (sat_cons (step298 p h) (sat_nil p)))
def c807 : List Lit := [(362, false)]
theorem step807 (p : Nat → Bool) (h : Constraints p) : clause p c807 = true :=
  Snake9.LocalRup.prove_clause [c799, c409] c807 (by decide) p (sat_cons (step799 p h) (sat_cons (step409 p h) (sat_nil p)))
def c808 : List Lit := [(352, false)]
theorem step808 (p : Nat → Bool) (h : Constraints p) : clause p c808 = true :=
  Snake9.LocalRup.prove_clause [c800, c394] c808 (by decide) p (sat_cons (step800 p h) (sat_cons (step394 p h) (sat_nil p)))
def c809 : List Lit := [(340, false)]
theorem step809 (p : Nat → Bool) (h : Constraints p) : clause p c809 = true :=
  Snake9.LocalRup.prove_clause [c801, c387] c809 (by decide) p (sat_cons (step801 p h) (sat_cons (step387 p h) (sat_nil p)))
def c810 : List Lit := [(288, false)]
theorem step810 (p : Nat → Bool) (h : Constraints p) : clause p c810 = true :=
  Snake9.LocalRup.prove_clause [c804, c336] c810 (by decide) p (sat_cons (step804 p h) (sat_cons (step336 p h) (sat_nil p)))
def c811 : List Lit := [(276, false)]
theorem step811 (p : Nat → Bool) (h : Constraints p) : clause p c811 = true :=
  Snake9.LocalRup.prove_clause [c805, c323] c811 (by decide) p (sat_cons (step805 p h) (sat_cons (step323 p h) (sat_nil p)))
def c812 : List Lit := [(250, false)]
theorem step812 (p : Nat → Bool) (h : Constraints p) : clause p c812 = true :=
  Snake9.LocalRup.prove_clause [c806, c295] c812 (by decide) p (sat_cons (step806 p h) (sat_cons (step295 p h) (sat_nil p)))
def c813 : List Lit := [(338, false)]
theorem step813 (p : Nat → Bool) (h : Constraints p) : clause p c813 = true :=
  Snake9.LocalRup.prove_clause [c809, c385] c813 (by decide) p (sat_cons (step809 p h) (sat_cons (step385 p h) (sat_nil p)))
def c814 : List Lit := [(272, false)]
theorem step814 (p : Nat → Bool) (h : Constraints p) : clause p c814 = true :=
  Snake9.LocalRup.prove_clause [c811, c321] c814 (by decide) p (sat_cons (step811 p h) (sat_cons (step321 p h) (sat_nil p)))
def c815 : List Lit := [(883, true)]
theorem step815 (p : Nat → Bool) (h : Constraints p) : clause p c815 = true :=
  Snake9.LocalRup.prove_clause [c782, c513] c815 (by decide) p (sat_cons (step782 p h) (sat_cons (step513 p h) (sat_nil p)))
def c816 : List Lit := [(886, true)]
theorem step816 (p : Nat → Bool) (h : Constraints p) : clause p c816 = true :=
  Snake9.LocalRup.prove_clause [c783, c514] c816 (by decide) p (sat_cons (step783 p h) (sat_cons (step514 p h) (sat_nil p)))
def c817 : List Lit := [(890, true)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true :=
  Snake9.LocalRup.prove_clause [c816, c515] c817 (by decide) p (sat_cons (step816 p h) (sat_cons (step515 p h) (sat_nil p)))
def c818 : List Lit := [(895, true)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true :=
  Snake9.LocalRup.prove_clause [c815, c817, c516] c818 (by decide) p (sat_cons (step815 p h) (sat_cons (step817 p h) (sat_cons (step516 p h) (sat_nil p))))
def c819 : List Lit := [(922, true)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true :=
  Snake9.LocalRup.prove_clause [c818, c517] c819 (by decide) p (sat_cons (step818 p h) (sat_cons (step517 p h) (sat_nil p)))
def c820 : List Lit := [(936, true)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true :=
  Snake9.LocalRup.prove_clause [c819, c518] c820 (by decide) p (sat_cons (step819 p h) (sat_cons (step518 p h) (sat_nil p)))
def c821 : List Lit := [(868, false), (937, true)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true :=
  Snake9.LocalRup.prove_clause [c819, c519] c821 (by decide) p (sat_cons (step819 p h) (sat_cons (step519 p h) (sat_nil p)))
def c822 : List Lit := [(869, false), (938, true)]
theorem step822 (p : Nat → Bool) (h : Constraints p) : clause p c822 = true :=
  Snake9.LocalRup.prove_clause [c819, c520] c822 (by decide) p (sat_cons (step819 p h) (sat_cons (step520 p h) (sat_nil p)))
def c823 : List Lit := [(829, false), (962, true)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true :=
  Snake9.LocalRup.prove_clause [c820, c523] c823 (by decide) p (sat_cons (step820 p h) (sat_cons (step523 p h) (sat_nil p)))
def c824 : List Lit := [(829, false)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true :=
  Snake9.LocalRup.prove_clause [c524, c823] c824 (by decide) p (sat_cons (step524 p h) (sat_cons (step823 p h) (sat_nil p)))
def c825 : List Lit := [(1365, true)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true :=
  Snake9.LocalRup.prove_clause [c680, c682, c678, c669, c671, c666, c667, c158, c171, c164] c825 (by decide) p (sat_cons (step680 p h) (sat_cons (step682 p h) (sat_cons (step678 p h) (sat_cons (step669 p h) (sat_cons (step671 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step158 p h) (sat_cons (step171 p h) (sat_cons (step164 p h) (sat_nil p)))))))))))
def c826 : List Lit := [(1371, true)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true :=
  Snake9.LocalRup.prove_clause [c825, c687] c826 (by decide) p (sat_cons (step825 p h) (sat_cons (step687 p h) (sat_nil p)))
def c827 : List Lit := [(80, false), (81, false), (79, false)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true :=
  Snake9.LocalRup.prove_clause [c807, c193, c185, c189, c407, c403] c827 (by decide) p (sat_cons (step807 p h) (sat_cons (step193 p h) (sat_cons (step185 p h) (sat_cons (step189 p h) (sat_cons (step407 p h) (sat_cons (step403 p h) (sat_nil p)))))))
def c828 : List Lit := [(1383, true)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true :=
  Snake9.LocalRup.prove_clause [c699, c701, c696, c697, c827] c828 (by decide) p (sat_cons (step699 p h) (sat_cons (step701 p h) (sat_cons (step696 p h) (sat_cons (step697 p h) (sat_cons (step827 p h) (sat_nil p))))))
def c829 : List Lit := [(1391, true)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true :=
  Snake9.LocalRup.prove_clause [c828, c711] c829 (by decide) p (sat_cons (step828 p h) (sat_cons (step711 p h) (sat_nil p)))
def c830 : List Lit := [(1417, true)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true :=
  Snake9.LocalRup.prove_clause [c829, c741] c830 (by decide) p (sat_cons (step829 p h) (sat_cons (step741 p h) (sat_nil p)))
def c831 : List Lit := [(1357, true), (172, true)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true :=
  Snake9.LocalRup.prove_clause [c669, c671, c666, c667, c158, c161] c831 (by decide) p (sat_cons (step669 p h) (sat_cons (step671 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step158 p h) (sat_cons (step161 p h) (sat_nil p)))))))
def c832 : List Lit := [(1355, true), (174, true)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true :=
  Snake9.LocalRup.prove_clause [c666, c667, c166, c165, c780] c832 (by decide) p (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step166 p h) (sat_cons (step165 p h) (sat_cons (step780 p h) (sat_nil p))))))
def c833 : List Lit := [(1346, true), (70, false), (1252, true), (407, false)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true :=
  Snake9.TreeRup.prove_clause [c450, c258, c257, c256, c784, c255, c253, c445, c399, c397, c388, c380, c379, c386, c384, c382, c166, c165, c780, c160, c162, c157, c381, c172, c168, c170, c540, c442, c448, c357, c303, c279, c278, c277, c301, c299, c285, c284, c401, c376, c374, c367, c366, c373, c372, c369, c658, c659, c657, c147, c151, c145, c149, c140, c536, c537, c543, c531, c527, c32, c525, c24, c15] c833 (by decide) p (sat_cons (step450 p h) (sat_cons (step258 p h) (sat_cons (step257 p h) (sat_cons (step256 p h) (sat_cons (step784 p h) (sat_cons (step255 p h) (sat_cons (step253 p h) (sat_cons (step445 p h) (sat_cons (step399 p h) (sat_cons (step397 p h) (sat_cons (step388 p h) (sat_cons (step380 p h) (sat_cons (step379 p h) (sat_cons (step386 p h) (sat_cons (step384 p h) (sat_cons (step382 p h) (sat_cons (step166 p h) (sat_cons (step165 p h) (sat_cons (step780 p h) (sat_cons (step160 p h) (sat_cons (step162 p h) (sat_cons (step157 p h) (sat_cons (step381 p h) (sat_cons (step172 p h) (sat_cons (step168 p h) (sat_cons (step170 p h) (sat_cons (step540 p h) (sat_cons (step442 p h) (sat_cons (step448 p h) (sat_cons (step357 p h) (sat_cons (step303 p h) (sat_cons (step279 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step301 p h) (sat_cons (step299 p h) (sat_cons (step285 p h) (sat_cons (step284 p h) (sat_cons (step401 p h) (sat_cons (step376 p h) (sat_cons (step374 p h) (sat_cons (step367 p h) (sat_cons (step366 p h) (sat_cons (step373 p h) (sat_cons (step372 p h) (sat_cons (step369 p h) (sat_cons (step658 p h) (sat_cons (step659 p h) (sat_cons (step657 p h) (sat_cons (step147 p h) (sat_cons (step151 p h) (sat_cons (step145 p h) (sat_cons (step149 p h) (sat_cons (step140 p h) (sat_cons (step536 p h) (sat_cons (step537 p h) (sat_cons (step543 p h) (sat_cons (step531 p h) (sat_cons (step527 p h) (sat_cons (step32 p h) (sat_cons (step525 p h) (sat_cons (step24 p h) (sat_cons (step15 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c834 : List Lit := [(1267, true), (129, true)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true :=
  Snake9.LocalRup.prove_clause [c566, c569, c561, c553, c555, c558, c559, c551, c38, c79] c834 (by decide) p (sat_cons (step566 p h) (sat_cons (step569 p h) (sat_cons (step561 p h) (sat_cons (step553 p h) (sat_cons (step555 p h) (sat_cons (step558 p h) (sat_cons (step559 p h) (sat_cons (step551 p h) (sat_cons (step38 p h) (sat_cons (step79 p h) (sat_nil p)))))))))))
def c835 : List Lit := [(1301, true), (146, true)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true :=
  Snake9.LocalRup.prove_clause [c608, c610, c605, c606, c115, c118] c835 (by decide) p (sat_cons (step608 p h) (sat_cons (step610 p h) (sat_cons (step605 p h) (sat_cons (step606 p h) (sat_cons (step115 p h) (sat_cons (step118 p h) (sat_nil p)))))))
def c836 : List Lit := [(1251, true), (34, false), (255, true)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true :=
  Snake9.LocalRup.prove_clause [c303, c279, c278, c277, c301, c299, c285, c284, c539, c542, c534, c527, c531, c532, c525, c32, c15, c23] c836 (by decide) p (sat_cons (step303 p h) (sat_cons (step279 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step301 p h) (sat_cons (step299 p h) (sat_cons (step285 p h) (sat_cons (step284 p h) (sat_cons (step539 p h) (sat_cons (step542 p h) (sat_cons (step534 p h) (sat_cons (step527 p h) (sat_cons (step531 p h) (sat_cons (step532 p h) (sat_cons (step525 p h) (sat_cons (step32 p h) (sat_cons (step15 p h) (sat_cons (step23 p h) (sat_nil p)))))))))))))))))))
def c837 : List Lit := [(1248, true), (1291, true), (34, false), (43, false), (117, true)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.LocalRup.prove_clause [c534, c536, c531, c532, c33, c100, c26, c599, c594] c837 (by decide) p (sat_cons (step534 p h) (sat_cons (step536 p h) (sat_cons (step531 p h) (sat_cons (step532 p h) (sat_cons (step33 p h) (sat_cons (step100 p h) (sat_cons (step26 p h) (sat_cons (step599 p h) (sat_cons (step594 p h) (sat_nil p))))))))))
def c838 : List Lit := [(35, true), (1291, true), (46, true), (142, true)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c244, c113, c599, c111, c593] c838 (by decide) p (sat_cons (step244 p h) (sat_cons (step113 p h) (sat_cons (step599 p h) (sat_cons (step111 p h) (sat_cons (step593 p h) (sat_nil p))))))
def c839 : List Lit := [(41, true), (1299, true), (1334, true), (307, true)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.TreeRup.prove_clause [c247, c235, c237, c606, c605, c355, c350, c347, c335, c333, c835, c357, c301, c297, c294, c291, c290, c834, c303, c280, c275, c274, c273, c352, c326, c322, c318, c317, c332, c331, c330, c279, c278, c277, c299, c285, c284, c122, c121, c127, c125, c613, c617, c625, c629, c650, c583, c836, c578, c645, c637, c601, c837, c545, c528, c838, c100, c101, c8, c15, c10, c526, c12] c839 (by decide) p (sat_cons (step247 p h) (sat_cons (step235 p h) (sat_cons (step237 p h) (sat_cons (step606 p h) (sat_cons (step605 p h) (sat_cons (step355 p h) (sat_cons (step350 p h) (sat_cons (step347 p h) (sat_cons (step335 p h) (sat_cons (step333 p h) (sat_cons (step835 p h) (sat_cons (step357 p h) (sat_cons (step301 p h) (sat_cons (step297 p h) (sat_cons (step294 p h) (sat_cons (step291 p h) (sat_cons (step290 p h) (sat_cons (step834 p h) (sat_cons (step303 p h) (sat_cons (step280 p h) (sat_cons (step275 p h) (sat_cons (step274 p h) (sat_cons (step273 p h) (sat_cons (step352 p h) (sat_cons (step326 p h) (sat_cons (step322 p h) (sat_cons (step318 p h) (sat_cons (step317 p h) (sat_cons (step332 p h) (sat_cons (step331 p h) (sat_cons (step330 p h) (sat_cons (step279 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step299 p h) (sat_cons (step285 p h) (sat_cons (step284 p h) (sat_cons (step122 p h) (sat_cons (step121 p h) (sat_cons (step127 p h) (sat_cons (step125 p h) (sat_cons (step613 p h) (sat_cons (step617 p h) (sat_cons (step625 p h) (sat_cons (step629 p h) (sat_cons (step650 p h) (sat_cons (step583 p h) (sat_cons (step836 p h) (sat_cons (step578 p h) (sat_cons (step645 p h) (sat_cons (step637 p h) (sat_cons (step601 p h) (sat_cons (step837 p h) (sat_cons (step545 p h) (sat_cons (step528 p h) (sat_cons (step838 p h) (sat_cons (step100 p h) (sat_cons (step101 p h) (sat_cons (step8 p h) (sat_cons (step15 p h) (sat_cons (step10 p h) (sat_cons (step526 p h) (sat_cons (step12 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c840 : List Lit := [(1299, true), (1334, true), (307, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.TreeRup.prove_clause [c247, c235, c237, c355, c350, c347, c335, c333, c835, c357, c301, c297, c294, c291, c290, c834, c303, c280, c275, c274, c273, c352, c326, c322, c318, c317, c332, c331, c279, c278, c277, c299, c285, c284, c345, c343, c337, c605, c606, c839, c779, c123, c120, c125, c613, c836, c617, c578, c625, c645, c629, c637, c650, c601, c583, c837, c838, c545, c100, c101, c528, c8, c15, c10, c526, c12] c840 (by decide) p (sat_cons (step247 p h) (sat_cons (step235 p h) (sat_cons (step237 p h) (sat_cons (step355 p h) (sat_cons (step350 p h) (sat_cons (step347 p h) (sat_cons (step335 p h) (sat_cons (step333 p h) (sat_cons (step835 p h) (sat_cons (step357 p h) (sat_cons (step301 p h) (sat_cons (step297 p h) (sat_cons (step294 p h) (sat_cons (step291 p h) (sat_cons (step290 p h) (sat_cons (step834 p h) (sat_cons (step303 p h) (sat_cons (step280 p h) (sat_cons (step275 p h) (sat_cons (step274 p h) (sat_cons (step273 p h) (sat_cons (step352 p h) (sat_cons (step326 p h) (sat_cons (step322 p h) (sat_cons (step318 p h) (sat_cons (step317 p h) (sat_cons (step332 p h) (sat_cons (step331 p h) (sat_cons (step279 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step299 p h) (sat_cons (step285 p h) (sat_cons (step284 p h) (sat_cons (step345 p h) (sat_cons (step343 p h) (sat_cons (step337 p h) (sat_cons (step605 p h) (sat_cons (step606 p h) (sat_cons (step839 p h) (sat_cons (step779 p h) (sat_cons (step123 p h) (sat_cons (step120 p h) (sat_cons (step125 p h) (sat_cons (step613 p h) (sat_cons (step836 p h) (sat_cons (step617 p h) (sat_cons (step578 p h) (sat_cons (step625 p h) (sat_cons (step645 p h) (sat_cons (step629 p h) (sat_cons (step637 p h) (sat_cons (step650 p h) (sat_cons (step601 p h) (sat_cons (step583 p h) (sat_cons (step837 p h) (sat_cons (step838 p h) (sat_cons (step545 p h) (sat_cons (step100 p h) (sat_cons (step101 p h) (sat_cons (step528 p h) (sat_cons (step8 p h) (sat_cons (step15 p h) (sat_cons (step10 p h) (sat_cons (step526 p h) (sat_cons (step12 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c841 : List Lit := [(7, true), (1242, true), (110, true)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c237, c10, c526, c12] c841 (by decide) p (sat_cons (step237 p h) (sat_cons (step10 p h) (sat_cons (step526 p h) (sat_cons (step12 p h) (sat_nil p)))))
def c842 : List Lit := [(11, true), (1372, false), (1384, false), (74, false), (183, false)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.TreeRup.prove_clause [c791, c450, c240, c775, c235, c265, c406, c408, c418, c439, c442, c448, c357, c301, c297, c294, c291, c290, c834, c714, c745, c757, c773, c355, c350, c347, c335, c333, c835, c624, c628, c651, c584, c303, c280, c275, c274, c273, c279, c278, c277, c299, c285, c284, c419, c416, c411, c410, c182, c34, c32, c533, c535, c540, c546, c581, c528, c646, c771, c759, c750, c716, c841, c15, c8, c173, c208, c710, c205, c705] c842 (by decide) p (sat_cons (step791 p h) (sat_cons (step450 p h) (sat_cons (step240 p h) (sat_cons (step775 p h) (sat_cons (step235 p h) (sat_cons (step265 p h) (sat_cons (step406 p h) (sat_cons (step408 p h) (sat_cons (step418 p h) (sat_cons (step439 p h) (sat_cons (step442 p h) (sat_cons (step448 p h) (sat_cons (step357 p h) (sat_cons (step301 p h) (sat_cons (step297 p h) (sat_cons (step294 p h) (sat_cons (step291 p h) (sat_cons (step290 p h) (sat_cons (step834 p h) (sat_cons (step714 p h) (sat_cons (step745 p h) (sat_cons (step757 p h) (sat_cons (step773 p h) (sat_cons (step355 p h) (sat_cons (step350 p h) (sat_cons (step347 p h) (sat_cons (step335 p h) (sat_cons (step333 p h) (sat_cons (step835 p h) (sat_cons (step624 p h) (sat_cons (step628 p h) (sat_cons (step651 p h) (sat_cons (step584 p h) (sat_cons (step303 p h) (sat_cons (step280 p h) (sat_cons (step275 p h) (sat_cons (step274 p h) (sat_cons (step273 p h) (sat_cons (step279 p h) (sat_cons (step278 p h) (sat_cons (step277 p h) (sat_cons (step299 p h) (sat_cons (step285 p h) (sat_cons (step284 p h) (sat_cons (step419 p h) (sat_cons (step416 p h) (sat_cons (step411 p h) (sat_cons (step410 p h) (sat_cons (step182 p h) (sat_cons (step34 p h) (sat_cons (step32 p h) (sat_cons (step533 p h) (sat_cons (step535 p h) (sat_cons (step540 p h) (sat_cons (step546 p h) (sat_cons (step581 p h) (sat_cons (step528 p h) (sat_cons (step646 p h) (sat_cons (step771 p h) (sat_cons (step759 p h) (sat_cons (step750 p h) (sat_cons (step716 p h) (sat_cons (step841 p h) (sat_cons (step15 p h) (sat_cons (step8 p h) (sat_cons (step173 p h) (sat_cons (step208 p h) (sat_cons (step710 p h) (sat_cons (step205 p h) (sat_cons (step705 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c843 : List Lit := [(87, false), (1400, true), (85, false), (74, false), (367, false)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c791, c786, c781, c252, c251, c784, c250, c249, c450, c418, c439, c442, c448, c355, c350, c345, c342, c340, c339, c341, c338, c445, c401, c378, c365, c362, c361, c364, c363, c136, c139, c360, c135, c133, c134, c132, c130, c129, c131, c440, c435, c424, c423, c419, c416, c411, c410, c205, c203, c197, c720, c217, c723] c843 (by decide) p (sat_cons (step791 p h) (sat_cons (step786 p h) (sat_cons (step781 p h) (sat_cons (step252 p h) (sat_cons (step251 p h) (sat_cons (step784 p h) (sat_cons (step250 p h) (sat_cons (step249 p h) (sat_cons (step450 p h) (sat_cons (step418 p h) (sat_cons (step439 p h) (sat_cons (step442 p h) (sat_cons (step448 p h) (sat_cons (step355 p h) (sat_cons (step350 p h) (sat_cons (step345 p h) (sat_cons (step342 p h) (sat_cons (step340 p h) (sat_cons (step339 p h) (sat_cons (step341 p h) (sat_cons (step338 p h) (sat_cons (step445 p h) (sat_cons (step401 p h) (sat_cons (step378 p h) (sat_cons (step365 p h) (sat_cons (step362 p h) (sat_cons (step361 p h) (sat_cons (step364 p h) (sat_cons (step363 p h) (sat_cons (step136 p h) (sat_cons (step139 p h) (sat_cons (step360 p h) (sat_cons (step135 p h) (sat_cons (step133 p h) (sat_cons (step134 p h) (sat_cons (step132 p h) (sat_cons (step130 p h) (sat_cons (step129 p h) (sat_cons (step131 p h) (sat_cons (step440 p h) (sat_cons (step435 p h) (sat_cons (step424 p h) (sat_cons (step423 p h) (sat_cons (step419 p h) (sat_cons (step416 p h) (sat_cons (step411 p h) (sat_cons (step410 p h) (sat_cons (step205 p h) (sat_cons (step203 p h) (sat_cons (step197 p h) (sat_cons (step720 p h) (sat_cons (step217 p h) (sat_cons (step723 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c844 : List Lit := [(1420, true), (85, false), (1384, false), (74, false), (367, false)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c791, c265, c783, c714, c419, c416, c412, c747, c739, c843, c207, c705, c198, c707, c715, c748, c735, c736, c732, c722, c724, c213] c844 (by decide) p (sat_cons (step791 p h) (sat_cons (step265 p h) (sat_cons (step783 p h) (sat_cons (step714 p h) (sat_cons (step419 p h) (sat_cons (step416 p h) (sat_cons (step412 p h) (sat_cons (step747 p h) (sat_cons (step739 p h) (sat_cons (step843 p h) (sat_cons (step207 p h) (sat_cons (step705 p h) (sat_cons (step198 p h) (sat_cons (step707 p h) (sat_cons (step715 p h) (sat_cons (step748 p h) (sat_cons (step735 p h) (sat_cons (step736 p h) (sat_cons (step732 p h) (sat_cons (step722 p h) (sat_cons (step724 p h) (sat_cons (step213 p h) (sat_nil p)))))))))))))))))))))))
end B112E175
