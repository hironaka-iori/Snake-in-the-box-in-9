import B112E051Inputs
namespace B112E051
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c819 : List Lit := [(344, false)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true :=
  Snake9.LocalRup.prove_clause [c461, c460] c819 (by decide) p (sat_cons (step461 p h) (sat_cons (step460 p h) (sat_nil p)))
def c820 : List Lit := [(342, false)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true :=
  Snake9.LocalRup.prove_clause [c819, c420] c820 (by decide) p (sat_cons (step819 p h) (sat_cons (step420 p h) (sat_nil p)))
def c821 : List Lit := [(286, false)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true :=
  Snake9.LocalRup.prove_clause [c819, c423] c821 (by decide) p (sat_cons (step819 p h) (sat_cons (step423 p h) (sat_nil p)))
def c822 : List Lit := [(340, false)]
theorem step822 (p : Nat → Bool) (h : Constraints p) : clause p c822 = true :=
  Snake9.LocalRup.prove_clause [c820, c416] c822 (by decide) p (sat_cons (step820 p h) (sat_cons (step416 p h) (sat_nil p)))
def c823 : List Lit := [(284, false)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true :=
  Snake9.LocalRup.prove_clause [c821, c390] c823 (by decide) p (sat_cons (step821 p h) (sat_cons (step390 p h) (sat_nil p)))
def c824 : List Lit := [(258, false)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true :=
  Snake9.LocalRup.prove_clause [c821, c393] c824 (by decide) p (sat_cons (step821 p h) (sat_cons (step393 p h) (sat_nil p)))
def c825 : List Lit := [(282, false)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true :=
  Snake9.LocalRup.prove_clause [c823, c385] c825 (by decide) p (sat_cons (step823 p h) (sat_cons (step385 p h) (sat_nil p)))
def c826 : List Lit := [(270, false)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true :=
  Snake9.LocalRup.prove_clause [c823, c388] c826 (by decide) p (sat_cons (step823 p h) (sat_cons (step388 p h) (sat_nil p)))
def c827 : List Lit := [(256, false)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true :=
  Snake9.LocalRup.prove_clause [c824, c358] c827 (by decide) p (sat_cons (step824 p h) (sat_cons (step358 p h) (sat_nil p)))
def c828 : List Lit := [(244, false)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true :=
  Snake9.LocalRup.prove_clause [c824, c361] c828 (by decide) p (sat_cons (step824 p h) (sat_cons (step361 p h) (sat_nil p)))
def c829 : List Lit := [(280, false)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true :=
  Snake9.LocalRup.prove_clause [c825, c380] c829 (by decide) p (sat_cons (step825 p h) (sat_cons (step380 p h) (sat_nil p)))
def c830 : List Lit := [(274, false)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true :=
  Snake9.LocalRup.prove_clause [c825, c383] c830 (by decide) p (sat_cons (step825 p h) (sat_cons (step383 p h) (sat_nil p)))
def c831 : List Lit := [(268, false)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true :=
  Snake9.LocalRup.prove_clause [c826, c370] c831 (by decide) p (sat_cons (step826 p h) (sat_cons (step370 p h) (sat_nil p)))
def c832 : List Lit := [(254, false)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true :=
  Snake9.LocalRup.prove_clause [c827, c356] c832 (by decide) p (sat_cons (step827 p h) (sat_cons (step356 p h) (sat_nil p)))
def c833 : List Lit := [(242, false)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true :=
  Snake9.LocalRup.prove_clause [c828, c345] c833 (by decide) p (sat_cons (step828 p h) (sat_cons (step345 p h) (sat_nil p)))
def c834 : List Lit := [(264, false)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true :=
  Snake9.LocalRup.prove_clause [c831, c368] c834 (by decide) p (sat_cons (step831 p h) (sat_cons (step368 p h) (sat_nil p)))
def c835 : List Lit := [(238, false)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true :=
  Snake9.LocalRup.prove_clause [c833, c343] c835 (by decide) p (sat_cons (step833 p h) (sat_cons (step343 p h) (sat_nil p)))
def c836 : List Lit := [(34, false), (845, true), (39, false), (37, false)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true :=
  Snake9.LocalRup.prove_clause [c99, c100, c550, c554, c559] c836 (by decide) p (sat_cons (step99 p h) (sat_cons (step100 p h) (sat_cons (step550 p h) (sat_cons (step554 p h) (sat_cons (step559 p h) (sat_nil p))))))
def c837 : List Lit := [(922, true), (57, true), (914, false)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.LocalRup.prove_clause [c320, c629, c639, c654, c651, c630, c642, c626, c632, c633, c155, c151] c837 (by decide) p (sat_cons (step320 p h) (sat_cons (step629 p h) (sat_cons (step639 p h) (sat_cons (step654 p h) (sat_cons (step651 p h) (sat_cons (step630 p h) (sat_cons (step642 p h) (sat_cons (step626 p h) (sat_cons (step632 p h) (sat_cons (step633 p h) (sat_cons (step155 p h) (sat_cons (step151 p h) (sat_nil p)))))))))))))
def c838 : List Lit := [(824, true), (812, false)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c290, c517, c528, c531, c521, c483, c487, c497, c477, c467, c495, c469, c2, c3] c838 (by decide) p (sat_cons (step290 p h) (sat_cons (step517 p h) (sat_cons (step528 p h) (sat_cons (step531 p h) (sat_cons (step521 p h) (sat_cons (step483 p h) (sat_cons (step487 p h) (sat_cons (step497 p h) (sat_cons (step477 p h) (sat_cons (step467 p h) (sat_cons (step495 p h) (sat_cons (step469 p h) (sat_cons (step2 p h) (sat_cons (step3 p h) (sat_nil p)))))))))))))))
def c839 : List Lit := [(16, false), (4, true), (2, false), (257, true)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c297, c290, c296, c295, c291, c359, c346, c336, c335, c344, c341, c337, c357, c355, c353, c349, c348, c352, c351, c39, c40, c803, c6, c34, c29, c1, c37, c25, c12, c31, c14, c9] c839 (by decide) p (sat_cons (step297 p h) (sat_cons (step290 p h) (sat_cons (step296 p h) (sat_cons (step295 p h) (sat_cons (step291 p h) (sat_cons (step359 p h) (sat_cons (step346 p h) (sat_cons (step336 p h) (sat_cons (step335 p h) (sat_cons (step344 p h) (sat_cons (step341 p h) (sat_cons (step337 p h) (sat_cons (step357 p h) (sat_cons (step355 p h) (sat_cons (step353 p h) (sat_cons (step349 p h) (sat_cons (step348 p h) (sat_cons (step352 p h) (sat_cons (step351 p h) (sat_cons (step39 p h) (sat_cons (step40 p h) (sat_cons (step803 p h) (sat_cons (step6 p h) (sat_cons (step34 p h) (sat_cons (step29 p h) (sat_cons (step1 p h) (sat_cons (step37 p h) (sat_cons (step25 p h) (sat_cons (step12 p h) (sat_cons (step31 p h) (sat_cons (step14 p h) (sat_cons (step9 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c840 : List Lit := [(9, true), (792, true), (16, true), (8, true), (127, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c295, c471, c28, c481, c26, c473] c840 (by decide) p (sat_cons (step295 p h) (sat_cons (step471 p h) (sat_cons (step28 p h) (sat_cons (step481 p h) (sat_cons (step26 p h) (sat_cons (step473 p h) (sat_nil p)))))))
def c841 : List Lit := [(935, true)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c325, c672, c674, c670, c666, c667, c199, c198] c841 (by decide) p (sat_cons (step325 p h) (sat_cons (step672 p h) (sat_cons (step674 p h) (sat_cons (step670 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step199 p h) (sat_cons (step198 p h) (sat_nil p)))))))))
def c842 : List Lit := [(939, true)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c841, c678] c842 (by decide) p (sat_cons (step841 p h) (sat_cons (step678 p h) (sat_nil p)))
def c843 : List Lit := [(969, true), (96, false), (57, false)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c716, c718, c714, c710, c259] c843 (by decide) p (sat_cons (step716 p h) (sat_cons (step718 p h) (sat_cons (step714 p h) (sat_cons (step710 p h) (sat_cons (step259 p h) (sat_nil p))))))
def c844 : List Lit := [(788, false), (795, true), (802, true), (2, false), (9, false), (21, false), (26, false)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c484, c475, c478, c488, c470, c467, c52, c3, c496] c844 (by decide) p (sat_cons (step484 p h) (sat_cons (step475 p h) (sat_cons (step478 p h) (sat_cons (step488 p h) (sat_cons (step470 p h) (sat_cons (step467 p h) (sat_cons (step52 p h) (sat_cons (step3 p h) (sat_cons (step496 p h) (sat_nil p))))))))))
def c845 : List Lit := [(788, true), (2, false), (9, false)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c296, c295, c472, c473, c38, c26, c22] c845 (by decide) p (sat_cons (step296 p h) (sat_cons (step295 p h) (sat_cons (step472 p h) (sat_cons (step473 p h) (sat_cons (step38 p h) (sat_cons (step26 p h) (sat_cons (step22 p h) (sat_nil p))))))))
def c846 : List Lit := [(2, false), (9, false), (824, true), (21, false), (810, false), (26, false)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c297, c845, c475, c483, c531, c523, c498, c844, c534, c519, c499, c39, c40, c22] c846 (by decide) p (sat_cons (step297 p h) (sat_cons (step845 p h) (sat_cons (step475 p h) (sat_cons (step483 p h) (sat_cons (step531 p h) (sat_cons (step523 p h) (sat_cons (step498 p h) (sat_cons (step844 p h) (sat_cons (step534 p h) (sat_cons (step519 p h) (sat_cons (step499 p h) (sat_cons (step39 p h) (sat_cons (step40 p h) (sat_cons (step22 p h) (sat_nil p)))))))))))))))
def c847 : List Lit := [(9, false), (824, true), (26, false), (21, false), (810, false)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c294, c290, c846, c2, c23, c24, c467, c803, c487, c499, c531, c519, c523, c534, c500, c488, c494, c477, c52, c470] c847 (by decide) p (sat_cons (step294 p h) (sat_cons (step290 p h) (sat_cons (step846 p h) (sat_cons (step2 p h) (sat_cons (step23 p h) (sat_cons (step24 p h) (sat_cons (step467 p h) (sat_cons (step803 p h) (sat_cons (step487 p h) (sat_cons (step499 p h) (sat_cons (step531 p h) (sat_cons (step519 p h) (sat_cons (step523 p h) (sat_cons (step534 p h) (sat_cons (step500 p h) (sat_cons (step488 p h) (sat_cons (step494 p h) (sat_cons (step477 p h) (sat_cons (step52 p h) (sat_cons (step470 p h) (sat_nil p)))))))))))))))))))))
def c848 : List Lit := [(16, true), (13, false), (11, false), (9, true)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c832, c33, c28, c351, c349, c354] c848 (by decide) p (sat_cons (step832 p h) (sat_cons (step33 p h) (sat_cons (step28 p h) (sat_cons (step351 p h) (sat_cons (step349 p h) (sat_cons (step354 p h) (sat_nil p)))))))
def c849 : List Lit := [(913, false), (920, true)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c320, c646, c638, c641, c649, c632, c633, c628, c155, c626, c151] c849 (by decide) p (sat_cons (step320 p h) (sat_cons (step646 p h) (sat_cons (step638 p h) (sat_cons (step641 p h) (sat_cons (step649 p h) (sat_cons (step632 p h) (sat_cons (step633 p h) (sat_cons (step628 p h) (sat_cons (step155 p h) (sat_cons (step626 p h) (sat_cons (step151 p h) (sat_nil p))))))))))))
def c850 : List Lit := [(72, false), (913, true), (75, true)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c321, c636, c635, c168, c159] c850 (by decide) p (sat_cons (step321 p h) (sat_cons (step636 p h) (sat_cons (step635 p h) (sat_cons (step168 p h) (sat_cons (step159 p h) (sat_nil p))))))
def c851 : List Lit := [(919, true)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c320, c645, c648, c640, c628, c632, c633, c626, c155, c151] c851 (by decide) p (sat_cons (step320 p h) (sat_cons (step645 p h) (sat_cons (step648 p h) (sat_cons (step640 p h) (sat_cons (step628 p h) (sat_cons (step632 p h) (sat_cons (step633 p h) (sat_cons (step626 p h) (sat_cons (step155 p h) (sat_cons (step151 p h) (sat_nil p)))))))))))
def c852 : List Lit := [(969, true), (57, false)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c328, c716, c718, c843, c714, c710, c711, c242, c243] c852 (by decide) p (sat_cons (step328 p h) (sat_cons (step716 p h) (sat_cons (step718 p h) (sat_cons (step843 p h) (sat_cons (step714 p h) (sat_cons (step710 p h) (sat_cons (step711 p h) (sat_cons (step242 p h) (sat_cons (step243 p h) (sat_nil p))))))))))
def c853 : List Lit := [(65, false), (58, false), (64, false)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c320, c151, c155] c853 (by decide) p (sat_cons (step320 p h) (sat_cons (step151 p h) (sat_cons (step155 p h) (sat_nil p))))
def c854 : List Lit := [(57, true), (920, true)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c652, c629, c630, c649, c626, c640, c632, c633, c853] c854 (by decide) p (sat_cons (step652 p h) (sat_cons (step629 p h) (sat_cons (step630 p h) (sat_cons (step649 p h) (sat_cons (step626 p h) (sat_cons (step640 p h) (sat_cons (step632 p h) (sat_cons (step633 p h) (sat_cons (step853 p h) (sat_nil p))))))))))
def c855 : List Lit := [(988, true), (91, false)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.LocalRup.prove_clause [c333, c752, c753, c283, c278] c855 (by decide) p (sat_cons (step333 p h) (sat_cons (step752 p h) (sat_cons (step753 p h) (sat_cons (step283 p h) (sat_cons (step278 p h) (sat_nil p))))))
def c856 : List Lit := [(112, false), (91, false)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c333, c283, c284, c817] c856 (by decide) p (sat_cons (step333 p h) (sat_cons (step283 p h) (sat_cons (step284 p h) (sat_cons (step817 p h) (sat_nil p)))))
def c857 : List Lit := [(99, false), (964, true), (87, false), (90, true), (93, false)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c226, c228, c709, c704] c857 (by decide) p (sat_cons (step226 p h) (sat_cons (step228 p h) (sat_cons (step709 p h) (sat_cons (step704 p h) (sat_nil p)))))
def c858 : List Lit := [(967, false), (963, false), (1008, true), (93, true), (965, false)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c787, c735, c719, c722, c734, c712, c784, c855, c761, c757] c858 (by decide) p (sat_cons (step787 p h) (sat_cons (step735 p h) (sat_cons (step719 p h) (sat_cons (step722 p h) (sat_cons (step734 p h) (sat_cons (step712 p h) (sat_cons (step784 p h) (sat_cons (step855 p h) (sat_cons (step761 p h) (sat_cons (step757 p h) (sat_nil p)))))))))))
def c859 : List Lit := [(963, true), (99, false), (87, false)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c331, c266, c814, c703, c706, c708, c704, c225] c859 (by decide) p (sat_cons (step331 p h) (sat_cons (step266 p h) (sat_cons (step814 p h) (sat_cons (step703 p h) (sat_cons (step706 p h) (sat_cons (step708 p h) (sat_cons (step704 p h) (sat_cons (step225 p h) (sat_nil p)))))))))
def c860 : List Lit := [(962, true), (86, false), (87, false)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c705, c707, c702, c222] c860 (by decide) p (sat_cons (step705 p h) (sat_cons (step707 p h) (sat_cons (step702 p h) (sat_cons (step222 p h) (sat_nil p)))))
def c861 : List Lit := [(56, false), (863, true), (57, false), (74, false)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c137, c138, c585] c861 (by decide) p (sat_cons (step137 p h) (sat_cons (step138 p h) (sat_cons (step585 p h) (sat_nil p))))
def c862 : List Lit := [(87, true), (963, true), (965, true), (57, false)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c328, c711, c710, c244, c245, c257, c239, c702, c708] c862 (by decide) p (sat_cons (step328 p h) (sat_cons (step711 p h) (sat_cons (step710 p h) (sat_cons (step244 p h) (sat_cons (step245 p h) (sat_cons (step257 p h) (sat_cons (step239 p h) (sat_cons (step702 p h) (sat_cons (step708 p h) (sat_nil p))))))))))
def c863 : List Lit := [(108, false), (111, false), (86, false)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c332, c276, c282] c863 (by decide) p (sat_cons (step332 p h) (sat_cons (step276 p h) (sat_cons (step282 p h) (sat_nil p))))
def c864 : List Lit := [(1008, true), (970, false), (90, true), (980, false)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true :=
  Snake9.LocalRup.prove_clause [c702, c705, c730, c746, c763, c784, c782, c734, c767, c764, c706, c747, c757, c704, c742, c753, c863] c864 (by decide) p (sat_cons (step702 p h) (sat_cons (step705 p h) (sat_cons (step730 p h) (sat_cons (step746 p h) (sat_cons (step763 p h) (sat_cons (step784 p h) (sat_cons (step782 p h) (sat_cons (step734 p h) (sat_cons (step767 p h) (sat_cons (step764 p h) (sat_cons (step706 p h) (sat_cons (step747 p h) (sat_cons (step757 p h) (sat_cons (step704 p h) (sat_cons (step742 p h) (sat_cons (step753 p h) (sat_cons (step863 p h) (sat_nil p))))))))))))))))))
def c865 : List Lit := [(101, false), (84, true), (97, false), (108, false), (86, false), (87, true)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true :=
  Snake9.LocalRup.prove_clause [c327, c236, c264, c221] c865 (by decide) p (sat_cons (step327 p h) (sat_cons (step236 p h) (sat_cons (step264 p h) (sat_cons (step221 p h) (sat_nil p)))))
def c866 : List Lit := [(98, true), (84, true), (108, false), (86, false), (87, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true :=
  Snake9.LocalRup.prove_clause [c327, c220, c221, c815] c866 (by decide) p (sat_cons (step327 p h) (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step815 p h) (sat_nil p)))))
def c867 : List Lit := [(57, false), (930, true), (70, false), (75, false)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true :=
  Snake9.LocalRup.prove_clause [c183, c184, c185, c665, c660] c867 (by decide) p (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step665 p h) (sat_cons (step660 p h) (sat_nil p))))))
def c868 : List Lit := [(26, true), (807, true), (74, true), (281, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true :=
  Snake9.LocalRup.prove_clause [c300, c381, c372, c371, c58, c379, c377, c374, c63, c504, c61] c868 (by decide) p (sat_cons (step300 p h) (sat_cons (step381 p h) (sat_cons (step372 p h) (sat_cons (step371 p h) (sat_cons (step58 p h) (sat_cons (step379 p h) (sat_cons (step377 p h) (sat_cons (step374 p h) (sat_cons (step63 p h) (sat_cons (step504 p h) (sat_cons (step61 p h) (sat_nil p))))))))))))
def c869 : List Lit := [(921, true), (57, true), (913, false)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true :=
  Snake9.LocalRup.prove_clause [c629, c638, c653, c650, c630, c641, c626, c632, c633, c853] c869 (by decide) p (sat_cons (step629 p h) (sat_cons (step638 p h) (sat_cons (step653 p h) (sat_cons (step650 p h) (sat_cons (step630 p h) (sat_cons (step641 p h) (sat_cons (step626 p h) (sat_cons (step632 p h) (sat_cons (step633 p h) (sat_cons (step853 p h) (sat_nil p)))))))))))
def c870 : List Lit := [(810, false), (822, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true :=
  Snake9.LocalRup.prove_clause [c297, c526, c515, c519, c529, c499, c483, c39, c40, c477, c803, c469] c870 (by decide) p (sat_cons (step297 p h) (sat_cons (step526 p h) (sat_cons (step515 p h) (sat_cons (step519 p h) (sat_cons (step529 p h) (sat_cons (step499 p h) (sat_cons (step483 p h) (sat_cons (step39 p h) (sat_cons (step40 p h) (sat_cons (step477 p h) (sat_cons (step803 p h) (sat_cons (step469 p h) (sat_nil p)))))))))))))
def c871 : List Lit := [(17, true), (822, true), (26, false)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true :=
  Snake9.LocalRup.prove_clause [c299, c297, c532, c484, c480, c526, c522, c498, c495, c496, c500, c50, c52, c39, c40, c471, c803] c871 (by decide) p (sat_cons (step299 p h) (sat_cons (step297 p h) (sat_cons (step532 p h) (sat_cons (step484 p h) (sat_cons (step480 p h) (sat_cons (step526 p h) (sat_cons (step522 p h) (sat_cons (step498 p h) (sat_cons (step495 p h) (sat_cons (step496 p h) (sat_cons (step500 p h) (sat_cons (step50 p h) (sat_cons (step52 p h) (sat_cons (step39 p h) (sat_cons (step40 p h) (sat_cons (step471 p h) (sat_cons (step803 p h) (sat_nil p))))))))))))))))))
def c872 : List Lit := [(13, false), (11, false), (9, false), (822, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true :=
  Snake9.LocalRup.prove_clause [c290, c803, c22, c499, c2, c518, c467, c529, c487] c872 (by decide) p (sat_cons (step290 p h) (sat_cons (step803 p h) (sat_cons (step22 p h) (sat_cons (step499 p h) (sat_cons (step2 p h) (sat_cons (step518 p h) (sat_cons (step467 p h) (sat_cons (step529 p h) (sat_cons (step487 p h) (sat_nil p))))))))))
def c873 : List Lit := [(13, true), (9, false), (17, false), (804, true), (22, false)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true :=
  Snake9.LocalRup.prove_clause [c297, c294, c299, c39, c23, c500, c41, c494, c51] c873 (by decide) p (sat_cons (step297 p h) (sat_cons (step294 p h) (sat_cons (step299 p h) (sat_cons (step39 p h) (sat_cons (step23 p h) (sat_cons (step500 p h) (sat_cons (step41 p h) (sat_cons (step494 p h) (sat_cons (step51 p h) (sat_nil p))))))))))
def c874 : List Lit := [(9, false), (17, false), (822, true), (22, false)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true :=
  Snake9.LocalRup.prove_clause [c297, c294, c299, c526, c522, c873, c872, c40, c24, c500, c41, c494, c51] c874 (by decide) p (sat_cons (step297 p h) (sat_cons (step294 p h) (sat_cons (step299 p h) (sat_cons (step526 p h) (sat_cons (step522 p h) (sat_cons (step873 p h) (sat_cons (step872 p h) (sat_cons (step40 p h) (sat_cons (step24 p h) (sat_cons (step500 p h) (sat_cons (step41 p h) (sat_cons (step494 p h) (sat_cons (step51 p h) (sat_nil p))))))))))))))
def c875 : List Lit := [(822, true), (22, false), (26, false)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true :=
  Snake9.LocalRup.prove_clause [c290, c299, c532, c871, c874, c469, c477, c483, c488, c529, c467, c518, c2, c497, c41, c494, c51] c875 (by decide) p (sat_cons (step290 p h) (sat_cons (step299 p h) (sat_cons (step532 p h) (sat_cons (step871 p h) (sat_cons (step874 p h) (sat_cons (step469 p h) (sat_cons (step477 p h) (sat_cons (step483 p h) (sat_cons (step488 p h) (sat_cons (step529 p h) (sat_cons (step467 p h) (sat_cons (step518 p h) (sat_cons (step2 p h) (sat_cons (step497 p h) (sat_cons (step41 p h) (sat_cons (step494 p h) (sat_cons (step51 p h) (sat_nil p))))))))))))))))))
def c876 : List Lit := [(257, true), (16, false), (8, true), (2, false)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true :=
  Snake9.LocalRup.prove_clause [c359, c839, c344, c10, c341, c338] c876 (by decide) p (sat_cons (step359 p h) (sat_cons (step839 p h) (sat_cons (step344 p h) (sat_cons (step10 p h) (sat_cons (step341 p h) (sat_cons (step338 p h) (sat_nil p)))))))
def c877 : List Lit := [(969, true), (90, false)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true :=
  Snake9.LocalRup.prove_clause [c328, c716, c718, c714, c710, c711, c242, c260, c243] c877 (by decide) p (sat_cons (step328 p h) (sat_cons (step716 p h) (sat_cons (step718 p h) (sat_cons (step714 p h) (sat_cons (step710 p h) (sat_cons (step711 p h) (sat_cons (step242 p h) (sat_cons (step260 p h) (sat_cons (step243 p h) (sat_nil p))))))))))
def c878 : List Lit := [(962, true), (87, false)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true :=
  Snake9.LocalRup.prove_clause [c705, c860, c703] c878 (by decide) p (sat_cons (step705 p h) (sat_cons (step860 p h) (sat_cons (step703 p h) (sat_nil p))))
def c879 : List Lit := [(996, true)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true :=
  Snake9.LocalRup.prove_clause [c334, c761, c763, c756, c745, c746, c755, c742, c743, c739, c289, c273, c287] c879 (by decide) p (sat_cons (step334 p h) (sat_cons (step761 p h) (sat_cons (step763 p h) (sat_cons (step756 p h) (sat_cons (step745 p h) (sat_cons (step746 p h) (sat_cons (step755 p h) (sat_cons (step742 p h) (sat_cons (step743 p h) (sat_cons (step739 p h) (sat_cons (step289 p h) (sat_cons (step273 p h) (sat_cons (step287 p h) (sat_nil p))))))))))))))
def c880 : List Lit := [(87, false), (969, false), (1007, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true :=
  Snake9.LocalRup.prove_clause [c879, c334, c781, c733, c878, c859, c729, c740, c778, c746, c767, c764, c749, c747, c756, c741, c742, c743, c755, c289, c273, c287] c880 (by decide) p (sat_cons (step879 p h) (sat_cons (step334 p h) (sat_cons (step781 p h) (sat_cons (step733 p h) (sat_cons (step878 p h) (sat_cons (step859 p h) (sat_cons (step729 p h) (sat_cons (step740 p h) (sat_cons (step778 p h) (sat_cons (step746 p h) (sat_cons (step767 p h) (sat_cons (step764 p h) (sat_cons (step749 p h) (sat_cons (step747 p h) (sat_cons (step756 p h) (sat_cons (step741 p h) (sat_cons (step742 p h) (sat_cons (step743 p h) (sat_cons (step755 p h) (sat_cons (step289 p h) (sat_cons (step273 p h) (sat_cons (step287 p h) (sat_nil p)))))))))))))))))))))))
def c881 : List Lit := [(997, true), (99, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true :=
  Snake9.LocalRup.prove_clause [c334, c740, c746, c767, c764, c749, c747, c756, c741, c742, c743, c755, c289, c273, c287] c881 (by decide) p (sat_cons (step334 p h) (sat_cons (step740 p h) (sat_cons (step746 p h) (sat_cons (step767 p h) (sat_cons (step764 p h) (sat_cons (step749 p h) (sat_cons (step747 p h) (sat_cons (step756 p h) (sat_cons (step741 p h) (sat_cons (step742 p h) (sat_cons (step743 p h) (sat_cons (step755 p h) (sat_cons (step289 p h) (sat_cons (step273 p h) (sat_cons (step287 p h) (sat_nil p))))))))))))))))
def c882 : List Lit := [(973, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true :=
  Snake9.LocalRup.prove_clause [c724, c728, c877, c705, c702] c882 (by decide) p (sat_cons (step724 p h) (sat_cons (step728 p h) (sat_cons (step877 p h) (sat_cons (step705 p h) (sat_cons (step702 p h) (sat_nil p))))))
end B112E051
