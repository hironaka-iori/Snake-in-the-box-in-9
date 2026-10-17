import B112E094Part0002
namespace B112E094
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c823 : List Lit := [(2, true), (83, true), (33, false), (37, true)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true :=
  Snake9.LocalRup.prove_clause [c183, c50] c823 (by decide) p (sat_cons (step183 p h) (sat_cons (step50 p h) (sat_nil p)))
def c824 : List Lit := [(36, false), (32, true)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true :=
  Snake9.LocalRup.prove_clause [c184, c54] c824 (by decide) p (sat_cons (step184 p h) (sat_cons (step54 p h) (sat_nil p)))
def c825 : List Lit := [(49, false), (53, true)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true :=
  Snake9.LocalRup.prove_clause [c189, c66] c825 (by decide) p (sat_cons (step189 p h) (sat_cons (step66 p h) (sat_nil p)))
def c826 : List Lit := [(71, true), (67, false)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true :=
  Snake9.LocalRup.prove_clause [c195, c84] c826 (by decide) p (sat_cons (step195 p h) (sat_cons (step84 p h) (sat_nil p)))
def c827 : List Lit := [(73, false), (72, true), (75, true)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true :=
  Snake9.LocalRup.prove_clause [c196, c89] c827 (by decide) p (sat_cons (step196 p h) (sat_cons (step89 p h) (sat_nil p)))
def c828 : List Lit := [(77, false), (79, true), (75, true)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true :=
  Snake9.LocalRup.prove_clause [c198, c97] c828 (by decide) p (sat_cons (step198 p h) (sat_cons (step97 p h) (sat_nil p)))
def c829 : List Lit := [(83, true), (72, true), (81, true), (80, false)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true :=
  Snake9.LocalRup.prove_clause [c200, c105] c829 (by decide) p (sat_cons (step200 p h) (sat_cons (step105 p h) (sat_nil p)))
def c830 : List Lit := [(32, true), (82, false), (81, true)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true :=
  Snake9.LocalRup.prove_clause [c201, c116] c830 (by decide) p (sat_cons (step201 p h) (sat_cons (step116 p h) (sat_nil p)))
def c831 : List Lit := [(84, false), (89, true), (83, true)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true :=
  Snake9.LocalRup.prove_clause [c202, c120] c831 (by decide) p (sat_cons (step202 p h) (sat_cons (step120 p h) (sat_nil p)))
def c832 : List Lit := [(83, true), (84, false), (81, true)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true :=
  Snake9.LocalRup.prove_clause [c202, c122] c832 (by decide) p (sat_cons (step202 p h) (sat_cons (step122 p h) (sat_nil p)))
def c833 : List Lit := [(85, true), (86, false), (89, true)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true :=
  Snake9.LocalRup.prove_clause [c203, c125] c833 (by decide) p (sat_cons (step203 p h) (sat_cons (step125 p h) (sat_nil p)))
def c834 : List Lit := [(85, true), (86, false), (81, true)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true :=
  Snake9.LocalRup.prove_clause [c203, c127] c834 (by decide) p (sat_cons (step203 p h) (sat_cons (step127 p h) (sat_nil p)))
def c835 : List Lit := [(103, false), (102, true)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true :=
  Snake9.LocalRup.prove_clause [c211, c167] c835 (by decide) p (sat_cons (step211 p h) (sat_cons (step167 p h) (sat_nil p)))
def c836 : List Lit := [(103, false), (100, true)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true :=
  Snake9.LocalRup.prove_clause [c211, c168] c836 (by decide) p (sat_cons (step211 p h) (sat_cons (step168 p h) (sat_nil p)))
def c837 : List Lit := [(357, false), (407, false)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.LocalRup.prove_clause [c635, c301] c837 (by decide) p (sat_cons (step635 p h) (sat_cons (step301 p h) (sat_nil p)))
def c838 : List Lit := [(33, true), (1267, true)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c781, c425] c838 (by decide) p (sat_cons (step781 p h) (sat_cons (step425 p h) (sat_nil p)))
def c839 : List Lit := [(1270, true), (1261, false)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c782, c429] c839 (by decide) p (sat_cons (step782 p h) (sat_cons (step429 p h) (sat_nil p)))
def c840 : List Lit := [(1288, false), (1296, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c664, c456] c840 (by decide) p (sat_cons (step664 p h) (sat_cons (step456 p h) (sat_nil p)))
def c841 : List Lit := [(1290, false), (1298, true)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c664, c458] c841 (by decide) p (sat_cons (step664 p h) (sat_cons (step458 p h) (sat_nil p)))
def c842 : List Lit := [(1311, true), (1296, false)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c702, c470] c842 (by decide) p (sat_cons (step702 p h) (sat_cons (step470 p h) (sat_nil p)))
def c843 : List Lit := [(1312, true), (1297, false)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c702, c471] c843 (by decide) p (sat_cons (step702 p h) (sat_cons (step471 p h) (sat_nil p)))
def c844 : List Lit := [(1313, true), (1298, false)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c702, c472] c844 (by decide) p (sat_cons (step702 p h) (sat_cons (step472 p h) (sat_nil p)))
def c845 : List Lit := [(1299, false), (1314, true)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c702, c473] c845 (by decide) p (sat_cons (step702 p h) (sat_cons (step473 p h) (sat_nil p)))
def c846 : List Lit := [(1311, true), (1248, false)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c665, c475] c846 (by decide) p (sat_cons (step665 p h) (sat_cons (step475 p h) (sat_nil p)))
def c847 : List Lit := [(1311, false), (1431, false)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c622, c617] c847 (by decide) p (sat_cons (step622 p h) (sat_cons (step617 p h) (sat_nil p)))
def c848 : List Lit := [(1312, false), (1430, false)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c622, c618] c848 (by decide) p (sat_cons (step622 p h) (sat_cons (step618 p h) (sat_nil p)))
def c849 : List Lit := [(1313, false), (1429, false)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c622, c619] c849 (by decide) p (sat_cons (step622 p h) (sat_cons (step619 p h) (sat_nil p)))
def c850 : List Lit := [(1314, false), (1428, false)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c622, c620] c850 (by decide) p (sat_cons (step622 p h) (sat_cons (step620 p h) (sat_nil p)))
def c851 : List Lit := [(1323, false), (103, false), (104, false), (1414, false), (1270, false), (1346, false)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c836, c835, c459, c842, c847, c615, c495, c684, c524, c611, c518, c848, c502, c843, c460, c449, c444, c446, c442, c439, c825, c160, c170, c500, c826] c851 (by decide) p (sat_cons (step836 p h) (sat_cons (step835 p h) (sat_cons (step459 p h) (sat_cons (step842 p h) (sat_cons (step847 p h) (sat_cons (step615 p h) (sat_cons (step495 p h) (sat_cons (step684 p h) (sat_cons (step524 p h) (sat_cons (step611 p h) (sat_cons (step518 p h) (sat_cons (step848 p h) (sat_cons (step502 p h) (sat_cons (step843 p h) (sat_cons (step460 p h) (sat_cons (step449 p h) (sat_cons (step444 p h) (sat_cons (step446 p h) (sat_cons (step442 p h) (sat_cons (step439 p h) (sat_cons (step825 p h) (sat_cons (step160 p h) (sat_cons (step170 p h) (sat_cons (step500 p h) (sat_cons (step826 p h) (sat_nil p))))))))))))))))))))))))))
def c852 : List Lit := [(1384, false), (83, false), (1346, false)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c809, c792, c411, c414, c839, c810, c780, c513, c519, c590, c589, c601, c850, c845, c462, c817, c645, c564, c581, c651, c569, c570, c836, c851, c485, c708, c726, c783, c461, c160, c844, c499, c849, c501, c606, c516, c520] c852 (by decide) p (sat_cons (step809 p h) (sat_cons (step792 p h) (sat_cons (step411 p h) (sat_cons (step414 p h) (sat_cons (step839 p h) (sat_cons (step810 p h) (sat_cons (step780 p h) (sat_cons (step513 p h) (sat_cons (step519 p h) (sat_cons (step590 p h) (sat_cons (step589 p h) (sat_cons (step601 p h) (sat_cons (step850 p h) (sat_cons (step845 p h) (sat_cons (step462 p h) (sat_cons (step817 p h) (sat_cons (step645 p h) (sat_cons (step564 p h) (sat_cons (step581 p h) (sat_cons (step651 p h) (sat_cons (step569 p h) (sat_cons (step570 p h) (sat_cons (step836 p h) (sat_cons (step851 p h) (sat_cons (step485 p h) (sat_cons (step708 p h) (sat_cons (step726 p h) (sat_cons (step783 p h) (sat_cons (step461 p h) (sat_cons (step160 p h) (sat_cons (step844 p h) (sat_cons (step499 p h) (sat_cons (step849 p h) (sat_cons (step501 p h) (sat_cons (step606 p h) (sat_cons (step516 p h) (sat_cons (step520 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c853 : List Lit := [(86, true), (1384, true), (83, false)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c549, c546, c785, c673, c537, c539, c543, c627, c552, c530, c532] c853 (by decide) p (sat_cons (step549 p h) (sat_cons (step546 p h) (sat_cons (step785 p h) (sat_cons (step673 p h) (sat_cons (step537 p h) (sat_cons (step539 p h) (sat_cons (step543 p h) (sat_cons (step627 p h) (sat_cons (step552 p h) (sat_cons (step530 p h) (sat_cons (step532 p h) (sat_nil p))))))))))))
def c854 : List Lit := [(83, false), (1346, false)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c852, c549, c555, c546, c533, c785, c673, c853, c833, c628, c530, c531, c532, c114, c552, c538, c543] c854 (by decide) p (sat_cons (step852 p h) (sat_cons (step549 p h) (sat_cons (step555 p h) (sat_cons (step546 p h) (sat_cons (step533 p h) (sat_cons (step785 p h) (sat_cons (step673 p h) (sat_cons (step853 p h) (sat_cons (step833 p h) (sat_cons (step628 p h) (sat_cons (step530 p h) (sat_cons (step531 p h) (sat_cons (step532 p h) (sat_cons (step114 p h) (sat_cons (step552 p h) (sat_cons (step538 p h) (sat_cons (step543 p h) (sat_nil p))))))))))))))))))
def c855 : List Lit := [(1384, true), (1376, true), (83, true)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.LocalRup.prove_clause [c785, c673, c831, c538, c539, c543, c833, c552, c628, c532, c530] c855 (by decide) p (sat_cons (step785 p h) (sat_cons (step673 p h) (sat_cons (step831 p h) (sat_cons (step538 p h) (sat_cons (step539 p h) (sat_cons (step543 p h) (sat_cons (step833 p h) (sat_cons (step552 p h) (sat_cons (step628 p h) (sat_cons (step532 p h) (sat_cons (step530 p h) (sat_nil p))))))))))))
def c856 : List Lit := [(1405, true), (1413, false), (1346, false)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c803, c810, c792, c839, c411, c414] c856 (by decide) p (sat_cons (step803 p h) (sat_cons (step810 p h) (sat_cons (step792 p h) (sat_cons (step839 p h) (sat_cons (step411 p h) (sat_cons (step414 p h) (sat_nil p)))))))
def c857 : List Lit := [(1270, true), (78, false), (32, false), (82, false), (1249, true)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c427, c839, c423, c838, c414, c813, c411, c412, c373, c45, c719, c405, c421, c385, c788, c797, c387, c694, c796, c389, c4, c398, c379, c381] c857 (by decide) p (sat_cons (step427 p h) (sat_cons (step839 p h) (sat_cons (step423 p h) (sat_cons (step838 p h) (sat_cons (step414 p h) (sat_cons (step813 p h) (sat_cons (step411 p h) (sat_cons (step412 p h) (sat_cons (step373 p h) (sat_cons (step45 p h) (sat_cons (step719 p h) (sat_cons (step405 p h) (sat_cons (step421 p h) (sat_cons (step385 p h) (sat_cons (step788 p h) (sat_cons (step797 p h) (sat_cons (step387 p h) (sat_cons (step694 p h) (sat_cons (step796 p h) (sat_cons (step389 p h) (sat_cons (step4 p h) (sat_cons (step398 p h) (sat_cons (step379 p h) (sat_cons (step381 p h) (sat_nil p)))))))))))))))))))))))))
def c858 : List Lit := [(1248, true), (1271, true), (83, true)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c792, c411, c414, c430, c838, c813, c695, c381, c378, c379, c696, c694, c796, c818, c1, c366, c360, c6, c823, c820, c12] c858 (by decide) p (sat_cons (step792 p h) (sat_cons (step411 p h) (sat_cons (step414 p h) (sat_cons (step430 p h) (sat_cons (step838 p h) (sat_cons (step813 p h) (sat_cons (step695 p h) (sat_cons (step381 p h) (sat_cons (step378 p h) (sat_cons (step379 p h) (sat_cons (step696 p h) (sat_cons (step694 p h) (sat_cons (step796 p h) (sat_cons (step818 p h) (sat_cons (step1 p h) (sat_cons (step366 p h) (sat_cons (step360 p h) (sat_cons (step6 p h) (sat_cons (step823 p h) (sat_cons (step820 p h) (sat_cons (step12 p h) (sat_nil p))))))))))))))))))))))
def c859 : List Lit := [(1233, true), (1, false), (1376, true), (1346, false)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c854, c855, c659, c856, c589, c764, c858, c808, c839, c414, c412, c411, c427, c838, c423, c778, c596, c794, c559, c385, c386, c719, c788, c536, c421, c824, c46, c45, c41, c531, c787, c829, c540, c774] c859 (by decide) p (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step659 p h) (sat_cons (step856 p h) (sat_cons (step589 p h) (sat_cons (step764 p h) (sat_cons (step858 p h) (sat_cons (step808 p h) (sat_cons (step839 p h) (sat_cons (step414 p h) (sat_cons (step412 p h) (sat_cons (step411 p h) (sat_cons (step427 p h) (sat_cons (step838 p h) (sat_cons (step423 p h) (sat_cons (step778 p h) (sat_cons (step596 p h) (sat_cons (step794 p h) (sat_cons (step559 p h) (sat_cons (step385 p h) (sat_cons (step386 p h) (sat_cons (step719 p h) (sat_cons (step788 p h) (sat_cons (step536 p h) (sat_cons (step421 p h) (sat_cons (step824 p h) (sat_cons (step46 p h) (sat_cons (step45 p h) (sat_cons (step41 p h) (sat_cons (step531 p h) (sat_cons (step787 p h) (sat_cons (step829 p h) (sat_cons (step540 p h) (sat_cons (step774 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c860 : List Lit := [(5, false), (1376, true), (1346, false)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c854, c855, c659, c856, c589, c795, c764, c858, c808, c427, c838, c813, c373, c405, c839, c414, c411, c819, c2, c4, c379, c381, c396, c410, c375, c859, c797, c800, c366, c360] c860 (by decide) p (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step659 p h) (sat_cons (step856 p h) (sat_cons (step589 p h) (sat_cons (step795 p h) (sat_cons (step764 p h) (sat_cons (step858 p h) (sat_cons (step808 p h) (sat_cons (step427 p h) (sat_cons (step838 p h) (sat_cons (step813 p h) (sat_cons (step373 p h) (sat_cons (step405 p h) (sat_cons (step839 p h) (sat_cons (step414 p h) (sat_cons (step411 p h) (sat_cons (step819 p h) (sat_cons (step2 p h) (sat_cons (step4 p h) (sat_cons (step379 p h) (sat_cons (step381 p h) (sat_cons (step396 p h) (sat_cons (step410 p h) (sat_cons (step375 p h) (sat_cons (step859 p h) (sat_cons (step797 p h) (sat_cons (step800 p h) (sat_cons (step366 p h) (sat_cons (step360 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c861 : List Lit := [(1376, true), (1346, false)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c854, c794, c855, c659, c856, c589, c764, c795, c858, c808, c427, c839, c423, c838, c414, c411, c412, c860, c796, c797, c385, c386, c859, c719, c21, c788, c822, c821, c421, c801, c46, c535, c691, c556, c543] c861 (by decide) p (sat_cons (step854 p h) (sat_cons (step794 p h) (sat_cons (step855 p h) (sat_cons (step659 p h) (sat_cons (step856 p h) (sat_cons (step589 p h) (sat_cons (step764 p h) (sat_cons (step795 p h) (sat_cons (step858 p h) (sat_cons (step808 p h) (sat_cons (step427 p h) (sat_cons (step839 p h) (sat_cons (step423 p h) (sat_cons (step838 p h) (sat_cons (step414 p h) (sat_cons (step411 p h) (sat_cons (step412 p h) (sat_cons (step860 p h) (sat_cons (step796 p h) (sat_cons (step797 p h) (sat_cons (step385 p h) (sat_cons (step386 p h) (sat_cons (step859 p h) (sat_cons (step719 p h) (sat_cons (step21 p h) (sat_cons (step788 p h) (sat_cons (step822 p h) (sat_cons (step821 p h) (sat_cons (step421 p h) (sat_cons (step801 p h) (sat_cons (step46 p h) (sat_cons (step535 p h) (sat_cons (step691 p h) (sat_cons (step556 p h) (sat_cons (step543 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c862 : List Lit := [(1346, false)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c794, c854, c861, c546, c549, c553, c659, c532, c534, c856, c529, c589, c764, c795, c858, c808, c839, c857, c414, c830, c411, c801] c862 (by decide) p (sat_cons (step794 p h) (sat_cons (step854 p h) (sat_cons (step861 p h) (sat_cons (step546 p h) (sat_cons (step549 p h) (sat_cons (step553 p h) (sat_cons (step659 p h) (sat_cons (step532 p h) (sat_cons (step534 p h) (sat_cons (step856 p h) (sat_cons (step529 p h) (sat_cons (step589 p h) (sat_cons (step764 p h) (sat_cons (step795 p h) (sat_cons (step858 p h) (sat_cons (step808 p h) (sat_cons (step839 p h) (sat_cons (step857 p h) (sat_cons (step414 p h) (sat_cons (step830 p h) (sat_cons (step411 p h) (sat_cons (step801 p h) (sat_nil p)))))))))))))))))))))))
def c863 : List Lit := [(1344, false)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c862, c509] c863 (by decide) p (sat_cons (step862 p h) (sat_cons (step509 p h) (sat_nil p)))
def c864 : List Lit := [(1342, false)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true :=
  Snake9.LocalRup.prove_clause [c862, c511] c864 (by decide) p (sat_cons (step862 p h) (sat_cons (step511 p h) (sat_nil p)))
def c865 : List Lit := [(88, true)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true :=
  Snake9.LocalRup.prove_clause [c862, c690] c865 (by decide) p (sat_cons (step862 p h) (sat_cons (step690 p h) (sat_nil p)))
def c866 : List Lit := [(82, false)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true :=
  Snake9.LocalRup.prove_clause [c862, c755] c866 (by decide) p (sat_cons (step862 p h) (sat_cons (step755 p h) (sat_nil p)))
def c867 : List Lit := [(77, true)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true :=
  Snake9.LocalRup.prove_clause [c863, c506] c867 (by decide) p (sat_cons (step863 p h) (sat_cons (step506 p h) (sat_nil p)))
def c868 : List Lit := [(76, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true :=
  Snake9.LocalRup.prove_clause [c863, c507] c868 (by decide) p (sat_cons (step863 p h) (sat_cons (step507 p h) (sat_nil p)))
def c869 : List Lit := [(73, true)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true :=
  Snake9.LocalRup.prove_clause [c864, c504] c869 (by decide) p (sat_cons (step864 p h) (sat_cons (step504 p h) (sat_nil p)))
def c870 : List Lit := [(1370, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true :=
  Snake9.LocalRup.prove_clause [c866, c529] c870 (by decide) p (sat_cons (step866 p h) (sat_cons (step529 p h) (sat_nil p)))
def c871 : List Lit := [(75, false)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true :=
  Snake9.LocalRup.prove_clause [c869, c868, c867, c91] c871 (by decide) p (sat_cons (step869 p h) (sat_cons (step868 p h) (sat_cons (step867 p h) (sat_cons (step91 p h) (sat_nil p)))))
def c872 : List Lit := [(79, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true :=
  Snake9.LocalRup.prove_clause [c871, c867, c828] c872 (by decide) p (sat_cons (step871 p h) (sat_cons (step867 p h) (sat_cons (step828 p h) (sat_nil p))))
def c873 : List Lit := [(72, true)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true :=
  Snake9.LocalRup.prove_clause [c871, c869, c827] c873 (by decide) p (sat_cons (step871 p h) (sat_cons (step869 p h) (sat_cons (step827 p h) (sat_nil p))))
def c874 : List Lit := [(78, false)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true :=
  Snake9.LocalRup.prove_clause [c872, c868, c867, c102] c874 (by decide) p (sat_cons (step872 p h) (sat_cons (step868 p h) (sat_cons (step867 p h) (sat_cons (step102 p h) (sat_nil p)))))
def c875 : List Lit := [(1373, true)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true :=
  Snake9.LocalRup.prove_clause [c874, c870, c535] c875 (by decide) p (sat_cons (step874 p h) (sat_cons (step870 p h) (sat_cons (step535 p h) (sat_nil p))))
def c876 : List Lit := [(1376, false), (1416, true)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true :=
  Snake9.LocalRup.prove_clause [c875, c865, c867, c662, c558, c546, c547, c557, c540, c596, c134, c654, c649, c575] c876 (by decide) p (sat_cons (step875 p h) (sat_cons (step865 p h) (sat_cons (step867 p h) (sat_cons (step662 p h) (sat_cons (step558 p h) (sat_cons (step546 p h) (sat_cons (step547 p h) (sat_cons (step557 p h) (sat_cons (step540 p h) (sat_cons (step596 p h) (sat_cons (step134 p h) (sat_cons (step654 p h) (sat_cons (step649 p h) (sat_cons (step575 p h) (sat_nil p)))))))))))))))
def c877 : List Lit := [(1377, false), (1386, true), (31, false)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true :=
  Snake9.LocalRup.prove_clause [c875, c874, c866, c873, c557, c542, c544, c560, c537, c538, c536, c108, c531, c834, c832, c104] c877 (by decide) p (sat_cons (step875 p h) (sat_cons (step874 p h) (sat_cons (step866 p h) (sat_cons (step873 p h) (sat_cons (step557 p h) (sat_cons (step542 p h) (sat_cons (step544 p h) (sat_cons (step560 p h) (sat_cons (step537 p h) (sat_cons (step538 p h) (sat_cons (step536 p h) (sat_cons (step108 p h) (sat_cons (step531 p h) (sat_cons (step834 p h) (sat_cons (step832 p h) (sat_cons (step104 p h) (sat_nil p)))))))))))))))))
def c878 : List Lit := [(87, false), (31, false)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true :=
  Snake9.LocalRup.prove_clause [c865, c867, c875, c874, c866, c792, c846, c847, c773, c876, c787, c134, c687, c649, c645, c575, c564, c581, c594, c559, c556, c536, c543, c531, c537, c107] c878 (by decide) p (sat_cons (step865 p h) (sat_cons (step867 p h) (sat_cons (step875 p h) (sat_cons (step874 p h) (sat_cons (step866 p h) (sat_cons (step792 p h) (sat_cons (step846 p h) (sat_cons (step847 p h) (sat_cons (step773 p h) (sat_cons (step876 p h) (sat_cons (step787 p h) (sat_cons (step134 p h) (sat_cons (step687 p h) (sat_cons (step649 p h) (sat_cons (step645 p h) (sat_cons (step575 p h) (sat_cons (step564 p h) (sat_cons (step581 p h) (sat_cons (step594 p h) (sat_cons (step559 p h) (sat_cons (step556 p h) (sat_cons (step536 p h) (sat_cons (step543 p h) (sat_cons (step531 p h) (sat_cons (step537 p h) (sat_cons (step107 p h) (sat_nil p)))))))))))))))))))))))))))
def c879 : List Lit := [(31, false)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true :=
  Snake9.LocalRup.prove_clause [c792, c846, c847, c773, c878, c540, c877, c661, c596, c598, c683, c850, c439, c478, c446, c841, c449, c783, c840, c708, c666, c476, c607, c848] c879 (by decide) p (sat_cons (step792 p h) (sat_cons (step846 p h) (sat_cons (step847 p h) (sat_cons (step773 p h) (sat_cons (step878 p h) (sat_cons (step540 p h) (sat_cons (step877 p h) (sat_cons (step661 p h) (sat_cons (step596 p h) (sat_cons (step598 p h) (sat_cons (step683 p h) (sat_cons (step850 p h) (sat_cons (step439 p h) (sat_cons (step478 p h) (sat_cons (step446 p h) (sat_cons (step841 p h) (sat_cons (step449 p h) (sat_cons (step783 p h) (sat_cons (step840 p h) (sat_cons (step708 p h) (sat_cons (step666 p h) (sat_cons (step476 p h) (sat_cons (step607 p h) (sat_cons (step848 p h) (sat_nil p)))))))))))))))))))))))))
def c880 : List Lit := [(1259, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true :=
  Snake9.LocalRup.prove_clause [c879, c411] c880 (by decide) p (sat_cons (step879 p h) (sat_cons (step411 p h) (sat_nil p)))
def c881 : List Lit := [(1261, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true :=
  Snake9.LocalRup.prove_clause [c880, c414] c881 (by decide) p (sat_cons (step880 p h) (sat_cons (step414 p h) (sat_nil p)))
def c882 : List Lit := [(1270, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true :=
  Snake9.LocalRup.prove_clause [c881, c839] c882 (by decide) p (sat_cons (step881 p h) (sat_cons (step839 p h) (sat_nil p)))
def c883 : List Lit := [(1296, true)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true :=
  Snake9.LocalRup.prove_clause [c882, c459] c883 (by decide) p (sat_cons (step882 p h) (sat_cons (step459 p h) (sat_nil p)))
def c884 : List Lit := [(1311, true)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true :=
  Snake9.LocalRup.prove_clause [c883, c842] c884 (by decide) p (sat_cons (step883 p h) (sat_cons (step842 p h) (sat_nil p)))
def c885 : List Lit := [(1431, false)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true :=
  Snake9.LocalRup.prove_clause [c884, c847] c885 (by decide) p (sat_cons (step884 p h) (sat_cons (step847 p h) (sat_nil p)))
def c886 : List Lit := [(80, true), (85, false), (87, true)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true :=
  Snake9.LocalRup.prove_clause [c873, c124, c88, c274, c266, c279, c267, c280, c268, c298, c270, c837] c886 (by decide) p (sat_cons (step873 p h) (sat_cons (step124 p h) (sat_cons (step88 p h) (sat_cons (step274 p h) (sat_cons (step266 p h) (sat_cons (step279 p h) (sat_cons (step267 p h) (sat_cons (step280 p h) (sat_cons (step268 p h) (sat_cons (step298 p h) (sat_cons (step270 p h) (sat_cons (step837 p h) (sat_nil p)))))))))))))
end B112E094
