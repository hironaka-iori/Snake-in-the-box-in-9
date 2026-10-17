import B112E185Part0000
namespace B112E185
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c861 : List Lit := [(882, false), (910, true)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c854, c668] c861 (by decide) p (sat_cons (step854 p h) (sat_cons (step668 p h) (sat_nil p)))
def c862 : List Lit := [(883, false), (911, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c854, c671] c862 (by decide) p (sat_cons (step854 p h) (sat_cons (step671 p h) (sat_nil p)))
def c863 : List Lit := [(926, true)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c803, c679] c863 (by decide) p (sat_cons (step803 p h) (sat_cons (step679 p h) (sat_nil p)))
def c864 : List Lit := [(88, true), (927, true)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true :=
  Snake9.LocalRup.prove_clause [c803, c680] c864 (by decide) p (sat_cons (step803 p h) (sat_cons (step680 p h) (sat_nil p)))
def c865 : List Lit := [(930, true)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true :=
  Snake9.LocalRup.prove_clause [c863, c683] c865 (by decide) p (sat_cons (step863 p h) (sat_cons (step683 p h) (sat_nil p)))
def c866 : List Lit := [(928, false), (931, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true :=
  Snake9.LocalRup.prove_clause [c863, c684] c866 (by decide) p (sat_cons (step863 p h) (sat_cons (step684 p h) (sat_nil p)))
def c867 : List Lit := [(934, true)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true :=
  Snake9.LocalRup.prove_clause [c865, c687] c867 (by decide) p (sat_cons (step865 p h) (sat_cons (step687 p h) (sat_nil p)))
def c868 : List Lit := [(923, false), (935, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true :=
  Snake9.LocalRup.prove_clause [c865, c689] c868 (by decide) p (sat_cons (step865 p h) (sat_cons (step689 p h) (sat_nil p)))
def c869 : List Lit := [(924, false), (936, true)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true :=
  Snake9.LocalRup.prove_clause [c865, c692] c869 (by decide) p (sat_cons (step865 p h) (sat_cons (step692 p h) (sat_nil p)))
def c870 : List Lit := [(955, false), (963, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true :=
  Snake9.LocalRup.prove_clause [c867, c717] c870 (by decide) p (sat_cons (step867 p h) (sat_cons (step717 p h) (sat_nil p)))
def c871 : List Lit := [(956, false), (964, true)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true :=
  Snake9.LocalRup.prove_clause [c867, c718] c871 (by decide) p (sat_cons (step867 p h) (sat_cons (step718 p h) (sat_nil p)))
def c872 : List Lit := [(963, false), (978, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true :=
  Snake9.LocalRup.prove_clause [c858, c727] c872 (by decide) p (sat_cons (step858 p h) (sat_cons (step727 p h) (sat_nil p)))
def c873 : List Lit := [(71, false), (73, false), (72, false)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true :=
  Snake9.LocalRup.prove_clause [c821, c203, c202, c199, c387, c386, c390] c873 (by decide) p (sat_cons (step821 p h) (sat_cons (step203 p h) (sat_cons (step202 p h) (sat_cons (step199 p h) (sat_cons (step387 p h) (sat_cons (step386 p h) (sat_cons (step390 p h) (sat_nil p))))))))
def c874 : List Lit := [(1434, true)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true :=
  Snake9.LocalRup.prove_clause [c772, c773, c771, c769, c770, c767, c768, c873] c874 (by decide) p (sat_cons (step772 p h) (sat_cons (step773 p h) (sat_cons (step771 p h) (sat_cons (step769 p h) (sat_cons (step770 p h) (sat_cons (step767 p h) (sat_cons (step768 p h) (sat_cons (step873 p h) (sat_nil p)))))))))
def c875 : List Lit := [(1322, true), (136, true)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true :=
  Snake9.LocalRup.prove_clause [c749, c750, c747, c748, c746, c100, c96] c875 (by decide) p (sat_cons (step749 p h) (sat_cons (step750 p h) (sat_cons (step747 p h) (sat_cons (step748 p h) (sat_cons (step746 p h) (sat_cons (step100 p h) (sat_cons (step96 p h) (sat_nil p))))))))
def c876 : List Lit := [(963, true), (943, false)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true :=
  Snake9.LocalRup.prove_clause [c294, c712, c870, c719, c713, c868, c705, c675, c677, c700, c673, c219, c217] c876 (by decide) p (sat_cons (step294 p h) (sat_cons (step712 p h) (sat_cons (step870 p h) (sat_cons (step719 p h) (sat_cons (step713 p h) (sat_cons (step868 p h) (sat_cons (step705 p h) (sat_cons (step675 p h) (sat_cons (step677 p h) (sat_cons (step700 p h) (sat_cons (step673 p h) (sat_cons (step219 p h) (sat_cons (step217 p h) (sat_nil p))))))))))))))
def c877 : List Lit := [(923, true), (80, false), (101, false)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true :=
  Snake9.LocalRup.prove_clause [c675, c677, c673, c217] c877 (by decide) p (sat_cons (step675 p h) (sat_cons (step677 p h) (sat_cons (step673 p h) (sat_cons (step217 p h) (sat_nil p)))))
def c878 : List Lit := [(12, true), (9, true), (758, true), (55, true), (7, true)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true :=
  Snake9.LocalRup.prove_clause [c257, c464, c449, c459, c452, c454, c461, c458, c451, c468, c444, c446, c441, c442, c6, c34, c9] c878 (by decide) p (sat_cons (step257 p h) (sat_cons (step464 p h) (sat_cons (step449 p h) (sat_cons (step459 p h) (sat_cons (step452 p h) (sat_cons (step454 p h) (sat_cons (step461 p h) (sat_cons (step458 p h) (sat_cons (step451 p h) (sat_cons (step468 p h) (sat_cons (step444 p h) (sat_cons (step446 p h) (sat_cons (step441 p h) (sat_cons (step442 p h) (sat_cons (step6 p h) (sat_cons (step34 p h) (sat_cons (step9 p h) (sat_nil p))))))))))))))))))
def c879 : List Lit := [(54, false), (20, false), (746, true)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true :=
  Snake9.LocalRup.prove_clause [c266, c86, c18, c24, c447, c442] c879 (by decide) p (sat_cons (step266 p h) (sat_cons (step86 p h) (sat_cons (step18 p h) (sat_cons (step24 p h) (sat_cons (step447 p h) (sat_cons (step442 p h) (sat_nil p)))))))
def c880 : List Lit := [(903, true), (74, true), (72, false), (69, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true :=
  Snake9.LocalRup.prove_clause [c288, c291, c633, c639, c857, c658, c640, c852, c635, c641, c197, c208, c873] c880 (by decide) p (sat_cons (step288 p h) (sat_cons (step291 p h) (sat_cons (step633 p h) (sat_cons (step639 p h) (sat_cons (step857 p h) (sat_cons (step658 p h) (sat_cons (step640 p h) (sat_cons (step852 p h) (sat_cons (step635 p h) (sat_cons (step641 p h) (sat_cons (step197 p h) (sat_cons (step208 p h) (sat_cons (step873 p h) (sat_nil p))))))))))))))
def c881 : List Lit := [(31, false), (19, false), (9, false), (764, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true :=
  Snake9.LocalRup.prove_clause [c79, c81, c479] c881 (by decide) p (sat_cons (step79 p h) (sat_cons (step81 p h) (sat_cons (step479 p h) (sat_nil p))))
def c882 : List Lit := [(105, true), (1480, true), (212, true), (215, true), (98, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true :=
  Snake9.LocalRup.prove_clause [c302, c303, c252, c254, c255, c779, c247, c780, c778] c882 (by decide) p (sat_cons (step302 p h) (sat_cons (step303 p h) (sat_cons (step252 p h) (sat_cons (step254 p h) (sat_cons (step255 p h) (sat_cons (step779 p h) (sat_cons (step247 p h) (sat_cons (step780 p h) (sat_cons (step778 p h) (sat_nil p))))))))))
def c883 : List Lit := [(62, false), (80, false), (101, false), (924, true)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true :=
  Snake9.LocalRup.prove_clause [c215, c216, c678, c673] c883 (by decide) p (sat_cons (step215 p h) (sat_cons (step216 p h) (sat_cons (step678 p h) (sat_cons (step673 p h) (sat_nil p)))))
def c884 : List Lit := [(902, true), (72, false), (69, true)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true :=
  Snake9.LocalRup.prove_clause [c288, c291, c638, c856, c655, c639, c852, c634, c641, c197, c208, c873] c884 (by decide) p (sat_cons (step288 p h) (sat_cons (step291 p h) (sat_cons (step638 p h) (sat_cons (step856 p h) (sat_cons (step655 p h) (sat_cons (step639 p h) (sat_cons (step852 p h) (sat_cons (step634 p h) (sat_cons (step641 p h) (sat_cons (step197 p h) (sat_cons (step208 p h) (sat_cons (step873 p h) (sat_nil p)))))))))))))
def c885 : List Lit := [(6, false), (746, true), (3, false), (54, false)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true :=
  Snake9.LocalRup.prove_clause [c15, c21, c447, c442] c885 (by decide) p (sat_cons (step15 p h) (sat_cons (step21 p h) (sat_cons (step447 p h) (sat_cons (step442 p h) (sat_nil p)))))
def c886 : List Lit := [(838, true)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true :=
  Snake9.LocalRup.prove_clause [c275, c847, c577, c570, c843, c554, c556, c534, c536, c552, c531, c528, c529, c122, c131, c109] c886 (by decide) p (sat_cons (step275 p h) (sat_cons (step847 p h) (sat_cons (step577 p h) (sat_cons (step570 p h) (sat_cons (step843 p h) (sat_cons (step554 p h) (sat_cons (step556 p h) (sat_cons (step534 p h) (sat_cons (step536 p h) (sat_cons (step552 p h) (sat_cons (step531 p h) (sat_cons (step528 p h) (sat_cons (step529 p h) (sat_cons (step122 p h) (sat_cons (step131 p h) (sat_cons (step109 p h) (sat_nil p)))))))))))))))))
def c887 : List Lit := [(745, true), (3, false), (54, false)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true :=
  Snake9.LocalRup.prove_clause [c444, c446, c442, c12] c887 (by decide) p (sat_cons (step444 p h) (sat_cons (step446 p h) (sat_cons (step442 p h) (sat_cons (step12 p h) (sat_nil p)))))
def c888 : List Lit := [(752, true), (3, false), (54, false)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true :=
  Snake9.LocalRup.prove_clause [c455, c457, c452, c450, c26] c888 (by decide) p (sat_cons (step455 p h) (sat_cons (step457 p h) (sat_cons (step452 p h) (sat_cons (step450 p h) (sat_cons (step26 p h) (sat_nil p))))))
def c889 : List Lit := [(6, false), (748, false), (788, true), (3, false), (54, false)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true :=
  Snake9.LocalRup.prove_clause [c27, c26, c885, c486, c452, c830, c458, c496, c472, c516] c889 (by decide) p (sat_cons (step27 p h) (sat_cons (step26 p h) (sat_cons (step885 p h) (sat_cons (step486 p h) (sat_cons (step452 p h) (sat_cons (step830 p h) (sat_cons (step458 p h) (sat_cons (step496 p h) (sat_cons (step472 p h) (sat_cons (step516 p h) (sat_nil p)))))))))))
def c890 : List Lit := [(746, false), (773, false), (748, false), (788, true), (752, false)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true :=
  Snake9.LocalRup.prove_clause [c263, c496, c516, c471, c472, c512, c458, c499, c452, c453, c480, c482, c54, c477, c478, c67, c68] c890 (by decide) p (sat_cons (step263 p h) (sat_cons (step496 p h) (sat_cons (step516 p h) (sat_cons (step471 p h) (sat_cons (step472 p h) (sat_cons (step512 p h) (sat_cons (step458 p h) (sat_cons (step499 p h) (sat_cons (step452 p h) (sat_cons (step453 p h) (sat_cons (step480 p h) (sat_cons (step482 p h) (sat_cons (step54 p h) (sat_cons (step477 p h) (sat_cons (step478 p h) (sat_cons (step67 p h) (sat_cons (step68 p h) (sat_nil p))))))))))))))))))
def c891 : List Lit := [(12, false), (746, true), (3, false), (54, false)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true :=
  Snake9.LocalRup.prove_clause [c23, c17, c442, c447] c891 (by decide) p (sat_cons (step23 p h) (sat_cons (step17 p h) (sat_cons (step442 p h) (sat_cons (step447 p h) (sat_nil p)))))
def c892 : List Lit := [(9, false), (116, true), (5, true), (7, true)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true :=
  Snake9.LocalRup.prove_clause [c260, c48, c49, c45, c789] c892 (by decide) p (sat_cons (step260 p h) (sat_cons (step48 p h) (sat_cons (step49 p h) (sat_cons (step45 p h) (sat_cons (step789 p h) (sat_nil p))))))
def c893 : List Lit := [(773, false), (778, true), (12, true), (55, true), (7, true), (787, true)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true :=
  Snake9.LocalRup.prove_clause [c260, c496, c499, c511, c480, c878, c477, c478, c48, c78] c893 (by decide) p (sat_cons (step260 p h) (sat_cons (step496 p h) (sat_cons (step499 p h) (sat_cons (step511 p h) (sat_cons (step480 p h) (sat_cons (step878 p h) (sat_cons (step477 p h) (sat_cons (step478 p h) (sat_cons (step48 p h) (sat_cons (step78 p h) (sat_nil p)))))))))))
def c894 : List Lit := [(20, false), (12, false), (3, false), (746, true)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true :=
  Snake9.LocalRup.prove_clause [c16, c22, c447, c442] c894 (by decide) p (sat_cons (step16 p h) (sat_cons (step22 p h) (sat_cons (step447 p h) (sat_cons (step442 p h) (sat_nil p)))))
def c895 : List Lit := [(765, true), (12, false), (3, false)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true :=
  Snake9.LocalRup.prove_clause [c265, c263, c480, c482, c477, c478, c68, c77, c67, c59] c895 (by decide) p (sat_cons (step265 p h) (sat_cons (step263 p h) (sat_cons (step480 p h) (sat_cons (step482 p h) (sat_cons (step477 p h) (sat_cons (step478 p h) (sat_cons (step68 p h) (sat_cons (step77 p h) (sat_cons (step67 p h) (sat_cons (step59 p h) (sat_nil p)))))))))))
def c896 : List Lit := [(12, false), (778, true), (746, true), (3, false)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true :=
  Snake9.LocalRup.prove_clause [c894, c895, c486, c499, c830] c896 (by decide) p (sat_cons (step894 p h) (sat_cons (step895 p h) (sat_cons (step486 p h) (sat_cons (step499 p h) (sat_cons (step830 p h) (sat_nil p))))))
def c897 : List Lit := [(21, false), (20, false), (6, false)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true :=
  Snake9.LocalRup.prove_clause [c266, c88, c85] c897 (by decide) p (sat_cons (step266 p h) (sat_cons (step88 p h) (sat_cons (step85 p h) (sat_nil p))))
def c898 : List Lit := [(768, true), (6, false)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true :=
  Snake9.LocalRup.prove_clause [c485, c486, c897] c898 (by decide) p (sat_cons (step485 p h) (sat_cons (step486 p h) (sat_cons (step897 p h) (sat_nil p))))
def c899 : List Lit := [(12, true), (757, true), (6, false)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true :=
  Snake9.LocalRup.prove_clause [c256, c463, c456, c452, c455, c467, c444, c446, c454, c441, c442, c6, c9, c3] c899 (by decide) p (sat_cons (step256 p h) (sat_cons (step463 p h) (sat_cons (step456 p h) (sat_cons (step452 p h) (sat_cons (step455 p h) (sat_cons (step467 p h) (sat_cons (step444 p h) (sat_cons (step446 p h) (sat_cons (step454 p h) (sat_cons (step441 p h) (sat_cons (step442 p h) (sat_cons (step6 p h) (sat_cons (step9 p h) (sat_cons (step3 p h) (sat_nil p)))))))))))))))
def c900 : List Lit := [(745, true), (3, true)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true :=
  Snake9.LocalRup.prove_clause [c256, c444, c446, c441, c442, c3, c4] c900 (by decide) p (sat_cons (step256 p h) (sat_cons (step444 p h) (sat_cons (step446 p h) (sat_cons (step441 p h) (sat_cons (step442 p h) (sat_cons (step3 p h) (sat_cons (step4 p h) (sat_nil p))))))))
def c901 : List Lit := [(12, false), (6, false), (3, false), (867, false), (963, false), (902, false), (876, false)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true :=
  Snake9.LocalRup.prove_clause [c743, c886, c898, c830, c26, c13, c895, c19, c608, c499, c442, c629, c447, c670, c470, c736, c507, c737, c589] c901 (by decide) p (sat_cons (step743 p h) (sat_cons (step886 p h) (sat_cons (step898 p h) (sat_cons (step830 p h) (sat_cons (step26 p h) (sat_cons (step13 p h) (sat_cons (step895 p h) (sat_cons (step19 p h) (sat_cons (step608 p h) (sat_cons (step499 p h) (sat_cons (step442 p h) (sat_cons (step629 p h) (sat_cons (step447 p h) (sat_cons (step670 p h) (sat_cons (step470 p h) (sat_cons (step736 p h) (sat_cons (step507 p h) (sat_cons (step737 p h) (sat_cons (step589 p h) (sat_nil p))))))))))))))))))))
def c902 : List Lit := [(765, true), (9, false)]
theorem step902 (p : Nat → Bool) (h : Constraints p) : clause p c902 = true :=
  Snake9.LocalRup.prove_clause [c264, c480, c482, c477, c478, c68, c78, c71] c902 (by decide) p (sat_cons (step264 p h) (sat_cons (step480 p h) (sat_cons (step482 p h) (sat_cons (step477 p h) (sat_cons (step478 p h) (sat_cons (step68 p h) (sat_cons (step78 p h) (sat_cons (step71 p h) (sat_nil p)))))))))
def c903 : List Lit := [(748, true), (3, false), (867, false), (963, false), (902, false), (876, false)]
theorem step903 (p : Nat → Bool) (h : Constraints p) : clause p c903 = true :=
  Snake9.LocalRup.prove_clause [c886, c743, c605, c626, c666, c735, c738, c592, c449, c450, c898, c830, c901, c452, c899, c455, c902, c499, c512, c507, c471, c589, c885, c737, c608, c736, c629, c670] c903 (by decide) p (sat_cons (step886 p h) (sat_cons (step743 p h) (sat_cons (step605 p h) (sat_cons (step626 p h) (sat_cons (step666 p h) (sat_cons (step735 p h) (sat_cons (step738 p h) (sat_cons (step592 p h) (sat_cons (step449 p h) (sat_cons (step450 p h) (sat_cons (step898 p h) (sat_cons (step830 p h) (sat_cons (step901 p h) (sat_cons (step452 p h) (sat_cons (step899 p h) (sat_cons (step455 p h) (sat_cons (step902 p h) (sat_cons (step499 p h) (sat_cons (step512 p h) (sat_cons (step507 p h) (sat_cons (step471 p h) (sat_cons (step589 p h) (sat_cons (step885 p h) (sat_cons (step737 p h) (sat_cons (step608 p h) (sat_cons (step736 p h) (sat_cons (step629 p h) (sat_cons (step670 p h) (sat_nil p)))))))))))))))))))))))))))))
def c904 : List Lit := [(6, false), (778, false), (3, false), (867, false), (963, false), (902, false), (876, false)]
theorem step904 (p : Nat → Bool) (h : Constraints p) : clause p c904 = true :=
  Snake9.LocalRup.prove_clause [c886, c743, c903, c605, c626, c666, c735, c738, c592, c889, c901, c608, c899, c629, c507, c670, c589, c736, c737] c904 (by decide) p (sat_cons (step886 p h) (sat_cons (step743 p h) (sat_cons (step903 p h) (sat_cons (step605 p h) (sat_cons (step626 p h) (sat_cons (step666 p h) (sat_cons (step735 p h) (sat_cons (step738 p h) (sat_cons (step592 p h) (sat_cons (step889 p h) (sat_cons (step901 p h) (sat_cons (step608 p h) (sat_cons (step899 p h) (sat_cons (step629 p h) (sat_cons (step507 p h) (sat_cons (step670 p h) (sat_cons (step589 p h) (sat_cons (step736 p h) (sat_cons (step737 p h) (sat_nil p))))))))))))))))))))
def c905 : List Lit := [(12, false), (787, true), (778, true), (752, false), (3, false)]
theorem step905 (p : Nat → Bool) (h : Constraints p) : clause p c905 = true :=
  Snake9.LocalRup.prove_clause [c895, c896, c833, c471, c511] c905 (by decide) p (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step833 p h) (sat_cons (step471 p h) (sat_cons (step511 p h) (sat_nil p))))))
def c906 : List Lit := [(777, true), (12, true), (759, true)]
theorem step906 (p : Nat → Bool) (h : Constraints p) : clause p c906 = true :=
  Snake9.LocalRup.prove_clause [c263, c452, c465, c496, c833, c830, c480, c482, c902, c898, c477, c478, c451, c68, c461, c462, c67, c469, c454, c51, c446] c906 (by decide) p (sat_cons (step263 p h) (sat_cons (step452 p h) (sat_cons (step465 p h) (sat_cons (step496 p h) (sat_cons (step833 p h) (sat_cons (step830 p h) (sat_cons (step480 p h) (sat_cons (step482 p h) (sat_cons (step902 p h) (sat_cons (step898 p h) (sat_cons (step477 p h) (sat_cons (step478 p h) (sat_cons (step451 p h) (sat_cons (step68 p h) (sat_cons (step461 p h) (sat_cons (step462 p h) (sat_cons (step67 p h) (sat_cons (step469 p h) (sat_cons (step454 p h) (sat_cons (step51 p h) (sat_cons (step446 p h) (sat_nil p))))))))))))))))))))))
def c907 : List Lit := [(787, true), (778, true), (748, false), (3, false)]
theorem step907 (p : Nat → Bool) (h : Constraints p) : clause p c907 = true :=
  Snake9.LocalRup.prove_clause [c261, c457, c836, c905, c452, c458, c906, c511, c464, c468, c459, c444, c446, c454, c441, c442, c6, c11, c57, c486, c31, c32, c830, c893] c907 (by decide) p (sat_cons (step261 p h) (sat_cons (step457 p h) (sat_cons (step836 p h) (sat_cons (step905 p h) (sat_cons (step452 p h) (sat_cons (step458 p h) (sat_cons (step906 p h) (sat_cons (step511 p h) (sat_cons (step464 p h) (sat_cons (step468 p h) (sat_cons (step459 p h) (sat_cons (step444 p h) (sat_cons (step446 p h) (sat_cons (step454 p h) (sat_cons (step441 p h) (sat_cons (step442 p h) (sat_cons (step6 p h) (sat_cons (step11 p h) (sat_cons (step57 p h) (sat_cons (step486 p h) (sat_cons (step31 p h) (sat_cons (step32 p h) (sat_cons (step830 p h) (sat_cons (step893 p h) (sat_nil p)))))))))))))))))))))))))
def c908 : List Lit := [(746, true), (5, true), (54, false), (3, false)]
theorem step908 (p : Nat → Bool) (h : Constraints p) : clause p c908 = true :=
  Snake9.LocalRup.prove_clause [c441, c445, c447, c443, c12] c908 (by decide) p (sat_cons (step441 p h) (sat_cons (step445 p h) (sat_cons (step447 p h) (sat_cons (step443 p h) (sat_cons (step12 p h) (sat_nil p))))))
def c909 : List Lit := [(750, false), (746, false), (6, true), (748, false), (788, true)]
theorem step909 (p : Nat → Bool) (h : Constraints p) : clause p c909 = true :=
  Snake9.LocalRup.prove_clause [c837, c473, c458, c472, c461, c516, c451, c833, c902] c909 (by decide) p (sat_cons (step837 p h) (sat_cons (step473 p h) (sat_cons (step458 p h) (sat_cons (step472 p h) (sat_cons (step461 p h) (sat_cons (step516 p h) (sat_cons (step451 p h) (sat_cons (step833 p h) (sat_cons (step902 p h) (sat_nil p))))))))))
def c910 : List Lit := [(748, false), (746, false), (773, false), (788, true)]
theorem step910 (p : Nat → Bool) (h : Constraints p) : clause p c910 = true :=
  Snake9.LocalRup.prove_clause [c457, c890] c910 (by decide) p (sat_cons (step457 p h) (sat_cons (step890 p h) (sat_nil p)))
def c911 : List Lit := [(750, true), (24, false), (747, true), (6, false), (9, false), (766, true), (5, true), (3, true)]
theorem step911 (p : Nat → Bool) (h : Constraints p) : clause p c911 = true :=
  Snake9.LocalRup.prove_clause [c259, c256, c38, c481, c452, c453, c63, c477, c479, c483, c44, c54, c892, c1, c39, c448, c443] c911 (by decide) p (sat_cons (step259 p h) (sat_cons (step256 p h) (sat_cons (step38 p h) (sat_cons (step481 p h) (sat_cons (step452 p h) (sat_cons (step453 p h) (sat_cons (step63 p h) (sat_cons (step477 p h) (sat_cons (step479 p h) (sat_cons (step483 p h) (sat_cons (step44 p h) (sat_cons (step54 p h) (sat_cons (step892 p h) (sat_cons (step1 p h) (sat_cons (step39 p h) (sat_cons (step448 p h) (sat_cons (step443 p h) (sat_nil p))))))))))))))))))
def c912 : List Lit := [(746, false), (5, true), (3, true), (788, true)]
theorem step912 (p : Nat → Bool) (h : Constraints p) : clause p c912 = true :=
  Snake9.LocalRup.prove_clause [c266, c86, c486, c830, c470, c508, c502, c910, c449, c450, c902, c499, c500, c512, c492, c474, c471, c828, c911, c455] c912 (by decide) p (sat_cons (step266 p h) (sat_cons (step86 p h) (sat_cons (step486 p h) (sat_cons (step830 p h) (sat_cons (step470 p h) (sat_cons (step508 p h) (sat_cons (step502 p h) (sat_cons (step910 p h) (sat_cons (step449 p h) (sat_cons (step450 p h) (sat_cons (step902 p h) (sat_cons (step499 p h) (sat_cons (step500 p h) (sat_cons (step512 p h) (sat_cons (step492 p h) (sat_cons (step474 p h) (sat_cons (step471 p h) (sat_cons (step828 p h) (sat_cons (step911 p h) (sat_cons (step455 p h) (sat_nil p)))))))))))))))))))))
def c913 : List Lit := [(748, true), (5, true), (3, true), (788, true)]
theorem step913 (p : Nat → Bool) (h : Constraints p) : clause p c913 = true :=
  Snake9.LocalRup.prove_clause [c256, c266, c259, c260, c86, c486, c830, c900, c912, c445, c443, c441, c447, c3, c5, c453, c455, c467, c508, c502, c481, c449, c450, c902, c38, c499, c500, c512, c492, c468, c828, c456, c39, c454, c48, c49, c63, c789, c479] c913 (by decide) p (sat_cons (step256 p h) (sat_cons (step266 p h) (sat_cons (step259 p h) (sat_cons (step260 p h) (sat_cons (step86 p h) (sat_cons (step486 p h) (sat_cons (step830 p h) (sat_cons (step900 p h) (sat_cons (step912 p h) (sat_cons (step445 p h) (sat_cons (step443 p h) (sat_cons (step441 p h) (sat_cons (step447 p h) (sat_cons (step3 p h) (sat_cons (step5 p h) (sat_cons (step453 p h) (sat_cons (step455 p h) (sat_cons (step467 p h) (sat_cons (step508 p h) (sat_cons (step502 p h) (sat_cons (step481 p h) (sat_cons (step449 p h) (sat_cons (step450 p h) (sat_cons (step902 p h) (sat_cons (step38 p h) (sat_cons (step499 p h) (sat_cons (step500 p h) (sat_cons (step512 p h) (sat_cons (step492 p h) (sat_cons (step468 p h) (sat_cons (step828 p h) (sat_cons (step456 p h) (sat_cons (step39 p h) (sat_cons (step454 p h) (sat_cons (step48 p h) (sat_cons (step49 p h) (sat_cons (step63 p h) (sat_cons (step789 p h) (sat_cons (step479 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c914 : List Lit := [(5, true), (3, true), (788, true)]
theorem step914 (p : Nat → Bool) (h : Constraints p) : clause p c914 = true :=
  Snake9.LocalRup.prove_clause [c266, c256, c900, c86, c486, c830, c496, c516, c469, c441, c912, c445, c447, c443, c1, c3, c5, c453, c913, c459, c458, c454, c468, c52, c512, c482, c499] c914 (by decide) p (sat_cons (step266 p h) (sat_cons (step256 p h) (sat_cons (step900 p h) (sat_cons (step86 p h) (sat_cons (step486 p h) (sat_cons (step830 p h) (sat_cons (step496 p h) (sat_cons (step516 p h) (sat_cons (step469 p h) (sat_cons (step441 p h) (sat_cons (step912 p h) (sat_cons (step445 p h) (sat_cons (step447 p h) (sat_cons (step443 p h) (sat_cons (step1 p h) (sat_cons (step3 p h) (sat_cons (step5 p h) (sat_cons (step453 p h) (sat_cons (step913 p h) (sat_cons (step459 p h) (sat_cons (step458 p h) (sat_cons (step454 p h) (sat_cons (step468 p h) (sat_cons (step52 p h) (sat_cons (step512 p h) (sat_cons (step482 p h) (sat_cons (step499 p h) (sat_nil p))))))))))))))))))))))))))))
def c915 : List Lit := [(758, false), (773, false), (869, false), (963, false), (902, false), (874, false)]
theorem step915 (p : Nat → Bool) (h : Constraints p) : clause p c915 = true :=
  Snake9.LocalRup.prove_clause [c886, c743, c263, c496, c616, c626, c666, c735, c738, c592, c512, c511, c499, c589, c480, c482, c737, c477, c478, c736, c68, c670, c65, c67, c627, c791, c619, c610] c915 (by decide) p (sat_cons (step886 p h) (sat_cons (step743 p h) (sat_cons (step263 p h) (sat_cons (step496 p h) (sat_cons (step616 p h) (sat_cons (step626 p h) (sat_cons (step666 p h) (sat_cons (step735 p h) (sat_cons (step738 p h) (sat_cons (step592 p h) (sat_cons (step512 p h) (sat_cons (step511 p h) (sat_cons (step499 p h) (sat_cons (step589 p h) (sat_cons (step480 p h) (sat_cons (step482 p h) (sat_cons (step737 p h) (sat_cons (step477 p h) (sat_cons (step478 p h) (sat_cons (step736 p h) (sat_cons (step68 p h) (sat_cons (step670 p h) (sat_cons (step65 p h) (sat_cons (step67 p h) (sat_cons (step627 p h) (sat_cons (step791 p h) (sat_cons (step619 p h) (sat_cons (step610 p h) (sat_nil p)))))))))))))))))))))))))))))
def c916 : List Lit := [(765, true), (750, true)]
theorem step916 (p : Nat → Bool) (h : Constraints p) : clause p c916 = true :=
  Snake9.LocalRup.prove_clause [c263, c453, c452, c480, c482, c477, c478, c54, c68, c67] c916 (by decide) p (sat_cons (step263 p h) (sat_cons (step453 p h) (sat_cons (step452 p h) (sat_cons (step480 p h) (sat_cons (step482 p h) (sat_cons (step477 p h) (sat_cons (step478 p h) (sat_cons (step54 p h) (sat_cons (step68 p h) (sat_cons (step67 p h) (sat_nil p)))))))))))
def c917 : List Lit := [(64, false), (871, true), (5, false), (3, true), (59, true), (69, true), (63, true)]
theorem step917 (p : Nat → Bool) (h : Constraints p) : clause p c917 = true :=
  Snake9.LocalRup.prove_clause [c285, c281, c811, c283, c185, c186, c169, c187, c604, c377, c609, c380, c164, c381, c384, c375, c372, c373, c371, c171, c176, c177] c917 (by decide) p (sat_cons (step285 p h) (sat_cons (step281 p h) (sat_cons (step811 p h) (sat_cons (step283 p h) (sat_cons (step185 p h) (sat_cons (step186 p h) (sat_cons (step169 p h) (sat_cons (step187 p h) (sat_cons (step604 p h) (sat_cons (step377 p h) (sat_cons (step609 p h) (sat_cons (step380 p h) (sat_cons (step164 p h) (sat_cons (step381 p h) (sat_cons (step384 p h) (sat_cons (step375 p h) (sat_cons (step372 p h) (sat_cons (step373 p h) (sat_cons (step371 p h) (sat_cons (step171 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_nil p)))))))))))))))))))))))
def c918 : List Lit := [(765, true), (753, true)]
theorem step918 (p : Nat → Bool) (h : Constraints p) : clause p c918 = true :=
  Snake9.LocalRup.prove_clause [c902, c916, c449, c458] c918 (by decide) p (sat_cons (step902 p h) (sat_cons (step916 p h) (sat_cons (step449 p h) (sat_cons (step458 p h) (sat_nil p)))))
def c919 : List Lit := [(963, true)]
theorem step919 (p : Nat → Bool) (h : Constraints p) : clause p c919 = true :=
  Snake9.LocalRup.prove_clause [c301, c294, c722, c876, c696, c694, c695, c241, c240, c681, c866, c688, c690, c719, c675, c677, c709, c673, c219, c705, c217, c700] c919 (by decide) p (sat_cons (step301 p h) (sat_cons (step294 p h) (sat_cons (step722 p h) (sat_cons (step876 p h) (sat_cons (step696 p h) (sat_cons (step694 p h) (sat_cons (step695 p h) (sat_cons (step241 p h) (sat_cons (step240 p h) (sat_cons (step681 p h) (sat_cons (step866 p h) (sat_cons (step688 p h) (sat_cons (step690 p h) (sat_cons (step719 p h) (sat_cons (step675 p h) (sat_cons (step677 p h) (sat_cons (step709 p h) (sat_cons (step673 p h) (sat_cons (step219 p h) (sat_cons (step705 p h) (sat_cons (step217 p h) (sat_cons (step700 p h) (sat_nil p)))))))))))))))))))))))
def c920 : List Lit := [(10, true), (746, true), (3, true), (750, true)]
theorem step920 (p : Nat → Bool) (h : Constraints p) : clause p c920 = true :=
  Snake9.LocalRup.prove_clause [c256, c262, c453, c452, c1, c61, c447, c62, c442] c920 (by decide) p (sat_cons (step256 p h) (sat_cons (step262 p h) (sat_cons (step453 p h) (sat_cons (step452 p h) (sat_cons (step1 p h) (sat_cons (step61 p h) (sat_cons (step447 p h) (sat_cons (step62 p h) (sat_cons (step442 p h) (sat_nil p))))))))))
def c921 : List Lit := [(746, true), (3, true), (750, true)]
theorem step921 (p : Nat → Bool) (h : Constraints p) : clause p c921 = true :=
  Snake9.LocalRup.prove_clause [c261, c453, c452, c920, c50, c790, c447, c57, c442, c7, c441] c921 (by decide) p (sat_cons (step261 p h) (sat_cons (step453 p h) (sat_cons (step452 p h) (sat_cons (step920 p h) (sat_cons (step50 p h) (sat_cons (step790 p h) (sat_cons (step447 p h) (sat_cons (step57 p h) (sat_cons (step442 p h) (sat_cons (step7 p h) (sat_cons (step441 p h) (sat_nil p))))))))))))
def c922 : List Lit := [(62, true), (882, true), (59, false), (874, false)]
theorem step922 (p : Nat → Bool) (h : Constraints p) : clause p c922 = true :=
  Snake9.LocalRup.prove_clause [c283, c624, c621, c610, c612, c619, c178, c627, c170, c607] c922 (by decide) p (sat_cons (step283 p h) (sat_cons (step624 p h) (sat_cons (step621 p h) (sat_cons (step610 p h) (sat_cons (step612 p h) (sat_cons (step619 p h) (sat_cons (step178 p h) (sat_cons (step627 p h) (sat_cons (step170 p h) (sat_cons (step607 p h) (sat_nil p)))))))))))
def c923 : List Lit := [(54, false), (59, false), (3, true)]
theorem step923 (p : Nat → Bool) (h : Constraints p) : clause p c923 = true :=
  Snake9.LocalRup.prove_clause [c281, c164, c165, c795] c923 (by decide) p (sat_cons (step281 p h) (sat_cons (step164 p h) (sat_cons (step165 p h) (sat_cons (step795 p h) (sat_nil p)))))
def c924 : List Lit := [(747, false), (759, true), (789, true), (70, false), (20, true), (765, false)]
theorem step924 (p : Nat → Bool) (h : Constraints p) : clause p c924 = true :=
  Snake9.LocalRup.prove_clause [c288, c198, c474, c475, c513, c457, c500, c450, c831, c89, c487] c924 (by decide) p (sat_cons (step288 p h) (sat_cons (step198 p h) (sat_cons (step474 p h) (sat_cons (step475 p h) (sat_cons (step513 p h) (sat_cons (step457 p h) (sat_cons (step500 p h) (sat_cons (step450 p h) (sat_cons (step831 p h) (sat_cons (step89 p h) (sat_cons (step487 p h) (sat_nil p))))))))))))
end B112E185
