import B112E146Inputs
namespace B112E146
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c817 : List Lit := [(63, true)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true :=
  Snake9.LocalRup.prove_clause [c259, c258] c817 (by decide) p (sat_cons (step259 p h) (sat_cons (step258 p h) (sat_nil p)))
def c818 : List Lit := [(86, false)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true :=
  Snake9.LocalRup.prove_clause [c348, c287] c818 (by decide) p (sat_cons (step348 p h) (sat_cons (step287 p h) (sat_nil p)))
def c819 : List Lit := [(97, false)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true :=
  Snake9.LocalRup.prove_clause [c353, c307] c819 (by decide) p (sat_cons (step353 p h) (sat_cons (step307 p h) (sat_nil p)))
def c820 : List Lit := [(450, false)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true :=
  Snake9.LocalRup.prove_clause [c463, c460] c820 (by decide) p (sat_cons (step463 p h) (sat_cons (step460 p h) (sat_nil p)))
def c821 : List Lit := [(338, false)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true :=
  Snake9.LocalRup.prove_clause [c463, c462] c821 (by decide) p (sat_cons (step463 p h) (sat_cons (step462 p h) (sat_nil p)))
def c822 : List Lit := [(448, false)]
theorem step822 (p : Nat → Bool) (h : Constraints p) : clause p c822 = true :=
  Snake9.LocalRup.prove_clause [c820, c456] c822 (by decide) p (sat_cons (step820 p h) (sat_cons (step456 p h) (sat_nil p)))
def c823 : List Lit := [(392, false)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true :=
  Snake9.LocalRup.prove_clause [c820, c459] c823 (by decide) p (sat_cons (step820 p h) (sat_cons (step459 p h) (sat_nil p)))
def c824 : List Lit := [(336, false)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true :=
  Snake9.LocalRup.prove_clause [c821, c417] c824 (by decide) p (sat_cons (step821 p h) (sat_cons (step417 p h) (sat_nil p)))
def c825 : List Lit := [(282, false)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true :=
  Snake9.LocalRup.prove_clause [c821, c420] c825 (by decide) p (sat_cons (step821 p h) (sat_cons (step420 p h) (sat_nil p)))
def c826 : List Lit := [(418, false)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true :=
  Snake9.LocalRup.prove_clause [c822, c454] c826 (by decide) p (sat_cons (step822 p h) (sat_cons (step454 p h) (sat_nil p)))
def c827 : List Lit := [(364, false)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true :=
  Snake9.LocalRup.prove_clause [c823, c437] c827 (by decide) p (sat_cons (step823 p h) (sat_cons (step437 p h) (sat_nil p)))
def c828 : List Lit := [(334, false)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true :=
  Snake9.LocalRup.prove_clause [c824, c412] c828 (by decide) p (sat_cons (step824 p h) (sat_cons (step412 p h) (sat_nil p)))
def c829 : List Lit := [(308, false)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true :=
  Snake9.LocalRup.prove_clause [c824, c415] c829 (by decide) p (sat_cons (step824 p h) (sat_cons (step415 p h) (sat_nil p)))
def c830 : List Lit := [(254, false)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true :=
  Snake9.LocalRup.prove_clause [c825, c380] c830 (by decide) p (sat_cons (step825 p h) (sat_cons (step380 p h) (sat_nil p)))
def c831 : List Lit := [(404, false)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true :=
  Snake9.LocalRup.prove_clause [c826, c452] c831 (by decide) p (sat_cons (step826 p h) (sat_cons (step452 p h) (sat_nil p)))
def c832 : List Lit := [(350, false)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true :=
  Snake9.LocalRup.prove_clause [c827, c435] c832 (by decide) p (sat_cons (step827 p h) (sat_cons (step435 p h) (sat_nil p)))
def c833 : List Lit := [(320, false)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true :=
  Snake9.LocalRup.prove_clause [c828, c410] c833 (by decide) p (sat_cons (step828 p h) (sat_cons (step410 p h) (sat_nil p)))
def c834 : List Lit := [(240, false)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true :=
  Snake9.LocalRup.prove_clause [c830, c372] c834 (by decide) p (sat_cons (step830 p h) (sat_cons (step372 p h) (sat_nil p)))
def c835 : List Lit := [(342, false)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true :=
  Snake9.LocalRup.prove_clause [c832, c433] c835 (by decide) p (sat_cons (step832 p h) (sat_cons (step433 p h) (sat_nil p)))
def c836 : List Lit := [(312, false)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true :=
  Snake9.LocalRup.prove_clause [c833, c404] c836 (by decide) p (sat_cons (step833 p h) (sat_cons (step404 p h) (sat_nil p)))
def c837 : List Lit := [(310, false)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.LocalRup.prove_clause [c836, c399] c837 (by decide) p (sat_cons (step836 p h) (sat_cons (step399 p h) (sat_nil p)))
def c838 : List Lit := [(1542, true)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c818, c728] c838 (by decide) p (sat_cons (step818 p h) (sat_cons (step728 p h) (sat_nil p)))
def c839 : List Lit := [(1540, false), (1543, true)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c818, c729] c839 (by decide) p (sat_cons (step818 p h) (sat_cons (step729 p h) (sat_nil p)))
def c840 : List Lit := [(1541, false), (1544, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c818, c730] c840 (by decide) p (sat_cons (step818 p h) (sat_cons (step730 p h) (sat_nil p)))
def c841 : List Lit := [(1547, true)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c819, c733] c841 (by decide) p (sat_cons (step819 p h) (sat_cons (step733 p h) (sat_nil p)))
def c842 : List Lit := [(95, true), (1548, true)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c819, c734] c842 (by decide) p (sat_cons (step819 p h) (sat_cons (step734 p h) (sat_nil p)))
def c843 : List Lit := [(1549, true)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c841, c735] c843 (by decide) p (sat_cons (step841 p h) (sat_cons (step735 p h) (sat_nil p)))
def c844 : List Lit := [(1545, false), (1550, true)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c841, c737] c844 (by decide) p (sat_cons (step841 p h) (sat_cons (step737 p h) (sat_nil p)))
def c845 : List Lit := [(1554, true)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c838, c843, c739] c845 (by decide) p (sat_cons (step838 p h) (sat_cons (step843 p h) (sat_cons (step739 p h) (sat_nil p))))
def c846 : List Lit := [(1550, false), (1555, true)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c838, c740] c846 (by decide) p (sat_cons (step838 p h) (sat_cons (step740 p h) (sat_nil p)))
def c847 : List Lit := [(1543, false), (1555, true)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c843, c741] c847 (by decide) p (sat_cons (step843 p h) (sat_cons (step741 p h) (sat_nil p)))
def c848 : List Lit := [(1544, false), (1556, true)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c843, c744] c848 (by decide) p (sat_cons (step843 p h) (sat_cons (step744 p h) (sat_nil p)))
def c849 : List Lit := [(1576, false), (1586, true)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c845, c764] c849 (by decide) p (sat_cons (step845 p h) (sat_cons (step764 p h) (sat_nil p)))
def c850 : List Lit := [(1577, false), (1587, true)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c845, c765] c850 (by decide) p (sat_cons (step845 p h) (sat_cons (step765 p h) (sat_nil p)))
def c851 : List Lit := [(1376, true)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c323, c512, c513, c98, c99, c806] c851 (by decide) p (sat_cons (step323 p h) (sat_cons (step512 p h) (sat_cons (step513 p h) (sat_cons (step98 p h) (sat_cons (step99 p h) (sat_cons (step806 p h) (sat_nil p)))))))
def c852 : List Lit := [(1517, true)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c343, c704, c706, c699, c686, c697, c683, c684, c275, c277] c852 (by decide) p (sat_cons (step343 p h) (sat_cons (step704 p h) (sat_cons (step706 p h) (sat_cons (step699 p h) (sat_cons (step686 p h) (sat_cons (step697 p h) (sat_cons (step683 p h) (sat_cons (step684 p h) (sat_cons (step275 p h) (sat_cons (step277 p h) (sat_nil p)))))))))))
def c853 : List Lit := [(1525, true)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c852, c713] c853 (by decide) p (sat_cons (step852 p h) (sat_cons (step713 p h) (sat_nil p)))
def c854 : List Lit := [(77, false), (1488, true)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c343, c669, c668, c276, c261] c854 (by decide) p (sat_cons (step343 p h) (sat_cons (step669 p h) (sat_cons (step668 p h) (sat_cons (step276 p h) (sat_cons (step261 p h) (sat_nil p))))))
def c855 : List Lit := [(1513, true), (1526, true), (1375, true)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.LocalRup.prove_clause [c852, c344, c345, c714, c709, c716, c673, c670, c854, c683, c689, c681, c687, c685, c675, c662, c659, c669, c699, c701, c697, c693, c694, c283, c278, c265, c273, c279, c511, c111] c855 (by decide) p (sat_cons (step852 p h) (sat_cons (step344 p h) (sat_cons (step345 p h) (sat_cons (step714 p h) (sat_cons (step709 p h) (sat_cons (step716 p h) (sat_cons (step673 p h) (sat_cons (step670 p h) (sat_cons (step854 p h) (sat_cons (step683 p h) (sat_cons (step689 p h) (sat_cons (step681 p h) (sat_cons (step687 p h) (sat_cons (step685 p h) (sat_cons (step675 p h) (sat_cons (step662 p h) (sat_cons (step659 p h) (sat_cons (step669 p h) (sat_cons (step699 p h) (sat_cons (step701 p h) (sat_cons (step697 p h) (sat_cons (step693 p h) (sat_cons (step694 p h) (sat_cons (step283 p h) (sat_cons (step278 p h) (sat_cons (step265 p h) (sat_cons (step273 p h) (sat_cons (step279 p h) (sat_cons (step511 p h) (sat_cons (step111 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c856 : List Lit := [(1526, true), (1375, true)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c852, c714, c716, c673, c670, c854, c683, c686, c855, c707] c856 (by decide) p (sat_cons (step852 p h) (sat_cons (step714 p h) (sat_cons (step716 p h) (sat_cons (step673 p h) (sat_cons (step670 p h) (sat_cons (step854 p h) (sat_cons (step683 p h) (sat_cons (step686 p h) (sat_cons (step855 p h) (sat_cons (step707 p h) (sat_nil p)))))))))))
def c857 : List Lit := [(21, false), (81, false), (60, false)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c322, c96, c111] c857 (by decide) p (sat_cons (step322 p h) (sat_cons (step96 p h) (sat_cons (step111 p h) (sat_nil p))))
def c858 : List Lit := [(81, false), (60, false), (67, false), (1384, true)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c851, c345, c857, c509, c516, c521, c506, c263, c108, c279] c858 (by decide) p (sat_cons (step851 p h) (sat_cons (step345 p h) (sat_cons (step857 p h) (sat_cons (step509 p h) (sat_cons (step516 p h) (sat_cons (step521 p h) (sat_cons (step506 p h) (sat_cons (step263 p h) (sat_cons (step108 p h) (sat_cons (step279 p h) (sat_nil p)))))))))))
def c859 : List Lit := [(1379, true)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c851, c322, c515, c516, c509, c510, c97, c94, c514, c95] c859 (by decide) p (sat_cons (step851 p h) (sat_cons (step322 p h) (sat_cons (step515 p h) (sat_cons (step516 p h) (sat_cons (step509 p h) (sat_cons (step510 p h) (sat_cons (step97 p h) (sat_cons (step94 p h) (sat_cons (step514 p h) (sat_cons (step95 p h) (sat_nil p)))))))))))
def c860 : List Lit := [(1383, true)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c859, c519] c860 (by decide) p (sat_cons (step859 p h) (sat_cons (step519 p h) (sat_nil p)))
def c861 : List Lit := [(1356, true), (20, false), (1369, true)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c320, c502, c501, c475, c476, c80, c17, c19] c861 (by decide) p (sat_cons (step320 p h) (sat_cons (step502 p h) (sat_cons (step501 p h) (sat_cons (step475 p h) (sat_cons (step476 p h) (sat_cons (step80 p h) (sat_cons (step17 p h) (sat_cons (step19 p h) (sat_nil p)))))))))
def c862 : List Lit := [(12, false), (16, true), (1371, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c321, c504, c501, c506, c45, c22] c862 (by decide) p (sat_cons (step321 p h) (sat_cons (step504 p h) (sat_cons (step501 p h) (sat_cons (step506 p h) (sat_cons (step45 p h) (sat_cons (step22 p h) (sat_nil p)))))))
def c863 : List Lit := [(1408, true), (36, false), (3, false)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c551, c552, c158] c863 (by decide) p (sat_cons (step551 p h) (sat_cons (step552 p h) (sat_cons (step158 p h) (sat_nil p))))
def c864 : List Lit := [(6, true), (1360, true), (12, true), (16, true)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true :=
  Snake9.LocalRup.prove_clause [c320, c475, c484, c473, c474, c482, c477, c19, c799, c18] c864 (by decide) p (sat_cons (step320 p h) (sat_cons (step475 p h) (sat_cons (step484 p h) (sat_cons (step473 p h) (sat_cons (step474 p h) (sat_cons (step482 p h) (sat_cons (step477 p h) (sat_cons (step19 p h) (sat_cons (step799 p h) (sat_cons (step18 p h) (sat_nil p)))))))))))
def c865 : List Lit := [(1359, true), (12, true), (16, true)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true :=
  Snake9.LocalRup.prove_clause [c320, c475, c479, c481, c477, c472, c19, c799, c18] c865 (by decide) p (sat_cons (step320 p h) (sat_cons (step475 p h) (sat_cons (step479 p h) (sat_cons (step481 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step19 p h) (sat_cons (step799 p h) (sat_cons (step18 p h) (sat_nil p))))))))))
def c866 : List Lit := [(10, false), (9, false), (16, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true :=
  Snake9.LocalRup.prove_clause [c320, c19, c799, c18] c866 (by decide) p (sat_cons (step320 p h) (sat_cons (step19 p h) (sat_cons (step799 p h) (sat_cons (step18 p h) (sat_nil p)))))
def c867 : List Lit := [(1427, true), (30, false)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true :=
  Snake9.LocalRup.prove_clause [c329, c588, c590, c585, c583, c195, c124] c867 (by decide) p (sat_cons (step329 p h) (sat_cons (step588 p h) (sat_cons (step590 p h) (sat_cons (step585 p h) (sat_cons (step583 p h) (sat_cons (step195 p h) (sat_cons (step124 p h) (sat_nil p))))))))
def c868 : List Lit := [(1576, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true :=
  Snake9.LocalRup.prove_clause [c357, c356, c355, c760, c761, c758, c759, c752, c754, c757, c756, c750, c748, c315, c314, c313, c309] c868 (by decide) p (sat_cons (step357 p h) (sat_cons (step356 p h) (sat_cons (step355 p h) (sat_cons (step760 p h) (sat_cons (step761 p h) (sat_cons (step758 p h) (sat_cons (step759 p h) (sat_cons (step752 p h) (sat_cons (step754 p h) (sat_cons (step757 p h) (sat_cons (step756 p h) (sat_cons (step750 p h) (sat_cons (step748 p h) (sat_cons (step315 p h) (sat_cons (step314 p h) (sat_cons (step313 p h) (sat_cons (step309 p h) (sat_nil p))))))))))))))))))
def c869 : List Lit := [(1586, true)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true :=
  Snake9.LocalRup.prove_clause [c868, c849] c869 (by decide) p (sat_cons (step868 p h) (sat_cons (step849 p h) (sat_nil p)))
def c870 : List Lit := [(1602, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true :=
  Snake9.LocalRup.prove_clause [c869, c853, c773] c870 (by decide) p (sat_cons (step869 p h) (sat_cons (step853 p h) (sat_cons (step773 p h) (sat_nil p))))
def c871 : List Lit := [(1476, false)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true :=
  Snake9.LocalRup.prove_clause [c870, c795, c794] c871 (by decide) p (sat_cons (step870 p h) (sat_cons (step795 p h) (sat_cons (step794 p h) (sat_nil p))))
def c872 : List Lit := [(1351, false), (1393, true), (16, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true :=
  Snake9.LocalRup.prove_clause [c860, c321, c859, c534, c491, c865, c22, c23, c862, c800, c521, c472, c530, c480, c490] c872 (by decide) p (sat_cons (step860 p h) (sat_cons (step321 p h) (sat_cons (step859 p h) (sat_cons (step534 p h) (sat_cons (step491 p h) (sat_cons (step865 p h) (sat_cons (step22 p h) (sat_cons (step23 p h) (sat_cons (step862 p h) (sat_cons (step800 p h) (sat_cons (step521 p h) (sat_cons (step472 p h) (sat_cons (step530 p h) (sat_cons (step480 p h) (sat_cons (step490 p h) (sat_nil p))))))))))))))))
def c873 : List Lit := [(1359, true), (2, false), (125, true), (16, true)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true :=
  Snake9.LocalRup.prove_clause [c321, c320, c865, c22, c23, c800, c30, c472, c21, c481, c18, c476] c873 (by decide) p (sat_cons (step321 p h) (sat_cons (step320 p h) (sat_cons (step865 p h) (sat_cons (step22 p h) (sat_cons (step23 p h) (sat_cons (step800 p h) (sat_cons (step30 p h) (sat_cons (step472 p h) (sat_cons (step21 p h) (sat_cons (step481 p h) (sat_cons (step18 p h) (sat_cons (step476 p h) (sat_nil p)))))))))))))
def c874 : List Lit := [(1427, true), (1556, true), (34, false), (36, false)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true :=
  Snake9.LocalRup.prove_clause [c331, c330, c329, c463, c818, c351, c350, c588, c590, c585, c586, c582, c583, c202, c197, c195, c188, c189, c127, c204, c396, c398, c402, c409, c411, c416, c461, c455, c453, c450, c444, c445, c442, c443, c439, c441, c440, c438, c292, c288, c297, c732, c298, c844, c295, c742, c725, c839] c874 (by decide) p (sat_cons (step331 p h) (sat_cons (step330 p h) (sat_cons (step329 p h) (sat_cons (step463 p h) (sat_cons (step818 p h) (sat_cons (step351 p h) (sat_cons (step350 p h) (sat_cons (step588 p h) (sat_cons (step590 p h) (sat_cons (step585 p h) (sat_cons (step586 p h) (sat_cons (step582 p h) (sat_cons (step583 p h) (sat_cons (step202 p h) (sat_cons (step197 p h) (sat_cons (step195 p h) (sat_cons (step188 p h) (sat_cons (step189 p h) (sat_cons (step127 p h) (sat_cons (step204 p h) (sat_cons (step396 p h) (sat_cons (step398 p h) (sat_cons (step402 p h) (sat_cons (step409 p h) (sat_cons (step411 p h) (sat_cons (step416 p h) (sat_cons (step461 p h) (sat_cons (step455 p h) (sat_cons (step453 p h) (sat_cons (step450 p h) (sat_cons (step444 p h) (sat_cons (step445 p h) (sat_cons (step442 p h) (sat_cons (step443 p h) (sat_cons (step439 p h) (sat_cons (step441 p h) (sat_cons (step440 p h) (sat_cons (step438 p h) (sat_cons (step292 p h) (sat_cons (step288 p h) (sat_cons (step297 p h) (sat_cons (step732 p h) (sat_cons (step298 p h) (sat_cons (step844 p h) (sat_cons (step295 p h) (sat_cons (step742 p h) (sat_cons (step725 p h) (sat_cons (step839 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c875 : List Lit := [(417, true), (92, false), (98, false), (39, true), (36, false)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true :=
  Snake9.LocalRup.prove_clause [c350, c449, c450, c448, c444, c447, c442, c443, c441, c440, c292, c299, c294, c301, c289] c875 (by decide) p (sat_cons (step350 p h) (sat_cons (step449 p h) (sat_cons (step450 p h) (sat_cons (step448 p h) (sat_cons (step444 p h) (sat_cons (step447 p h) (sat_cons (step442 p h) (sat_cons (step443 p h) (sat_cons (step441 p h) (sat_cons (step440 p h) (sat_cons (step292 p h) (sat_cons (step299 p h) (sat_cons (step294 p h) (sat_cons (step301 p h) (sat_cons (step289 p h) (sat_nil p))))))))))))))))
def c876 : List Lit := [(35, true), (33, true), (1435, false), (1454, true), (43, true), (1411, false), (305, true), (39, true)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true :=
  Snake9.LocalRup.prove_clause [c330, c329, c586, c391, c387, c386, c390, c389, c388, c200, c553, c196, c564, c190, c567, c194, c631, c584, c618, c594] c876 (by decide) p (sat_cons (step330 p h) (sat_cons (step329 p h) (sat_cons (step586 p h) (sat_cons (step391 p h) (sat_cons (step387 p h) (sat_cons (step386 p h) (sat_cons (step390 p h) (sat_cons (step389 p h) (sat_cons (step388 p h) (sat_cons (step200 p h) (sat_cons (step553 p h) (sat_cons (step196 p h) (sat_cons (step564 p h) (sat_cons (step190 p h) (sat_cons (step567 p h) (sat_cons (step194 p h) (sat_cons (step631 p h) (sat_cons (step584 p h) (sat_cons (step618 p h) (sat_cons (step594 p h) (sat_nil p)))))))))))))))))))))
def c877 : List Lit := [(3, true), (121, true), (1350, true)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true :=
  Snake9.LocalRup.prove_clause [c318, c466, c15, c10] c877 (by decide) p (sat_cons (step318 p h) (sat_cons (step466 p h) (sat_cons (step15 p h) (sat_cons (step10 p h) (sat_nil p)))))
def c878 : List Lit := [(53, false), (1370, true), (16, false), (3, false), (52, false), (35, false)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true :=
  Snake9.LocalRup.prove_clause [c227, c67, c503] c878 (by decide) p (sat_cons (step227 p h) (sat_cons (step67 p h) (sat_cons (step503 p h) (sat_nil p))))
def c879 : List Lit := [(18, false), (1357, true), (16, false), (3, false)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true :=
  Snake9.LocalRup.prove_clause [c57, c61, c477] c879 (by decide) p (sat_cons (step57 p h) (sat_cons (step61 p h) (sat_cons (step477 p h) (sat_nil p))))
def c880 : List Lit := [(91, true), (1556, true), (89, true), (206, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true :=
  Snake9.LocalRup.prove_clause [c350, c732, c298, c844, c295, c742, c725, c839] c880 (by decide) p (sat_cons (step350 p h) (sat_cons (step732 p h) (sat_cons (step298 p h) (sat_cons (step844 p h) (sat_cons (step295 p h) (sat_cons (step742 p h) (sat_cons (step725 p h) (sat_cons (step839 p h) (sat_nil p)))))))))
end B112E146
