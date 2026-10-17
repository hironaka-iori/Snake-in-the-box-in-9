import B112E120Inputs
namespace B112E120
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c838 : List Lit := [(49, false), (44, false), (47, false)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c3, c79] c838 (by decide) p (sat_cons (step3 p h) (sat_cons (step79 p h) (sat_nil p)))
def c839 : List Lit := [(49, false), (44, false), (48, false)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c3, c80] c839 (by decide) p (sat_cons (step3 p h) (sat_cons (step80 p h) (sat_nil p)))
def c840 : List Lit := [(49, false), (44, false), (59, false)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c3, c81] c840 (by decide) p (sat_cons (step3 p h) (sat_cons (step81 p h) (sat_nil p)))
def c841 : List Lit := [(49, false), (47, false), (48, false)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c3, c82] c841 (by decide) p (sat_cons (step3 p h) (sat_cons (step82 p h) (sat_nil p)))
def c842 : List Lit := [(49, false), (47, false), (59, false)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c3, c83] c842 (by decide) p (sat_cons (step3 p h) (sat_cons (step83 p h) (sat_nil p)))
def c843 : List Lit := [(49, false), (48, false), (59, false)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c3, c84] c843 (by decide) p (sat_cons (step3 p h) (sat_cons (step84 p h) (sat_nil p)))
def c844 : List Lit := [(8, false)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c330, c12] c844 (by decide) p (sat_cons (step330 p h) (sat_cons (step12 p h) (sat_nil p)))
def c845 : List Lit := [(63, false)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c350, c110] c845 (by decide) p (sat_cons (step350 p h) (sat_cons (step110 p h) (sat_nil p)))
def c846 : List Lit := [(458, false)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c467, c464] c846 (by decide) p (sat_cons (step467 p h) (sat_cons (step464 p h) (sat_nil p)))
def c847 : List Lit := [(344, false)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c467, c466] c847 (by decide) p (sat_cons (step467 p h) (sat_cons (step466 p h) (sat_nil p)))
def c848 : List Lit := [(456, false)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c846, c460] c848 (by decide) p (sat_cons (step846 p h) (sat_cons (step460 p h) (sat_nil p)))
def c849 : List Lit := [(400, false)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c846, c463] c849 (by decide) p (sat_cons (step846 p h) (sat_cons (step463 p h) (sat_nil p)))
def c850 : List Lit := [(342, false)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c847, c396] c850 (by decide) p (sat_cons (step847 p h) (sat_cons (step396 p h) (sat_nil p)))
def c851 : List Lit := [(454, false)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c848, c456] c851 (by decide) p (sat_cons (step848 p h) (sat_cons (step456 p h) (sat_nil p)))
def c852 : List Lit := [(370, false)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c849, c425] c852 (by decide) p (sat_cons (step849 p h) (sat_cons (step425 p h) (sat_nil p)))
def c853 : List Lit := [(312, false)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c850, c394] c853 (by decide) p (sat_cons (step850 p h) (sat_cons (step394 p h) (sat_nil p)))
def c854 : List Lit := [(438, false)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c851, c454] c854 (by decide) p (sat_cons (step851 p h) (sat_cons (step454 p h) (sat_nil p)))
def c855 : List Lit := [(368, false)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.LocalRup.prove_clause [c852, c414] c855 (by decide) p (sat_cons (step852 p h) (sat_cons (step414 p h) (sat_nil p)))
def c856 : List Lit := [(436, false)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c854, c445] c856 (by decide) p (sat_cons (step854 p h) (sat_cons (step445 p h) (sat_nil p)))
def c857 : List Lit := [(360, false)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c855, c412] c857 (by decide) p (sat_cons (step855 p h) (sat_cons (step412 p h) (sat_nil p)))
def c858 : List Lit := [(434, false)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c856, c443] c858 (by decide) p (sat_cons (step856 p h) (sat_cons (step443 p h) (sat_nil p)))
def c859 : List Lit := [(358, false)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c857, c407] c859 (by decide) p (sat_cons (step857 p h) (sat_cons (step407 p h) (sat_nil p)))
def c860 : List Lit := [(1406, true)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c844, c471] c860 (by decide) p (sat_cons (step844 p h) (sat_cons (step471 p h) (sat_nil p)))
def c861 : List Lit := [(10, true), (1407, true)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c844, c472] c861 (by decide) p (sat_cons (step844 p h) (sat_cons (step472 p h) (sat_nil p)))
def c862 : List Lit := [(1410, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c860, c476] c862 (by decide) p (sat_cons (step860 p h) (sat_cons (step476 p h) (sat_nil p)))
def c863 : List Lit := [(1408, false), (1411, true)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c860, c477] c863 (by decide) p (sat_cons (step860 p h) (sat_cons (step477 p h) (sat_nil p)))
def c864 : List Lit := [(1409, false), (1412, true)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true :=
  Snake9.LocalRup.prove_clause [c860, c478] c864 (by decide) p (sat_cons (step860 p h) (sat_cons (step478 p h) (sat_nil p)))
def c865 : List Lit := [(1414, true)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true :=
  Snake9.LocalRup.prove_clause [c862, c481] c865 (by decide) p (sat_cons (step862 p h) (sat_cons (step481 p h) (sat_nil p)))
def c866 : List Lit := [(1403, false), (1415, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true :=
  Snake9.LocalRup.prove_clause [c862, c484] c866 (by decide) p (sat_cons (step862 p h) (sat_cons (step484 p h) (sat_nil p)))
def c867 : List Lit := [(1441, true)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true :=
  Snake9.LocalRup.prove_clause [c865, c513] c867 (by decide) p (sat_cons (step865 p h) (sat_cons (step513 p h) (sat_nil p)))
def c868 : List Lit := [(1434, false), (1442, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true :=
  Snake9.LocalRup.prove_clause [c865, c514] c868 (by decide) p (sat_cons (step865 p h) (sat_cons (step514 p h) (sat_nil p)))
def c869 : List Lit := [(1435, false), (1443, true)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true :=
  Snake9.LocalRup.prove_clause [c865, c515] c869 (by decide) p (sat_cons (step865 p h) (sat_cons (step515 p h) (sat_nil p)))
def c870 : List Lit := [(1436, false), (1444, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true :=
  Snake9.LocalRup.prove_clause [c865, c516] c870 (by decide) p (sat_cons (step865 p h) (sat_cons (step516 p h) (sat_nil p)))
def c871 : List Lit := [(1437, false), (1445, true)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true :=
  Snake9.LocalRup.prove_clause [c865, c517] c871 (by decide) p (sat_cons (step865 p h) (sat_cons (step517 p h) (sat_nil p)))
def c872 : List Lit := [(1497, false), (1512, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true :=
  Snake9.LocalRup.prove_clause [c867, c591] c872 (by decide) p (sat_cons (step867 p h) (sat_cons (step591 p h) (sat_nil p)))
def c873 : List Lit := [(1526, true)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true :=
  Snake9.LocalRup.prove_clause [c845, c607] c873 (by decide) p (sat_cons (step845 p h) (sat_cons (step607 p h) (sat_nil p)))
def c874 : List Lit := [(62, true), (1527, true)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true :=
  Snake9.LocalRup.prove_clause [c845, c608] c874 (by decide) p (sat_cons (step845 p h) (sat_cons (step608 p h) (sat_nil p)))
def c875 : List Lit := [(1528, true)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true :=
  Snake9.LocalRup.prove_clause [c873, c609] c875 (by decide) p (sat_cons (step873 p h) (sat_cons (step609 p h) (sat_nil p)))
def c876 : List Lit := [(59, true), (1529, true)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true :=
  Snake9.LocalRup.prove_clause [c873, c611] c876 (by decide) p (sat_cons (step873 p h) (sat_cons (step611 p h) (sat_nil p)))
def c877 : List Lit := [(1539, true)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true :=
  Snake9.LocalRup.prove_clause [c875, c627] c877 (by decide) p (sat_cons (step875 p h) (sat_cons (step627 p h) (sat_nil p)))
def c878 : List Lit := [(1535, false), (1540, true)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true :=
  Snake9.LocalRup.prove_clause [c875, c628] c878 (by decide) p (sat_cons (step875 p h) (sat_cons (step628 p h) (sat_nil p)))
def c879 : List Lit := [(1536, false), (1541, true)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true :=
  Snake9.LocalRup.prove_clause [c875, c629] c879 (by decide) p (sat_cons (step875 p h) (sat_cons (step629 p h) (sat_nil p)))
def c880 : List Lit := [(1560, false), (1568, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true :=
  Snake9.LocalRup.prove_clause [c877, c677] c880 (by decide) p (sat_cons (step877 p h) (sat_cons (step677 p h) (sat_nil p)))
def c881 : List Lit := [(1561, false), (1569, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true :=
  Snake9.LocalRup.prove_clause [c877, c678] c881 (by decide) p (sat_cons (step877 p h) (sat_cons (step678 p h) (sat_nil p)))
def c882 : List Lit := [(1562, false), (1570, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true :=
  Snake9.LocalRup.prove_clause [c877, c679] c882 (by decide) p (sat_cons (step877 p h) (sat_cons (step679 p h) (sat_nil p)))
def c883 : List Lit := [(1563, false), (1571, true)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true :=
  Snake9.LocalRup.prove_clause [c877, c680] c883 (by decide) p (sat_cons (step877 p h) (sat_cons (step680 p h) (sat_nil p)))
def c884 : List Lit := [(46, false), (55, false), (53, false)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true :=
  Snake9.LocalRup.prove_clause [c347, c91, c93] c884 (by decide) p (sat_cons (step347 p h) (sat_cons (step91 p h) (sat_cons (step93 p h) (sat_nil p))))
def c885 : List Lit := [(1488, true)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true :=
  Snake9.LocalRup.prove_clause [c568, c571, c561, c563, c552, c559, c555, c884] c885 (by decide) p (sat_cons (step568 p h) (sat_cons (step571 p h) (sat_cons (step561 p h) (sat_cons (step563 p h) (sat_cons (step552 p h) (sat_cons (step559 p h) (sat_cons (step555 p h) (sat_cons (step884 p h) (sat_nil p)))))))))
def c886 : List Lit := [(1464, true)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true :=
  Snake9.LocalRup.prove_clause [c340, c536, c538, c534, c531, c532, c61, c65] c886 (by decide) p (sat_cons (step340 p h) (sat_cons (step536 p h) (sat_cons (step538 p h) (sat_cons (step534 p h) (sat_cons (step531 p h) (sat_cons (step532 p h) (sat_cons (step61 p h) (sat_cons (step65 p h) (sat_nil p)))))))))
def c887 : List Lit := [(1468, true)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true :=
  Snake9.LocalRup.prove_clause [c886, c541] c887 (by decide) p (sat_cons (step886 p h) (sat_cons (step541 p h) (sat_nil p)))
def c888 : List Lit := [(1496, true)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true :=
  Snake9.LocalRup.prove_clause [c887, c885, c578] c888 (by decide) p (sat_cons (step887 p h) (sat_cons (step885 p h) (sat_cons (step578 p h) (sat_nil p))))
def c889 : List Lit := [(1512, true)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true :=
  Snake9.LocalRup.prove_clause [c888, c885, c886, c332, c872, c592, c582, c868, c518, c543, c504, c507, c482, c527, c529, c498, c499, c490, c863, c525, c496, c492, c493, c473, c474, c56, c35, c24, c27] c889 (by decide) p (sat_cons (step888 p h) (sat_cons (step885 p h) (sat_cons (step886 p h) (sat_cons (step332 p h) (sat_cons (step872 p h) (sat_cons (step592 p h) (sat_cons (step582 p h) (sat_cons (step868 p h) (sat_cons (step518 p h) (sat_cons (step543 p h) (sat_cons (step504 p h) (sat_cons (step507 p h) (sat_cons (step482 p h) (sat_cons (step527 p h) (sat_cons (step529 p h) (sat_cons (step498 p h) (sat_cons (step499 p h) (sat_cons (step490 p h) (sat_cons (step863 p h) (sat_cons (step525 p h) (sat_cons (step496 p h) (sat_cons (step492 p h) (sat_cons (step493 p h) (sat_cons (step473 p h) (sat_cons (step474 p h) (sat_cons (step56 p h) (sat_cons (step35 p h) (sat_cons (step24 p h) (sat_cons (step27 p h) (sat_nil p))))))))))))))))))))))))))))))
def c890 : List Lit := [(1651, false)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true :=
  Snake9.LocalRup.prove_clause [c889, c821, c815] c890 (by decide) p (sat_cons (step889 p h) (sat_cons (step821 p h) (sat_cons (step815 p h) (sat_nil p))))
def c891 : List Lit := [(77, true), (1568, true)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true :=
  Snake9.LocalRup.prove_clause [c355, c880, c671, c644, c640, c642, c643, c646, c132, c666, c136, c681, c616, c878, c619] c891 (by decide) p (sat_cons (step355 p h) (sat_cons (step880 p h) (sat_cons (step671 p h) (sat_cons (step644 p h) (sat_cons (step640 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step646 p h) (sat_cons (step132 p h) (sat_cons (step666 p h) (sat_cons (step136 p h) (sat_cons (step681 p h) (sat_cons (step616 p h) (sat_cons (step878 p h) (sat_cons (step619 p h) (sat_nil p))))))))))))))))
def c892 : List Lit := [(1555, true), (77, false)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true :=
  Snake9.LocalRup.prove_clause [c357, c654, c656, c651, c652, c648, c649, c235, c183, c168, c187] c892 (by decide) p (sat_cons (step357 p h) (sat_cons (step654 p h) (sat_cons (step656 p h) (sat_cons (step651 p h) (sat_cons (step652 p h) (sat_cons (step648 p h) (sat_cons (step649 p h) (sat_cons (step235 p h) (sat_cons (step183 p h) (sat_cons (step168 p h) (sat_cons (step187 p h) (sat_nil p))))))))))))
def c893 : List Lit := [(1568, true)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true :=
  Snake9.LocalRup.prove_clause [c355, c880, c891, c892, c662, c667, c681, c643, c645, c878, c641, c619, c132, c616, c136] c893 (by decide) p (sat_cons (step355 p h) (sat_cons (step880 p h) (sat_cons (step891 p h) (sat_cons (step892 p h) (sat_cons (step662 p h) (sat_cons (step667 p h) (sat_cons (step681 p h) (sat_cons (step643 p h) (sat_cons (step645 p h) (sat_cons (step878 p h) (sat_cons (step641 p h) (sat_cons (step619 p h) (sat_cons (step132 p h) (sat_cons (step616 p h) (sat_cons (step136 p h) (sat_nil p))))))))))))))))
def c894 : List Lit := [(1434, true)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true :=
  Snake9.LocalRup.prove_clause [c335, c504, c507, c499, c489, c492, c493, c487, c488, c42, c32, c33] c894 (by decide) p (sat_cons (step335 p h) (sat_cons (step504 p h) (sat_cons (step507 p h) (sat_cons (step499 p h) (sat_cons (step489 p h) (sat_cons (step492 p h) (sat_cons (step493 p h) (sat_cons (step487 p h) (sat_cons (step488 p h) (sat_cons (step42 p h) (sat_cons (step32 p h) (sat_cons (step33 p h) (sat_nil p)))))))))))))
def c895 : List Lit := [(1442, true)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true :=
  Snake9.LocalRup.prove_clause [c894, c868] c895 (by decide) p (sat_cons (step894 p h) (sat_cons (step868 p h) (sat_nil p)))
def c896 : List Lit := [(1443, true), (1553, true)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true :=
  Snake9.LocalRup.prove_clause [c894, c329, c334, c652, c651, c869, c519, c482, c866, c863, c470, c473, c474, c468, c469, c9, c11, c492, c499, c508, c490, c217, c31, c21, c30] c896 (by decide) p (sat_cons (step894 p h) (sat_cons (step329 p h) (sat_cons (step334 p h) (sat_cons (step652 p h) (sat_cons (step651 p h) (sat_cons (step869 p h) (sat_cons (step519 p h) (sat_cons (step482 p h) (sat_cons (step866 p h) (sat_cons (step863 p h) (sat_cons (step470 p h) (sat_cons (step473 p h) (sat_cons (step474 p h) (sat_cons (step468 p h) (sat_cons (step469 p h) (sat_cons (step9 p h) (sat_cons (step11 p h) (sat_cons (step492 p h) (sat_cons (step499 p h) (sat_cons (step508 p h) (sat_cons (step490 p h) (sat_cons (step217 p h) (sat_cons (step31 p h) (sat_cons (step21 p h) (sat_cons (step30 p h) (sat_nil p))))))))))))))))))))))))))
def c897 : List Lit := [(16, false), (13, true), (15, false), (1553, true)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true :=
  Snake9.LocalRup.prove_clause [c334, c652, c651, c217, c31, c30] c897 (by decide) p (sat_cons (step334 p h) (sat_cons (step652 p h) (sat_cons (step651 p h) (sat_cons (step217 p h) (sat_cons (step31 p h) (sat_cons (step30 p h) (sat_nil p)))))))
def c898 : List Lit := [(1457, true), (32, false), (14, false)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true :=
  Snake9.LocalRup.prove_clause [c527, c529, c525, c55] c898 (by decide) p (sat_cons (step527 p h) (sat_cons (step529 p h) (sat_cons (step525 p h) (sat_cons (step55 p h) (sat_nil p)))))
def c899 : List Lit := [(1602, true), (84, true), (86, false)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true :=
  Snake9.LocalRup.prove_clause [c366, c742, c743, c300, c302] c899 (by decide) p (sat_cons (step366 p h) (sat_cons (step742 p h) (sat_cons (step743 p h) (sat_cons (step300 p h) (sat_cons (step302 p h) (sat_nil p))))))
def c900 : List Lit := [(100, true), (1590, true), (97, false), (85, false)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true :=
  Snake9.LocalRup.prove_clause [c716, c712, c714, c718, c277, c710] c900 (by decide) p (sat_cons (step716 p h) (sat_cons (step712 p h) (sat_cons (step714 p h) (sat_cons (step718 p h) (sat_cons (step277 p h) (sat_cons (step710 p h) (sat_nil p)))))))
def c901 : List Lit := [(100, false), (78, true), (79, true), (215, true)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true :=
  Snake9.LocalRup.prove_clause [c363, c287, c288, c284, c837] c901 (by decide) p (sat_cons (step363 p h) (sat_cons (step287 p h) (sat_cons (step288 p h) (sat_cons (step284 p h) (sat_cons (step837 p h) (sat_nil p))))))
end B112E120
