import B112E183Inputs
namespace B112E183
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c828 : List Lit := [(49, false), (50, false), (51, false)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true :=
  Snake9.LocalRup.prove_clause [c121, c123] c828 (by decide) p (sat_cons (step121 p h) (sat_cons (step123 p h) (sat_nil p)))
def c829 : List Lit := [(64, false)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true :=
  Snake9.LocalRup.prove_clause [c292, c153] c829 (by decide) p (sat_cons (step292 p h) (sat_cons (step153 p h) (sat_nil p)))
def c830 : List Lit := [(74, false)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true :=
  Snake9.LocalRup.prove_clause [c297, c176] c830 (by decide) p (sat_cons (step297 p h) (sat_cons (step176 p h) (sat_nil p)))
def c831 : List Lit := [(78, false)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true :=
  Snake9.LocalRup.prove_clause [c300, c184] c831 (by decide) p (sat_cons (step300 p h) (sat_cons (step184 p h) (sat_nil p)))
def c832 : List Lit := [(434, false)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true :=
  Snake9.LocalRup.prove_clause [c502, c499] c832 (by decide) p (sat_cons (step502 p h) (sat_cons (step499 p h) (sat_nil p)))
def c833 : List Lit := [(326, false)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true :=
  Snake9.LocalRup.prove_clause [c502, c501] c833 (by decide) p (sat_cons (step502 p h) (sat_cons (step501 p h) (sat_nil p)))
def c834 : List Lit := [(432, false)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true :=
  Snake9.LocalRup.prove_clause [c832, c495] c834 (by decide) p (sat_cons (step832 p h) (sat_cons (step495 p h) (sat_nil p)))
def c835 : List Lit := [(378, false)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true :=
  Snake9.LocalRup.prove_clause [c832, c498] c835 (by decide) p (sat_cons (step832 p h) (sat_cons (step498 p h) (sat_nil p)))
def c836 : List Lit := [(324, false)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true :=
  Snake9.LocalRup.prove_clause [c833, c392] c836 (by decide) p (sat_cons (step833 p h) (sat_cons (step392 p h) (sat_nil p)))
def c837 : List Lit := [(272, false)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.LocalRup.prove_clause [c833, c395] c837 (by decide) p (sat_cons (step833 p h) (sat_cons (step395 p h) (sat_nil p)))
def c838 : List Lit := [(404, false)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c834, c493] c838 (by decide) p (sat_cons (step834 p h) (sat_cons (step493 p h) (sat_nil p)))
def c839 : List Lit := [(376, false)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c835, c445] c839 (by decide) p (sat_cons (step835 p h) (sat_cons (step445 p h) (sat_nil p)))
def c840 : List Lit := [(350, false)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c835, c448] c840 (by decide) p (sat_cons (step835 p h) (sat_cons (step448 p h) (sat_nil p)))
def c841 : List Lit := [(322, false)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c836, c388] c841 (by decide) p (sat_cons (step836 p h) (sat_cons (step388 p h) (sat_nil p)))
def c842 : List Lit := [(296, false)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c836, c390] c842 (by decide) p (sat_cons (step836 p h) (sat_cons (step390 p h) (sat_nil p)))
def c843 : List Lit := [(270, false)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c837, c354] c843 (by decide) p (sat_cons (step837 p h) (sat_cons (step354 p h) (sat_nil p)))
def c844 : List Lit := [(402, false)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c838, c469] c844 (by decide) p (sat_cons (step838 p h) (sat_cons (step469 p h) (sat_nil p)))
def c845 : List Lit := [(390, false)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c838, c472] c845 (by decide) p (sat_cons (step838 p h) (sat_cons (step472 p h) (sat_nil p)))
def c846 : List Lit := [(374, false)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c839, c440] c846 (by decide) p (sat_cons (step839 p h) (sat_cons (step440 p h) (sat_nil p)))
def c847 : List Lit := [(362, false)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c839, c443] c847 (by decide) p (sat_cons (step839 p h) (sat_cons (step443 p h) (sat_nil p)))
def c848 : List Lit := [(348, false)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c840, c415] c848 (by decide) p (sat_cons (step840 p h) (sat_cons (step415 p h) (sat_nil p)))
def c849 : List Lit := [(336, false)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c840, c418] c849 (by decide) p (sat_cons (step840 p h) (sat_cons (step418 p h) (sat_nil p)))
def c850 : List Lit := [(308, false)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c841, c386] c850 (by decide) p (sat_cons (step841 p h) (sat_cons (step386 p h) (sat_nil p)))
def c851 : List Lit := [(282, false)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c842, c377] c851 (by decide) p (sat_cons (step842 p h) (sat_cons (step377 p h) (sat_nil p)))
def c852 : List Lit := [(268, false)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c843, c349] c852 (by decide) p (sat_cons (step843 p h) (sat_cons (step349 p h) (sat_nil p)))
def c853 : List Lit := [(256, false)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c843, c352] c853 (by decide) p (sat_cons (step843 p h) (sat_cons (step352 p h) (sat_nil p)))
def c854 : List Lit := [(394, false)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c844, c467] c854 (by decide) p (sat_cons (step844 p h) (sat_cons (step467 p h) (sat_nil p)))
def c855 : List Lit := [(372, false)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.LocalRup.prove_clause [c846, c436] c855 (by decide) p (sat_cons (step846 p h) (sat_cons (step436 p h) (sat_nil p)))
def c856 : List Lit := [(354, false)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c847, c428] c856 (by decide) p (sat_cons (step847 p h) (sat_cons (step428 p h) (sat_nil p)))
def c857 : List Lit := [(280, false)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c851, c364] c857 (by decide) p (sat_cons (step851 p h) (sat_cons (step364 p h) (sat_nil p)))
def c858 : List Lit := [(266, false)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c852, c345] c858 (by decide) p (sat_cons (step852 p h) (sat_cons (step345 p h) (sat_nil p)))
def c859 : List Lit := [(248, false)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c853, c335] c859 (by decide) p (sat_cons (step853 p h) (sat_cons (step335 p h) (sat_nil p)))
def c860 : List Lit := [(392, false)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c854, c460] c860 (by decide) p (sat_cons (step854 p h) (sat_cons (step460 p h) (sat_nil p)))
def c861 : List Lit := [(1410, true)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c122, c616, c619, c613, c603, c606, c602, c120] c861 (by decide) p (sat_cons (step122 p h) (sat_cons (step616 p h) (sat_cons (step619 p h) (sat_cons (step613 p h) (sat_cons (step603 p h) (sat_cons (step606 p h) (sat_cons (step602 p h) (sat_cons (step120 p h) (sat_nil p)))))))))
def c862 : List Lit := [(1417, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c861, c623] c862 (by decide) p (sat_cons (step861 p h) (sat_cons (step623 p h) (sat_nil p)))
def c863 : List Lit := [(68, false), (73, false), (71, false)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c847, c170, c175, c169, c423, c419, c424, c420, c427] c863 (by decide) p (sat_cons (step847 p h) (sat_cons (step170 p h) (sat_cons (step175 p h) (sat_cons (step169 p h) (sat_cons (step423 p h) (sat_cons (step419 p h) (sat_cons (step424 p h) (sat_cons (step420 p h) (sat_cons (step427 p h) (sat_nil p))))))))))
def c864 : List Lit := [(1452, true), (1446, false), (173, true)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true :=
  Snake9.LocalRup.prove_clause [c665, c671, c674, c668, c658, c152, c655, c656, c144] c864 (by decide) p (sat_cons (step665 p h) (sat_cons (step671 p h) (sat_cons (step674 p h) (sat_cons (step668 p h) (sat_cons (step658 p h) (sat_cons (step152 p h) (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step144 p h) (sat_nil p))))))))))
def c865 : List Lit := [(1441, true), (62, false), (63, false)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true :=
  Snake9.LocalRup.prove_clause [c655, c656, c144] c865 (by decide) p (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step144 p h) (sat_nil p))))
def c866 : List Lit := [(1464, true), (1492, true), (80, false), (69, false), (191, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true :=
  Snake9.LocalRup.prove_clause [c692, c693, c191, c188, c204, c724, c730] c866 (by decide) p (sat_cons (step692 p h) (sat_cons (step693 p h) (sat_cons (step191 p h) (sat_cons (step188 p h) (sat_cons (step204 p h) (sat_cons (step724 p h) (sat_cons (step730 p h) (sat_nil p))))))))
def c867 : List Lit := [(1518, true), (208, true)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true :=
  Snake9.LocalRup.prove_clause [c770, c773, c766, c756, c759, c760, c264, c248] c867 (by decide) p (sat_cons (step770 p h) (sat_cons (step773 p h) (sat_cons (step766 p h) (sat_cons (step756 p h) (sat_cons (step759 p h) (sat_cons (step760 p h) (sat_cons (step264 p h) (sat_cons (step248 p h) (sat_nil p)))))))))
def c868 : List Lit := [(16, false), (1341, true), (19, false), (14, false), (247, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true :=
  Snake9.LocalRup.prove_clause [c328, c327, c329, c50, c41, c45, c48, c517, c511, c512, c35] c868 (by decide) p (sat_cons (step328 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step50 p h) (sat_cons (step41 p h) (sat_cons (step45 p h) (sat_cons (step48 p h) (sat_cons (step517 p h) (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step35 p h) (sat_nil p))))))))))))
def c869 : List Lit := [(1338, true), (12, false), (14, false)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true :=
  Snake9.LocalRup.prove_clause [c511, c512, c35] c869 (by decide) p (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step35 p h) (sat_nil p))))
def c870 : List Lit := [(1542, true), (80, false), (69, false), (1452, false), (1459, false), (361, false)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true :=
  Snake9.LocalRup.prove_clause [c839, c832, c831, c304, c702, c713, c441, c444, c497, c490, c489, c479, c475, c474, c867, c778, c491, c470, c453, c452, c451, c442, c435, c433, c430, c432, c431, c798, c805, c782, c715, c746, c704, c866, c695, c698, c703, c689, c714, c186, c802, c207, c780, c213, c740, c742, c737, c727, c209, c724] c870 (by decide) p (sat_cons (step839 p h) (sat_cons (step832 p h) (sat_cons (step831 p h) (sat_cons (step304 p h) (sat_cons (step702 p h) (sat_cons (step713 p h) (sat_cons (step441 p h) (sat_cons (step444 p h) (sat_cons (step497 p h) (sat_cons (step490 p h) (sat_cons (step489 p h) (sat_cons (step479 p h) (sat_cons (step475 p h) (sat_cons (step474 p h) (sat_cons (step867 p h) (sat_cons (step778 p h) (sat_cons (step491 p h) (sat_cons (step470 p h) (sat_cons (step453 p h) (sat_cons (step452 p h) (sat_cons (step451 p h) (sat_cons (step442 p h) (sat_cons (step435 p h) (sat_cons (step433 p h) (sat_cons (step430 p h) (sat_cons (step432 p h) (sat_cons (step431 p h) (sat_cons (step798 p h) (sat_cons (step805 p h) (sat_cons (step782 p h) (sat_cons (step715 p h) (sat_cons (step746 p h) (sat_cons (step704 p h) (sat_cons (step866 p h) (sat_cons (step695 p h) (sat_cons (step698 p h) (sat_cons (step703 p h) (sat_cons (step689 p h) (sat_cons (step714 p h) (sat_cons (step186 p h) (sat_cons (step802 p h) (sat_cons (step207 p h) (sat_cons (step780 p h) (sat_cons (step213 p h) (sat_cons (step740 p h) (sat_cons (step742 p h) (sat_cons (step737 p h) (sat_cons (step727 p h) (sat_cons (step209 p h) (sat_cons (step724 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c871 : List Lit := [(1499, true), (198, true)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true :=
  Snake9.LocalRup.prove_clause [c740, c742, c737, c727, c724, c725, c209, c213] c871 (by decide) p (sat_cons (step740 p h) (sat_cons (step742 p h) (sat_cons (step737 p h) (sat_cons (step727 p h) (sat_cons (step724 p h) (sat_cons (step725 p h) (sat_cons (step209 p h) (sat_cons (step213 p h) (sat_nil p)))))))))
def c872 : List Lit := [(1541, true), (1452, false), (433, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true :=
  Snake9.LocalRup.prove_clause [c712, c494, c490, c489, c479, c475, c474, c867, c491, c470, c453, c452, c451, c871, c780, c496, c444, c439, c435, c432, c431, c792, c782, c746, c797, c713, c700, c702, c695, c686, c693, c866, c192] c872 (by decide) p (sat_cons (step712 p h) (sat_cons (step494 p h) (sat_cons (step490 p h) (sat_cons (step489 p h) (sat_cons (step479 p h) (sat_cons (step475 p h) (sat_cons (step474 p h) (sat_cons (step867 p h) (sat_cons (step491 p h) (sat_cons (step470 p h) (sat_cons (step453 p h) (sat_cons (step452 p h) (sat_cons (step451 p h) (sat_cons (step871 p h) (sat_cons (step780 p h) (sat_cons (step496 p h) (sat_cons (step444 p h) (sat_cons (step439 p h) (sat_cons (step435 p h) (sat_cons (step432 p h) (sat_cons (step431 p h) (sat_cons (step792 p h) (sat_cons (step782 p h) (sat_cons (step746 p h) (sat_cons (step797 p h) (sat_cons (step713 p h) (sat_cons (step700 p h) (sat_cons (step702 p h) (sat_cons (step695 p h) (sat_cons (step686 p h) (sat_cons (step693 p h) (sat_cons (step866 p h) (sat_cons (step192 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c873 : List Lit := [(175, false), (66, false), (57, false)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true :=
  Snake9.LocalRup.prove_clause [c840, c407, c155, c410, c134, c411, c397, c417, c398, c403] c873 (by decide) p (sat_cons (step840 p h) (sat_cons (step407 p h) (sat_cons (step155 p h) (sat_cons (step410 p h) (sat_cons (step134 p h) (sat_cons (step411 p h) (sat_cons (step397 p h) (sat_cons (step417 p h) (sat_cons (step398 p h) (sat_cons (step403 p h) (sat_nil p)))))))))))
def c874 : List Lit := [(1500, true), (198, true), (1494, false)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true :=
  Snake9.LocalRup.prove_clause [c735, c741, c743, c738, c727, c724, c725, c209, c213] c874 (by decide) p (sat_cons (step735 p h) (sat_cons (step741 p h) (sat_cons (step743 p h) (sat_cons (step738 p h) (sat_cons (step727 p h) (sat_cons (step724 p h) (sat_cons (step725 p h) (sat_cons (step209 p h) (sat_cons (step213 p h) (sat_nil p))))))))))
def c875 : List Lit := [(88, false), (90, false), (91, false), (198, true)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true :=
  Snake9.LocalRup.prove_clause [c213, c209] c875 (by decide) p (sat_cons (step213 p h) (sat_cons (step209 p h) (sat_nil p)))
def c876 : List Lit := [(23, true), (1359, true), (29, true), (136, true)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true :=
  Snake9.LocalRup.prove_clause [c281, c534, c59, c543, c77, c537] c876 (by decide) p (sat_cons (step281 p h) (sat_cons (step534 p h) (sat_cons (step59 p h) (sat_cons (step543 p h) (sat_cons (step77 p h) (sat_cons (step537 p h) (sat_nil p)))))))
def c877 : List Lit := [(1351, true), (1341, true), (247, true)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true :=
  Snake9.LocalRup.prove_clause [c530, c532, c527, c528, c868] c877 (by decide) p (sat_cons (step530 p h) (sat_cons (step532 p h) (sat_cons (step527 p h) (sat_cons (step528 p h) (sat_cons (step868 p h) (sat_nil p))))))
def c878 : List Lit := [(1343, true), (123, true)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true :=
  Snake9.LocalRup.prove_clause [c518, c520, c514, c506, c508, c511, c512, c503, c504, c9, c31, c39] c878 (by decide) p (sat_cons (step518 p h) (sat_cons (step520 p h) (sat_cons (step514 p h) (sat_cons (step506 p h) (sat_cons (step508 p h) (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step503 p h) (sat_cons (step504 p h) (sat_cons (step9 p h) (sat_cons (step31 p h) (sat_cons (step39 p h) (sat_nil p)))))))))))))
def c879 : List Lit := [(13, false), (7, false), (10, false), (123, true), (21, false)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true :=
  Snake9.LocalRup.prove_clause [c15, c39, c38, c821] c879 (by decide) p (sat_cons (step15 p h) (sat_cons (step39 p h) (sat_cons (step38 p h) (sat_cons (step821 p h) (sat_nil p)))))
def c880 : List Lit := [(68, true), (1467, false), (71, true), (183, true), (1482, true), (173, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true :=
  Snake9.LocalRup.prove_clause [c296, c662, c173, c864, c175, c716, c683, c707, c685] c880 (by decide) p (sat_cons (step296 p h) (sat_cons (step662 p h) (sat_cons (step173 p h) (sat_cons (step864 p h) (sat_cons (step175 p h) (sat_cons (step716 p h) (sat_cons (step683 p h) (sat_cons (step707 p h) (sat_cons (step685 p h) (sat_nil p))))))))))
def c881 : List Lit := [(1370, true), (271, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true :=
  Snake9.LocalRup.prove_clause [c355, c325, c323, c322, c321, c878, c353, c350, c333, c566, c562, c519, c552, c877] c881 (by decide) p (sat_cons (step355 p h) (sat_cons (step325 p h) (sat_cons (step323 p h) (sat_cons (step322 p h) (sat_cons (step321 p h) (sat_cons (step878 p h) (sat_cons (step353 p h) (sat_cons (step350 p h) (sat_cons (step333 p h) (sat_cons (step566 p h) (sat_cons (step562 p h) (sat_cons (step519 p h) (sat_cons (step552 p h) (sat_cons (step877 p h) (sat_nil p)))))))))))))))
def c882 : List Lit := [(1466, false), (1471, true), (1479, true), (173, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true :=
  Snake9.LocalRup.prove_clause [c700, c703, c713, c684, c864, c681, c682, c662, c863] c882 (by decide) p (sat_cons (step700 p h) (sat_cons (step703 p h) (sat_cons (step713 p h) (sat_cons (step684 p h) (sat_cons (step864 p h) (sat_cons (step681 p h) (sat_cons (step682 p h) (sat_cons (step662 p h) (sat_cons (step863 p h) (sat_nil p))))))))))
def c883 : List Lit := [(73, false), (19, false), (76, false), (183, true)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true :=
  Snake9.LocalRup.prove_clause [c174, c181] c883 (by decide) p (sat_cons (step174 p h) (sat_cons (step181 p h) (sat_nil p)))
def c884 : List Lit := [(1336, true), (9, true), (25, true), (70, true), (21, false), (3, true), (1333, false)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true :=
  Snake9.LocalRup.prove_clause [c507, c509, c505, c11, c22] c884 (by decide) p (sat_cons (step507 p h) (sat_cons (step509 p h) (sat_cons (step505 p h) (sat_cons (step11 p h) (sat_cons (step22 p h) (sat_nil p))))))
def c885 : List Lit := [(1383, true), (36, true), (23, false)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true :=
  Snake9.LocalRup.prove_clause [c580, c582, c578, c86, c89] c885 (by decide) p (sat_cons (step580 p h) (sat_cons (step582 p h) (sat_cons (step578 p h) (sat_cons (step86 p h) (sat_cons (step89 p h) (sat_nil p))))))
def c886 : List Lit := [(1518, true)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true :=
  Snake9.LocalRup.prove_clause [c770, c773, c766, c754, c756, c759, c760, c751, c264, c245, c247] c886 (by decide) p (sat_cons (step770 p h) (sat_cons (step773 p h) (sat_cons (step766 p h) (sat_cons (step754 p h) (sat_cons (step756 p h) (sat_cons (step759 p h) (sat_cons (step760 p h) (sat_cons (step751 p h) (sat_cons (step264 p h) (sat_cons (step245 p h) (sat_cons (step247 p h) (sat_nil p))))))))))))
def c887 : List Lit := [(1525, true)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true :=
  Snake9.LocalRup.prove_clause [c886, c778] c887 (by decide) p (sat_cons (step886 p h) (sat_cons (step778 p h) (sat_nil p)))
def c888 : List Lit := [(25, true), (1381, true), (35, false), (36, true)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true :=
  Snake9.LocalRup.prove_clause [c842, c578, c90, c361, c363, c376, c373, c367, c366, c577, c102, c101, c823] c888 (by decide) p (sat_cons (step842 p h) (sat_cons (step578 p h) (sat_cons (step90 p h) (sat_cons (step361 p h) (sat_cons (step363 p h) (sat_cons (step376 p h) (sat_cons (step373 p h) (sat_cons (step367 p h) (sat_cons (step366 p h) (sat_cons (step577 p h) (sat_cons (step102 p h) (sat_cons (step101 p h) (sat_cons (step823 p h) (sat_nil p))))))))))))))
def c889 : List Lit := [(1354, false), (1373, true), (3, true), (1341, false), (25, false), (35, false)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true :=
  Snake9.LocalRup.prove_clause [c504, c506, c522, c573, c549, c542, c548, c575, c525, c543, c507, c538, c505, c70] c889 (by decide) p (sat_cons (step504 p h) (sat_cons (step506 p h) (sat_cons (step522 p h) (sat_cons (step573 p h) (sat_cons (step549 p h) (sat_cons (step542 p h) (sat_cons (step548 p h) (sat_cons (step575 p h) (sat_cons (step525 p h) (sat_cons (step543 p h) (sat_cons (step507 p h) (sat_cons (step538 p h) (sat_cons (step505 p h) (sat_cons (step70 p h) (sat_nil p)))))))))))))))
def c890 : List Lit := [(24, true), (1357, true), (136, true)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true :=
  Snake9.LocalRup.prove_clause [c282, c79, c539, c76] c890 (by decide) p (sat_cons (step282 p h) (sat_cons (step79 p h) (sat_cons (step539 p h) (sat_cons (step76 p h) (sat_nil p)))))
def c891 : List Lit := [(14, false), (3, false), (124, true), (18, true)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true :=
  Snake9.LocalRup.prove_clause [c41, c42, c819] c891 (by decide) p (sat_cons (step41 p h) (sat_cons (step42 p h) (sat_cons (step819 p h) (sat_nil p))))
end B112E183
