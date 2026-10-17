import B112E090Inputs
namespace B112E090
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c758 : List Lit := [(6, true)]
theorem step758 (p : Nat → Bool) (h : Constraints p) : clause p c758 = true :=
  Snake9.LocalRup.prove_clause [c6, c5] c758 (by decide) p (sat_cons (step6 p h) (sat_cons (step5 p h) (sat_nil p)))
def c759 : List Lit := [(115, true), (4, true)]
theorem step759 (p : Nat → Bool) (h : Constraints p) : clause p c759 = true :=
  Snake9.LocalRup.prove_clause [c758, c7] c759 (by decide) p (sat_cons (step758 p h) (sat_cons (step7 p h) (sat_nil p)))
def c760 : List Lit := [(31, false)]
theorem step760 (p : Nat → Bool) (h : Constraints p) : clause p c760 = true :=
  Snake9.LocalRup.prove_clause [c257, c71] c760 (by decide) p (sat_cons (step257 p h) (sat_cons (step71 p h) (sat_nil p)))
def c761 : List Lit := [(42, false)]
theorem step761 (p : Nat → Bool) (h : Constraints p) : clause p c761 = true :=
  Snake9.LocalRup.prove_clause [c261, c86] c761 (by decide) p (sat_cons (step261 p h) (sat_cons (step86 p h) (sat_nil p)))
def c762 : List Lit := [(55, false)]
theorem step762 (p : Nat → Bool) (h : Constraints p) : clause p c762 = true :=
  Snake9.LocalRup.prove_clause [c266, c144] c762 (by decide) p (sat_cons (step266 p h) (sat_cons (step144 p h) (sat_nil p)))
def c763 : List Lit := [(430, false)]
theorem step763 (p : Nat → Bool) (h : Constraints p) : clause p c763 = true :=
  Snake9.LocalRup.prove_clause [c426, c423] c763 (by decide) p (sat_cons (step426 p h) (sat_cons (step423 p h) (sat_nil p)))
def c764 : List Lit := [(324, false)]
theorem step764 (p : Nat → Bool) (h : Constraints p) : clause p c764 = true :=
  Snake9.LocalRup.prove_clause [c426, c425] c764 (by decide) p (sat_cons (step426 p h) (sat_cons (step425 p h) (sat_nil p)))
def c765 : List Lit := [(428, false)]
theorem step765 (p : Nat → Bool) (h : Constraints p) : clause p c765 = true :=
  Snake9.LocalRup.prove_clause [c763, c419] c765 (by decide) p (sat_cons (step763 p h) (sat_cons (step419 p h) (sat_nil p)))
def c766 : List Lit := [(376, false)]
theorem step766 (p : Nat → Bool) (h : Constraints p) : clause p c766 = true :=
  Snake9.LocalRup.prove_clause [c763, c422] c766 (by decide) p (sat_cons (step763 p h) (sat_cons (step422 p h) (sat_nil p)))
def c767 : List Lit := [(322, false)]
theorem step767 (p : Nat → Bool) (h : Constraints p) : clause p c767 = true :=
  Snake9.LocalRup.prove_clause [c764, c345] c767 (by decide) p (sat_cons (step764 p h) (sat_cons (step345 p h) (sat_nil p)))
def c768 : List Lit := [(270, false)]
theorem step768 (p : Nat → Bool) (h : Constraints p) : clause p c768 = true :=
  Snake9.LocalRup.prove_clause [c764, c348] c768 (by decide) p (sat_cons (step764 p h) (sat_cons (step348 p h) (sat_nil p)))
def c769 : List Lit := [(400, false)]
theorem step769 (p : Nat → Bool) (h : Constraints p) : clause p c769 = true :=
  Snake9.LocalRup.prove_clause [c765, c417] c769 (by decide) p (sat_cons (step765 p h) (sat_cons (step417 p h) (sat_nil p)))
def c770 : List Lit := [(374, false)]
theorem step770 (p : Nat → Bool) (h : Constraints p) : clause p c770 = true :=
  Snake9.LocalRup.prove_clause [c766, c390] c770 (by decide) p (sat_cons (step766 p h) (sat_cons (step390 p h) (sat_nil p)))
def c771 : List Lit := [(348, false)]
theorem step771 (p : Nat → Bool) (h : Constraints p) : clause p c771 = true :=
  Snake9.LocalRup.prove_clause [c766, c393] c771 (by decide) p (sat_cons (step766 p h) (sat_cons (step393 p h) (sat_nil p)))
def c772 : List Lit := [(320, false)]
theorem step772 (p : Nat → Bool) (h : Constraints p) : clause p c772 = true :=
  Snake9.LocalRup.prove_clause [c767, c342] c772 (by decide) p (sat_cons (step767 p h) (sat_cons (step342 p h) (sat_nil p)))
def c773 : List Lit := [(268, false)]
theorem step773 (p : Nat → Bool) (h : Constraints p) : clause p c773 = true :=
  Snake9.LocalRup.prove_clause [c768, c313] c773 (by decide) p (sat_cons (step768 p h) (sat_cons (step313 p h) (sat_nil p)))
def c774 : List Lit := [(398, false)]
theorem step774 (p : Nat → Bool) (h : Constraints p) : clause p c774 = true :=
  Snake9.LocalRup.prove_clause [c769, c409] c774 (by decide) p (sat_cons (step769 p h) (sat_cons (step409 p h) (sat_nil p)))
def c775 : List Lit := [(372, false)]
theorem step775 (p : Nat → Bool) (h : Constraints p) : clause p c775 = true :=
  Snake9.LocalRup.prove_clause [c770, c386] c775 (by decide) p (sat_cons (step770 p h) (sat_cons (step386 p h) (sat_nil p)))
def c776 : List Lit := [(346, false)]
theorem step776 (p : Nat → Bool) (h : Constraints p) : clause p c776 = true :=
  Snake9.LocalRup.prove_clause [c771, c370] c776 (by decide) p (sat_cons (step771 p h) (sat_cons (step370 p h) (sat_nil p)))
def c777 : List Lit := [(254, false)]
theorem step777 (p : Nat → Bool) (h : Constraints p) : clause p c777 = true :=
  Snake9.LocalRup.prove_clause [c773, c311] c777 (by decide) p (sat_cons (step773 p h) (sat_cons (step311 p h) (sat_nil p)))
def c778 : List Lit := [(390, false)]
theorem step778 (p : Nat → Bool) (h : Constraints p) : clause p c778 = true :=
  Snake9.LocalRup.prove_clause [c774, c407] c778 (by decide) p (sat_cons (step774 p h) (sat_cons (step407 p h) (sat_nil p)))
def c779 : List Lit := [(344, false)]
theorem step779 (p : Nat → Bool) (h : Constraints p) : clause p c779 = true :=
  Snake9.LocalRup.prove_clause [c776, c365] c779 (by decide) p (sat_cons (step776 p h) (sat_cons (step365 p h) (sat_nil p)))
def c780 : List Lit := [(338, false)]
theorem step780 (p : Nat → Bool) (h : Constraints p) : clause p c780 = true :=
  Snake9.LocalRup.prove_clause [c776, c368] c780 (by decide) p (sat_cons (step776 p h) (sat_cons (step368 p h) (sat_nil p)))
def c781 : List Lit := [(1340, true)]
theorem step781 (p : Nat → Bool) (h : Constraints p) : clause p c781 = true :=
  Snake9.LocalRup.prove_clause [c760, c475] c781 (by decide) p (sat_cons (step760 p h) (sat_cons (step475 p h) (sat_nil p)))
def c782 : List Lit := [(29, true), (1341, true)]
theorem step782 (p : Nat → Bool) (h : Constraints p) : clause p c782 = true :=
  Snake9.LocalRup.prove_clause [c760, c476] c782 (by decide) p (sat_cons (step760 p h) (sat_cons (step476 p h) (sat_nil p)))
def c783 : List Lit := [(1342, true)]
theorem step783 (p : Nat → Bool) (h : Constraints p) : clause p c783 = true :=
  Snake9.LocalRup.prove_clause [c781, c477] c783 (by decide) p (sat_cons (step781 p h) (sat_cons (step477 p h) (sat_nil p)))
def c784 : List Lit := [(27, true), (1343, true)]
theorem step784 (p : Nat → Bool) (h : Constraints p) : clause p c784 = true :=
  Snake9.LocalRup.prove_clause [c781, c479] c784 (by decide) p (sat_cons (step781 p h) (sat_cons (step479 p h) (sat_nil p)))
def c785 : List Lit := [(1353, true)]
theorem step785 (p : Nat → Bool) (h : Constraints p) : clause p c785 = true :=
  Snake9.LocalRup.prove_clause [c783, c490] c785 (by decide) p (sat_cons (step783 p h) (sat_cons (step490 p h) (sat_nil p)))
def c786 : List Lit := [(1349, false), (1354, true)]
theorem step786 (p : Nat → Bool) (h : Constraints p) : clause p c786 = true :=
  Snake9.LocalRup.prove_clause [c783, c491] c786 (by decide) p (sat_cons (step783 p h) (sat_cons (step491 p h) (sat_nil p)))
def c787 : List Lit := [(1350, false), (1355, true)]
theorem step787 (p : Nat → Bool) (h : Constraints p) : clause p c787 = true :=
  Snake9.LocalRup.prove_clause [c783, c492] c787 (by decide) p (sat_cons (step783 p h) (sat_cons (step492 p h) (sat_nil p)))
def c788 : List Lit := [(1360, true)]
theorem step788 (p : Nat → Bool) (h : Constraints p) : clause p c788 = true :=
  Snake9.LocalRup.prove_clause [c761, c498] c788 (by decide) p (sat_cons (step761 p h) (sat_cons (step498 p h) (sat_nil p)))
def c789 : List Lit := [(45, true), (1361, true)]
theorem step789 (p : Nat → Bool) (h : Constraints p) : clause p c789 = true :=
  Snake9.LocalRup.prove_clause [c761, c499] c789 (by decide) p (sat_cons (step761 p h) (sat_cons (step499 p h) (sat_nil p)))
def c790 : List Lit := [(1362, true)]
theorem step790 (p : Nat → Bool) (h : Constraints p) : clause p c790 = true :=
  Snake9.LocalRup.prove_clause [c788, c500] c790 (by decide) p (sat_cons (step788 p h) (sat_cons (step500 p h) (sat_nil p)))
def c791 : List Lit := [(40, true), (1363, true)]
theorem step791 (p : Nat → Bool) (h : Constraints p) : clause p c791 = true :=
  Snake9.LocalRup.prove_clause [c788, c502] c791 (by decide) p (sat_cons (step788 p h) (sat_cons (step502 p h) (sat_nil p)))
def c792 : List Lit := [(1369, false), (1374, true)]
theorem step792 (p : Nat → Bool) (h : Constraints p) : clause p c792 = true :=
  Snake9.LocalRup.prove_clause [c790, c518] c792 (by decide) p (sat_cons (step790 p h) (sat_cons (step518 p h) (sat_nil p)))
def c793 : List Lit := [(1370, false), (1375, true)]
theorem step793 (p : Nat → Bool) (h : Constraints p) : clause p c793 = true :=
  Snake9.LocalRup.prove_clause [c790, c519] c793 (by decide) p (sat_cons (step790 p h) (sat_cons (step519 p h) (sat_nil p)))
def c794 : List Lit := [(1371, false), (1376, true)]
theorem step794 (p : Nat → Bool) (h : Constraints p) : clause p c794 = true :=
  Snake9.LocalRup.prove_clause [c790, c520] c794 (by decide) p (sat_cons (step790 p h) (sat_cons (step520 p h) (sat_nil p)))
def c795 : List Lit := [(1372, false), (1377, true)]
theorem step795 (p : Nat → Bool) (h : Constraints p) : clause p c795 = true :=
  Snake9.LocalRup.prove_clause [c790, c521] c795 (by decide) p (sat_cons (step790 p h) (sat_cons (step521 p h) (sat_nil p)))
def c796 : List Lit := [(1374, false), (1382, true)]
theorem step796 (p : Nat → Bool) (h : Constraints p) : clause p c796 = true :=
  Snake9.LocalRup.prove_clause [c785, c530] c796 (by decide) p (sat_cons (step785 p h) (sat_cons (step530 p h) (sat_nil p)))
def c797 : List Lit := [(1375, false), (1383, true)]
theorem step797 (p : Nat → Bool) (h : Constraints p) : clause p c797 = true :=
  Snake9.LocalRup.prove_clause [c785, c531] c797 (by decide) p (sat_cons (step785 p h) (sat_cons (step531 p h) (sat_nil p)))
def c798 : List Lit := [(1376, false), (1384, true)]
theorem step798 (p : Nat → Bool) (h : Constraints p) : clause p c798 = true :=
  Snake9.LocalRup.prove_clause [c785, c532] c798 (by decide) p (sat_cons (step785 p h) (sat_cons (step532 p h) (sat_nil p)))
def c799 : List Lit := [(1377, false), (1385, true)]
theorem step799 (p : Nat → Bool) (h : Constraints p) : clause p c799 = true :=
  Snake9.LocalRup.prove_clause [c785, c533] c799 (by decide) p (sat_cons (step785 p h) (sat_cons (step533 p h) (sat_nil p)))
def c800 : List Lit := [(1378, false), (1386, true)]
theorem step800 (p : Nat → Bool) (h : Constraints p) : clause p c800 = true :=
  Snake9.LocalRup.prove_clause [c785, c534] c800 (by decide) p (sat_cons (step785 p h) (sat_cons (step534 p h) (sat_nil p)))
def c801 : List Lit := [(1409, true)]
theorem step801 (p : Nat → Bool) (h : Constraints p) : clause p c801 = true :=
  Snake9.LocalRup.prove_clause [c762, c564] c801 (by decide) p (sat_cons (step762 p h) (sat_cons (step564 p h) (sat_nil p)))
def c802 : List Lit := [(56, true), (1410, true)]
theorem step802 (p : Nat → Bool) (h : Constraints p) : clause p c802 = true :=
  Snake9.LocalRup.prove_clause [c762, c565] c802 (by decide) p (sat_cons (step762 p h) (sat_cons (step565 p h) (sat_nil p)))
def c803 : List Lit := [(1411, true)]
theorem step803 (p : Nat → Bool) (h : Constraints p) : clause p c803 = true :=
  Snake9.LocalRup.prove_clause [c801, c566] c803 (by decide) p (sat_cons (step801 p h) (sat_cons (step566 p h) (sat_nil p)))
def c804 : List Lit := [(54, true), (1412, true)]
theorem step804 (p : Nat → Bool) (h : Constraints p) : clause p c804 = true :=
  Snake9.LocalRup.prove_clause [c801, c568] c804 (by decide) p (sat_cons (step801 p h) (sat_cons (step568 p h) (sat_nil p)))
def c805 : List Lit := [(1422, true)]
theorem step805 (p : Nat → Bool) (h : Constraints p) : clause p c805 = true :=
  Snake9.LocalRup.prove_clause [c803, c583] c805 (by decide) p (sat_cons (step803 p h) (sat_cons (step583 p h) (sat_nil p)))
def c806 : List Lit := [(1418, false), (1423, true)]
theorem step806 (p : Nat → Bool) (h : Constraints p) : clause p c806 = true :=
  Snake9.LocalRup.prove_clause [c803, c584] c806 (by decide) p (sat_cons (step803 p h) (sat_cons (step584 p h) (sat_nil p)))
def c807 : List Lit := [(1419, false), (1424, true)]
theorem step807 (p : Nat → Bool) (h : Constraints p) : clause p c807 = true :=
  Snake9.LocalRup.prove_clause [c803, c585] c807 (by decide) p (sat_cons (step803 p h) (sat_cons (step585 p h) (sat_nil p)))
def c808 : List Lit := [(1442, false), (1450, true)]
theorem step808 (p : Nat → Bool) (h : Constraints p) : clause p c808 = true :=
  Snake9.LocalRup.prove_clause [c805, c623] c808 (by decide) p (sat_cons (step805 p h) (sat_cons (step623 p h) (sat_nil p)))
def c809 : List Lit := [(1443, false), (1451, true)]
theorem step809 (p : Nat → Bool) (h : Constraints p) : clause p c809 = true :=
  Snake9.LocalRup.prove_clause [c805, c624] c809 (by decide) p (sat_cons (step805 p h) (sat_cons (step624 p h) (sat_nil p)))
def c810 : List Lit := [(1444, false), (1452, true)]
theorem step810 (p : Nat → Bool) (h : Constraints p) : clause p c810 = true :=
  Snake9.LocalRup.prove_clause [c805, c625] c810 (by decide) p (sat_cons (step805 p h) (sat_cons (step625 p h) (sat_nil p)))
def c811 : List Lit := [(1445, false), (1453, true)]
theorem step811 (p : Nat → Bool) (h : Constraints p) : clause p c811 = true :=
  Snake9.LocalRup.prove_clause [c805, c626] c811 (by decide) p (sat_cons (step805 p h) (sat_cons (step626 p h) (sat_nil p)))
def c812 : List Lit := [(1374, true)]
theorem step812 (p : Nat → Bool) (h : Constraints p) : clause p c812 = true :=
  Snake9.LocalRup.prove_clause [c262, c792, c522, c510, c512, c501, c507, c508, c504, c505, c789, c126, c95, c89] c812 (by decide) p (sat_cons (step262 p h) (sat_cons (step792 p h) (sat_cons (step522 p h) (sat_cons (step510 p h) (sat_cons (step512 p h) (sat_cons (step501 p h) (sat_cons (step507 p h) (sat_cons (step508 p h) (sat_cons (step504 p h) (sat_cons (step505 p h) (sat_cons (step789 p h) (sat_cons (step126 p h) (sat_cons (step95 p h) (sat_cons (step89 p h) (sat_nil p)))))))))))))))
def c813 : List Lit := [(1382, true)]
theorem step813 (p : Nat → Bool) (h : Constraints p) : clause p c813 = true :=
  Snake9.LocalRup.prove_clause [c812, c796] c813 (by decide) p (sat_cons (step812 p h) (sat_cons (step796 p h) (sat_nil p)))
def c814 : List Lit := [(1450, true)]
theorem step814 (p : Nat → Bool) (h : Constraints p) : clause p c814 = true :=
  Snake9.LocalRup.prove_clause [c274, c808, c627, c613, c616, c586, c608, c596, c598, c804, c601, c594, c182, c171, c179] c814 (by decide) p (sat_cons (step274 p h) (sat_cons (step808 p h) (sat_cons (step627 p h) (sat_cons (step613 p h) (sat_cons (step616 p h) (sat_cons (step586 p h) (sat_cons (step608 p h) (sat_cons (step596 p h) (sat_cons (step598 p h) (sat_cons (step804 p h) (sat_cons (step601 p h) (sat_cons (step594 p h) (sat_cons (step182 p h) (sat_cons (step171 p h) (sat_cons (step179 p h) (sat_nil p))))))))))))))))
def c815 : List Lit := [(22, true), (1465, true), (1321, true)]
theorem step815 (p : Nat → Bool) (h : Constraints p) : clause p c815 = true :=
  Snake9.LocalRup.prove_clause [c250, c645, c643, c647, c455, c453, c442, c444, c450, c458, c437, c439, c435, c37, c27, c23] c815 (by decide) p (sat_cons (step250 p h) (sat_cons (step645 p h) (sat_cons (step643 p h) (sat_cons (step647 p h) (sat_cons (step455 p h) (sat_cons (step453 p h) (sat_cons (step442 p h) (sat_cons (step444 p h) (sat_cons (step450 p h) (sat_cons (step458 p h) (sat_cons (step437 p h) (sat_cons (step439 p h) (sat_cons (step435 p h) (sat_cons (step37 p h) (sat_cons (step27 p h) (sat_cons (step23 p h) (sat_nil p)))))))))))))))))
def c816 : List Lit := [(1309, true), (22, false), (85, false)]
theorem step816 (p : Nat → Bool) (h : Constraints p) : clause p c816 = true :=
  Snake9.LocalRup.prove_clause [c249, c437, c439, c434, c435, c36, c13, c19] c816 (by decide) p (sat_cons (step249 p h) (sat_cons (step437 p h) (sat_cons (step439 p h) (sat_cons (step434 p h) (sat_cons (step435 p h) (sat_cons (step36 p h) (sat_cons (step13 p h) (sat_cons (step19 p h) (sat_nil p)))))))))
def c817 : List Lit := [(1316, true), (88, false)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true :=
  Snake9.LocalRup.prove_clause [c254, c448, c450, c445, c446, c442, c48, c58, c55] c817 (by decide) p (sat_cons (step254 p h) (sat_cons (step448 p h) (sat_cons (step450 p h) (sat_cons (step445 p h) (sat_cons (step446 p h) (sat_cons (step442 p h) (sat_cons (step48 p h) (sat_cons (step58 p h) (sat_cons (step55 p h) (sat_nil p))))))))))
def c818 : List Lit := [(1316, false), (1328, true)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true :=
  Snake9.LocalRup.prove_clause [c250, c249, c467, c454, c458, c470, c437, c439, c431, c434, c435, c430, c31, c428, c23, c19, c742] c818 (by decide) p (sat_cons (step250 p h) (sat_cons (step249 p h) (sat_cons (step467 p h) (sat_cons (step454 p h) (sat_cons (step458 p h) (sat_cons (step470 p h) (sat_cons (step437 p h) (sat_cons (step439 p h) (sat_cons (step431 p h) (sat_cons (step434 p h) (sat_cons (step435 p h) (sat_cons (step430 p h) (sat_cons (step31 p h) (sat_cons (step428 p h) (sat_cons (step23 p h) (sat_cons (step19 p h) (sat_cons (step742 p h) (sat_nil p))))))))))))))))))
def c819 : List Lit := [(1398, true)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true :=
  Snake9.LocalRup.prove_clause [c813, c812, c254, c545, c549, c539, c818, c448, c450, c445, c446, c442, c48, c55, c56, c57, c784, c484, c494, c485] c819 (by decide) p (sat_cons (step813 p h) (sat_cons (step812 p h) (sat_cons (step254 p h) (sat_cons (step545 p h) (sat_cons (step549 p h) (sat_cons (step539 p h) (sat_cons (step818 p h) (sat_cons (step448 p h) (sat_cons (step450 p h) (sat_cons (step445 p h) (sat_cons (step446 p h) (sat_cons (step442 p h) (sat_cons (step48 p h) (sat_cons (step55 p h) (sat_cons (step56 p h) (sat_cons (step57 p h) (sat_cons (step784 p h) (sat_cons (step484 p h) (sat_cons (step494 p h) (sat_cons (step485 p h) (sat_nil p)))))))))))))))))))))
def c820 : List Lit := [(1526, false)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true :=
  Snake9.LocalRup.prove_clause [c819, c741, c735] c820 (by decide) p (sat_cons (step819 p h) (sat_cons (step741 p h) (sat_cons (step735 p h) (sat_nil p))))
def c821 : List Lit := [(1309, true), (1312, true)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true :=
  Snake9.LocalRup.prove_clause [c249, c443, c442, c437, c439, c434, c435, c34, c13, c19] c821 (by decide) p (sat_cons (step249 p h) (sat_cons (step443 p h) (sat_cons (step442 p h) (sat_cons (step437 p h) (sat_cons (step439 p h) (sat_cons (step434 p h) (sat_cons (step435 p h) (sat_cons (step34 p h) (sat_cons (step13 p h) (sat_cons (step19 p h) (sat_nil p)))))))))))
end B112E090
