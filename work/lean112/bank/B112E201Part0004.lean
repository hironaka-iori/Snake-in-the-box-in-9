import B112E201Part0003
namespace B112E201
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c928 : List Lit := [(15, false), (1338, true), (14, false)]
theorem step928 (p : Nat → Bool) (h : Constraints p) : clause p c928 = true :=
  Snake9.LocalRup.prove_clause [c443, c920, c38] c928 (by decide) p (sat_cons (step443 p h) (sat_cons (step920 p h) (sat_cons (step38 p h) (sat_nil p))))
def c929 : List Lit := [(1370, true), (14, false), (1352, false)]
theorem step929 (p : Nat → Bool) (h : Constraints p) : clause p c929 = true :=
  Snake9.TreeRup.prove_clause [c819, c731, c815, c708, c887, c705, c667, c197, c855, c222, c775, c874, c162, c478, c711, c475, c89, c907, c911, c916, c502, c503, c724, c538, c499, c497, c492, c663, c105, c512, c653, c659, c897, c905, c908, c589, c664, c657, c596, c597, c539, c543, c638, c882, c593, c594, c150, c531, c461, c635, c95, c469, c152, c153, c488, c474, c159, c151, c926, c435, c456, c927, c67, c439, c447, c448, c458, c443, c436, c898, c928, c592, c434, c899, c40, c566, c567, c585, c579, c571, c144, c50, c85, c622, c623, c633, c617, c641, c161, c608, c601, c603] c929 (by decide) p (sat_cons (step819 p h) (sat_cons (step731 p h) (sat_cons (step815 p h) (sat_cons (step708 p h) (sat_cons (step887 p h) (sat_cons (step705 p h) (sat_cons (step667 p h) (sat_cons (step197 p h) (sat_cons (step855 p h) (sat_cons (step222 p h) (sat_cons (step775 p h) (sat_cons (step874 p h) (sat_cons (step162 p h) (sat_cons (step478 p h) (sat_cons (step711 p h) (sat_cons (step475 p h) (sat_cons (step89 p h) (sat_cons (step907 p h) (sat_cons (step911 p h) (sat_cons (step916 p h) (sat_cons (step502 p h) (sat_cons (step503 p h) (sat_cons (step724 p h) (sat_cons (step538 p h) (sat_cons (step499 p h) (sat_cons (step497 p h) (sat_cons (step492 p h) (sat_cons (step663 p h) (sat_cons (step105 p h) (sat_cons (step512 p h) (sat_cons (step653 p h) (sat_cons (step659 p h) (sat_cons (step897 p h) (sat_cons (step905 p h) (sat_cons (step908 p h) (sat_cons (step589 p h) (sat_cons (step664 p h) (sat_cons (step657 p h) (sat_cons (step596 p h) (sat_cons (step597 p h) (sat_cons (step539 p h) (sat_cons (step543 p h) (sat_cons (step638 p h) (sat_cons (step882 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step150 p h) (sat_cons (step531 p h) (sat_cons (step461 p h) (sat_cons (step635 p h) (sat_cons (step95 p h) (sat_cons (step469 p h) (sat_cons (step152 p h) (sat_cons (step153 p h) (sat_cons (step488 p h) (sat_cons (step474 p h) (sat_cons (step159 p h) (sat_cons (step151 p h) (sat_cons (step926 p h) (sat_cons (step435 p h) (sat_cons (step456 p h) (sat_cons (step927 p h) (sat_cons (step67 p h) (sat_cons (step439 p h) (sat_cons (step447 p h) (sat_cons (step448 p h) (sat_cons (step458 p h) (sat_cons (step443 p h) (sat_cons (step436 p h) (sat_cons (step898 p h) (sat_cons (step928 p h) (sat_cons (step592 p h) (sat_cons (step434 p h) (sat_cons (step899 p h) (sat_cons (step40 p h) (sat_cons (step566 p h) (sat_cons (step567 p h) (sat_cons (step585 p h) (sat_cons (step579 p h) (sat_cons (step571 p h) (sat_cons (step144 p h) (sat_cons (step50 p h) (sat_cons (step85 p h) (sat_cons (step622 p h) (sat_cons (step623 p h) (sat_cons (step633 p h) (sat_cons (step617 p h) (sat_cons (step641 p h) (sat_cons (step161 p h) (sat_cons (step608 p h) (sat_cons (step601 p h) (sat_cons (step603 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c930 : List Lit := [(20, false), (1352, false), (17, false), (14, false)]
theorem step930 (p : Nat → Bool) (h : Constraints p) : clause p c930 = true :=
  Snake9.LocalRup.prove_clause [c929, c45, c44, c569, c925, c576] c930 (by decide) p (sat_cons (step929 p h) (sat_cons (step45 p h) (sat_cons (step44 p h) (sat_cons (step569 p h) (sat_cons (step925 p h) (sat_cons (step576 p h) (sat_nil p)))))))
def c931 : List Lit := [(1353, false)]
theorem step931 (p : Nat → Bool) (h : Constraints p) : clause p c931 = true :=
  Snake9.LocalRup.prove_clause [c728, c889, c726, c708, c869, c674, c813, c202, c895, c814, c846, c200, c815, c667, c542, c544, c663, c523, c653, c510, c908, c884, c702, c112, c113, c115, c101, c110, c490, c108, c492, c105, c512, c897, c905, c664, c657, c543, c882, c527, c714] c931 (by decide) p (sat_cons (step728 p h) (sat_cons (step889 p h) (sat_cons (step726 p h) (sat_cons (step708 p h) (sat_cons (step869 p h) (sat_cons (step674 p h) (sat_cons (step813 p h) (sat_cons (step202 p h) (sat_cons (step895 p h) (sat_cons (step814 p h) (sat_cons (step846 p h) (sat_cons (step200 p h) (sat_cons (step815 p h) (sat_cons (step667 p h) (sat_cons (step542 p h) (sat_cons (step544 p h) (sat_cons (step663 p h) (sat_cons (step523 p h) (sat_cons (step653 p h) (sat_cons (step510 p h) (sat_cons (step908 p h) (sat_cons (step884 p h) (sat_cons (step702 p h) (sat_cons (step112 p h) (sat_cons (step113 p h) (sat_cons (step115 p h) (sat_cons (step101 p h) (sat_cons (step110 p h) (sat_cons (step490 p h) (sat_cons (step108 p h) (sat_cons (step492 p h) (sat_cons (step105 p h) (sat_cons (step512 p h) (sat_cons (step897 p h) (sat_cons (step905 p h) (sat_cons (step664 p h) (sat_cons (step657 p h) (sat_cons (step543 p h) (sat_cons (step882 p h) (sat_cons (step527 p h) (sat_cons (step714 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c932 : List Lit := [(1346, false)]
theorem step932 (p : Nat → Bool) (h : Constraints p) : clause p c932 = true :=
  Snake9.LocalRup.prove_clause [c931, c461] c932 (by decide) p (sat_cons (step931 p h) (sat_cons (step461 p h) (sat_nil p)))
def c933 : List Lit := [(1342, false)]
theorem step933 (p : Nat → Bool) (h : Constraints p) : clause p c933 = true :=
  Snake9.LocalRup.prove_clause [c932, c453] c933 (by decide) p (sat_cons (step932 p h) (sat_cons (step453 p h) (sat_nil p)))
def c934 : List Lit := [(1337, false), (16, true)]
theorem step934 (p : Nat → Bool) (h : Constraints p) : clause p c934 = true :=
  Snake9.LocalRup.prove_clause [c933, c932, c449, c450, c456, c920, c435, c433] c934 (by decide) p (sat_cons (step933 p h) (sat_cons (step932 p h) (sat_cons (step449 p h) (sat_cons (step450 p h) (sat_cons (step456 p h) (sat_cons (step920 p h) (sat_cons (step435 p h) (sat_cons (step433 p h) (sat_nil p)))))))))
def c935 : List Lit := [(22, true), (16, true), (14, false)]
theorem step935 (p : Nat → Bool) (h : Constraints p) : clause p c935 = true :=
  Snake9.TreeRup.prove_clause [c931, c889, c672, c699, c774, c758, c185, c180, c188, c772, c869, c189, c796, c813, c674, c895, c187, c202, c814, c846, c200, c815, c199, c667, c708, c887, c875, c855, c222, c874, c932, c934, c439, c447, c458, c924, c460, c463, c540, c427, c421, c4, c232, c6, c441, c930, c53, c52, c33, c35, c669, c58, c32, c714, c73, c63, c928, c529, c60, c448, c510, c76, c456, c884, c70, c435, c112, c101, c68, c115, c490, c110, c492, c108, c512, c105, c527, c102, c897, c538, c664, c663, c539, c653, c659, c528, c647, c908, c517, c903, c596, c597, c495, c905, c594, c657, c152, c153, c638, c159, c151, c635, c926] c935 (by decide) p (sat_cons (step931 p h) (sat_cons (step889 p h) (sat_cons (step672 p h) (sat_cons (step699 p h) (sat_cons (step774 p h) (sat_cons (step758 p h) (sat_cons (step185 p h) (sat_cons (step180 p h) (sat_cons (step188 p h) (sat_cons (step772 p h) (sat_cons (step869 p h) (sat_cons (step189 p h) (sat_cons (step796 p h) (sat_cons (step813 p h) (sat_cons (step674 p h) (sat_cons (step895 p h) (sat_cons (step187 p h) (sat_cons (step202 p h) (sat_cons (step814 p h) (sat_cons (step846 p h) (sat_cons (step200 p h) (sat_cons (step815 p h) (sat_cons (step199 p h) (sat_cons (step667 p h) (sat_cons (step708 p h) (sat_cons (step887 p h) (sat_cons (step875 p h) (sat_cons (step855 p h) (sat_cons (step222 p h) (sat_cons (step874 p h) (sat_cons (step932 p h) (sat_cons (step934 p h) (sat_cons (step439 p h) (sat_cons (step447 p h) (sat_cons (step458 p h) (sat_cons (step924 p h) (sat_cons (step460 p h) (sat_cons (step463 p h) (sat_cons (step540 p h) (sat_cons (step427 p h) (sat_cons (step421 p h) (sat_cons (step4 p h) (sat_cons (step232 p h) (sat_cons (step6 p h) (sat_cons (step441 p h) (sat_cons (step930 p h) (sat_cons (step53 p h) (sat_cons (step52 p h) (sat_cons (step33 p h) (sat_cons (step35 p h) (sat_cons (step669 p h) (sat_cons (step58 p h) (sat_cons (step32 p h) (sat_cons (step714 p h) (sat_cons (step73 p h) (sat_cons (step63 p h) (sat_cons (step928 p h) (sat_cons (step529 p h) (sat_cons (step60 p h) (sat_cons (step448 p h) (sat_cons (step510 p h) (sat_cons (step76 p h) (sat_cons (step456 p h) (sat_cons (step884 p h) (sat_cons (step70 p h) (sat_cons (step435 p h) (sat_cons (step112 p h) (sat_cons (step101 p h) (sat_cons (step68 p h) (sat_cons (step115 p h) (sat_cons (step490 p h) (sat_cons (step110 p h) (sat_cons (step492 p h) (sat_cons (step108 p h) (sat_cons (step512 p h) (sat_cons (step105 p h) (sat_cons (step527 p h) (sat_cons (step102 p h) (sat_cons (step897 p h) (sat_cons (step538 p h) (sat_cons (step664 p h) (sat_cons (step663 p h) (sat_cons (step539 p h) (sat_cons (step653 p h) (sat_cons (step659 p h) (sat_cons (step528 p h) (sat_cons (step647 p h) (sat_cons (step908 p h) (sat_cons (step517 p h) (sat_cons (step903 p h) (sat_cons (step596 p h) (sat_cons (step597 p h) (sat_cons (step495 p h) (sat_cons (step905 p h) (sat_cons (step594 p h) (sat_cons (step657 p h) (sat_cons (step152 p h) (sat_cons (step153 p h) (sat_cons (step638 p h) (sat_cons (step159 p h) (sat_cons (step151 p h) (sat_cons (step635 p h) (sat_cons (step926 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c936 : List Lit := [(17, true), (19, false), (47, false), (1352, false), (20, false), (22, false)]
theorem step936 (p : Nat → Bool) (h : Constraints p) : clause p c936 = true :=
  Snake9.LocalRup.prove_clause [c889, c774, c188, c869, c813, c674, c895, c202, c814, c846, c200, c815, c199, c667, c708, c855, c222, c540, c53, c52, c54, c714, c73, c529, c510, c884, c112, c101, c115, c490, c110, c492, c108, c512, c105, c527, c102, c538, c663, c653, c908, c596, c597, c593, c594, c150, c67, c152, c927, c159] c936 (by decide) p (sat_cons (step889 p h) (sat_cons (step774 p h) (sat_cons (step188 p h) (sat_cons (step869 p h) (sat_cons (step813 p h) (sat_cons (step674 p h) (sat_cons (step895 p h) (sat_cons (step202 p h) (sat_cons (step814 p h) (sat_cons (step846 p h) (sat_cons (step200 p h) (sat_cons (step815 p h) (sat_cons (step199 p h) (sat_cons (step667 p h) (sat_cons (step708 p h) (sat_cons (step855 p h) (sat_cons (step222 p h) (sat_cons (step540 p h) (sat_cons (step53 p h) (sat_cons (step52 p h) (sat_cons (step54 p h) (sat_cons (step714 p h) (sat_cons (step73 p h) (sat_cons (step529 p h) (sat_cons (step510 p h) (sat_cons (step884 p h) (sat_cons (step112 p h) (sat_cons (step101 p h) (sat_cons (step115 p h) (sat_cons (step490 p h) (sat_cons (step110 p h) (sat_cons (step492 p h) (sat_cons (step108 p h) (sat_cons (step512 p h) (sat_cons (step105 p h) (sat_cons (step527 p h) (sat_cons (step102 p h) (sat_cons (step538 p h) (sat_cons (step663 p h) (sat_cons (step653 p h) (sat_cons (step908 p h) (sat_cons (step596 p h) (sat_cons (step597 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step150 p h) (sat_cons (step67 p h) (sat_cons (step152 p h) (sat_cons (step927 p h) (sat_cons (step159 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c937 : List Lit := [(31, true), (17, false), (14, true), (47, false), (1352, false), (22, false)]
theorem step937 (p : Nat → Bool) (h : Constraints p) : clause p c937 = true :=
  Snake9.LocalRup.prove_clause [c889, c869, c813, c674, c895, c202, c814, c846, c200, c815, c199, c667, c708, c855, c222, c182, c540, c468, c714, c529, c510, c884, c112, c101, c115, c490, c110, c492, c108, c512, c105, c527, c102, c897, c538, c664, c663, c539, c653, c531, c908, c596, c597, c593, c594, c150, c152, c153, c159, c151, c927, c48, c67, c711, c473, c487] c937 (by decide) p (sat_cons (step889 p h) (sat_cons (step869 p h) (sat_cons (step813 p h) (sat_cons (step674 p h) (sat_cons (step895 p h) (sat_cons (step202 p h) (sat_cons (step814 p h) (sat_cons (step846 p h) (sat_cons (step200 p h) (sat_cons (step815 p h) (sat_cons (step199 p h) (sat_cons (step667 p h) (sat_cons (step708 p h) (sat_cons (step855 p h) (sat_cons (step222 p h) (sat_cons (step182 p h) (sat_cons (step540 p h) (sat_cons (step468 p h) (sat_cons (step714 p h) (sat_cons (step529 p h) (sat_cons (step510 p h) (sat_cons (step884 p h) (sat_cons (step112 p h) (sat_cons (step101 p h) (sat_cons (step115 p h) (sat_cons (step490 p h) (sat_cons (step110 p h) (sat_cons (step492 p h) (sat_cons (step108 p h) (sat_cons (step512 p h) (sat_cons (step105 p h) (sat_cons (step527 p h) (sat_cons (step102 p h) (sat_cons (step897 p h) (sat_cons (step538 p h) (sat_cons (step664 p h) (sat_cons (step663 p h) (sat_cons (step539 p h) (sat_cons (step653 p h) (sat_cons (step531 p h) (sat_cons (step908 p h) (sat_cons (step596 p h) (sat_cons (step597 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step150 p h) (sat_cons (step152 p h) (sat_cons (step153 p h) (sat_cons (step159 p h) (sat_cons (step151 p h) (sat_cons (step927 p h) (sat_cons (step48 p h) (sat_cons (step67 p h) (sat_cons (step711 p h) (sat_cons (step473 p h) (sat_cons (step487 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c938 : List Lit := [(1524, true), (48, false), (1509, false)]
theorem step938 (p : Nat → Bool) (h : Constraints p) : clause p c938 = true :=
  Snake9.LocalRup.prove_clause [c708, c653, c657, c908, c905, c702] c938 (by decide) p (sat_cons (step708 p h) (sat_cons (step653 p h) (sat_cons (step657 p h) (sat_cons (step908 p h) (sat_cons (step905 p h) (sat_cons (step702 p h) (sat_nil p)))))))
def c939 : List Lit := [(31, false), (14, true), (1352, false), (20, false)]
theorem step939 (p : Nat → Bool) (h : Constraints p) : clause p c939 = true :=
  Snake9.LocalRup.prove_clause [c727, c708, c726, c869, c813, c674, c202, c814, c846, c200, c815, c667, c774, c796, c932, c725, c882, c652, c664, c539, c523, c510, c884, c112, c115, c110, c108, c105, c938, c663, c538, c527, c877, c72, c51, c69, c54, c74, c432, c442, c438, c445, c458] c939 (by decide) p (sat_cons (step727 p h) (sat_cons (step708 p h) (sat_cons (step726 p h) (sat_cons (step869 p h) (sat_cons (step813 p h) (sat_cons (step674 p h) (sat_cons (step202 p h) (sat_cons (step814 p h) (sat_cons (step846 p h) (sat_cons (step200 p h) (sat_cons (step815 p h) (sat_cons (step667 p h) (sat_cons (step774 p h) (sat_cons (step796 p h) (sat_cons (step932 p h) (sat_cons (step725 p h) (sat_cons (step882 p h) (sat_cons (step652 p h) (sat_cons (step664 p h) (sat_cons (step539 p h) (sat_cons (step523 p h) (sat_cons (step510 p h) (sat_cons (step884 p h) (sat_cons (step112 p h) (sat_cons (step115 p h) (sat_cons (step110 p h) (sat_cons (step108 p h) (sat_cons (step105 p h) (sat_cons (step938 p h) (sat_cons (step663 p h) (sat_cons (step538 p h) (sat_cons (step527 p h) (sat_cons (step877 p h) (sat_cons (step72 p h) (sat_cons (step51 p h) (sat_cons (step69 p h) (sat_cons (step54 p h) (sat_cons (step74 p h) (sat_cons (step432 p h) (sat_cons (step442 p h) (sat_cons (step438 p h) (sat_cons (step445 p h) (sat_cons (step458 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c940 : List Lit := [(17, false), (1352, false), (20, false), (22, false)]
theorem step940 (p : Nat → Bool) (h : Constraints p) : clause p c940 = true :=
  Snake9.LocalRup.prove_clause [c889, c674, c813, c869, c540, c930, c939, c714, c937, c529, c113, c510, c884] c940 (by decide) p (sat_cons (step889 p h) (sat_cons (step674 p h) (sat_cons (step813 p h) (sat_cons (step869 p h) (sat_cons (step540 p h) (sat_cons (step930 p h) (sat_cons (step939 p h) (sat_cons (step714 p h) (sat_cons (step937 p h) (sat_cons (step529 p h) (sat_cons (step113 p h) (sat_cons (step510 p h) (sat_cons (step884 p h) (sat_nil p))))))))))))))
def c941 : List Lit := [(1352, false), (20, false), (22, false)]
theorem step941 (p : Nat → Bool) (h : Constraints p) : clause p c941 = true :=
  Snake9.LocalRup.prove_clause [c889, c774, c184, c869, c674, c813, c540, c940, c53, c52, c669, c714, c55, c529, c936, c510, c113, c884] c941 (by decide) p (sat_cons (step889 p h) (sat_cons (step774 p h) (sat_cons (step184 p h) (sat_cons (step869 p h) (sat_cons (step674 p h) (sat_cons (step813 p h) (sat_cons (step540 p h) (sat_cons (step940 p h) (sat_cons (step53 p h) (sat_cons (step52 p h) (sat_cons (step669 p h) (sat_cons (step714 p h) (sat_cons (step55 p h) (sat_cons (step529 p h) (sat_cons (step936 p h) (sat_cons (step510 p h) (sat_cons (step113 p h) (sat_cons (step884 p h) (sat_nil p)))))))))))))))))))
def c942 : List Lit := [(1345, true)]
theorem step942 (p : Nat → Bool) (h : Constraints p) : clause p c942 = true :=
  Snake9.LocalRup.prove_clause [c457, c924] c942 (by decide) p (sat_cons (step457 p h) (sat_cons (step924 p h) (sat_nil p)))
def c943 : List Lit := [(1352, true)]
theorem step943 (p : Nat → Bool) (h : Constraints p) : clause p c943 = true :=
  Snake9.LocalRup.prove_clause [c942, c460] c943 (by decide) p (sat_cons (step942 p h) (sat_cons (step460 p h) (sat_nil p)))
def c944 : List Lit := [(1325, false)]
theorem step944 (p : Nat → Bool) (h : Constraints p) : clause p c944 = true :=
  Snake9.LocalRup.prove_clause [c942, c931, c463] c944 (by decide) p (sat_cons (step942 p h) (sat_cons (step931 p h) (sat_cons (step463 p h) (sat_nil p))))
def c945 : List Lit := [(1415, true)]
theorem step945 (p : Nat → Bool) (h : Constraints p) : clause p c945 = true :=
  Snake9.LocalRup.prove_clause [c943, c728, c537] c945 (by decide) p (sat_cons (step943 p h) (sat_cons (step728 p h) (sat_cons (step537 p h) (sat_nil p))))
def c946 : List Lit := [(1404, false)]
theorem step946 (p : Nat → Bool) (h : Constraints p) : clause p c946 = true :=
  Snake9.LocalRup.prove_clause [c943, c889, c540] c946 (by decide) p (sat_cons (step943 p h) (sat_cons (step889 p h) (sat_cons (step540 p h) (sat_nil p))))
def c947 : List Lit := [(1317, false)]
theorem step947 (p : Nat → Bool) (h : Constraints p) : clause p c947 = true :=
  Snake9.LocalRup.prove_clause [c944, c427] c947 (by decide) p (sat_cons (step944 p h) (sat_cons (step427 p h) (sat_nil p)))
def c948 : List Lit := [(1525, false)]
theorem step948 (p : Nat → Bool) (h : Constraints p) : clause p c948 = true :=
  Snake9.LocalRup.prove_clause [c945, c667, c662] c948 (by decide) p (sat_cons (step945 p h) (sat_cons (step667 p h) (sat_cons (step662 p h) (sat_nil p))))
def c949 : List Lit := [(2, true)]
theorem step949 (p : Nat → Bool) (h : Constraints p) : clause p c949 = true :=
  Snake9.LocalRup.prove_clause [c947, c421] c949 (by decide) p (sat_cons (step947 p h) (sat_cons (step421 p h) (sat_nil p)))
def c950 : List Lit := [(111, true)]
theorem step950 (p : Nat → Bool) (h : Constraints p) : clause p c950 = true :=
  Snake9.LocalRup.prove_clause [c949, c672, c4] c950 (by decide) p (sat_cons (step949 p h) (sat_cons (step672 p h) (sat_cons (step4 p h) (sat_nil p))))
def c951 : List Lit := [(112, false)]
theorem step951 (p : Nat → Bool) (h : Constraints p) : clause p c951 = true :=
  Snake9.LocalRup.prove_clause [c950, c699, c232] c951 (by decide) p (sat_cons (step950 p h) (sat_cons (step699 p h) (sat_cons (step232 p h) (sat_nil p))))
def c952 : List Lit := [(47, true)]
theorem step952 (p : Nat → Bool) (h : Constraints p) : clause p c952 = true :=
  Snake9.LocalRup.prove_clause [c951, c895, c6] c952 (by decide) p (sat_cons (step951 p h) (sat_cons (step895 p h) (sat_cons (step6 p h) (sat_nil p))))
def c953 : List Lit := [(31, true), (22, false)]
theorem step953 (p : Nat → Bool) (h : Constraints p) : clause p c953 = true :=
  Snake9.LocalRup.prove_clause [c946, c869, c813, c674, c895, c952, c202, c814, c846, c200, c815, c667, c943, c708, c855, c222, c468, c714, c529, c510, c884, c112, c101, c115, c490, c110, c492, c108, c512, c105, c527, c897, c538, c664, c663, c539, c653, c531, c908, c488, c596, c597, c593, c594, c149, c152, c159, c927, c67, c474, c473, c469, c487, c711] c953 (by decide) p (sat_cons (step946 p h) (sat_cons (step869 p h) (sat_cons (step813 p h) (sat_cons (step674 p h) (sat_cons (step895 p h) (sat_cons (step952 p h) (sat_cons (step202 p h) (sat_cons (step814 p h) (sat_cons (step846 p h) (sat_cons (step200 p h) (sat_cons (step815 p h) (sat_cons (step667 p h) (sat_cons (step943 p h) (sat_cons (step708 p h) (sat_cons (step855 p h) (sat_cons (step222 p h) (sat_cons (step468 p h) (sat_cons (step714 p h) (sat_cons (step529 p h) (sat_cons (step510 p h) (sat_cons (step884 p h) (sat_cons (step112 p h) (sat_cons (step101 p h) (sat_cons (step115 p h) (sat_cons (step490 p h) (sat_cons (step110 p h) (sat_cons (step492 p h) (sat_cons (step108 p h) (sat_cons (step512 p h) (sat_cons (step105 p h) (sat_cons (step527 p h) (sat_cons (step897 p h) (sat_cons (step538 p h) (sat_cons (step664 p h) (sat_cons (step663 p h) (sat_cons (step539 p h) (sat_cons (step653 p h) (sat_cons (step531 p h) (sat_cons (step908 p h) (sat_cons (step488 p h) (sat_cons (step596 p h) (sat_cons (step597 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step149 p h) (sat_cons (step152 p h) (sat_cons (step159 p h) (sat_cons (step927 p h) (sat_cons (step67 p h) (sat_cons (step474 p h) (sat_cons (step473 p h) (sat_cons (step469 p h) (sat_cons (step487 p h) (sat_cons (step711 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c954 : List Lit := [(1471, true), (22, false)]
theorem step954 (p : Nat → Bool) (h : Constraints p) : clause p c954 = true :=
  Snake9.LocalRup.prove_clause [c708, c726, c869, c674, c813, c202, c814, c200, c846, c815, c667, c943, c727, c855, c796, c953, c725, c882, c652, c664, c539, c523, c510, c884, c112, c115, c110, c108, c105, c938, c663, c538, c527, c877, c593, c594, c67, c152, c70, c71, c78] c954 (by decide) p (sat_cons (step708 p h) (sat_cons (step726 p h) (sat_cons (step869 p h) (sat_cons (step674 p h) (sat_cons (step813 p h) (sat_cons (step202 p h) (sat_cons (step814 p h) (sat_cons (step200 p h) (sat_cons (step846 p h) (sat_cons (step815 p h) (sat_cons (step667 p h) (sat_cons (step943 p h) (sat_cons (step727 p h) (sat_cons (step855 p h) (sat_cons (step796 p h) (sat_cons (step953 p h) (sat_cons (step725 p h) (sat_cons (step882 p h) (sat_cons (step652 p h) (sat_cons (step664 p h) (sat_cons (step539 p h) (sat_cons (step523 p h) (sat_cons (step510 p h) (sat_cons (step884 p h) (sat_cons (step112 p h) (sat_cons (step115 p h) (sat_cons (step110 p h) (sat_cons (step108 p h) (sat_cons (step105 p h) (sat_cons (step938 p h) (sat_cons (step663 p h) (sat_cons (step538 p h) (sat_cons (step527 p h) (sat_cons (step877 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step67 p h) (sat_cons (step152 p h) (sat_cons (step70 p h) (sat_cons (step71 p h) (sat_cons (step78 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c955 : List Lit := [(22, false)]
theorem step955 (p : Nat → Bool) (h : Constraints p) : clause p c955 = true :=
  Snake9.TreeRup.prove_clause [c727, c708, c726, c869, c813, c674, c202, c814, c846, c200, c815, c667, c943, c794, c948, c932, c941, c440, c447, c458, c953, c725, c882, c652, c664, c539, c523, c510, c884, c112, c115, c110, c108, c105, c938, c663, c538, c527, c911, c483, c475, c479, c478, c481, c477, c485, c470, c467, c82, c84, c954, c596, c908, c658, c905, c576, c569, c570, c46, c437, c438, c456, c432, c433, c448, c43, c920] c955 (by decide) p (sat_cons (step727 p h) (sat_cons (step708 p h) (sat_cons (step726 p h) (sat_cons (step869 p h) (sat_cons (step813 p h) (sat_cons (step674 p h) (sat_cons (step202 p h) (sat_cons (step814 p h) (sat_cons (step846 p h) (sat_cons (step200 p h) (sat_cons (step815 p h) (sat_cons (step667 p h) (sat_cons (step943 p h) (sat_cons (step794 p h) (sat_cons (step948 p h) (sat_cons (step932 p h) (sat_cons (step941 p h) (sat_cons (step440 p h) (sat_cons (step447 p h) (sat_cons (step458 p h) (sat_cons (step953 p h) (sat_cons (step725 p h) (sat_cons (step882 p h) (sat_cons (step652 p h) (sat_cons (step664 p h) (sat_cons (step539 p h) (sat_cons (step523 p h) (sat_cons (step510 p h) (sat_cons (step884 p h) (sat_cons (step112 p h) (sat_cons (step115 p h) (sat_cons (step110 p h) (sat_cons (step108 p h) (sat_cons (step105 p h) (sat_cons (step938 p h) (sat_cons (step663 p h) (sat_cons (step538 p h) (sat_cons (step527 p h) (sat_cons (step911 p h) (sat_cons (step483 p h) (sat_cons (step475 p h) (sat_cons (step479 p h) (sat_cons (step478 p h) (sat_cons (step481 p h) (sat_cons (step477 p h) (sat_cons (step485 p h) (sat_cons (step470 p h) (sat_cons (step467 p h) (sat_cons (step82 p h) (sat_cons (step84 p h) (sat_cons (step954 p h) (sat_cons (step596 p h) (sat_cons (step908 p h) (sat_cons (step658 p h) (sat_cons (step905 p h) (sat_cons (step576 p h) (sat_cons (step569 p h) (sat_cons (step570 p h) (sat_cons (step46 p h) (sat_cons (step437 p h) (sat_cons (step438 p h) (sat_cons (step456 p h) (sat_cons (step432 p h) (sat_cons (step433 p h) (sat_cons (step448 p h) (sat_cons (step43 p h) (sat_cons (step920 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c956 : List Lit := [(1336, true)]
theorem step956 (p : Nat → Bool) (h : Constraints p) : clause p c956 = true :=
  Snake9.LocalRup.prove_clause [c955, c439] c956 (by decide) p (sat_cons (step955 p h) (sat_cons (step439 p h) (sat_nil p)))
def c957 : List Lit := [(1340, true)]
theorem step957 (p : Nat → Bool) (h : Constraints p) : clause p c957 = true :=
  Snake9.LocalRup.prove_clause [c956, c447] c957 (by decide) p (sat_cons (step956 p h) (sat_cons (step447 p h) (sat_nil p)))
def c958 : List Lit := [(1334, false)]
theorem step958 (p : Nat → Bool) (h : Constraints p) : clause p c958 = true :=
  Snake9.LocalRup.prove_clause [c957, c932, c458] c958 (by decide) p (sat_cons (step957 p h) (sat_cons (step932 p h) (sat_cons (step458 p h) (sat_nil p))))
def c959 : List Lit := [(1332, false)]
theorem step959 (p : Nat → Bool) (h : Constraints p) : clause p c959 = true :=
  Snake9.LocalRup.prove_clause [c958, c436] c959 (by decide) p (sat_cons (step958 p h) (sat_cons (step436 p h) (sat_nil p)))
def c960 : List Lit := [(79, false), (17, false), (34, false)]
theorem step960 (p : Nat → Bool) (h : Constraints p) : clause p c960 = true :=
  Snake9.LocalRup.prove_clause [c932, c955, c46, c47, c437, c441, c456, c449] c960 (by decide) p (sat_cons (step932 p h) (sat_cons (step955 p h) (sat_cons (step46 p h) (sat_cons (step47 p h) (sat_cons (step437 p h) (sat_cons (step441 p h) (sat_cons (step456 p h) (sat_cons (step449 p h) (sat_nil p)))))))))
def c961 : List Lit := [(31, false)]
theorem step961 (p : Nat → Bool) (h : Constraints p) : clause p c961 = true :=
  Snake9.TreeRup.prove_clause [c727, c708, c726, c869, c813, c674, c202, c814, c846, c200, c815, c667, c943, c794, c820, c948, c725, c882, c652, c664, c539, c523, c510, c884, c112, c115, c110, c108, c105, c938, c663, c538, c527, c911, c483, c475, c479, c478, c481, c477, c485, c470, c467, c82, c84, c86, c960, c569, c576, c905, c658, c908, c596, c597, c594, c168, c169, c170, c915, c617, c624, c626, c605, c620, c630, c608, c634, c642] c961 (by decide) p (sat_cons (step727 p h) (sat_cons (step708 p h) (sat_cons (step726 p h) (sat_cons (step869 p h) (sat_cons (step813 p h) (sat_cons (step674 p h) (sat_cons (step202 p h) (sat_cons (step814 p h) (sat_cons (step846 p h) (sat_cons (step200 p h) (sat_cons (step815 p h) (sat_cons (step667 p h) (sat_cons (step943 p h) (sat_cons (step794 p h) (sat_cons (step820 p h) (sat_cons (step948 p h) (sat_cons (step725 p h) (sat_cons (step882 p h) (sat_cons (step652 p h) (sat_cons (step664 p h) (sat_cons (step539 p h) (sat_cons (step523 p h) (sat_cons (step510 p h) (sat_cons (step884 p h) (sat_cons (step112 p h) (sat_cons (step115 p h) (sat_cons (step110 p h) (sat_cons (step108 p h) (sat_cons (step105 p h) (sat_cons (step938 p h) (sat_cons (step663 p h) (sat_cons (step538 p h) (sat_cons (step527 p h) (sat_cons (step911 p h) (sat_cons (step483 p h) (sat_cons (step475 p h) (sat_cons (step479 p h) (sat_cons (step478 p h) (sat_cons (step481 p h) (sat_cons (step477 p h) (sat_cons (step485 p h) (sat_cons (step470 p h) (sat_cons (step467 p h) (sat_cons (step82 p h) (sat_cons (step84 p h) (sat_cons (step86 p h) (sat_cons (step960 p h) (sat_cons (step569 p h) (sat_cons (step576 p h) (sat_cons (step905 p h) (sat_cons (step658 p h) (sat_cons (step908 p h) (sat_cons (step596 p h) (sat_cons (step597 p h) (sat_cons (step594 p h) (sat_cons (step168 p h) (sat_cons (step169 p h) (sat_cons (step170 p h) (sat_cons (step915 p h) (sat_cons (step617 p h) (sat_cons (step624 p h) (sat_cons (step626 p h) (sat_cons (step605 p h) (sat_cons (step620 p h) (sat_cons (step630 p h) (sat_cons (step608 p h) (sat_cons (step634 p h) (sat_cons (step642 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c962 : List Lit := [(1374, true)]
theorem step962 (p : Nat → Bool) (h : Constraints p) : clause p c962 = true :=
  Snake9.LocalRup.prove_clause [c961, c714] c962 (by decide) p (sat_cons (step961 p h) (sat_cons (step714 p h) (sat_nil p)))
def c963 : List Lit := [(1395, false)]
theorem step963 (p : Nat → Bool) (h : Constraints p) : clause p c963 = true :=
  Snake9.LocalRup.prove_clause [c962, c946, c529] c963 (by decide) p (sat_cons (step962 p h) (sat_cons (step946 p h) (sat_cons (step529 p h) (sat_nil p))))
def c964 : List Lit := [(1390, false)]
theorem step964 (p : Nat → Bool) (h : Constraints p) : clause p c964 = true :=
  Snake9.LocalRup.prove_clause [c963, c869, c510] c964 (by decide) p (sat_cons (step963 p h) (sat_cons (step869 p h) (sat_cons (step510 p h) (sat_nil p))))
def c965 : List Lit := [(53, true)]
theorem step965 (p : Nat → Bool) (h : Constraints p) : clause p c965 = true :=
  Snake9.LocalRup.prove_clause [c964, c884] c965 (by decide) p (sat_cons (step964 p h) (sat_cons (step884 p h) (sat_nil p)))
def c966 : List Lit := [(54, true)]
theorem step966 (p : Nat → Bool) (h : Constraints p) : clause p c966 = true :=
  Snake9.LocalRup.prove_clause [c965, c674, c813, c112] c966 (by decide) p (sat_cons (step965 p h) (sat_cons (step674 p h) (sat_cons (step813 p h) (sat_cons (step112 p h) (sat_nil p)))))
def c967 : List Lit := [(45, false)]
theorem step967 (p : Nat → Bool) (h : Constraints p) : clause p c967 = true :=
  Snake9.LocalRup.prove_clause [c965, c952, c895, c101] c967 (by decide) p (sat_cons (step965 p h) (sat_cons (step952 p h) (sat_cons (step895 p h) (sat_cons (step101 p h) (sat_nil p)))))
def c968 : List Lit := [(51, true)]
theorem step968 (p : Nat → Bool) (h : Constraints p) : clause p c968 = true :=
  Snake9.LocalRup.prove_clause [c966, c202, c115] c968 (by decide) p (sat_cons (step966 p h) (sat_cons (step202 p h) (sat_cons (step115 p h) (sat_nil p))))
def c969 : List Lit := [(1380, true)]
theorem step969 (p : Nat → Bool) (h : Constraints p) : clause p c969 = true :=
  Snake9.LocalRup.prove_clause [c967, c846, c490] c969 (by decide) p (sat_cons (step967 p h) (sat_cons (step846 p h) (sat_cons (step490 p h) (sat_nil p))))
def c970 : List Lit := [(50, true)]
theorem step970 (p : Nat → Bool) (h : Constraints p) : clause p c970 = true :=
  Snake9.LocalRup.prove_clause [c968, c814, c110] c970 (by decide) p (sat_cons (step968 p h) (sat_cons (step814 p h) (sat_cons (step110 p h) (sat_nil p))))
def c971 : List Lit := [(1382, true)]
theorem step971 (p : Nat → Bool) (h : Constraints p) : clause p c971 = true :=
  Snake9.LocalRup.prove_clause [c969, c492] c971 (by decide) p (sat_cons (step969 p h) (sat_cons (step492 p h) (sat_nil p)))
def c972 : List Lit := [(49, true)]
theorem step972 (p : Nat → Bool) (h : Constraints p) : clause p c972 = true :=
  Snake9.LocalRup.prove_clause [c970, c200, c846, c108] c972 (by decide) p (sat_cons (step970 p h) (sat_cons (step200 p h) (sat_cons (step846 p h) (sat_cons (step108 p h) (sat_nil p)))))
def c973 : List Lit := [(1393, true)]
theorem step973 (p : Nat → Bool) (h : Constraints p) : clause p c973 = true :=
  Snake9.LocalRup.prove_clause [c971, c512] c973 (by decide) p (sat_cons (step971 p h) (sat_cons (step512 p h) (sat_nil p)))
def c974 : List Lit := [(48, true)]
theorem step974 (p : Nat → Bool) (h : Constraints p) : clause p c974 = true :=
  Snake9.LocalRup.prove_clause [c972, c815, c105] c974 (by decide) p (sat_cons (step972 p h) (sat_cons (step815 p h) (sat_cons (step105 p h) (sat_nil p))))
def c975 : List Lit := [(1402, true)]
theorem step975 (p : Nat → Bool) (h : Constraints p) : clause p c975 = true :=
  Snake9.LocalRup.prove_clause [c973, c962, c527] c975 (by decide) p (sat_cons (step973 p h) (sat_cons (step962 p h) (sat_cons (step527 p h) (sat_nil p))))
def c976 : List Lit := [(57, true)]
theorem step976 (p : Nat → Bool) (h : Constraints p) : clause p c976 = true :=
  Snake9.LocalRup.prove_clause [c974, c199, c102] c976 (by decide) p (sat_cons (step974 p h) (sat_cons (step199 p h) (sat_cons (step102 p h) (sat_nil p))))
def c977 : List Lit := [(1523, true)]
theorem step977 (p : Nat → Bool) (h : Constraints p) : clause p c977 = true :=
  Snake9.LocalRup.prove_clause [c974, c897] c977 (by decide) p (sat_cons (step974 p h) (sat_cons (step897 p h) (sat_nil p)))
def c978 : List Lit := [(1416, true)]
theorem step978 (p : Nat → Bool) (h : Constraints p) : clause p c978 = true :=
  Snake9.LocalRup.prove_clause [c975, c943, c538] c978 (by decide) p (sat_cons (step975 p h) (sat_cons (step943 p h) (sat_cons (step538 p h) (sat_nil p))))
def c979 : List Lit := [(1417, false)]
theorem step979 (p : Nat → Bool) (h : Constraints p) : clause p c979 = true :=
  Snake9.LocalRup.prove_clause [c977, c667, c664] c979 (by decide) p (sat_cons (step977 p h) (sat_cons (step667 p h) (sat_cons (step664 p h) (sat_nil p))))
def c980 : List Lit := [(1524, false)]
theorem step980 (p : Nat → Bool) (h : Constraints p) : clause p c980 = true :=
  Snake9.LocalRup.prove_clause [c978, c667, c663] c980 (by decide) p (sat_cons (step978 p h) (sat_cons (step667 p h) (sat_cons (step663 p h) (sat_nil p))))
def c981 : List Lit := [(1403, false)]
theorem step981 (p : Nat → Bool) (h : Constraints p) : clause p c981 = true :=
  Snake9.LocalRup.prove_clause [c979, c943, c539] c981 (by decide) p (sat_cons (step979 p h) (sat_cons (step943 p h) (sat_cons (step539 p h) (sat_nil p))))
def c982 : List Lit := [(1510, false)]
theorem step982 (p : Nat → Bool) (h : Constraints p) : clause p c982 = true :=
  Snake9.LocalRup.prove_clause [c980, c708, c653] c982 (by decide) p (sat_cons (step980 p h) (sat_cons (step708 p h) (sat_cons (step653 p h) (sat_nil p))))
def c983 : List Lit := [(1462, false)]
theorem step983 (p : Nat → Bool) (h : Constraints p) : clause p c983 = true :=
  Snake9.LocalRup.prove_clause [c980, c887, c659] c983 (by decide) p (sat_cons (step980 p h) (sat_cons (step887 p h) (sat_cons (step659 p h) (sat_nil p))))
def c984 : List Lit := [(1509, false)]
theorem step984 (p : Nat → Bool) (h : Constraints p) : clause p c984 = true :=
  Snake9.LocalRup.prove_clause [c980, c974, c938] c984 (by decide) p (sat_cons (step980 p h) (sat_cons (step974 p h) (sat_cons (step938 p h) (sat_nil p))))
def c985 : List Lit := [(1394, false)]
theorem step985 (p : Nat → Bool) (h : Constraints p) : clause p c985 = true :=
  Snake9.LocalRup.prove_clause [c981, c962, c528] c985 (by decide) p (sat_cons (step981 p h) (sat_cons (step962 p h) (sat_cons (step528 p h) (sat_nil p))))
def c986 : List Lit := [(1483, false)]
theorem step986 (p : Nat → Bool) (h : Constraints p) : clause p c986 = true :=
  Snake9.LocalRup.prove_clause [c982, c875, c647] c986 (by decide) p (sat_cons (step982 p h) (sat_cons (step875 p h) (sat_cons (step647 p h) (sat_nil p))))
def c987 : List Lit := [(1473, false)]
theorem step987 (p : Nat → Bool) (h : Constraints p) : clause p c987 = true :=
  Snake9.LocalRup.prove_clause [c982, c908] c987 (by decide) p (sat_cons (step982 p h) (sat_cons (step908 p h) (sat_nil p)))
def c988 : List Lit := [(1454, false)]
theorem step988 (p : Nat → Bool) (h : Constraints p) : clause p c988 = true :=
  Snake9.LocalRup.prove_clause [c983, c705, c589] c988 (by decide) p (sat_cons (step983 p h) (sat_cons (step705 p h) (sat_cons (step589 p h) (sat_nil p))))
def c989 : List Lit := [(1502, false)]
theorem step989 (p : Nat → Bool) (h : Constraints p) : clause p c989 = true :=
  Snake9.LocalRup.prove_clause [c984, c638] c989 (by decide) p (sat_cons (step984 p h) (sat_cons (step638 p h) (sat_nil p)))
def c990 : List Lit := [(1383, false)]
theorem step990 (p : Nat → Bool) (h : Constraints p) : clause p c990 = true :=
  Snake9.LocalRup.prove_clause [c985, c517] c990 (by decide) p (sat_cons (step985 p h) (sat_cons (step517 p h) (sat_nil p)))
def c991 : List Lit := [(1448, true)]
theorem step991 (p : Nat → Bool) (h : Constraints p) : clause p c991 = true :=
  Snake9.LocalRup.prove_clause [c986, c961, c958, c903] c991 (by decide) p (sat_cons (step986 p h) (sat_cons (step961 p h) (sat_cons (step958 p h) (sat_cons (step903 p h) (sat_nil p)))))
end B112E201
