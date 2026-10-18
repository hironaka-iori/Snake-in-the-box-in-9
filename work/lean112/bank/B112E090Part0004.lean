import B112E090Part0003
namespace B112E090
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1014 : List Lit := [(75, false), (66, false), (61, false)]
theorem step1014 (p : Nat → Bool) (h : Constraints p) : clause p c1014 = true :=
  Snake9.LocalRup.prove_clause [c275, c181, c162] c1014 (by decide) p (sat_cons (step275 p h) (sat_cons (step181 p h) (sat_cons (step162 p h) (sat_nil p))))
def c1015 : List Lit := [(1453, true), (1436, false), (61, false), (68, true), (54, false)]
theorem step1015 (p : Nat → Bool) (h : Constraints p) : clause p c1015 = true :=
  Snake9.LocalRup.prove_clause [c606, c598, c811, c619, c612, c922, c1014, c600, c602, c609, c618, c622, c630, c847, c806, c846, c576, c574] c1015 (by decide) p (sat_cons (step606 p h) (sat_cons (step598 p h) (sat_cons (step811 p h) (sat_cons (step619 p h) (sat_cons (step612 p h) (sat_cons (step922 p h) (sat_cons (step1014 p h) (sat_cons (step600 p h) (sat_cons (step602 p h) (sat_cons (step609 p h) (sat_cons (step618 p h) (sat_cons (step622 p h) (sat_cons (step630 p h) (sat_cons (step847 p h) (sat_cons (step806 p h) (sat_cons (step846 p h) (sat_cons (step576 p h) (sat_cons (step574 p h) (sat_nil p)))))))))))))))))))
def c1016 : List Lit := [(1496, false), (1376, false), (50, false)]
theorem step1016 (p : Nat → Bool) (h : Constraints p) : clause p c1016 = true :=
  Snake9.LocalRup.prove_clause [c741, c798, c909, c737, c1009, c936, c948, c1010, c1013, c1012, c1011, c1015, c727, c885, c704, c645, c664, c642, c643, c996, c860, c650] c1016 (by decide) p (sat_cons (step741 p h) (sat_cons (step798 p h) (sat_cons (step909 p h) (sat_cons (step737 p h) (sat_cons (step1009 p h) (sat_cons (step936 p h) (sat_cons (step948 p h) (sat_cons (step1010 p h) (sat_cons (step1013 p h) (sat_cons (step1012 p h) (sat_cons (step1011 p h) (sat_cons (step1015 p h) (sat_cons (step727 p h) (sat_cons (step885 p h) (sat_cons (step704 p h) (sat_cons (step645 p h) (sat_cons (step664 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step996 p h) (sat_cons (step860 p h) (sat_cons (step650 p h) (sat_nil p)))))))))))))))))))))))
def c1017 : List Lit := [(1463, true), (1424, true), (1376, false), (50, false)]
theorem step1017 (p : Nat → Bool) (h : Constraints p) : clause p c1017 = true :=
  Snake9.LocalRup.prove_clause [c278, c282, c741, c426, c255, c1016, c854, c653, c798, c909, c737, c936, c948, c1010, c1013, c1012, c1011, c1015, c727, c706, c665, c661, c939, c642, c643, c860, c883, c209, c650, c652, c660, c996, c655, c664, c669, c227, c703, c647, c194, c726, c835, c738, c424, c552, c346, c537, c312, c786, c493, c869, c309, c486, c784, c308, c481, c65, c307, c45, c306, c68] c1017 (by decide) p (sat_cons (step278 p h) (sat_cons (step282 p h) (sat_cons (step741 p h) (sat_cons (step426 p h) (sat_cons (step255 p h) (sat_cons (step1016 p h) (sat_cons (step854 p h) (sat_cons (step653 p h) (sat_cons (step798 p h) (sat_cons (step909 p h) (sat_cons (step737 p h) (sat_cons (step936 p h) (sat_cons (step948 p h) (sat_cons (step1010 p h) (sat_cons (step1013 p h) (sat_cons (step1012 p h) (sat_cons (step1011 p h) (sat_cons (step1015 p h) (sat_cons (step727 p h) (sat_cons (step706 p h) (sat_cons (step665 p h) (sat_cons (step661 p h) (sat_cons (step939 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step860 p h) (sat_cons (step883 p h) (sat_cons (step209 p h) (sat_cons (step650 p h) (sat_cons (step652 p h) (sat_cons (step660 p h) (sat_cons (step996 p h) (sat_cons (step655 p h) (sat_cons (step664 p h) (sat_cons (step669 p h) (sat_cons (step227 p h) (sat_cons (step703 p h) (sat_cons (step647 p h) (sat_cons (step194 p h) (sat_cons (step726 p h) (sat_cons (step835 p h) (sat_cons (step738 p h) (sat_cons (step424 p h) (sat_cons (step552 p h) (sat_cons (step346 p h) (sat_cons (step537 p h) (sat_cons (step312 p h) (sat_cons (step786 p h) (sat_cons (step493 p h) (sat_cons (step869 p h) (sat_cons (step309 p h) (sat_cons (step486 p h) (sat_cons (step784 p h) (sat_cons (step308 p h) (sat_cons (step481 p h) (sat_cons (step65 p h) (sat_cons (step307 p h) (sat_cons (step45 p h) (sat_cons (step306 p h) (sat_cons (step68 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1018 : List Lit := [(1424, true), (50, false), (44, true), (48, true)]
theorem step1018 (p : Nat → Bool) (h : Constraints p) : clause p c1018 = true :=
  Snake9.LocalRup.prove_clause [c262, c741, c990, c1016, c693, c681, c678, c798, c909, c737, c936, c939, c948, c1010, c1013, c95, c1012, c506, c1011, c515, c1015, c727, c706, c1017, c645, c945, c669, c726, c996, c738, c651, c817, c818, c552, c799, c537, c529, c786, c486, c481, c851, c791, c503, c525, c789, c516, c950, c507] c1018 (by decide) p (sat_cons (step262 p h) (sat_cons (step741 p h) (sat_cons (step990 p h) (sat_cons (step1016 p h) (sat_cons (step693 p h) (sat_cons (step681 p h) (sat_cons (step678 p h) (sat_cons (step798 p h) (sat_cons (step909 p h) (sat_cons (step737 p h) (sat_cons (step936 p h) (sat_cons (step939 p h) (sat_cons (step948 p h) (sat_cons (step1010 p h) (sat_cons (step1013 p h) (sat_cons (step95 p h) (sat_cons (step1012 p h) (sat_cons (step506 p h) (sat_cons (step1011 p h) (sat_cons (step515 p h) (sat_cons (step1015 p h) (sat_cons (step727 p h) (sat_cons (step706 p h) (sat_cons (step1017 p h) (sat_cons (step645 p h) (sat_cons (step945 p h) (sat_cons (step669 p h) (sat_cons (step726 p h) (sat_cons (step996 p h) (sat_cons (step738 p h) (sat_cons (step651 p h) (sat_cons (step817 p h) (sat_cons (step818 p h) (sat_cons (step552 p h) (sat_cons (step799 p h) (sat_cons (step537 p h) (sat_cons (step529 p h) (sat_cons (step786 p h) (sat_cons (step486 p h) (sat_cons (step481 p h) (sat_cons (step851 p h) (sat_cons (step791 p h) (sat_cons (step503 p h) (sat_cons (step525 p h) (sat_cons (step789 p h) (sat_cons (step516 p h) (sat_cons (step950 p h) (sat_cons (step507 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c1019 : List Lit := [(1465, false), (1506, true), (1330, true), (1453, false), (1376, false)]
theorem step1019 (p : Nat → Bool) (h : Constraints p) : clause p c1019 = true :=
  Snake9.LocalRup.prove_clause [c741, c255, c253, c798, c909, c737, c727, c706, c945, c1006, c726, c651, c738, c817, c557, c818, c552, c537, c786, c493, c869, c485, c486, c478, c784, c483, c481, c782, c66, c906, c918, c913, c52, c458, c14, c471, c428, c431, c430] c1019 (by decide) p (sat_cons (step741 p h) (sat_cons (step255 p h) (sat_cons (step253 p h) (sat_cons (step798 p h) (sat_cons (step909 p h) (sat_cons (step737 p h) (sat_cons (step727 p h) (sat_cons (step706 p h) (sat_cons (step945 p h) (sat_cons (step1006 p h) (sat_cons (step726 p h) (sat_cons (step651 p h) (sat_cons (step738 p h) (sat_cons (step817 p h) (sat_cons (step557 p h) (sat_cons (step818 p h) (sat_cons (step552 p h) (sat_cons (step537 p h) (sat_cons (step786 p h) (sat_cons (step493 p h) (sat_cons (step869 p h) (sat_cons (step485 p h) (sat_cons (step486 p h) (sat_cons (step478 p h) (sat_cons (step784 p h) (sat_cons (step483 p h) (sat_cons (step481 p h) (sat_cons (step782 p h) (sat_cons (step66 p h) (sat_cons (step906 p h) (sat_cons (step918 p h) (sat_cons (step913 p h) (sat_cons (step52 p h) (sat_cons (step458 p h) (sat_cons (step14 p h) (sat_cons (step471 p h) (sat_cons (step428 p h) (sat_cons (step431 p h) (sat_cons (step430 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1020 : List Lit := [(91, true), (85, false), (83, false), (84, true), (1453, false), (1376, false), (50, false), (48, true)]
theorem step1020 (p : Nat → Bool) (h : Constraints p) : clause p c1020 = true :=
  Snake9.LocalRup.prove_clause [c282, c741, c426, c255, c278, c1016, c854, c653, c798, c909, c737, c727, c706, c665, c661, c693, c681, c678, c650, c652, c660, c996, c817, c655, c664, c818, c227, c703, c194, c726, c835, c738, c424, c552, c346, c799, c537, c312, c786, c493, c869, c309, c486, c784, c308, c481, c65, c307, c851, c306, c791, c68, c525, c45, c964, c209] c1020 (by decide) p (sat_cons (step282 p h) (sat_cons (step741 p h) (sat_cons (step426 p h) (sat_cons (step255 p h) (sat_cons (step278 p h) (sat_cons (step1016 p h) (sat_cons (step854 p h) (sat_cons (step653 p h) (sat_cons (step798 p h) (sat_cons (step909 p h) (sat_cons (step737 p h) (sat_cons (step727 p h) (sat_cons (step706 p h) (sat_cons (step665 p h) (sat_cons (step661 p h) (sat_cons (step693 p h) (sat_cons (step681 p h) (sat_cons (step678 p h) (sat_cons (step650 p h) (sat_cons (step652 p h) (sat_cons (step660 p h) (sat_cons (step996 p h) (sat_cons (step817 p h) (sat_cons (step655 p h) (sat_cons (step664 p h) (sat_cons (step818 p h) (sat_cons (step227 p h) (sat_cons (step703 p h) (sat_cons (step194 p h) (sat_cons (step726 p h) (sat_cons (step835 p h) (sat_cons (step738 p h) (sat_cons (step424 p h) (sat_cons (step552 p h) (sat_cons (step346 p h) (sat_cons (step799 p h) (sat_cons (step537 p h) (sat_cons (step312 p h) (sat_cons (step786 p h) (sat_cons (step493 p h) (sat_cons (step869 p h) (sat_cons (step309 p h) (sat_cons (step486 p h) (sat_cons (step784 p h) (sat_cons (step308 p h) (sat_cons (step481 p h) (sat_cons (step65 p h) (sat_cons (step307 p h) (sat_cons (step851 p h) (sat_cons (step306 p h) (sat_cons (step791 p h) (sat_cons (step68 p h) (sat_cons (step525 p h) (sat_cons (step45 p h) (sat_cons (step964 p h) (sat_cons (step209 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1021 : List Lit := [(84, true), (1453, false), (1424, false), (1376, false), (50, false), (48, true)]
theorem step1021 (p : Nat → Bool) (h : Constraints p) : clause p c1021 = true :=
  Snake9.LocalRup.prove_clause [c284, c281, c278, c741, c245, c260, c798, c1016, c854, c653, c656, c663, c699, c725, c739, c562, c693, c681, c679, c239, c909, c737, c1011, c606, c613, c633, c723, c1019, c645, c647, c642, c643, c1008, c1020, c860, c228, c224, c207, c212, c938, c964, c442, c815, c997, c450, c467, c729, c738, c557, c552, c935, c799, c427, c525, c3, c791, c934, c84] c1021 (by decide) p (sat_cons (step284 p h) (sat_cons (step281 p h) (sat_cons (step278 p h) (sat_cons (step741 p h) (sat_cons (step245 p h) (sat_cons (step260 p h) (sat_cons (step798 p h) (sat_cons (step1016 p h) (sat_cons (step854 p h) (sat_cons (step653 p h) (sat_cons (step656 p h) (sat_cons (step663 p h) (sat_cons (step699 p h) (sat_cons (step725 p h) (sat_cons (step739 p h) (sat_cons (step562 p h) (sat_cons (step693 p h) (sat_cons (step681 p h) (sat_cons (step679 p h) (sat_cons (step239 p h) (sat_cons (step909 p h) (sat_cons (step737 p h) (sat_cons (step1011 p h) (sat_cons (step606 p h) (sat_cons (step613 p h) (sat_cons (step633 p h) (sat_cons (step723 p h) (sat_cons (step1019 p h) (sat_cons (step645 p h) (sat_cons (step647 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step1008 p h) (sat_cons (step1020 p h) (sat_cons (step860 p h) (sat_cons (step228 p h) (sat_cons (step224 p h) (sat_cons (step207 p h) (sat_cons (step212 p h) (sat_cons (step938 p h) (sat_cons (step964 p h) (sat_cons (step442 p h) (sat_cons (step815 p h) (sat_cons (step997 p h) (sat_cons (step450 p h) (sat_cons (step467 p h) (sat_cons (step729 p h) (sat_cons (step738 p h) (sat_cons (step557 p h) (sat_cons (step552 p h) (sat_cons (step935 p h) (sat_cons (step799 p h) (sat_cons (step427 p h) (sat_cons (step525 p h) (sat_cons (step3 p h) (sat_cons (step791 p h) (sat_cons (step934 p h) (sat_cons (step84 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1022 : List Lit := [(1401, true), (85, false), (84, false), (1376, false), (50, false)]
theorem step1022 (p : Nat → Bool) (h : Constraints p) : clause p c1022 = true :=
  Snake9.LocalRup.prove_clause [c250, c201, c434, c437, c753, c883, c798, c557, c552, c468, c537, c905, c458, c462, c471, c438, c994, c440, c431, c436, c205, c430, c24, c428, c12] c1022 (by decide) p (sat_cons (step250 p h) (sat_cons (step201 p h) (sat_cons (step434 p h) (sat_cons (step437 p h) (sat_cons (step753 p h) (sat_cons (step883 p h) (sat_cons (step798 p h) (sat_cons (step557 p h) (sat_cons (step552 p h) (sat_cons (step468 p h) (sat_cons (step537 p h) (sat_cons (step905 p h) (sat_cons (step458 p h) (sat_cons (step462 p h) (sat_cons (step471 p h) (sat_cons (step438 p h) (sat_cons (step994 p h) (sat_cons (step440 p h) (sat_cons (step431 p h) (sat_cons (step436 p h) (sat_cons (step205 p h) (sat_cons (step430 p h) (sat_cons (step24 p h) (sat_cons (step428 p h) (sat_cons (step12 p h) (sat_nil p))))))))))))))))))))))))))
def c1023 : List Lit := [(1418, true), (84, false), (50, false)]
theorem step1023 (p : Nat → Bool) (h : Constraints p) : clause p c1023 = true :=
  Snake9.LocalRup.prove_clause [c268, c576, c578, c574, c570, c571, c926, c151, c115] c1023 (by decide) p (sat_cons (step268 p h) (sat_cons (step576 p h) (sat_cons (step578 p h) (sat_cons (step574 p h) (sat_cons (step570 p h) (sat_cons (step571 p h) (sat_cons (step926 p h) (sat_cons (step151 p h) (sat_cons (step115 p h) (sat_nil p))))))))))
def c1024 : List Lit := [(1523, true), (1418, false), (1453, false), (1424, false), (1376, false), (50, false)]
theorem step1024 (p : Nat → Bool) (h : Constraints p) : clause p c1024 = true :=
  Snake9.LocalRup.prove_clause [c741, c798, c1016, c854, c653, c656, c663, c699, c725, c739, c562, c632, c729, c718, c1019, c645, c642, c643, c1008, c958] c1024 (by decide) p (sat_cons (step741 p h) (sat_cons (step798 p h) (sat_cons (step1016 p h) (sat_cons (step854 p h) (sat_cons (step653 p h) (sat_cons (step656 p h) (sat_cons (step663 p h) (sat_cons (step699 p h) (sat_cons (step725 p h) (sat_cons (step739 p h) (sat_cons (step562 p h) (sat_cons (step632 p h) (sat_cons (step729 p h) (sat_cons (step718 p h) (sat_cons (step1019 p h) (sat_cons (step645 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step1008 p h) (sat_cons (step958 p h) (sat_nil p)))))))))))))))))))))
def c1025 : List Lit := [(1453, false), (1424, false), (1376, false), (50, false), (48, true)]
theorem step1025 (p : Nat → Bool) (h : Constraints p) : clause p c1025 = true :=
  Snake9.LocalRup.prove_clause [c741, c1016, c854, c653, c656, c663, c699, c798, c909, c737, c725, c727, c739, c562, c1021, c1023, c1024, c738, c1022, c643, c645, c874, c1019, c604, c723, c606, c633, c613] c1025 (by decide) p (sat_cons (step741 p h) (sat_cons (step1016 p h) (sat_cons (step854 p h) (sat_cons (step653 p h) (sat_cons (step656 p h) (sat_cons (step663 p h) (sat_cons (step699 p h) (sat_cons (step798 p h) (sat_cons (step909 p h) (sat_cons (step737 p h) (sat_cons (step725 p h) (sat_cons (step727 p h) (sat_cons (step739 p h) (sat_cons (step562 p h) (sat_cons (step1021 p h) (sat_cons (step1023 p h) (sat_cons (step1024 p h) (sat_cons (step738 p h) (sat_cons (step1022 p h) (sat_cons (step643 p h) (sat_cons (step645 p h) (sat_cons (step874 p h) (sat_cons (step1019 p h) (sat_cons (step604 p h) (sat_cons (step723 p h) (sat_cons (step606 p h) (sat_cons (step633 p h) (sat_cons (step613 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1026 : List Lit := [(1442, true), (50, false)]
theorem step1026 (p : Nat → Bool) (h : Constraints p) : clause p c1026 = true :=
  Snake9.LocalRup.prove_clause [c271, c613, c616, c608, c596, c598, c601, c594, c182, c168, c169, c752] c1026 (by decide) p (sat_cons (step271 p h) (sat_cons (step613 p h) (sat_cons (step616 p h) (sat_cons (step608 p h) (sat_cons (step596 p h) (sat_cons (step598 p h) (sat_cons (step601 p h) (sat_cons (step594 p h) (sat_cons (step182 p h) (sat_cons (step168 p h) (sat_cons (step169 p h) (sat_cons (step752 p h) (sat_nil p)))))))))))))
def c1027 : List Lit := [(1436, true), (1401, true), (1506, true), (1463, false), (1376, false)]
theorem step1027 (p : Nat → Bool) (h : Constraints p) : clause p c1027 = true :=
  Snake9.LocalRup.prove_clause [c280, c603, c604, c873, c651, c817, c191, c818, c218, c552, c869, c537] c1027 (by decide) p (sat_cons (step280 p h) (sat_cons (step603 p h) (sat_cons (step604 p h) (sat_cons (step873 p h) (sat_cons (step651 p h) (sat_cons (step817 p h) (sat_cons (step191 p h) (sat_cons (step818 p h) (sat_cons (step218 p h) (sat_cons (step552 p h) (sat_cons (step869 p h) (sat_cons (step537 p h) (sat_nil p)))))))))))))
def c1028 : List Lit := [(1436, false), (1443, true), (50, false)]
theorem step1028 (p : Nat → Bool) (h : Constraints p) : clause p c1028 = true :=
  Snake9.LocalRup.prove_clause [c271, c614, c606, c960, c609, c617, c601, c596, c598, c594, c182, c752, c168] c1028 (by decide) p (sat_cons (step271 p h) (sat_cons (step614 p h) (sat_cons (step606 p h) (sat_cons (step960 p h) (sat_cons (step609 p h) (sat_cons (step617 p h) (sat_cons (step601 p h) (sat_cons (step596 p h) (sat_cons (step598 p h) (sat_cons (step594 p h) (sat_cons (step182 p h) (sat_cons (step752 p h) (sat_cons (step168 p h) (sat_nil p))))))))))))))
def c1029 : List Lit := [(50, false), (44, true), (48, true)]
theorem step1029 (p : Nat → Bool) (h : Constraints p) : clause p c1029 = true :=
  Snake9.LocalRup.prove_clause [c741, c990, c798, c909, c737, c1018, c1025, c634, c1008, c643, c1026, c633, c723, c1028, c604, c1027, c874, c738, c722] c1029 (by decide) p (sat_cons (step741 p h) (sat_cons (step990 p h) (sat_cons (step798 p h) (sat_cons (step909 p h) (sat_cons (step737 p h) (sat_cons (step1018 p h) (sat_cons (step1025 p h) (sat_cons (step634 p h) (sat_cons (step1008 p h) (sat_cons (step643 p h) (sat_cons (step1026 p h) (sat_cons (step633 p h) (sat_cons (step723 p h) (sat_cons (step1028 p h) (sat_cons (step604 p h) (sat_cons (step1027 p h) (sat_cons (step874 p h) (sat_cons (step738 p h) (sat_cons (step722 p h) (sat_nil p))))))))))))))))))))
def c1030 : List Lit := [(1424, false), (1436, true), (1523, true), (1506, true), (1463, false), (1371, false)]
theorem step1030 (p : Nat → Bool) (h : Constraints p) : clause p c1030 = true :=
  Snake9.TreeRup.prove_clause [c280, c741, c274, c260, c284, c277, c604, c873, c651, c603, c191, c218, c869, c817, c818, c874, c722, c636, c645, c989, c945, c794, c632, c942, c633, c717, c596, c598, c613, c739, c593, c594, c608, c553, c601, c541, c538, c182, c870, c525, c179, c481, c501, c791, c171, c789, c83, c87, c804, c678, c850, c680, c588, c681, c648, c238, c239, c923, c693, c187, c757, c107, c707, c197, c669, c194, c657, c655] c1030 (by decide) p (sat_cons (step280 p h) (sat_cons (step741 p h) (sat_cons (step274 p h) (sat_cons (step260 p h) (sat_cons (step284 p h) (sat_cons (step277 p h) (sat_cons (step604 p h) (sat_cons (step873 p h) (sat_cons (step651 p h) (sat_cons (step603 p h) (sat_cons (step191 p h) (sat_cons (step218 p h) (sat_cons (step869 p h) (sat_cons (step817 p h) (sat_cons (step818 p h) (sat_cons (step874 p h) (sat_cons (step722 p h) (sat_cons (step636 p h) (sat_cons (step645 p h) (sat_cons (step989 p h) (sat_cons (step945 p h) (sat_cons (step794 p h) (sat_cons (step632 p h) (sat_cons (step942 p h) (sat_cons (step633 p h) (sat_cons (step717 p h) (sat_cons (step596 p h) (sat_cons (step598 p h) (sat_cons (step613 p h) (sat_cons (step739 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step608 p h) (sat_cons (step553 p h) (sat_cons (step601 p h) (sat_cons (step541 p h) (sat_cons (step538 p h) (sat_cons (step182 p h) (sat_cons (step870 p h) (sat_cons (step525 p h) (sat_cons (step179 p h) (sat_cons (step481 p h) (sat_cons (step501 p h) (sat_cons (step791 p h) (sat_cons (step171 p h) (sat_cons (step789 p h) (sat_cons (step83 p h) (sat_cons (step87 p h) (sat_cons (step804 p h) (sat_cons (step678 p h) (sat_cons (step850 p h) (sat_cons (step680 p h) (sat_cons (step588 p h) (sat_cons (step681 p h) (sat_cons (step648 p h) (sat_cons (step238 p h) (sat_cons (step239 p h) (sat_cons (step923 p h) (sat_cons (step693 p h) (sat_cons (step187 p h) (sat_cons (step757 p h) (sat_cons (step107 p h) (sat_cons (step707 p h) (sat_cons (step197 p h) (sat_cons (step669 p h) (sat_cons (step194 p h) (sat_cons (step657 p h) (sat_cons (step655 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1031 : List Lit := [(1442, true), (1424, true)]
theorem step1031 (p : Nat → Bool) (h : Constraints p) : clause p c1031 = true :=
  Snake9.LocalRup.prove_clause [c274, c807, c613, c616, c608, c596, c598, c600, c601, c593, c594, c182, c923, c179, c1014, c171, c570, c804, c578, c587] c1031 (by decide) p (sat_cons (step274 p h) (sat_cons (step807 p h) (sat_cons (step613 p h) (sat_cons (step616 p h) (sat_cons (step608 p h) (sat_cons (step596 p h) (sat_cons (step598 p h) (sat_cons (step600 p h) (sat_cons (step601 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step182 p h) (sat_cons (step923 p h) (sat_cons (step179 p h) (sat_cons (step1014 p h) (sat_cons (step171 p h) (sat_cons (step570 p h) (sat_cons (step804 p h) (sat_cons (step578 p h) (sat_cons (step587 p h) (sat_nil p)))))))))))))))))))))
def c1032 : List Lit := [(3, false), (1, true)]
theorem step1032 (p : Nat → Bool) (h : Constraints p) : clause p c1032 = true :=
  Snake9.LocalRup.prove_clause [c245, c3] c1032 (by decide) p (sat_cons (step245 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1033 : List Lit := [(4, false), (10, true)]
theorem step1033 (p : Nat → Bool) (h : Constraints p) : clause p c1033 = true :=
  Snake9.LocalRup.prove_clause [c246, c4] c1033 (by decide) p (sat_cons (step246 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1034 : List Lit := [(8, false), (7, true)]
theorem step1034 (p : Nat → Bool) (h : Constraints p) : clause p c1034 = true :=
  Snake9.LocalRup.prove_clause [c247, c9] c1034 (by decide) p (sat_cons (step247 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1035 : List Lit := [(9, false), (2, true)]
theorem step1035 (p : Nat → Bool) (h : Constraints p) : clause p c1035 = true :=
  Snake9.LocalRup.prove_clause [c248, c10] c1035 (by decide) p (sat_cons (step248 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1036 : List Lit := [(15, true), (19, true), (14, false)]
theorem step1036 (p : Nat → Bool) (h : Constraints p) : clause p c1036 = true :=
  Snake9.LocalRup.prove_clause [c249, c18] c1036 (by decide) p (sat_cons (step249 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1037 : List Lit := [(19, true), (17, true), (16, false)]
theorem step1037 (p : Nat → Bool) (h : Constraints p) : clause p c1037 = true :=
  Snake9.LocalRup.prove_clause [c250, c23] c1037 (by decide) p (sat_cons (step250 p h) (sat_cons (step23 p h) (sat_nil p)))
def c1038 : List Lit := [(11, true), (16, false), (19, true)]
theorem step1038 (p : Nat → Bool) (h : Constraints p) : clause p c1038 = true :=
  Snake9.LocalRup.prove_clause [c250, c24] c1038 (by decide) p (sat_cons (step250 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1039 : List Lit := [(18, false), (26, true), (84, true)]
theorem step1039 (p : Nat → Bool) (h : Constraints p) : clause p c1039 = true :=
  Snake9.LocalRup.prove_clause [c251, c28] c1039 (by decide) p (sat_cons (step251 p h) (sat_cons (step28 p h) (sat_nil p)))
def c1040 : List Lit := [(19, true), (18, false), (84, true)]
theorem step1040 (p : Nat → Bool) (h : Constraints p) : clause p c1040 = true :=
  Snake9.LocalRup.prove_clause [c251, c29] c1040 (by decide) p (sat_cons (step251 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1041 : List Lit := [(19, true), (18, false), (26, true)]
theorem step1041 (p : Nat → Bool) (h : Constraints p) : clause p c1041 = true :=
  Snake9.LocalRup.prove_clause [c251, c30] c1041 (by decide) p (sat_cons (step251 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1042 : List Lit := [(12, true), (23, false), (25, true)]
theorem step1042 (p : Nat → Bool) (h : Constraints p) : clause p c1042 = true :=
  Snake9.LocalRup.prove_clause [c253, c52] c1042 (by decide) p (sat_cons (step253 p h) (sat_cons (step52 p h) (sat_nil p)))
def c1043 : List Lit := [(21, true), (12, true), (23, false)]
theorem step1043 (p : Nat → Bool) (h : Constraints p) : clause p c1043 = true :=
  Snake9.LocalRup.prove_clause [c253, c53] c1043 (by decide) p (sat_cons (step253 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1044 : List Lit := [(21, true), (26, true), (24, false)]
theorem step1044 (p : Nat → Bool) (h : Constraints p) : clause p c1044 = true :=
  Snake9.LocalRup.prove_clause [c254, c54] c1044 (by decide) p (sat_cons (step254 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1045 : List Lit := [(21, true), (24, false), (25, true)]
theorem step1045 (p : Nat → Bool) (h : Constraints p) : clause p c1045 = true :=
  Snake9.LocalRup.prove_clause [c254, c55] c1045 (by decide) p (sat_cons (step254 p h) (sat_cons (step55 p h) (sat_nil p)))
def c1046 : List Lit := [(28, true), (25, true), (27, false)]
theorem step1046 (p : Nat → Bool) (h : Constraints p) : clause p c1046 = true :=
  Snake9.LocalRup.prove_clause [c255, c65] c1046 (by decide) p (sat_cons (step255 p h) (sat_cons (step65 p h) (sat_nil p)))
def c1047 : List Lit := [(26, true), (25, true), (27, false)]
theorem step1047 (p : Nat → Bool) (h : Constraints p) : clause p c1047 = true :=
  Snake9.LocalRup.prove_clause [c255, c66] c1047 (by decide) p (sat_cons (step255 p h) (sat_cons (step66 p h) (sat_nil p)))
def c1048 : List Lit := [(30, true), (12, true), (29, false)]
theorem step1048 (p : Nat → Bool) (h : Constraints p) : clause p c1048 = true :=
  Snake9.LocalRup.prove_clause [c256, c69] c1048 (by decide) p (sat_cons (step256 p h) (sat_cons (step69 p h) (sat_nil p)))
def c1049 : List Lit := [(40, false), (43, true)]
theorem step1049 (p : Nat → Bool) (h : Constraints p) : clause p c1049 = true :=
  Snake9.LocalRup.prove_clause [c260, c83] c1049 (by decide) p (sat_cons (step260 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1050 : List Lit := [(40, false), (41, true)]
theorem step1050 (p : Nat → Bool) (h : Constraints p) : clause p c1050 = true :=
  Snake9.LocalRup.prove_clause [c260, c84] c1050 (by decide) p (sat_cons (step260 p h) (sat_cons (step84 p h) (sat_nil p)))
def c1051 : List Lit := [(40, true), (33, true), (152, true), (43, false)]
theorem step1051 (p : Nat → Bool) (h : Constraints p) : clause p c1051 = true :=
  Snake9.LocalRup.prove_clause [c761, c88] c1051 (by decide) p (sat_cons (step761 p h) (sat_cons (step88 p h) (sat_nil p)))
def c1052 : List Lit := [(47, true), (51, true), (46, false)]
theorem step1052 (p : Nat → Bool) (h : Constraints p) : clause p c1052 = true :=
  Snake9.LocalRup.prove_clause [c262, c94] c1052 (by decide) p (sat_cons (step262 p h) (sat_cons (step94 p h) (sat_nil p)))
def c1053 : List Lit := [(49, true), (51, true), (48, false)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true :=
  Snake9.LocalRup.prove_clause [c263, c99] c1053 (by decide) p (sat_cons (step263 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1054 : List Lit := [(44, true), (51, true), (48, false)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true :=
  Snake9.LocalRup.prove_clause [c263, c100] c1054 (by decide) p (sat_cons (step263 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1055 : List Lit := [(49, true), (44, true), (48, false)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true :=
  Snake9.LocalRup.prove_clause [c263, c101] c1055 (by decide) p (sat_cons (step263 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1056 : List Lit := [(53, false), (162, true), (54, true)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true :=
  Snake9.LocalRup.prove_clause [c762, c140] c1056 (by decide) p (sat_cons (step762 p h) (sat_cons (step140 p h) (sat_nil p)))
def c1057 : List Lit := [(86, true), (69, true), (44, true), (54, false)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true :=
  Snake9.LocalRup.prove_clause [c265, c142] c1057 (by decide) p (sat_cons (step265 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1058 : List Lit := [(56, false), (57, true)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true :=
  Snake9.LocalRup.prove_clause [c267, c145] c1058 (by decide) p (sat_cons (step267 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1059 : List Lit := [(56, false), (53, true)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true :=
  Snake9.LocalRup.prove_clause [c267, c146] c1059 (by decide) p (sat_cons (step267 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1060 : List Lit := [(58, false), (59, true)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true :=
  Snake9.LocalRup.prove_clause [c268, c150] c1060 (by decide) p (sat_cons (step268 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1061 : List Lit := [(58, false), (57, true)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true :=
  Snake9.LocalRup.prove_clause [c268, c151] c1061 (by decide) p (sat_cons (step268 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1062 : List Lit := [(60, true), (63, false), (67, true)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true :=
  Snake9.LocalRup.prove_clause [c269, c158] c1062 (by decide) p (sat_cons (step269 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1063 : List Lit := [(60, true), (64, true), (63, false)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true :=
  Snake9.LocalRup.prove_clause [c269, c159] c1063 (by decide) p (sat_cons (step269 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1064 : List Lit := [(65, true), (49, true), (66, false)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true :=
  Snake9.LocalRup.prove_clause [c270, c164] c1064 (by decide) p (sat_cons (step270 p h) (sat_cons (step164 p h) (sat_nil p)))
def c1065 : List Lit := [(62, true), (49, true), (66, false)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true :=
  Snake9.LocalRup.prove_clause [c270, c165] c1065 (by decide) p (sat_cons (step270 p h) (sat_cons (step165 p h) (sat_nil p)))
def c1066 : List Lit := [(76, true), (51, true), (68, false)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true :=
  Snake9.LocalRup.prove_clause [c271, c169] c1066 (by decide) p (sat_cons (step271 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1067 : List Lit := [(71, false), (72, true)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true :=
  Snake9.LocalRup.prove_clause [c273, c174] c1067 (by decide) p (sat_cons (step273 p h) (sat_cons (step174 p h) (sat_nil p)))
def c1068 : List Lit := [(76, true), (69, true), (74, false)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true :=
  Snake9.LocalRup.prove_clause [c274, c179] c1068 (by decide) p (sat_cons (step274 p h) (sat_cons (step179 p h) (sat_nil p)))
def c1069 : List Lit := [(75, false), (73, true)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true :=
  Snake9.LocalRup.prove_clause [c275, c180] c1069 (by decide) p (sat_cons (step275 p h) (sat_cons (step180 p h) (sat_nil p)))
def c1070 : List Lit := [(77, true), (80, false), (84, true)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true :=
  Snake9.LocalRup.prove_clause [c276, c189] c1070 (by decide) p (sat_cons (step276 p h) (sat_cons (step189 p h) (sat_nil p)))
def c1071 : List Lit := [(81, true), (77, true), (80, false)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true :=
  Snake9.LocalRup.prove_clause [c276, c190] c1071 (by decide) p (sat_cons (step276 p h) (sat_cons (step190 p h) (sat_nil p)))
def c1072 : List Lit := [(82, true), (79, true), (83, false), (49, true)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true :=
  Snake9.LocalRup.prove_clause [c277, c197] c1072 (by decide) p (sat_cons (step277 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1073 : List Lit := [(82, true), (17, true), (79, true), (83, false)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true :=
  Snake9.LocalRup.prove_clause [c277, c198] c1073 (by decide) p (sat_cons (step277 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1074 : List Lit := [(93, true), (51, true), (85, false), (84, true)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true :=
  Snake9.LocalRup.prove_clause [c278, c207] c1074 (by decide) p (sat_cons (step278 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1075 : List Lit := [(86, true), (93, true), (87, false)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true :=
  Snake9.LocalRup.prove_clause [c279, c215] c1075 (by decide) p (sat_cons (step279 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1076 : List Lit := [(89, true), (25, true), (88, false)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true :=
  Snake9.LocalRup.prove_clause [c280, c217] c1076 (by decide) p (sat_cons (step280 p h) (sat_cons (step217 p h) (sat_nil p)))
def c1077 : List Lit := [(81, true), (25, true), (88, false)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true :=
  Snake9.LocalRup.prove_clause [c280, c218] c1077 (by decide) p (sat_cons (step280 p h) (sat_cons (step218 p h) (sat_nil p)))
end B112E090
