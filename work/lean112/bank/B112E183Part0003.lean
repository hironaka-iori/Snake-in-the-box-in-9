import B112E183Part0002
namespace B112E183
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1020 : List Lit := [(71, false), (89, false), (1501, true), (83, true), (1481, true), (198, true), (202, true), (431, false), (84, false), (96, true)]
theorem step1020 (p : Nat → Bool) (h : Constraints p) : clause p c1020 = true :=
  Snake9.TreeRup.prove_clause [c832, c502, c886, c305, c831, c830, c295, c817, c732, c735, c747, c728, c692, c1005, c974, c874, c782, c798, c813, c997, c494, c500, c393, c353, c348, c344, c341, c340, c391, c389, c375, c363, c361, c497, c446, c416, c403, c398, c397, c414, c412, c406, c405, c411, c409, c408, c444, c439, c435, c433, c430, c432, c431, c350, c333, c441, c426, c421, c437, c429, c1018, c684, c998, c704, c703, c724, c1001, c726, c698, c1017, c727, c191, c213, c689, c690, c162, c744, c210, c187, c736, c200, c734, c216, c234, c956, c228, c227, c549, c180, c541, c876, c167, c890, c19, c18, c516, c508, c521, c1019, c812, c803, c714, c916, c975, c663, c959, c643, c571, c567, c522, c552, c877] c1020 (by decide) p (sat_cons (step832 p h) (sat_cons (step502 p h) (sat_cons (step886 p h) (sat_cons (step305 p h) (sat_cons (step831 p h) (sat_cons (step830 p h) (sat_cons (step295 p h) (sat_cons (step817 p h) (sat_cons (step732 p h) (sat_cons (step735 p h) (sat_cons (step747 p h) (sat_cons (step728 p h) (sat_cons (step692 p h) (sat_cons (step1005 p h) (sat_cons (step974 p h) (sat_cons (step874 p h) (sat_cons (step782 p h) (sat_cons (step798 p h) (sat_cons (step813 p h) (sat_cons (step997 p h) (sat_cons (step494 p h) (sat_cons (step500 p h) (sat_cons (step393 p h) (sat_cons (step353 p h) (sat_cons (step348 p h) (sat_cons (step344 p h) (sat_cons (step341 p h) (sat_cons (step340 p h) (sat_cons (step391 p h) (sat_cons (step389 p h) (sat_cons (step375 p h) (sat_cons (step363 p h) (sat_cons (step361 p h) (sat_cons (step497 p h) (sat_cons (step446 p h) (sat_cons (step416 p h) (sat_cons (step403 p h) (sat_cons (step398 p h) (sat_cons (step397 p h) (sat_cons (step414 p h) (sat_cons (step412 p h) (sat_cons (step406 p h) (sat_cons (step405 p h) (sat_cons (step411 p h) (sat_cons (step409 p h) (sat_cons (step408 p h) (sat_cons (step444 p h) (sat_cons (step439 p h) (sat_cons (step435 p h) (sat_cons (step433 p h) (sat_cons (step430 p h) (sat_cons (step432 p h) (sat_cons (step431 p h) (sat_cons (step350 p h) (sat_cons (step333 p h) (sat_cons (step441 p h) (sat_cons (step426 p h) (sat_cons (step421 p h) (sat_cons (step437 p h) (sat_cons (step429 p h) (sat_cons (step1018 p h) (sat_cons (step684 p h) (sat_cons (step998 p h) (sat_cons (step704 p h) (sat_cons (step703 p h) (sat_cons (step724 p h) (sat_cons (step1001 p h) (sat_cons (step726 p h) (sat_cons (step698 p h) (sat_cons (step1017 p h) (sat_cons (step727 p h) (sat_cons (step191 p h) (sat_cons (step213 p h) (sat_cons (step689 p h) (sat_cons (step690 p h) (sat_cons (step162 p h) (sat_cons (step744 p h) (sat_cons (step210 p h) (sat_cons (step187 p h) (sat_cons (step736 p h) (sat_cons (step200 p h) (sat_cons (step734 p h) (sat_cons (step216 p h) (sat_cons (step234 p h) (sat_cons (step956 p h) (sat_cons (step228 p h) (sat_cons (step227 p h) (sat_cons (step549 p h) (sat_cons (step180 p h) (sat_cons (step541 p h) (sat_cons (step876 p h) (sat_cons (step167 p h) (sat_cons (step890 p h) (sat_cons (step19 p h) (sat_cons (step18 p h) (sat_cons (step516 p h) (sat_cons (step508 p h) (sat_cons (step521 p h) (sat_cons (step1019 p h) (sat_cons (step812 p h) (sat_cons (step803 p h) (sat_cons (step714 p h) (sat_cons (step916 p h) (sat_cons (step975 p h) (sat_cons (step663 p h) (sat_cons (step959 p h) (sat_cons (step643 p h) (sat_cons (step571 p h) (sat_cons (step567 p h) (sat_cons (step522 p h) (sat_cons (step552 p h) (sat_cons (step877 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1021 : List Lit := [(1358, true), (1384, true), (5, false), (325, true)]
theorem step1021 (p : Nat → Bool) (h : Constraints p) : clause p c1021 = true :=
  Snake9.LocalRup.prove_clause [c393, c353, c348, c344, c341, c340, c391, c389, c375, c363, c361, c540, c542, c537, c534, c77, c897, c61, c583, c91, c578] c1021 (by decide) p (sat_cons (step393 p h) (sat_cons (step353 p h) (sat_cons (step348 p h) (sat_cons (step344 p h) (sat_cons (step341 p h) (sat_cons (step340 p h) (sat_cons (step391 p h) (sat_cons (step389 p h) (sat_cons (step375 p h) (sat_cons (step363 p h) (sat_cons (step361 p h) (sat_cons (step540 p h) (sat_cons (step542 p h) (sat_cons (step537 p h) (sat_cons (step534 p h) (sat_cons (step77 p h) (sat_cons (step897 p h) (sat_cons (step61 p h) (sat_cons (step583 p h) (sat_cons (step91 p h) (sat_cons (step578 p h) (sat_nil p))))))))))))))))))))))
def c1022 : List Lit := [(1452, true), (1351, false), (5, false), (68, false), (1471, false), (1434, true), (1527, false), (167, true), (325, true)]
theorem step1022 (p : Nat → Bool) (h : Constraints p) : clause p c1022 = true :=
  Snake9.LocalRup.prove_clause [c913, c861, c393, c881, c639, c631, c391, c389, c375, c363, c361, c353, c350, c333, c916, c975, c135, c663, c899, c585, c588, c592, c598, c625, c648, c564, c554, c545, c1021, c966, c553, c643, c944, c956, c628, c909, c595, c608, c580, c125, c578, c536, c86, c91] c1022 (by decide) p (sat_cons (step913 p h) (sat_cons (step861 p h) (sat_cons (step393 p h) (sat_cons (step881 p h) (sat_cons (step639 p h) (sat_cons (step631 p h) (sat_cons (step391 p h) (sat_cons (step389 p h) (sat_cons (step375 p h) (sat_cons (step363 p h) (sat_cons (step361 p h) (sat_cons (step353 p h) (sat_cons (step350 p h) (sat_cons (step333 p h) (sat_cons (step916 p h) (sat_cons (step975 p h) (sat_cons (step135 p h) (sat_cons (step663 p h) (sat_cons (step899 p h) (sat_cons (step585 p h) (sat_cons (step588 p h) (sat_cons (step592 p h) (sat_cons (step598 p h) (sat_cons (step625 p h) (sat_cons (step648 p h) (sat_cons (step564 p h) (sat_cons (step554 p h) (sat_cons (step545 p h) (sat_cons (step1021 p h) (sat_cons (step966 p h) (sat_cons (step553 p h) (sat_cons (step643 p h) (sat_cons (step944 p h) (sat_cons (step956 p h) (sat_cons (step628 p h) (sat_cons (step909 p h) (sat_cons (step595 p h) (sat_cons (step608 p h) (sat_cons (step580 p h) (sat_cons (step125 p h) (sat_cons (step578 p h) (sat_cons (step536 p h) (sat_cons (step86 p h) (sat_cons (step91 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1023 : List Lit := [(89, false), (1501, true), (83, true), (1481, true), (198, true), (202, true), (431, false), (84, false), (96, true)]
theorem step1023 (p : Nat → Bool) (h : Constraints p) : clause p c1023 = true :=
  Snake9.TreeRup.prove_clause [c832, c502, c886, c296, c299, c305, c831, c830, c295, c817, c862, c913, c861, c282, c732, c735, c747, c728, c692, c1005, c874, c782, c997, c706, c685, c974, c798, c813, c494, c500, c393, c353, c348, c344, c342, c339, c341, c340, c391, c389, c375, c363, c361, c497, c446, c416, c403, c398, c397, c414, c411, c409, c408, c444, c441, c425, c424, c423, c439, c435, c433, c430, c432, c431, c350, c333, c426, c421, c437, c429, c881, c1020, c682, c683, c684, c998, c174, c175, c704, c703, c724, c1001, c726, c902, c173, c698, c727, c191, c213, c527, c182, c162, c689, c744, c210, c530, c187, c736, c200, c734, c234, c228, c227, c180, c167, c1022, c714, c803, c812, c647, c638, c564, c628, c554, c597, c541, c1021, c890, c966, c553, c642, c956, c625, c592, c594, c590, c580, c70, c578, c66, c91, c78, c84, c77] c1023 (by decide) p (sat_cons (step832 p h) (sat_cons (step502 p h) (sat_cons (step886 p h) (sat_cons (step296 p h) (sat_cons (step299 p h) (sat_cons (step305 p h) (sat_cons (step831 p h) (sat_cons (step830 p h) (sat_cons (step295 p h) (sat_cons (step817 p h) (sat_cons (step862 p h) (sat_cons (step913 p h) (sat_cons (step861 p h) (sat_cons (step282 p h) (sat_cons (step732 p h) (sat_cons (step735 p h) (sat_cons (step747 p h) (sat_cons (step728 p h) (sat_cons (step692 p h) (sat_cons (step1005 p h) (sat_cons (step874 p h) (sat_cons (step782 p h) (sat_cons (step997 p h) (sat_cons (step706 p h) (sat_cons (step685 p h) (sat_cons (step974 p h) (sat_cons (step798 p h) (sat_cons (step813 p h) (sat_cons (step494 p h) (sat_cons (step500 p h) (sat_cons (step393 p h) (sat_cons (step353 p h) (sat_cons (step348 p h) (sat_cons (step344 p h) (sat_cons (step342 p h) (sat_cons (step339 p h) (sat_cons (step341 p h) (sat_cons (step340 p h) (sat_cons (step391 p h) (sat_cons (step389 p h) (sat_cons (step375 p h) (sat_cons (step363 p h) (sat_cons (step361 p h) (sat_cons (step497 p h) (sat_cons (step446 p h) (sat_cons (step416 p h) (sat_cons (step403 p h) (sat_cons (step398 p h) (sat_cons (step397 p h) (sat_cons (step414 p h) (sat_cons (step411 p h) (sat_cons (step409 p h) (sat_cons (step408 p h) (sat_cons (step444 p h) (sat_cons (step441 p h) (sat_cons (step425 p h) (sat_cons (step424 p h) (sat_cons (step423 p h) (sat_cons (step439 p h) (sat_cons (step435 p h) (sat_cons (step433 p h) (sat_cons (step430 p h) (sat_cons (step432 p h) (sat_cons (step431 p h) (sat_cons (step350 p h) (sat_cons (step333 p h) (sat_cons (step426 p h) (sat_cons (step421 p h) (sat_cons (step437 p h) (sat_cons (step429 p h) (sat_cons (step881 p h) (sat_cons (step1020 p h) (sat_cons (step682 p h) (sat_cons (step683 p h) (sat_cons (step684 p h) (sat_cons (step998 p h) (sat_cons (step174 p h) (sat_cons (step175 p h) (sat_cons (step704 p h) (sat_cons (step703 p h) (sat_cons (step724 p h) (sat_cons (step1001 p h) (sat_cons (step726 p h) (sat_cons (step902 p h) (sat_cons (step173 p h) (sat_cons (step698 p h) (sat_cons (step727 p h) (sat_cons (step191 p h) (sat_cons (step213 p h) (sat_cons (step527 p h) (sat_cons (step182 p h) (sat_cons (step162 p h) (sat_cons (step689 p h) (sat_cons (step744 p h) (sat_cons (step210 p h) (sat_cons (step530 p h) (sat_cons (step187 p h) (sat_cons (step736 p h) (sat_cons (step200 p h) (sat_cons (step734 p h) (sat_cons (step234 p h) (sat_cons (step228 p h) (sat_cons (step227 p h) (sat_cons (step180 p h) (sat_cons (step167 p h) (sat_cons (step1022 p h) (sat_cons (step714 p h) (sat_cons (step803 p h) (sat_cons (step812 p h) (sat_cons (step647 p h) (sat_cons (step638 p h) (sat_cons (step564 p h) (sat_cons (step628 p h) (sat_cons (step554 p h) (sat_cons (step597 p h) (sat_cons (step541 p h) (sat_cons (step1021 p h) (sat_cons (step890 p h) (sat_cons (step966 p h) (sat_cons (step553 p h) (sat_cons (step642 p h) (sat_cons (step956 p h) (sat_cons (step625 p h) (sat_cons (step592 p h) (sat_cons (step594 p h) (sat_cons (step590 p h) (sat_cons (step580 p h) (sat_cons (step70 p h) (sat_cons (step578 p h) (sat_cons (step66 p h) (sat_cons (step91 p h) (sat_cons (step78 p h) (sat_cons (step84 p h) (sat_cons (step77 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1024 : List Lit := [(96, true), (1544, true)]
theorem step1024 (p : Nat → Bool) (h : Constraints p) : clause p c1024 = true :=
  Snake9.LocalRup.prove_clause [c834, c832, c886, c831, c732, c995, c1012, c490, c492, c497, c468, c470, c444, c466, c453, c439, c441, c459, c452, c435, c426, c456, c451, c432, c433, c420, c421, c874, c431, c430, c419, c782, c807, c997, c1013, c692, c1014, c785, c1023, c168, c682, c684, c998, c704, c724, c1001, c698, c727, c191, c689, c744, c187, c736, c200, c734, c236] c1024 (by decide) p (sat_cons (step834 p h) (sat_cons (step832 p h) (sat_cons (step886 p h) (sat_cons (step831 p h) (sat_cons (step732 p h) (sat_cons (step995 p h) (sat_cons (step1012 p h) (sat_cons (step490 p h) (sat_cons (step492 p h) (sat_cons (step497 p h) (sat_cons (step468 p h) (sat_cons (step470 p h) (sat_cons (step444 p h) (sat_cons (step466 p h) (sat_cons (step453 p h) (sat_cons (step439 p h) (sat_cons (step441 p h) (sat_cons (step459 p h) (sat_cons (step452 p h) (sat_cons (step435 p h) (sat_cons (step426 p h) (sat_cons (step456 p h) (sat_cons (step451 p h) (sat_cons (step432 p h) (sat_cons (step433 p h) (sat_cons (step420 p h) (sat_cons (step421 p h) (sat_cons (step874 p h) (sat_cons (step431 p h) (sat_cons (step430 p h) (sat_cons (step419 p h) (sat_cons (step782 p h) (sat_cons (step807 p h) (sat_cons (step997 p h) (sat_cons (step1013 p h) (sat_cons (step692 p h) (sat_cons (step1014 p h) (sat_cons (step785 p h) (sat_cons (step1023 p h) (sat_cons (step168 p h) (sat_cons (step682 p h) (sat_cons (step684 p h) (sat_cons (step998 p h) (sat_cons (step704 p h) (sat_cons (step724 p h) (sat_cons (step1001 p h) (sat_cons (step698 p h) (sat_cons (step727 p h) (sat_cons (step191 p h) (sat_cons (step689 p h) (sat_cons (step744 p h) (sat_cons (step187 p h) (sat_cons (step736 p h) (sat_cons (step200 p h) (sat_cons (step734 p h) (sat_cons (step236 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1025 : List Lit := [(1, false), (10, true), (3, true)]
theorem step1025 (p : Nat → Bool) (h : Constraints p) : clause p c1025 = true :=
  Snake9.LocalRup.prove_clause [c276, c2] c1025 (by decide) p (sat_cons (step276 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1026 : List Lit := [(2, true), (8, true), (5, false), (23, true)]
theorem step1026 (p : Nat → Bool) (h : Constraints p) : clause p c1026 = true :=
  Snake9.LocalRup.prove_clause [c277, c20] c1026 (by decide) p (sat_cons (step277 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1027 : List Lit := [(9, false), (8, true), (19, true)]
theorem step1027 (p : Nat → Bool) (h : Constraints p) : clause p c1027 = true :=
  Snake9.LocalRup.prove_clause [c278, c29] c1027 (by decide) p (sat_cons (step278 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1028 : List Lit := [(9, false), (7, true), (19, true)]
theorem step1028 (p : Nat → Bool) (h : Constraints p) : clause p c1028 = true :=
  Snake9.LocalRup.prove_clause [c278, c30] c1028 (by decide) p (sat_cons (step278 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1029 : List Lit := [(3, true), (21, true), (20, false)]
theorem step1029 (p : Nat → Bool) (h : Constraints p) : clause p c1029 = true :=
  Snake9.LocalRup.prove_clause [c280, c54] c1029 (by decide) p (sat_cons (step280 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1030 : List Lit := [(22, false), (23, true), (29, true)]
theorem step1030 (p : Nat → Bool) (h : Constraints p) : clause p c1030 = true :=
  Snake9.LocalRup.prove_clause [c281, c59] c1030 (by decide) p (sat_cons (step281 p h) (sat_cons (step59 p h) (sat_nil p)))
def c1031 : List Lit := [(22, false), (26, true), (23, true)]
theorem step1031 (p : Nat → Bool) (h : Constraints p) : clause p c1031 = true :=
  Snake9.LocalRup.prove_clause [c281, c60] c1031 (by decide) p (sat_cons (step281 p h) (sat_cons (step60 p h) (sat_nil p)))
def c1032 : List Lit := [(27, false), (26, true)]
theorem step1032 (p : Nat → Bool) (h : Constraints p) : clause p c1032 = true :=
  Snake9.LocalRup.prove_clause [c282, c78] c1032 (by decide) p (sat_cons (step282 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1033 : List Lit := [(27, false), (24, true)]
theorem step1033 (p : Nat → Bool) (h : Constraints p) : clause p c1033 = true :=
  Snake9.LocalRup.prove_clause [c282, c79] c1033 (by decide) p (sat_cons (step282 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1034 : List Lit := [(30, false), (31, true), (29, true)]
theorem step1034 (p : Nat → Bool) (h : Constraints p) : clause p c1034 = true :=
  Snake9.LocalRup.prove_clause [c283, c87] c1034 (by decide) p (sat_cons (step283 p h) (sat_cons (step87 p h) (sat_nil p)))
def c1035 : List Lit := [(23, true), (30, false), (29, true)]
theorem step1035 (p : Nat → Bool) (h : Constraints p) : clause p c1035 = true :=
  Snake9.LocalRup.prove_clause [c283, c88] c1035 (by decide) p (sat_cons (step283 p h) (sat_cons (step88 p h) (sat_nil p)))
def c1036 : List Lit := [(33, false), (35, true)]
theorem step1036 (p : Nat → Bool) (h : Constraints p) : clause p c1036 = true :=
  Snake9.LocalRup.prove_clause [c284, c95] c1036 (by decide) p (sat_cons (step284 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1037 : List Lit := [(36, false), (35, true), (19, true)]
theorem step1037 (p : Nat → Bool) (h : Constraints p) : clause p c1037 = true :=
  Snake9.LocalRup.prove_clause [c285, c104] c1037 (by decide) p (sat_cons (step285 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1038 : List Lit := [(31, true), (36, false), (19, true)]
theorem step1038 (p : Nat → Bool) (h : Constraints p) : clause p c1038 = true :=
  Snake9.LocalRup.prove_clause [c285, c105] c1038 (by decide) p (sat_cons (step285 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1039 : List Lit := [(42, false), (41, true)]
theorem step1039 (p : Nat → Bool) (h : Constraints p) : clause p c1039 = true :=
  Snake9.LocalRup.prove_clause [c287, c113] c1039 (by decide) p (sat_cons (step287 p h) (sat_cons (step113 p h) (sat_nil p)))
def c1040 : List Lit := [(42, false), (40, true)]
theorem step1040 (p : Nat → Bool) (h : Constraints p) : clause p c1040 = true :=
  Snake9.LocalRup.prove_clause [c287, c114] c1040 (by decide) p (sat_cons (step287 p h) (sat_cons (step114 p h) (sat_nil p)))
def c1041 : List Lit := [(43, false), (49, false)]
theorem step1041 (p : Nat → Bool) (h : Constraints p) : clause p c1041 = true :=
  Snake9.LocalRup.prove_clause [c122, c120] c1041 (by decide) p (sat_cons (step122 p h) (sat_cons (step120 p h) (sat_nil p)))
def c1042 : List Lit := [(21, true), (56, true), (53, false), (57, true)]
theorem step1042 (p : Nat → Bool) (h : Constraints p) : clause p c1042 = true :=
  Snake9.LocalRup.prove_clause [c289, c129] c1042 (by decide) p (sat_cons (step289 p h) (sat_cons (step129 p h) (sat_nil p)))
def c1043 : List Lit := [(65, true), (57, true), (59, false)]
theorem step1043 (p : Nat → Bool) (h : Constraints p) : clause p c1043 = true :=
  Snake9.LocalRup.prove_clause [c290, c141] c1043 (by decide) p (sat_cons (step290 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1044 : List Lit := [(66, true), (65, false), (175, true)]
theorem step1044 (p : Nat → Bool) (h : Constraints p) : clause p c1044 = true :=
  Snake9.LocalRup.prove_clause [c829, c156] c1044 (by decide) p (sat_cons (step829 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1045 : List Lit := [(66, false), (65, true)]
theorem step1045 (p : Nat → Bool) (h : Constraints p) : clause p c1045 = true :=
  Snake9.LocalRup.prove_clause [c293, c158] c1045 (by decide) p (sat_cons (step293 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1046 : List Lit := [(66, false), (63, true)]
theorem step1046 (p : Nat → Bool) (h : Constraints p) : clause p c1046 = true :=
  Snake9.LocalRup.prove_clause [c293, c159] c1046 (by decide) p (sat_cons (step293 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1047 : List Lit := [(70, false), (7, true), (83, true)]
theorem step1047 (p : Nat → Bool) (h : Constraints p) : clause p c1047 = true :=
  Snake9.LocalRup.prove_clause [c295, c167] c1047 (by decide) p (sat_cons (step295 p h) (sat_cons (step167 p h) (sat_nil p)))
def c1048 : List Lit := [(73, true), (71, true), (72, false)]
theorem step1048 (p : Nat → Bool) (h : Constraints p) : clause p c1048 = true :=
  Snake9.LocalRup.prove_clause [c296, c171] c1048 (by decide) p (sat_cons (step296 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1049 : List Lit := [(73, true), (68, true), (72, false)]
theorem step1049 (p : Nat → Bool) (h : Constraints p) : clause p c1049 = true :=
  Snake9.LocalRup.prove_clause [c296, c172] c1049 (by decide) p (sat_cons (step296 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1050 : List Lit := [(72, false), (68, true), (71, true)]
theorem step1050 (p : Nat → Bool) (h : Constraints p) : clause p c1050 = true :=
  Snake9.LocalRup.prove_clause [c296, c173] c1050 (by decide) p (sat_cons (step296 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1051 : List Lit := [(75, false), (91, true)]
theorem step1051 (p : Nat → Bool) (h : Constraints p) : clause p c1051 = true :=
  Snake9.LocalRup.prove_clause [c298, c177] c1051 (by decide) p (sat_cons (step298 p h) (sat_cons (step177 p h) (sat_nil p)))
def c1052 : List Lit := [(75, false), (76, true)]
theorem step1052 (p : Nat → Bool) (h : Constraints p) : clause p c1052 = true :=
  Snake9.LocalRup.prove_clause [c298, c178] c1052 (by decide) p (sat_cons (step298 p h) (sat_cons (step178 p h) (sat_nil p)))
def c1053 : List Lit := [(77, true), (75, true), (76, false), (186, true)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true :=
  Snake9.LocalRup.prove_clause [c830, c179] c1053 (by decide) p (sat_cons (step830 p h) (sat_cons (step179 p h) (sat_nil p)))
def c1054 : List Lit := [(70, true), (75, true), (186, true), (76, false)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true :=
  Snake9.LocalRup.prove_clause [c830, c180] c1054 (by decide) p (sat_cons (step830 p h) (sat_cons (step180 p h) (sat_nil p)))
def c1055 : List Lit := [(19, true), (76, true), (77, false)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true :=
  Snake9.LocalRup.prove_clause [c299, c182] c1055 (by decide) p (sat_cons (step299 p h) (sat_cons (step182 p h) (sat_nil p)))
def c1056 : List Lit := [(19, true), (77, false), (73, true)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true :=
  Snake9.LocalRup.prove_clause [c299, c183] c1056 (by decide) p (sat_cons (step299 p h) (sat_cons (step183 p h) (sat_nil p)))
def c1057 : List Lit := [(86, true), (82, true), (79, false)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true :=
  Snake9.LocalRup.prove_clause [c831, c185] c1057 (by decide) p (sat_cons (step831 p h) (sat_cons (step185 p h) (sat_nil p)))
def c1058 : List Lit := [(82, true), (79, false), (189, true)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true :=
  Snake9.LocalRup.prove_clause [c831, c187] c1058 (by decide) p (sat_cons (step831 p h) (sat_cons (step187 p h) (sat_nil p)))
def c1059 : List Lit := [(81, true), (90, true), (80, false)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true :=
  Snake9.LocalRup.prove_clause [c301, c189] c1059 (by decide) p (sat_cons (step301 p h) (sat_cons (step189 p h) (sat_nil p)))
def c1060 : List Lit := [(81, true), (85, false), (83, true)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true :=
  Snake9.LocalRup.prove_clause [c303, c206] c1060 (by decide) p (sat_cons (step303 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1061 : List Lit := [(86, false), (88, true)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true :=
  Snake9.LocalRup.prove_clause [c304, c207] c1061 (by decide) p (sat_cons (step304 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1062 : List Lit := [(86, false), (79, true)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true :=
  Snake9.LocalRup.prove_clause [c304, c208] c1062 (by decide) p (sat_cons (step304 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1063 : List Lit := [(91, true), (87, false), (90, true)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true :=
  Snake9.LocalRup.prove_clause [c305, c210] c1063 (by decide) p (sat_cons (step305 p h) (sat_cons (step210 p h) (sat_nil p)))
def c1064 : List Lit := [(29, true), (92, true), (71, true), (104, true), (89, false)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true :=
  Snake9.LocalRup.prove_clause [c306, c221] c1064 (by decide) p (sat_cons (step306 p h) (sat_cons (step221 p h) (sat_nil p)))
def c1065 : List Lit := [(29, true), (104, true), (89, false), (90, true), (71, true)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true :=
  Snake9.LocalRup.prove_clause [c306, c222] c1065 (by decide) p (sat_cons (step306 p h) (sat_cons (step222 p h) (sat_nil p)))
def c1066 : List Lit := [(93, false), (92, true)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true :=
  Snake9.LocalRup.prove_clause [c307, c237] c1066 (by decide) p (sat_cons (step307 p h) (sat_cons (step237 p h) (sat_nil p)))
def c1067 : List Lit := [(93, false), (84, true)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true :=
  Snake9.LocalRup.prove_clause [c307, c238] c1067 (by decide) p (sat_cons (step307 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1068 : List Lit := [(94, false), (91, true), (90, true)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true :=
  Snake9.LocalRup.prove_clause [c308, c240] c1068 (by decide) p (sat_cons (step308 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1069 : List Lit := [(102, false), (101, true)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true :=
  Snake9.LocalRup.prove_clause [c311, c258] c1069 (by decide) p (sat_cons (step311 p h) (sat_cons (step258 p h) (sat_nil p)))
def c1070 : List Lit := [(54, true), (103, false), (104, true)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true :=
  Snake9.LocalRup.prove_clause [c312, c260] c1070 (by decide) p (sat_cons (step312 p h) (sat_cons (step260 p h) (sat_nil p)))
def c1071 : List Lit := [(108, false), (107, true)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true :=
  Snake9.LocalRup.prove_clause [c313, c270] c1071 (by decide) p (sat_cons (step313 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1072 : List Lit := [(110, false), (106, true)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true :=
  Snake9.LocalRup.prove_clause [c314, c275] c1072 (by decide) p (sat_cons (step314 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1073 : List Lit := [(124, false), (245, false)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true :=
  Snake9.LocalRup.prove_clause [c859, c330] c1073 (by decide) p (sat_cons (step859 p h) (sat_cons (step330 p h) (sat_nil p)))
def c1074 : List Lit := [(247, false), (253, false)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true :=
  Snake9.LocalRup.prove_clause [c853, c334] c1074 (by decide) p (sat_cons (step853 p h) (sat_cons (step334 p h) (sat_nil p)))
def c1075 : List Lit := [(261, false), (263, false)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true :=
  Snake9.LocalRup.prove_clause [c858, c343] c1075 (by decide) p (sat_cons (step858 p h) (sat_cons (step343 p h) (sat_nil p)))
def c1076 : List Lit := [(259, false), (265, false)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true :=
  Snake9.LocalRup.prove_clause [c852, c347] c1076 (by decide) p (sat_cons (step852 p h) (sat_cons (step347 p h) (sat_nil p)))
def c1077 : List Lit := [(255, false), (267, false)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true :=
  Snake9.LocalRup.prove_clause [c843, c351] c1077 (by decide) p (sat_cons (step843 p h) (sat_cons (step351 p h) (sat_nil p)))
def c1078 : List Lit := [(243, false), (269, false)]
theorem step1078 (p : Nat → Bool) (h : Constraints p) : clause p c1078 = true :=
  Snake9.LocalRup.prove_clause [c837, c356] c1078 (by decide) p (sat_cons (step837 p h) (sat_cons (step356 p h) (sat_nil p)))
def c1079 : List Lit := [(141, false), (277, false)]
theorem step1079 (p : Nat → Bool) (h : Constraints p) : clause p c1079 = true :=
  Snake9.LocalRup.prove_clause [c857, c362] c1079 (by decide) p (sat_cons (step857 p h) (sat_cons (step362 p h) (sat_nil p)))
def c1080 : List Lit := [(281, false), (293, false)]
theorem step1080 (p : Nat → Bool) (h : Constraints p) : clause p c1080 = true :=
  Snake9.LocalRup.prove_clause [c842, c376] c1080 (by decide) p (sat_cons (step842 p h) (sat_cons (step376 p h) (sat_nil p)))
def c1081 : List Lit := [(271, false), (323, false)]
theorem step1081 (p : Nat → Bool) (h : Constraints p) : clause p c1081 = true :=
  Snake9.LocalRup.prove_clause [c833, c394] c1081 (by decide) p (sat_cons (step833 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1082 : List Lit := [(179, false), (351, false)]
theorem step1082 (p : Nat → Bool) (h : Constraints p) : clause p c1082 = true :=
  Snake9.LocalRup.prove_clause [c856, c422] c1082 (by decide) p (sat_cons (step856 p h) (sat_cons (step422 p h) (sat_nil p)))
def c1083 : List Lit := [(353, false), (359, false)]
theorem step1083 (p : Nat → Bool) (h : Constraints p) : clause p c1083 = true :=
  Snake9.LocalRup.prove_clause [c847, c427] c1083 (by decide) p (sat_cons (step847 p h) (sat_cons (step427 p h) (sat_nil p)))
end B112E183
