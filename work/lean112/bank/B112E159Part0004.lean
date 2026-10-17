import B112E159Part0003
namespace B112E159
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1261 : List Lit := [(894, true), (26, false), (4, false), (888, false), (925, true), (857, false), (16, false), (88, false), (94, false)]
theorem step1261 (p : Nat → Bool) (h : Constraints p) : clause p c1261 = true :=
  Snake9.LocalRup.prove_clause [c392, c1050, c1204, c688, c710, c6, c7, c978, c714, c691, c1196, c1195, c682, c664, c1212, c673, c628, c745, c766] c1261 (by decide) p (sat_cons (step392 p h) (sat_cons (step1050 p h) (sat_cons (step1204 p h) (sat_cons (step688 p h) (sat_cons (step710 p h) (sat_cons (step6 p h) (sat_cons (step7 p h) (sat_cons (step978 p h) (sat_cons (step714 p h) (sat_cons (step691 p h) (sat_cons (step1196 p h) (sat_cons (step1195 p h) (sat_cons (step682 p h) (sat_cons (step664 p h) (sat_cons (step1212 p h) (sat_cons (step673 p h) (sat_cons (step628 p h) (sat_cons (step745 p h) (sat_cons (step766 p h) (sat_nil p))))))))))))))))))))
def c1262 : List Lit := [(870, false), (894, false), (26, false), (114, false), (41, true), (3, false), (883, false), (925, true), (1017, false), (1022, false), (1039, false), (88, false), (94, false), (98, false), (1006, false)]
theorem step1262 (p : Nat → Bool) (h : Constraints p) : clause p c1262 = true :=
  Snake9.LocalRup.prove_clause [c977, c1050, c1040, c1064, c1126, c627, c1053, c826, c1061, c844, c1202, c740, c759, c766, c972, c628, c955, c1212, c939, c682, c926, c692, c914, c683, c906, c371] c1262 (by decide) p (sat_cons (step977 p h) (sat_cons (step1050 p h) (sat_cons (step1040 p h) (sat_cons (step1064 p h) (sat_cons (step1126 p h) (sat_cons (step627 p h) (sat_cons (step1053 p h) (sat_cons (step826 p h) (sat_cons (step1061 p h) (sat_cons (step844 p h) (sat_cons (step1202 p h) (sat_cons (step740 p h) (sat_cons (step759 p h) (sat_cons (step766 p h) (sat_cons (step972 p h) (sat_cons (step628 p h) (sat_cons (step955 p h) (sat_cons (step1212 p h) (sat_cons (step939 p h) (sat_cons (step682 p h) (sat_cons (step926 p h) (sat_cons (step692 p h) (sat_cons (step914 p h) (sat_cons (step683 p h) (sat_cons (step906 p h) (sat_cons (step371 p h) (sat_nil p)))))))))))))))))))))))))))
def c1263 : List Lit := [(857, false), (1022, false), (101, false), (88, false), (94, false), (997, true), (1006, false)]
theorem step1263 (p : Nat → Bool) (h : Constraints p) : clause p c1263 = true :=
  Snake9.TreeRup.prove_clause [c1162, c1049, c392, c391, c1011, c977, c1050, c866, c1064, c1126, c627, c867, c1052, c1063, c921, c937, c1053, c826, c1061, c844, c671, c1235, c1240, c925, c938, c954, c973, c1255, c694, c1040, c1260, c583, c1031, c567, c568, c6, c7, c1204, c1237, c5, c978, c688, c3, c710, c435, c733, c436, c757, c439, c970, c447, c968, c464, c855, c1207, c344, c1110, c1165, c1261, c1262, c734, c672, c773, c1224, c629, c40, c39, c1190, c596, c645, c97, c94, c599, c588, c604, c593, c620] c1263 (by decide) p (sat_cons (step1162 p h) (sat_cons (step1049 p h) (sat_cons (step392 p h) (sat_cons (step391 p h) (sat_cons (step1011 p h) (sat_cons (step977 p h) (sat_cons (step1050 p h) (sat_cons (step866 p h) (sat_cons (step1064 p h) (sat_cons (step1126 p h) (sat_cons (step627 p h) (sat_cons (step867 p h) (sat_cons (step1052 p h) (sat_cons (step1063 p h) (sat_cons (step921 p h) (sat_cons (step937 p h) (sat_cons (step1053 p h) (sat_cons (step826 p h) (sat_cons (step1061 p h) (sat_cons (step844 p h) (sat_cons (step671 p h) (sat_cons (step1235 p h) (sat_cons (step1240 p h) (sat_cons (step925 p h) (sat_cons (step938 p h) (sat_cons (step954 p h) (sat_cons (step973 p h) (sat_cons (step1255 p h) (sat_cons (step694 p h) (sat_cons (step1040 p h) (sat_cons (step1260 p h) (sat_cons (step583 p h) (sat_cons (step1031 p h) (sat_cons (step567 p h) (sat_cons (step568 p h) (sat_cons (step6 p h) (sat_cons (step7 p h) (sat_cons (step1204 p h) (sat_cons (step1237 p h) (sat_cons (step5 p h) (sat_cons (step978 p h) (sat_cons (step688 p h) (sat_cons (step3 p h) (sat_cons (step710 p h) (sat_cons (step435 p h) (sat_cons (step733 p h) (sat_cons (step436 p h) (sat_cons (step757 p h) (sat_cons (step439 p h) (sat_cons (step970 p h) (sat_cons (step447 p h) (sat_cons (step968 p h) (sat_cons (step464 p h) (sat_cons (step855 p h) (sat_cons (step1207 p h) (sat_cons (step344 p h) (sat_cons (step1110 p h) (sat_cons (step1165 p h) (sat_cons (step1261 p h) (sat_cons (step1262 p h) (sat_cons (step734 p h) (sat_cons (step672 p h) (sat_cons (step773 p h) (sat_cons (step1224 p h) (sat_cons (step629 p h) (sat_cons (step40 p h) (sat_cons (step39 p h) (sat_cons (step1190 p h) (sat_cons (step596 p h) (sat_cons (step645 p h) (sat_cons (step97 p h) (sat_cons (step94 p h) (sat_cons (step599 p h) (sat_cons (step588 p h) (sat_cons (step604 p h) (sat_cons (step593 p h) (sat_cons (step620 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1264 : List Lit := [(862, true), (838, true), (821, false), (828, false), (17, false), (27, false), (16, false), (88, false)]
theorem step1264 (p : Nat → Bool) (h : Constraints p) : clause p c1264 = true :=
  Snake9.LocalRup.prove_clause [c655, c656, c41, c40, c39, c597, c593, c607, c621] c1264 (by decide) p (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step41 p h) (sat_cons (step40 p h) (sat_cons (step39 p h) (sat_cons (step597 p h) (sat_cons (step593 p h) (sat_cons (step607 p h) (sat_cons (step621 p h) (sat_nil p))))))))))
def c1265 : List Lit := [(801, true), (876, false), (862, false), (894, false), (905, true), (888, false), (845, false), (114, false), (1022, false), (978, false), (101, false), (98, false), (1006, false)]
theorem step1265 (p : Nat → Bool) (h : Constraints p) : clause p c1265 = true :=
  Snake9.LocalRup.prove_clause [c391, c1011, c566, c977, c567, c568, c1237, c5, c3, c435, c436, c439, c447, c464, c506, c564, c559, c557, c556, c546, c545, c543, c661, c667, c735, c734, c718, c765, c692, c972, c683, c955, c371, c939, c906, c1201, c914, c1240, c926] c1265 (by decide) p (sat_cons (step391 p h) (sat_cons (step1011 p h) (sat_cons (step566 p h) (sat_cons (step977 p h) (sat_cons (step567 p h) (sat_cons (step568 p h) (sat_cons (step1237 p h) (sat_cons (step5 p h) (sat_cons (step3 p h) (sat_cons (step435 p h) (sat_cons (step436 p h) (sat_cons (step439 p h) (sat_cons (step447 p h) (sat_cons (step464 p h) (sat_cons (step506 p h) (sat_cons (step564 p h) (sat_cons (step559 p h) (sat_cons (step557 p h) (sat_cons (step556 p h) (sat_cons (step546 p h) (sat_cons (step545 p h) (sat_cons (step543 p h) (sat_cons (step661 p h) (sat_cons (step667 p h) (sat_cons (step735 p h) (sat_cons (step734 p h) (sat_cons (step718 p h) (sat_cons (step765 p h) (sat_cons (step692 p h) (sat_cons (step972 p h) (sat_cons (step683 p h) (sat_cons (step955 p h) (sat_cons (step371 p h) (sat_cons (step939 p h) (sat_cons (step906 p h) (sat_cons (step1201 p h) (sat_cons (step914 p h) (sat_cons (step1240 p h) (sat_cons (step926 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1266 : List Lit := [(876, false), (34, false), (862, false), (894, false), (925, true), (888, false), (836, false), (114, false), (1022, false), (978, false), (101, false), (98, false), (1006, false)]
theorem step1266 (p : Nat → Bool) (h : Constraints p) : clause p c1266 = true :=
  Snake9.LocalRup.prove_clause [c1050, c1049, c1163, c977, c728, c628, c766, c1265, c1031, c583, c633, c773, c772, c729, c734, c972, c718, c667, c955, c692, c661, c939, c683, c652, c653, c371, c154, c906, c1060, c914, c926] c1266 (by decide) p (sat_cons (step1050 p h) (sat_cons (step1049 p h) (sat_cons (step1163 p h) (sat_cons (step977 p h) (sat_cons (step728 p h) (sat_cons (step628 p h) (sat_cons (step766 p h) (sat_cons (step1265 p h) (sat_cons (step1031 p h) (sat_cons (step583 p h) (sat_cons (step633 p h) (sat_cons (step773 p h) (sat_cons (step772 p h) (sat_cons (step729 p h) (sat_cons (step734 p h) (sat_cons (step972 p h) (sat_cons (step718 p h) (sat_cons (step667 p h) (sat_cons (step955 p h) (sat_cons (step692 p h) (sat_cons (step661 p h) (sat_cons (step939 p h) (sat_cons (step683 p h) (sat_cons (step652 p h) (sat_cons (step653 p h) (sat_cons (step371 p h) (sat_cons (step154 p h) (sat_cons (step906 p h) (sat_cons (step1060 p h) (sat_cons (step914 p h) (sat_cons (step926 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1267 : List Lit := [(34, false), (862, false), (894, false), (925, true), (888, false), (836, false), (45, true), (114, false), (1022, false), (978, false), (101, false), (98, false), (1006, false)]
theorem step1267 (p : Nat → Bool) (h : Constraints p) : clause p c1267 = true :=
  Snake9.LocalRup.prove_clause [c1050, c1049, c628, c766, c740, c668, c664, c1266, c1195, c682, c567, c1244, c1031, c667, c583, c734, c633, c773] c1267 (by decide) p (sat_cons (step1050 p h) (sat_cons (step1049 p h) (sat_cons (step628 p h) (sat_cons (step766 p h) (sat_cons (step740 p h) (sat_cons (step668 p h) (sat_cons (step664 p h) (sat_cons (step1266 p h) (sat_cons (step1195 p h) (sat_cons (step682 p h) (sat_cons (step567 p h) (sat_cons (step1244 p h) (sat_cons (step1031 p h) (sat_cons (step667 p h) (sat_cons (step583 p h) (sat_cons (step734 p h) (sat_cons (step633 p h) (sat_cons (step773 p h) (sat_nil p)))))))))))))))))))
def c1268 : List Lit := [(862, false), (894, false), (1006, false), (925, true), (888, false), (836, false), (45, true), (114, false), (1022, false), (978, false), (101, false), (98, false)]
theorem step1268 (p : Nat → Bool) (h : Constraints p) : clause p c1268 = true :=
  Snake9.LocalRup.prove_clause [c403, c1163, c1049, c392, c1267, c6, c567, c1031, c583, c633, c773, c729, c734, c718, c667, c659, c661, c1244, c652, c653, c682, c126, c124, c692, c127, c683, c657, c172] c1268 (by decide) p (sat_cons (step403 p h) (sat_cons (step1163 p h) (sat_cons (step1049 p h) (sat_cons (step392 p h) (sat_cons (step1267 p h) (sat_cons (step6 p h) (sat_cons (step567 p h) (sat_cons (step1031 p h) (sat_cons (step583 p h) (sat_cons (step633 p h) (sat_cons (step773 p h) (sat_cons (step729 p h) (sat_cons (step734 p h) (sat_cons (step718 p h) (sat_cons (step667 p h) (sat_cons (step659 p h) (sat_cons (step661 p h) (sat_cons (step1244 p h) (sat_cons (step652 p h) (sat_cons (step653 p h) (sat_cons (step682 p h) (sat_cons (step126 p h) (sat_cons (step124 p h) (sat_cons (step692 p h) (sat_cons (step127 p h) (sat_cons (step683 p h) (sat_cons (step657 p h) (sat_cons (step172 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1269 : List Lit := [(894, false), (925, true), (888, false), (821, false), (828, false), (45, true), (114, false), (17, false), (27, false), (1022, false), (101, false), (88, false), (98, false), (1006, false)]
theorem step1269 (p : Nat → Bool) (h : Constraints p) : clause p c1269 = true :=
  Snake9.LocalRup.prove_clause [c1163, c1050, c1064, c1113, c1053, c826, c1061, c844, c728, c778, c630, c1264, c1268] c1269 (by decide) p (sat_cons (step1163 p h) (sat_cons (step1050 p h) (sat_cons (step1064 p h) (sat_cons (step1113 p h) (sat_cons (step1053 p h) (sat_cons (step826 p h) (sat_cons (step1061 p h) (sat_cons (step844 p h) (sat_cons (step728 p h) (sat_cons (step778 p h) (sat_cons (step630 p h) (sat_cons (step1264 p h) (sat_cons (step1268 p h) (sat_nil p))))))))))))))
def c1270 : List Lit := [(804, false), (817, true), (847, true), (46, false), (41, false), (884, true), (823, false), (23, true), (31, true), (30, false), (16, false)]
theorem step1270 (p : Nat → Bool) (h : Constraints p) : clause p c1270 = true :=
  Snake9.LocalRup.prove_clause [c1049, c409, c402, c583, c584, c634, c1246, c616, c696, c249, c234, c117, c116, c207, c45, c600, c596, c605] c1270 (by decide) p (sat_cons (step1049 p h) (sat_cons (step409 p h) (sat_cons (step402 p h) (sat_cons (step583 p h) (sat_cons (step584 p h) (sat_cons (step634 p h) (sat_cons (step1246 p h) (sat_cons (step616 p h) (sat_cons (step696 p h) (sat_cons (step249 p h) (sat_cons (step234 p h) (sat_cons (step117 p h) (sat_cons (step116 p h) (sat_cons (step207 p h) (sat_cons (step45 p h) (sat_cons (step600 p h) (sat_cons (step596 p h) (sat_cons (step605 p h) (sat_nil p)))))))))))))))))))
def c1271 : List Lit := [(817, true), (847, true), (16, false), (46, false), (41, false), (884, true), (823, false), (23, true), (31, true), (30, false)]
theorem step1271 (p : Nat → Bool) (h : Constraints p) : clause p c1271 = true :=
  Snake9.LocalRup.prove_clause [c392, c1270, c1031, c567, c6, c7, c978] c1271 (by decide) p (sat_cons (step392 p h) (sat_cons (step1270 p h) (sat_cons (step1031 p h) (sat_cons (step567 p h) (sat_cons (step6 p h) (sat_cons (step7 p h) (sat_cons (step978 p h) (sat_nil p))))))))
def c1272 : List Lit := [(925, true), (888, false), (821, false), (45, true), (23, true), (114, false), (31, true), (30, false), (27, false), (1022, false), (101, false), (88, false), (98, false), (1006, false)]
theorem step1272 (p : Nat → Bool) (h : Constraints p) : clause p c1272 = true :=
  Snake9.LocalRup.prove_clause [c400, c680, c688, c710, c1064, c599, c1113, c590, c101, c1269, c714, c1222, c711, c691, c689, c667, c1041, c682, c684, c733, c778, c638, c1271] c1272 (by decide) p (sat_cons (step400 p h) (sat_cons (step680 p h) (sat_cons (step688 p h) (sat_cons (step710 p h) (sat_cons (step1064 p h) (sat_cons (step599 p h) (sat_cons (step1113 p h) (sat_cons (step590 p h) (sat_cons (step101 p h) (sat_cons (step1269 p h) (sat_cons (step714 p h) (sat_cons (step1222 p h) (sat_cons (step711 p h) (sat_cons (step691 p h) (sat_cons (step689 p h) (sat_cons (step667 p h) (sat_cons (step1041 p h) (sat_cons (step682 p h) (sat_cons (step684 p h) (sat_cons (step733 p h) (sat_cons (step778 p h) (sat_cons (step638 p h) (sat_cons (step1271 p h) (sat_nil p))))))))))))))))))))))))
def c1273 : List Lit := [(1057, true), (114, false), (1022, false), (1039, false), (1016, false), (963, false), (98, false), (1038, false), (1006, false)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true :=
  Snake9.LocalRup.prove_clause [c415, c413, c418, c1061, c844, c962, c954, c958, c852, c938, c845, c848, c1098, c922, c804, c806, c914, c801, c790, c906, c795, c788, c374, c285, c271, c824, c281, c831, c292, c837, c815, c817] c1273 (by decide) p (sat_cons (step415 p h) (sat_cons (step413 p h) (sat_cons (step418 p h) (sat_cons (step1061 p h) (sat_cons (step844 p h) (sat_cons (step962 p h) (sat_cons (step954 p h) (sat_cons (step958 p h) (sat_cons (step852 p h) (sat_cons (step938 p h) (sat_cons (step845 p h) (sat_cons (step848 p h) (sat_cons (step1098 p h) (sat_cons (step922 p h) (sat_cons (step804 p h) (sat_cons (step806 p h) (sat_cons (step914 p h) (sat_cons (step801 p h) (sat_cons (step790 p h) (sat_cons (step906 p h) (sat_cons (step795 p h) (sat_cons (step788 p h) (sat_cons (step374 p h) (sat_cons (step285 p h) (sat_cons (step271 p h) (sat_cons (step824 p h) (sat_cons (step281 p h) (sat_cons (step831 p h) (sat_cons (step292 p h) (sat_cons (step837 p h) (sat_cons (step815 p h) (sat_cons (step817 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1274 : List Lit := [(90, true), (997, true), (1000, true), (995, true), (1038, false), (1006, false)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true :=
  Snake9.LocalRup.prove_clause [c977, c402, c867, c866, c862, c859, c860, c864, c1052, c1053, c826, c1059, c871, c1063, c921, c937, c1178, c1263, c647, c649, c644, c645, c123, c343, c1110, c1165, c97, c99, c94, c588, c1273, c973, c1272, c1040, c694, c695, c106, c252, c116] c1274 (by decide) p (sat_cons (step977 p h) (sat_cons (step402 p h) (sat_cons (step867 p h) (sat_cons (step866 p h) (sat_cons (step862 p h) (sat_cons (step859 p h) (sat_cons (step860 p h) (sat_cons (step864 p h) (sat_cons (step1052 p h) (sat_cons (step1053 p h) (sat_cons (step826 p h) (sat_cons (step1059 p h) (sat_cons (step871 p h) (sat_cons (step1063 p h) (sat_cons (step921 p h) (sat_cons (step937 p h) (sat_cons (step1178 p h) (sat_cons (step1263 p h) (sat_cons (step647 p h) (sat_cons (step649 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step123 p h) (sat_cons (step343 p h) (sat_cons (step1110 p h) (sat_cons (step1165 p h) (sat_cons (step97 p h) (sat_cons (step99 p h) (sat_cons (step94 p h) (sat_cons (step588 p h) (sat_cons (step1273 p h) (sat_cons (step973 p h) (sat_cons (step1272 p h) (sat_cons (step1040 p h) (sat_cons (step694 p h) (sat_cons (step695 p h) (sat_cons (step106 p h) (sat_cons (step252 p h) (sat_cons (step116 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1275 : List Lit := [(883, true), (30, false), (31, true), (29, false)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true :=
  Snake9.LocalRup.prove_clause [c402, c694, c695, c106, c252, c116] c1275 (by decide) p (sat_cons (step402 p h) (sat_cons (step694 p h) (sat_cons (step695 p h) (sat_cons (step106 p h) (sat_cons (step252 p h) (sat_cons (step116 p h) (sat_nil p)))))))
def c1276 : List Lit := [(46, true), (903, true), (888, false)]
theorem step1276 (p : Nat → Bool) (h : Constraints p) : clause p c1276 = true :=
  Snake9.LocalRup.prove_clause [c1163, c728, c714, c687, c684, c685, c686, c689, c710, c711, c681, c733, c1041, c667, c1179, c1244] c1276 (by decide) p (sat_cons (step1163 p h) (sat_cons (step728 p h) (sat_cons (step714 p h) (sat_cons (step687 p h) (sat_cons (step684 p h) (sat_cons (step685 p h) (sat_cons (step686 p h) (sat_cons (step689 p h) (sat_cons (step710 p h) (sat_cons (step711 p h) (sat_cons (step681 p h) (sat_cons (step733 p h) (sat_cons (step1041 p h) (sat_cons (step667 p h) (sat_cons (step1179 p h) (sat_cons (step1244 p h) (sat_nil p)))))))))))))))))
def c1277 : List Lit := [(903, true), (889, false), (862, false)]
theorem step1277 (p : Nat → Bool) (h : Constraints p) : clause p c1277 = true :=
  Snake9.LocalRup.prove_clause [c1163, c707, c728, c733, c711, c667, c688, c1152] c1277 (by decide) p (sat_cons (step1163 p h) (sat_cons (step707 p h) (sat_cons (step728 p h) (sat_cons (step733 p h) (sat_cons (step711 p h) (sat_cons (step667 p h) (sat_cons (step688 p h) (sat_cons (step1152 p h) (sat_nil p)))))))))
def c1278 : List Lit := [(49, false), (1026, true), (117, true), (114, false), (98, false)]
theorem step1278 (p : Nat → Bool) (h : Constraints p) : clause p c1278 = true :=
  Snake9.LocalRup.prove_clause [c371, c372, c906, c910, c915] c1278 (by decide) p (sat_cons (step371 p h) (sat_cons (step372 p h) (sat_cons (step906 p h) (sat_cons (step910 p h) (sat_cons (step915 p h) (sat_nil p))))))
def c1279 : List Lit := [(889, false), (878, false), (862, false), (905, true)]
theorem step1279 (p : Nat → Bool) (h : Constraints p) : clause p c1279 = true :=
  Snake9.LocalRup.prove_clause [c1163, c687, c730, c719, c715, c690, c735, c1152, c667] c1279 (by decide) p (sat_cons (step1163 p h) (sat_cons (step687 p h) (sat_cons (step730 p h) (sat_cons (step719 p h) (sat_cons (step715 p h) (sat_cons (step690 p h) (sat_cons (step735 p h) (sat_cons (step1152 p h) (sat_cons (step667 p h) (sat_nil p))))))))))
def c1280 : List Lit := [(904, true), (889, false), (877, false), (862, false)]
theorem step1280 (p : Nat → Bool) (h : Constraints p) : clause p c1280 = true :=
  Snake9.LocalRup.prove_clause [c1163, c686, c711, c729, c734, c715, c667, c689, c1152] c1280 (by decide) p (sat_cons (step1163 p h) (sat_cons (step686 p h) (sat_cons (step711 p h) (sat_cons (step729 p h) (sat_cons (step734 p h) (sat_cons (step715 p h) (sat_cons (step667 p h) (sat_cons (step689 p h) (sat_cons (step1152 p h) (sat_nil p))))))))))
def c1281 : List Lit := [(903, true), (862, false), (857, false)]
theorem step1281 (p : Nat → Bool) (h : Constraints p) : clause p c1281 = true :=
  Snake9.LocalRup.prove_clause [c1162, c671, c1174, c733, c1040, c1043, c1223, c686, c689, c1042, c1152, c738, c672] c1281 (by decide) p (sat_cons (step1162 p h) (sat_cons (step671 p h) (sat_cons (step1174 p h) (sat_cons (step733 p h) (sat_cons (step1040 p h) (sat_cons (step1043 p h) (sat_cons (step1223 p h) (sat_cons (step686 p h) (sat_cons (step689 p h) (sat_cons (step1042 p h) (sat_cons (step1152 p h) (sat_cons (step738 p h) (sat_cons (step672 p h) (sat_nil p))))))))))))))
def c1282 : List Lit := [(883, true), (880, true), (817, true)]
theorem step1282 (p : Nat → Bool) (h : Constraints p) : clause p c1282 = true :=
  Snake9.LocalRup.prove_clause [c694, c1223, c689, c681, c1204, c1246, c567, c584, c1031] c1282 (by decide) p (sat_cons (step694 p h) (sat_cons (step1223 p h) (sat_cons (step689 p h) (sat_cons (step681 p h) (sat_cons (step1204 p h) (sat_cons (step1246 p h) (sat_cons (step567 p h) (sat_cons (step584 p h) (sat_cons (step1031 p h) (sat_nil p))))))))))
def c1283 : List Lit := [(2, false), (3, true)]
theorem step1283 (p : Nat → Bool) (h : Constraints p) : clause p c1283 = true :=
  Snake9.LocalRup.prove_clause [c1011, c2] c1283 (by decide) p (sat_cons (step1011 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1284 : List Lit := [(2, false), (120, true)]
theorem step1284 (p : Nat → Bool) (h : Constraints p) : clause p c1284 = true :=
  Snake9.LocalRup.prove_clause [c1011, c3] c1284 (by decide) p (sat_cons (step1011 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1285 : List Lit := [(3, false), (53, true)]
theorem step1285 (p : Nat → Bool) (h : Constraints p) : clause p c1285 = true :=
  Snake9.LocalRup.prove_clause [c391, c4] c1285 (by decide) p (sat_cons (step391 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1286 : List Lit := [(3, false), (2, true)]
theorem step1286 (p : Nat → Bool) (h : Constraints p) : clause p c1286 = true :=
  Snake9.LocalRup.prove_clause [c391, c5] c1286 (by decide) p (sat_cons (step391 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1287 : List Lit := [(34, true), (4, false)]
theorem step1287 (p : Nat → Bool) (h : Constraints p) : clause p c1287 = true :=
  Snake9.LocalRup.prove_clause [c392, c6] c1287 (by decide) p (sat_cons (step392 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1288 : List Lit := [(4, false), (6, true)]
theorem step1288 (p : Nat → Bool) (h : Constraints p) : clause p c1288 = true :=
  Snake9.LocalRup.prove_clause [c392, c7] c1288 (by decide) p (sat_cons (step392 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1289 : List Lit := [(8, true), (40, true), (5, false)]
theorem step1289 (p : Nat → Bool) (h : Constraints p) : clause p c1289 = true :=
  Snake9.LocalRup.prove_clause [c393, c9] c1289 (by decide) p (sat_cons (step393 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1290 : List Lit := [(6, true), (40, true), (5, false)]
theorem step1290 (p : Nat → Bool) (h : Constraints p) : clause p c1290 = true :=
  Snake9.LocalRup.prove_clause [c393, c10] c1290 (by decide) p (sat_cons (step393 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1291 : List Lit := [(8, true), (10, false), (52, true)]
theorem step1291 (p : Nat → Bool) (h : Constraints p) : clause p c1291 = true :=
  Snake9.LocalRup.prove_clause [c394, c22] c1291 (by decide) p (sat_cons (step394 p h) (sat_cons (step22 p h) (sat_nil p)))
def c1292 : List Lit := [(22, true), (12, false), (16, true)]
theorem step1292 (p : Nat → Bool) (h : Constraints p) : clause p c1292 = true :=
  Snake9.LocalRup.prove_clause [c395, c25] c1292 (by decide) p (sat_cons (step395 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1293 : List Lit := [(13, true), (22, true), (12, false)]
theorem step1293 (p : Nat → Bool) (h : Constraints p) : clause p c1293 = true :=
  Snake9.LocalRup.prove_clause [c395, c26] c1293 (by decide) p (sat_cons (step395 p h) (sat_cons (step26 p h) (sat_nil p)))
def c1294 : List Lit := [(13, true), (12, false), (16, true)]
theorem step1294 (p : Nat → Bool) (h : Constraints p) : clause p c1294 = true :=
  Snake9.LocalRup.prove_clause [c395, c27] c1294 (by decide) p (sat_cons (step395 p h) (sat_cons (step27 p h) (sat_nil p)))
def c1295 : List Lit := [(14, false), (34, true), (26, true)]
theorem step1295 (p : Nat → Bool) (h : Constraints p) : clause p c1295 = true :=
  Snake9.LocalRup.prove_clause [c396, c31] c1295 (by decide) p (sat_cons (step396 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1296 : List Lit := [(19, true), (14, false), (34, true)]
theorem step1296 (p : Nat → Bool) (h : Constraints p) : clause p c1296 = true :=
  Snake9.LocalRup.prove_clause [c396, c32] c1296 (by decide) p (sat_cons (step396 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1297 : List Lit := [(19, true), (14, false), (26, true)]
theorem step1297 (p : Nat → Bool) (h : Constraints p) : clause p c1297 = true :=
  Snake9.LocalRup.prove_clause [c396, c33] c1297 (by decide) p (sat_cons (step396 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1298 : List Lit := [(35, true), (86, true), (15, false), (20, true)]
theorem step1298 (p : Nat → Bool) (h : Constraints p) : clause p c1298 = true :=
  Snake9.LocalRup.prove_clause [c397, c34] c1298 (by decide) p (sat_cons (step397 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1299 : List Lit := [(13, true), (86, true), (20, true), (15, false)]
theorem step1299 (p : Nat → Bool) (h : Constraints p) : clause p c1299 = true :=
  Snake9.LocalRup.prove_clause [c397, c35] c1299 (by decide) p (sat_cons (step397 p h) (sat_cons (step35 p h) (sat_nil p)))
def c1300 : List Lit := [(13, true), (35, true), (20, true), (15, false)]
theorem step1300 (p : Nat → Bool) (h : Constraints p) : clause p c1300 = true :=
  Snake9.LocalRup.prove_clause [c397, c36] c1300 (by decide) p (sat_cons (step397 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1301 : List Lit := [(18, false), (19, true), (20, true), (40, true), (28, true)]
theorem step1301 (p : Nat → Bool) (h : Constraints p) : clause p c1301 = true :=
  Snake9.LocalRup.prove_clause [c398, c48] c1301 (by decide) p (sat_cons (step398 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1302 : List Lit := [(28, true), (16, true), (40, true), (20, true), (18, false)]
theorem step1302 (p : Nat → Bool) (h : Constraints p) : clause p c1302 = true :=
  Snake9.LocalRup.prove_clause [c398, c49] c1302 (by decide) p (sat_cons (step398 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1303 : List Lit := [(28, true), (16, true), (40, true), (18, false), (19, true)]
theorem step1303 (p : Nat → Bool) (h : Constraints p) : clause p c1303 = true :=
  Snake9.LocalRup.prove_clause [c398, c50] c1303 (by decide) p (sat_cons (step398 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1304 : List Lit := [(40, true), (16, true), (19, true), (20, true), (18, false)]
theorem step1304 (p : Nat → Bool) (h : Constraints p) : clause p c1304 = true :=
  Snake9.LocalRup.prove_clause [c398, c51] c1304 (by decide) p (sat_cons (step398 p h) (sat_cons (step51 p h) (sat_nil p)))
def c1305 : List Lit := [(28, true), (16, true), (19, true), (20, true), (18, false)]
theorem step1305 (p : Nat → Bool) (h : Constraints p) : clause p c1305 = true :=
  Snake9.LocalRup.prove_clause [c398, c52] c1305 (by decide) p (sat_cons (step398 p h) (sat_cons (step52 p h) (sat_nil p)))
def c1306 : List Lit := [(25, true), (23, false), (26, true)]
theorem step1306 (p : Nat → Bool) (h : Constraints p) : clause p c1306 = true :=
  Snake9.LocalRup.prove_clause [c399, c81] c1306 (by decide) p (sat_cons (step399 p h) (sat_cons (step81 p h) (sat_nil p)))
def c1307 : List Lit := [(22, true), (23, false), (26, true)]
theorem step1307 (p : Nat → Bool) (h : Constraints p) : clause p c1307 = true :=
  Snake9.LocalRup.prove_clause [c399, c82] c1307 (by decide) p (sat_cons (step399 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1308 : List Lit := [(25, true), (22, true), (23, false)]
theorem step1308 (p : Nat → Bool) (h : Constraints p) : clause p c1308 = true :=
  Snake9.LocalRup.prove_clause [c399, c83] c1308 (by decide) p (sat_cons (step399 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1309 : List Lit := [(25, true), (31, true), (27, false)]
theorem step1309 (p : Nat → Bool) (h : Constraints p) : clause p c1309 = true :=
  Snake9.LocalRup.prove_clause [c400, c100] c1309 (by decide) p (sat_cons (step400 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1310 : List Lit := [(17, true), (31, true), (27, false)]
theorem step1310 (p : Nat → Bool) (h : Constraints p) : clause p c1310 = true :=
  Snake9.LocalRup.prove_clause [c400, c101] c1310 (by decide) p (sat_cons (step400 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1311 : List Lit := [(25, true), (17, true), (27, false)]
theorem step1311 (p : Nat → Bool) (h : Constraints p) : clause p c1311 = true :=
  Snake9.LocalRup.prove_clause [c400, c102] c1311 (by decide) p (sat_cons (step400 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1312 : List Lit := [(28, true), (26, true), (100, true), (31, true), (29, false)]
theorem step1312 (p : Nat → Bool) (h : Constraints p) : clause p c1312 = true :=
  Snake9.LocalRup.prove_clause [c401, c110] c1312 (by decide) p (sat_cons (step401 p h) (sat_cons (step110 p h) (sat_nil p)))
def c1313 : List Lit := [(19, true), (28, true), (100, true), (29, false), (31, true)]
theorem step1313 (p : Nat → Bool) (h : Constraints p) : clause p c1313 = true :=
  Snake9.LocalRup.prove_clause [c401, c111] c1313 (by decide) p (sat_cons (step401 p h) (sat_cons (step111 p h) (sat_nil p)))
def c1314 : List Lit := [(19, true), (26, true), (29, false), (100, true), (31, true)]
theorem step1314 (p : Nat → Bool) (h : Constraints p) : clause p c1314 = true :=
  Snake9.LocalRup.prove_clause [c401, c112] c1314 (by decide) p (sat_cons (step401 p h) (sat_cons (step112 p h) (sat_nil p)))
def c1315 : List Lit := [(19, true), (26, true), (29, false), (28, true), (31, true)]
theorem step1315 (p : Nat → Bool) (h : Constraints p) : clause p c1315 = true :=
  Snake9.LocalRup.prove_clause [c401, c113] c1315 (by decide) p (sat_cons (step401 p h) (sat_cons (step113 p h) (sat_nil p)))
def c1316 : List Lit := [(28, true), (52, true), (31, true), (30, false)]
theorem step1316 (p : Nat → Bool) (h : Constraints p) : clause p c1316 = true :=
  Snake9.LocalRup.prove_clause [c402, c116] c1316 (by decide) p (sat_cons (step402 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1317 : List Lit := [(20, true), (52, true), (31, true), (30, false)]
theorem step1317 (p : Nat → Bool) (h : Constraints p) : clause p c1317 = true :=
  Snake9.LocalRup.prove_clause [c402, c117] c1317 (by decide) p (sat_cons (step402 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1318 : List Lit := [(20, true), (52, true), (30, false), (28, true)]
theorem step1318 (p : Nat → Bool) (h : Constraints p) : clause p c1318 = true :=
  Snake9.LocalRup.prove_clause [c402, c118] c1318 (by decide) p (sat_cons (step402 p h) (sat_cons (step118 p h) (sat_nil p)))
def c1319 : List Lit := [(20, true), (28, true), (31, true), (30, false)]
theorem step1319 (p : Nat → Bool) (h : Constraints p) : clause p c1319 = true :=
  Snake9.LocalRup.prove_clause [c402, c119] c1319 (by decide) p (sat_cons (step402 p h) (sat_cons (step119 p h) (sat_nil p)))
def c1320 : List Lit := [(32, false), (38, true), (34, true)]
theorem step1320 (p : Nat → Bool) (h : Constraints p) : clause p c1320 = true :=
  Snake9.LocalRup.prove_clause [c403, c124] c1320 (by decide) p (sat_cons (step403 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1321 : List Lit := [(33, true), (32, false), (38, true)]
theorem step1321 (p : Nat → Bool) (h : Constraints p) : clause p c1321 = true :=
  Snake9.LocalRup.prove_clause [c403, c125] c1321 (by decide) p (sat_cons (step403 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1322 : List Lit := [(33, true), (32, false), (34, true)]
theorem step1322 (p : Nat → Bool) (h : Constraints p) : clause p c1322 = true :=
  Snake9.LocalRup.prove_clause [c403, c126] c1322 (by decide) p (sat_cons (step403 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1323 : List Lit := [(35, true), (42, true), (34, true), (47, true), (36, false)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true :=
  Snake9.LocalRup.prove_clause [c404, c163] c1323 (by decide) p (sat_cons (step404 p h) (sat_cons (step163 p h) (sat_nil p)))
def c1324 : List Lit := [(38, true), (40, true), (48, true), (37, false)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true :=
  Snake9.LocalRup.prove_clause [c405, c167] c1324 (by decide) p (sat_cons (step405 p h) (sat_cons (step167 p h) (sat_nil p)))
end B112E159
