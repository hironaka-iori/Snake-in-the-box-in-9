import B112E081Inputs
namespace B112E081
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1194 : List Lit := [(105, true)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true :=
  Snake9.LocalRup.prove_clause [c524, c523] c1194 (by decide) p (sat_cons (step524 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1195 : List Lit := [(222, true), (110, true)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true :=
  Snake9.LocalRup.prove_clause [c1194, c525] c1195 (by decide) p (sat_cons (step1194 p h) (sat_cons (step525 p h) (sat_nil p)))
def c1196 : List Lit := [(37, false)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true :=
  Snake9.LocalRup.prove_clause [c546, c148] c1196 (by decide) p (sat_cons (step546 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1197 : List Lit := [(43, false)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true :=
  Snake9.LocalRup.prove_clause [c549, c159] c1197 (by decide) p (sat_cons (step549 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1198 : List Lit := [(45, false)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true :=
  Snake9.LocalRup.prove_clause [c550, c161] c1198 (by decide) p (sat_cons (step550 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1199 : List Lit := [(462, false)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true :=
  Snake9.LocalRup.prove_clause [c724, c721] c1199 (by decide) p (sat_cons (step724 p h) (sat_cons (step721 p h) (sat_nil p)))
def c1200 : List Lit := [(348, false)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true :=
  Snake9.LocalRup.prove_clause [c724, c723] c1200 (by decide) p (sat_cons (step724 p h) (sat_cons (step723 p h) (sat_nil p)))
def c1201 : List Lit := [(404, false)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true :=
  Snake9.LocalRup.prove_clause [c1199, c720] c1201 (by decide) p (sat_cons (step1199 p h) (sat_cons (step720 p h) (sat_nil p)))
def c1202 : List Lit := [(290, false)]
theorem step1202 (p : Nat → Bool) (h : Constraints p) : clause p c1202 = true :=
  Snake9.LocalRup.prove_clause [c1200, c656] c1202 (by decide) p (sat_cons (step1200 p h) (sat_cons (step656 p h) (sat_nil p)))
def c1203 : List Lit := [(374, false)]
theorem step1203 (p : Nat → Bool) (h : Constraints p) : clause p c1203 = true :=
  Snake9.LocalRup.prove_clause [c1201, c691] c1203 (by decide) p (sat_cons (step1201 p h) (sat_cons (step691 p h) (sat_nil p)))
def c1204 : List Lit := [(288, false)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true :=
  Snake9.LocalRup.prove_clause [c1202, c619] c1204 (by decide) p (sat_cons (step1202 p h) (sat_cons (step619 p h) (sat_nil p)))
def c1205 : List Lit := [(260, false)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true :=
  Snake9.LocalRup.prove_clause [c1202, c622] c1205 (by decide) p (sat_cons (step1202 p h) (sat_cons (step622 p h) (sat_nil p)))
def c1206 : List Lit := [(360, false)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true :=
  Snake9.LocalRup.prove_clause [c1203, c678] c1206 (by decide) p (sat_cons (step1203 p h) (sat_cons (step678 p h) (sat_nil p)))
def c1207 : List Lit := [(286, false)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true :=
  Snake9.LocalRup.prove_clause [c1204, c617] c1207 (by decide) p (sat_cons (step1204 p h) (sat_cons (step617 p h) (sat_nil p)))
def c1208 : List Lit := [(258, false)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true :=
  Snake9.LocalRup.prove_clause [c1205, c602] c1208 (by decide) p (sat_cons (step1205 p h) (sat_cons (step602 p h) (sat_nil p)))
def c1209 : List Lit := [(246, false)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true :=
  Snake9.LocalRup.prove_clause [c1205, c605] c1209 (by decide) p (sat_cons (step1205 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1210 : List Lit := [(358, false)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true :=
  Snake9.LocalRup.prove_clause [c1206, c665] c1210 (by decide) p (sat_cons (step1206 p h) (sat_cons (step665 p h) (sat_nil p)))
def c1211 : List Lit := [(256, false)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true :=
  Snake9.LocalRup.prove_clause [c1208, c600] c1211 (by decide) p (sat_cons (step1208 p h) (sat_cons (step600 p h) (sat_nil p)))
def c1212 : List Lit := [(244, false)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true :=
  Snake9.LocalRup.prove_clause [c1209, c590] c1212 (by decide) p (sat_cons (step1209 p h) (sat_cons (step590 p h) (sat_nil p)))
def c1213 : List Lit := [(240, false)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true :=
  Snake9.LocalRup.prove_clause [c1212, c588] c1213 (by decide) p (sat_cons (step1212 p h) (sat_cons (step588 p h) (sat_nil p)))
def c1214 : List Lit := [(856, true)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true :=
  Snake9.LocalRup.prove_clause [c1196, c814] c1214 (by decide) p (sat_cons (step1196 p h) (sat_cons (step814 p h) (sat_nil p)))
def c1215 : List Lit := [(35, true), (857, true)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true :=
  Snake9.LocalRup.prove_clause [c1196, c815] c1215 (by decide) p (sat_cons (step1196 p h) (sat_cons (step815 p h) (sat_nil p)))
def c1216 : List Lit := [(860, true)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true :=
  Snake9.LocalRup.prove_clause [c1214, c818] c1216 (by decide) p (sat_cons (step1214 p h) (sat_cons (step818 p h) (sat_nil p)))
def c1217 : List Lit := [(858, false), (861, true)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true :=
  Snake9.LocalRup.prove_clause [c1214, c819] c1217 (by decide) p (sat_cons (step1214 p h) (sat_cons (step819 p h) (sat_nil p)))
def c1218 : List Lit := [(864, true)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true :=
  Snake9.LocalRup.prove_clause [c1216, c823] c1218 (by decide) p (sat_cons (step1216 p h) (sat_cons (step823 p h) (sat_nil p)))
def c1219 : List Lit := [(853, false), (865, true)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true :=
  Snake9.LocalRup.prove_clause [c1216, c825] c1219 (by decide) p (sat_cons (step1216 p h) (sat_cons (step825 p h) (sat_nil p)))
def c1220 : List Lit := [(854, false), (866, true)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true :=
  Snake9.LocalRup.prove_clause [c1216, c828] c1220 (by decide) p (sat_cons (step1216 p h) (sat_cons (step828 p h) (sat_nil p)))
def c1221 : List Lit := [(855, false), (867, true)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true :=
  Snake9.LocalRup.prove_clause [c1216, c832] c1221 (by decide) p (sat_cons (step1216 p h) (sat_cons (step832 p h) (sat_nil p)))
def c1222 : List Lit := [(872, true)]
theorem step1222 (p : Nat → Bool) (h : Constraints p) : clause p c1222 = true :=
  Snake9.LocalRup.prove_clause [c1197, c1198, c835] c1222 (by decide) p (sat_cons (step1197 p h) (sat_cons (step1198 p h) (sat_cons (step835 p h) (sat_nil p))))
def c1223 : List Lit := [(876, true)]
theorem step1223 (p : Nat → Bool) (h : Constraints p) : clause p c1223 = true :=
  Snake9.LocalRup.prove_clause [c1222, c839] c1223 (by decide) p (sat_cons (step1222 p h) (sat_cons (step839 p h) (sat_nil p)))
def c1224 : List Lit := [(873, false), (877, true)]
theorem step1224 (p : Nat → Bool) (h : Constraints p) : clause p c1224 = true :=
  Snake9.LocalRup.prove_clause [c1222, c840] c1224 (by decide) p (sat_cons (step1222 p h) (sat_cons (step840 p h) (sat_nil p)))
def c1225 : List Lit := [(874, false), (878, true)]
theorem step1225 (p : Nat → Bool) (h : Constraints p) : clause p c1225 = true :=
  Snake9.LocalRup.prove_clause [c1222, c841] c1225 (by decide) p (sat_cons (step1222 p h) (sat_cons (step841 p h) (sat_nil p)))
def c1226 : List Lit := [(888, true)]
theorem step1226 (p : Nat → Bool) (h : Constraints p) : clause p c1226 = true :=
  Snake9.LocalRup.prove_clause [c1223, c856] c1226 (by decide) p (sat_cons (step1223 p h) (sat_cons (step856 p h) (sat_nil p)))
def c1227 : List Lit := [(883, false), (889, true)]
theorem step1227 (p : Nat → Bool) (h : Constraints p) : clause p c1227 = true :=
  Snake9.LocalRup.prove_clause [c1223, c857] c1227 (by decide) p (sat_cons (step1223 p h) (sat_cons (step857 p h) (sat_nil p)))
def c1228 : List Lit := [(884, false), (890, true)]
theorem step1228 (p : Nat → Bool) (h : Constraints p) : clause p c1228 = true :=
  Snake9.LocalRup.prove_clause [c1223, c858] c1228 (by decide) p (sat_cons (step1223 p h) (sat_cons (step858 p h) (sat_nil p)))
def c1229 : List Lit := [(885, false), (891, true)]
theorem step1229 (p : Nat → Bool) (h : Constraints p) : clause p c1229 = true :=
  Snake9.LocalRup.prove_clause [c1223, c859] c1229 (by decide) p (sat_cons (step1223 p h) (sat_cons (step859 p h) (sat_nil p)))
def c1230 : List Lit := [(886, false), (892, true)]
theorem step1230 (p : Nat → Bool) (h : Constraints p) : clause p c1230 = true :=
  Snake9.LocalRup.prove_clause [c1223, c860] c1230 (by decide) p (sat_cons (step1223 p h) (sat_cons (step860 p h) (sat_nil p)))
def c1231 : List Lit := [(889, false), (898, true)]
theorem step1231 (p : Nat → Bool) (h : Constraints p) : clause p c1231 = true :=
  Snake9.LocalRup.prove_clause [c1218, c871] c1231 (by decide) p (sat_cons (step1218 p h) (sat_cons (step871 p h) (sat_nil p)))
def c1232 : List Lit := [(890, false), (899, true)]
theorem step1232 (p : Nat → Bool) (h : Constraints p) : clause p c1232 = true :=
  Snake9.LocalRup.prove_clause [c1218, c872] c1232 (by decide) p (sat_cons (step1218 p h) (sat_cons (step872 p h) (sat_nil p)))
def c1233 : List Lit := [(891, false), (900, true)]
theorem step1233 (p : Nat → Bool) (h : Constraints p) : clause p c1233 = true :=
  Snake9.LocalRup.prove_clause [c1218, c873] c1233 (by decide) p (sat_cons (step1218 p h) (sat_cons (step873 p h) (sat_nil p)))
def c1234 : List Lit := [(892, false), (901, true)]
theorem step1234 (p : Nat → Bool) (h : Constraints p) : clause p c1234 = true :=
  Snake9.LocalRup.prove_clause [c1218, c874] c1234 (by decide) p (sat_cons (step1218 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1235 : List Lit := [(893, false), (902, true)]
theorem step1235 (p : Nat → Bool) (h : Constraints p) : clause p c1235 = true :=
  Snake9.LocalRup.prove_clause [c1218, c875] c1235 (by decide) p (sat_cons (step1218 p h) (sat_cons (step875 p h) (sat_nil p)))
def c1236 : List Lit := [(894, false), (903, true)]
theorem step1236 (p : Nat → Bool) (h : Constraints p) : clause p c1236 = true :=
  Snake9.LocalRup.prove_clause [c1218, c876] c1236 (by decide) p (sat_cons (step1218 p h) (sat_cons (step876 p h) (sat_nil p)))
def c1237 : List Lit := [(867, false), (900, true)]
theorem step1237 (p : Nat → Bool) (h : Constraints p) : clause p c1237 = true :=
  Snake9.LocalRup.prove_clause [c1226, c889] c1237 (by decide) p (sat_cons (step1226 p h) (sat_cons (step889 p h) (sat_nil p)))
def c1238 : List Lit := [(868, false), (901, true)]
theorem step1238 (p : Nat → Bool) (h : Constraints p) : clause p c1238 = true :=
  Snake9.LocalRup.prove_clause [c1226, c894] c1238 (by decide) p (sat_cons (step1226 p h) (sat_cons (step894 p h) (sat_nil p)))
def c1239 : List Lit := [(870, false), (903, true)]
theorem step1239 (p : Nat → Bool) (h : Constraints p) : clause p c1239 = true :=
  Snake9.LocalRup.prove_clause [c1226, c901] c1239 (by decide) p (sat_cons (step1226 p h) (sat_cons (step901 p h) (sat_nil p)))
def c1240 : List Lit := [(34, false), (841, true), (19, false), (89, false)]
theorem step1240 (p : Nat → Bool) (h : Constraints p) : clause p c1240 = true :=
  Snake9.LocalRup.prove_clause [c92, c76, c86, c95, c96, c726, c756, c762, c728, c761, c770, c746, c787, c793] c1240 (by decide) p (sat_cons (step92 p h) (sat_cons (step76 p h) (sat_cons (step86 p h) (sat_cons (step95 p h) (sat_cons (step96 p h) (sat_cons (step726 p h) (sat_cons (step756 p h) (sat_cons (step762 p h) (sat_cons (step728 p h) (sat_cons (step761 p h) (sat_cons (step770 p h) (sat_cons (step746 p h) (sat_cons (step787 p h) (sat_cons (step793 p h) (sat_nil p)))))))))))))))
def c1241 : List Lit := [(810, true)]
theorem step1241 (p : Nat → Bool) (h : Constraints p) : clause p c1241 = true :=
  Snake9.LocalRup.prove_clause [c536, c744, c746, c739, c741, c728, c736, c733, c726, c48, c39] c1241 (by decide) p (sat_cons (step536 p h) (sat_cons (step744 p h) (sat_cons (step746 p h) (sat_cons (step739 p h) (sat_cons (step741 p h) (sat_cons (step728 p h) (sat_cons (step736 p h) (sat_cons (step733 p h) (sat_cons (step726 p h) (sat_cons (step48 p h) (sat_cons (step39 p h) (sat_nil p))))))))))))
def c1242 : List Lit := [(87, true), (1004, true), (215, true), (218, true), (205, true), (59, true), (47, true), (60, true), (92, true), (32, true)]
theorem step1242 (p : Nat → Bool) (h : Constraints p) : clause p c1242 = true :=
  Snake9.LocalRup.prove_clause [c573, c575, c574, c1054, c476, c1060, c503, c1082, c1062, c509, c1071, c1065, c1066, c518, c505, c506, c516, c520] c1242 (by decide) p (sat_cons (step573 p h) (sat_cons (step575 p h) (sat_cons (step574 p h) (sat_cons (step1054 p h) (sat_cons (step476 p h) (sat_cons (step1060 p h) (sat_cons (step503 p h) (sat_cons (step1082 p h) (sat_cons (step1062 p h) (sat_cons (step509 p h) (sat_cons (step1071 p h) (sat_cons (step1065 p h) (sat_cons (step1066 p h) (sat_cons (step518 p h) (sat_cons (step505 p h) (sat_cons (step506 p h) (sat_cons (step516 p h) (sat_cons (step520 p h) (sat_nil p)))))))))))))))))))
def c1243 : List Lit := [(881, false), (869, false), (215, true), (218, true), (205, true), (59, true), (47, true), (46, false), (60, true), (92, true), (32, true), (1, false), (840, false)]
theorem step1243 (p : Nat → Bool) (h : Constraints p) : clause p c1243 = true :=
  Snake9.LocalRup.prove_clause [c1156, c940, c942, c965, c1023, c1054, c1057, c1077, c1097, c837, c1224, c848, c862, c898, c920, c1152, c1107, c1103, c1242, c173, c176, c170, c843, c950, c838, c851, c953, c1225, c868, c966, c900, c1029, c922, c1108, c1154] c1243 (by decide) p (sat_cons (step1156 p h) (sat_cons (step940 p h) (sat_cons (step942 p h) (sat_cons (step965 p h) (sat_cons (step1023 p h) (sat_cons (step1054 p h) (sat_cons (step1057 p h) (sat_cons (step1077 p h) (sat_cons (step1097 p h) (sat_cons (step837 p h) (sat_cons (step1224 p h) (sat_cons (step848 p h) (sat_cons (step862 p h) (sat_cons (step898 p h) (sat_cons (step920 p h) (sat_cons (step1152 p h) (sat_cons (step1107 p h) (sat_cons (step1103 p h) (sat_cons (step1242 p h) (sat_cons (step173 p h) (sat_cons (step176 p h) (sat_cons (step170 p h) (sat_cons (step843 p h) (sat_cons (step950 p h) (sat_cons (step838 p h) (sat_cons (step851 p h) (sat_cons (step953 p h) (sat_cons (step1225 p h) (sat_cons (step868 p h) (sat_cons (step966 p h) (sat_cons (step900 p h) (sat_cons (step1029 p h) (sat_cons (step922 p h) (sat_cons (step1108 p h) (sat_cons (step1154 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1244 : List Lit := [(822, false), (818, false), (18, true), (19, false), (841, true), (16, true), (89, false)]
theorem step1244 (p : Nat → Bool) (h : Constraints p) : clause p c1244 = true :=
  Snake9.TreeRup.prove_clause [c1241, c537, c542, c541, c534, c530, c1200, c724, c1196, c548, c547, c1156, c793, c758, c784, c773, c1240, c806, c770, c771, c783, c787, c765, c766, c797, c792, c761, c749, c58, c66, c85, c726, c764, c728, c731, c108, c747, c812, c739, c741, c737, c733, c734, c128, c30, c123, c120, c36, c99, c102, c103, c118, c37, c8, c12, c1215, c611, c940, c1158, c31, c612, c942, c837, c613, c1224, c616, c861, c618, c654, c655, c722, c652, c717, c636, c637, c716, c635, c627, c705, c706, c631, c626, c704, c699, c629, c630, c625, c702, c703, c694, c151, c150, c147, c701, c700, c158, c155, c817, c822, c831, c897, c919, c1151, c1243, c846, c174, c175, c950, c1242, c953, c1103, c966, c1111, c1029] c1244 (by decide) p (sat_cons (step1241 p h) (sat_cons (step537 p h) (sat_cons (step542 p h) (sat_cons (step541 p h) (sat_cons (step534 p h) (sat_cons (step530 p h) (sat_cons (step1200 p h) (sat_cons (step724 p h) (sat_cons (step1196 p h) (sat_cons (step548 p h) (sat_cons (step547 p h) (sat_cons (step1156 p h) (sat_cons (step793 p h) (sat_cons (step758 p h) (sat_cons (step784 p h) (sat_cons (step773 p h) (sat_cons (step1240 p h) (sat_cons (step806 p h) (sat_cons (step770 p h) (sat_cons (step771 p h) (sat_cons (step783 p h) (sat_cons (step787 p h) (sat_cons (step765 p h) (sat_cons (step766 p h) (sat_cons (step797 p h) (sat_cons (step792 p h) (sat_cons (step761 p h) (sat_cons (step749 p h) (sat_cons (step58 p h) (sat_cons (step66 p h) (sat_cons (step85 p h) (sat_cons (step726 p h) (sat_cons (step764 p h) (sat_cons (step728 p h) (sat_cons (step731 p h) (sat_cons (step108 p h) (sat_cons (step747 p h) (sat_cons (step812 p h) (sat_cons (step739 p h) (sat_cons (step741 p h) (sat_cons (step737 p h) (sat_cons (step733 p h) (sat_cons (step734 p h) (sat_cons (step128 p h) (sat_cons (step30 p h) (sat_cons (step123 p h) (sat_cons (step120 p h) (sat_cons (step36 p h) (sat_cons (step99 p h) (sat_cons (step102 p h) (sat_cons (step103 p h) (sat_cons (step118 p h) (sat_cons (step37 p h) (sat_cons (step8 p h) (sat_cons (step12 p h) (sat_cons (step1215 p h) (sat_cons (step611 p h) (sat_cons (step940 p h) (sat_cons (step1158 p h) (sat_cons (step31 p h) (sat_cons (step612 p h) (sat_cons (step942 p h) (sat_cons (step837 p h) (sat_cons (step613 p h) (sat_cons (step1224 p h) (sat_cons (step616 p h) (sat_cons (step861 p h) (sat_cons (step618 p h) (sat_cons (step654 p h) (sat_cons (step655 p h) (sat_cons (step722 p h) (sat_cons (step652 p h) (sat_cons (step717 p h) (sat_cons (step636 p h) (sat_cons (step637 p h) (sat_cons (step716 p h) (sat_cons (step635 p h) (sat_cons (step627 p h) (sat_cons (step705 p h) (sat_cons (step706 p h) (sat_cons (step631 p h) (sat_cons (step626 p h) (sat_cons (step704 p h) (sat_cons (step699 p h) (sat_cons (step629 p h) (sat_cons (step630 p h) (sat_cons (step625 p h) (sat_cons (step702 p h) (sat_cons (step703 p h) (sat_cons (step694 p h) (sat_cons (step151 p h) (sat_cons (step150 p h) (sat_cons (step147 p h) (sat_cons (step701 p h) (sat_cons (step700 p h) (sat_cons (step158 p h) (sat_cons (step155 p h) (sat_cons (step817 p h) (sat_cons (step822 p h) (sat_cons (step831 p h) (sat_cons (step897 p h) (sat_cons (step919 p h) (sat_cons (step1151 p h) (sat_cons (step1243 p h) (sat_cons (step846 p h) (sat_cons (step174 p h) (sat_cons (step175 p h) (sat_cons (step950 p h) (sat_cons (step1242 p h) (sat_cons (step953 p h) (sat_cons (step1103 p h) (sat_cons (step966 p h) (sat_cons (step1111 p h) (sat_cons (step1029 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1245 : List Lit := [(34, true), (854, true), (31, false), (29, false)]
theorem step1245 (p : Nat → Bool) (h : Constraints p) : clause p c1245 = true :=
  Snake9.LocalRup.prove_clause [c810, c806, c808, c812, c126] c1245 (by decide) p (sat_cons (step810 p h) (sat_cons (step806 p h) (sat_cons (step808 p h) (sat_cons (step812 p h) (sat_cons (step126 p h) (sat_nil p))))))
def c1246 : List Lit := [(853, true), (31, false), (29, false)]
theorem step1246 (p : Nat → Bool) (h : Constraints p) : clause p c1246 = true :=
  Snake9.LocalRup.prove_clause [c809, c811, c807, c126] c1246 (by decide) p (sat_cons (step809 p h) (sat_cons (step811 p h) (sat_cons (step807 p h) (sat_cons (step126 p h) (sat_nil p)))))
def c1247 : List Lit := [(939, true), (58, true), (55, false), (69, true)]
theorem step1247 (p : Nat → Bool) (h : Constraints p) : clause p c1247 = true :=
  Snake9.LocalRup.prove_clause [c559, c950, c954, c956, c952, c947, c416, c409] c1247 (by decide) p (sat_cons (step559 p h) (sat_cons (step950 p h) (sat_cons (step954 p h) (sat_cons (step956 p h) (sat_cons (step952 p h) (sat_cons (step947 p h) (sat_cons (step416 p h) (sat_cons (step409 p h) (sat_nil p)))))))))
def c1248 : List Lit := [(68, false), (62, false), (58, true), (52, false)]
theorem step1248 (p : Nat → Bool) (h : Constraints p) : clause p c1248 = true :=
  Snake9.LocalRup.prove_clause [c559, c417, c389] c1248 (by decide) p (sat_cons (step559 p h) (sat_cons (step417 p h) (sat_cons (step389 p h) (sat_nil p))))
def c1249 : List Lit := [(934, true), (67, false), (55, false)]
theorem step1249 (p : Nat → Bool) (h : Constraints p) : clause p c1249 = true :=
  Snake9.LocalRup.prove_clause [c947, c948, c407] c1249 (by decide) p (sat_cons (step947 p h) (sat_cons (step948 p h) (sat_cons (step407 p h) (sat_nil p))))
def c1250 : List Lit := [(77, false), (85, false), (74, false)]
theorem step1250 (p : Nat → Bool) (h : Constraints p) : clause p c1250 = true :=
  Snake9.LocalRup.prove_clause [c567, c443, c466] c1250 (by decide) p (sat_cons (step567 p h) (sat_cons (step443 p h) (sat_cons (step466 p h) (sat_nil p))))
def c1251 : List Lit := [(966, true), (71, true)]
theorem step1251 (p : Nat → Bool) (h : Constraints p) : clause p c1251 = true :=
  Snake9.LocalRup.prove_clause [c981, c988, c1014, c1011, c991, c989, c1000, c982, c984, c998, c1250] c1251 (by decide) p (sat_cons (step981 p h) (sat_cons (step988 p h) (sat_cons (step1014 p h) (sat_cons (step1011 p h) (sat_cons (step991 p h) (sat_cons (step989 p h) (sat_cons (step1000 p h) (sat_cons (step982 p h) (sat_cons (step984 p h) (sat_cons (step998 p h) (sat_cons (step1250 p h) (sat_nil p))))))))))))
def c1252 : List Lit := [(934, true), (64, true), (55, false)]
theorem step1252 (p : Nat → Bool) (h : Constraints p) : clause p c1252 = true :=
  Snake9.LocalRup.prove_clause [c557, c948, c1249, c395] c1252 (by decide) p (sat_cons (step557 p h) (sat_cons (step948 p h) (sat_cons (step1249 p h) (sat_cons (step395 p h) (sat_nil p)))))
def c1253 : List Lit := [(68, false), (58, true), (930, true), (52, false)]
theorem step1253 (p : Nat → Bool) (h : Constraints p) : clause p c1253 = true :=
  Snake9.LocalRup.prove_clause [c559, c417, c388, c1248, c941] c1253 (by decide) p (sat_cons (step559 p h) (sat_cons (step417 p h) (sat_cons (step388 p h) (sat_cons (step1248 p h) (sat_cons (step941 p h) (sat_nil p))))))
def c1254 : List Lit := [(67, false), (60, false), (935, true), (55, false)]
theorem step1254 (p : Nat → Bool) (h : Constraints p) : clause p c1254 = true :=
  Snake9.LocalRup.prove_clause [c404, c405, c949] c1254 (by decide) p (sat_cons (step404 p h) (sat_cons (step405 p h) (sat_cons (step949 p h) (sat_nil p))))
def c1255 : List Lit := [(68, false), (930, true), (52, false), (55, false)]
theorem step1255 (p : Nat → Bool) (h : Constraints p) : clause p c1255 = true :=
  Snake9.LocalRup.prove_clause [c321, c1253] c1255 (by decide) p (sat_cons (step321 p h) (sat_cons (step1253 p h) (sat_nil p)))
def c1256 : List Lit := [(77, false), (959, true), (967, true), (52, false), (71, false)]
theorem step1256 (p : Nat → Bool) (h : Constraints p) : clause p c1256 = true :=
  Snake9.LocalRup.prove_clause [c567, c561, c998, c997, c465, c464, c1250, c431, c980, c428, c988, c460, c1012, c996, c1005] c1256 (by decide) p (sat_cons (step567 p h) (sat_cons (step561 p h) (sat_cons (step998 p h) (sat_cons (step997 p h) (sat_cons (step465 p h) (sat_cons (step464 p h) (sat_cons (step1250 p h) (sat_cons (step431 p h) (sat_cons (step980 p h) (sat_cons (step428 p h) (sat_cons (step988 p h) (sat_cons (step460 p h) (sat_cons (step1012 p h) (sat_cons (step996 p h) (sat_cons (step1005 p h) (sat_nil p))))))))))))))))
def c1257 : List Lit := [(934, true), (59, true), (83, false)]
theorem step1257 (p : Nat → Bool) (h : Constraints p) : clause p c1257 = true :=
  Snake9.LocalRup.prove_clause [c557, c947, c948, c396, c397, c399] c1257 (by decide) p (sat_cons (step557 p h) (sat_cons (step947 p h) (sat_cons (step948 p h) (sat_cons (step396 p h) (sat_cons (step397 p h) (sat_cons (step399 p h) (sat_nil p)))))))
end B112E081
