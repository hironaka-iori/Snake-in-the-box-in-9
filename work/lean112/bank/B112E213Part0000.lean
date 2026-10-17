import B112E213Inputs
namespace B112E213
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1204 : List Lit := [(107, true)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true :=
  Snake9.LocalRup.prove_clause [c501, c500] c1204 (by decide) p (sat_cons (step501 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1205 : List Lit := [(224, true), (108, true)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true :=
  Snake9.LocalRup.prove_clause [c1204, c502] c1205 (by decide) p (sat_cons (step1204 p h) (sat_cons (step502 p h) (sat_nil p)))
def c1206 : List Lit := [(99, false)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true :=
  Snake9.LocalRup.prove_clause [c553, c494] c1206 (by decide) p (sat_cons (step553 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1207 : List Lit := [(101, false)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true :=
  Snake9.LocalRup.prove_clause [c555, c497] c1207 (by decide) p (sat_cons (step555 p h) (sat_cons (step497 p h) (sat_nil p)))
def c1208 : List Lit := [(103, false)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true :=
  Snake9.LocalRup.prove_clause [c556, c499] c1208 (by decide) p (sat_cons (step556 p h) (sat_cons (step499 p h) (sat_nil p)))
def c1209 : List Lit := [(462, false)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true :=
  Snake9.LocalRup.prove_clause [c713, c710] c1209 (by decide) p (sat_cons (step713 p h) (sat_cons (step710 p h) (sat_nil p)))
def c1210 : List Lit := [(348, false)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true :=
  Snake9.LocalRup.prove_clause [c713, c712] c1210 (by decide) p (sat_cons (step713 p h) (sat_cons (step712 p h) (sat_nil p)))
def c1211 : List Lit := [(460, false)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true :=
  Snake9.LocalRup.prove_clause [c1209, c706] c1211 (by decide) p (sat_cons (step1209 p h) (sat_cons (step706 p h) (sat_nil p)))
def c1212 : List Lit := [(404, false)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true :=
  Snake9.LocalRup.prove_clause [c1209, c709] c1212 (by decide) p (sat_cons (step1209 p h) (sat_cons (step709 p h) (sat_nil p)))
def c1213 : List Lit := [(346, false)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true :=
  Snake9.LocalRup.prove_clause [c1210, c640] c1213 (by decide) p (sat_cons (step1210 p h) (sat_cons (step640 p h) (sat_nil p)))
def c1214 : List Lit := [(290, false)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true :=
  Snake9.LocalRup.prove_clause [c1210, c643] c1214 (by decide) p (sat_cons (step1210 p h) (sat_cons (step643 p h) (sat_nil p)))
def c1215 : List Lit := [(430, false)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true :=
  Snake9.LocalRup.prove_clause [c1211, c704] c1215 (by decide) p (sat_cons (step1211 p h) (sat_cons (step704 p h) (sat_nil p)))
def c1216 : List Lit := [(402, false)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true :=
  Snake9.LocalRup.prove_clause [c1212, c666] c1216 (by decide) p (sat_cons (step1212 p h) (sat_cons (step666 p h) (sat_nil p)))
def c1217 : List Lit := [(316, false)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true :=
  Snake9.LocalRup.prove_clause [c1213, c638] c1217 (by decide) p (sat_cons (step1213 p h) (sat_cons (step638 p h) (sat_nil p)))
def c1218 : List Lit := [(288, false)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true :=
  Snake9.LocalRup.prove_clause [c1214, c604] c1218 (by decide) p (sat_cons (step1214 p h) (sat_cons (step604 p h) (sat_nil p)))
def c1219 : List Lit := [(260, false)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true :=
  Snake9.LocalRup.prove_clause [c1214, c607] c1219 (by decide) p (sat_cons (step1214 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1220 : List Lit := [(428, false)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true :=
  Snake9.LocalRup.prove_clause [c1215, c683] c1220 (by decide) p (sat_cons (step1215 p h) (sat_cons (step683 p h) (sat_nil p)))
def c1221 : List Lit := [(386, false)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true :=
  Snake9.LocalRup.prove_clause [c1216, c664] c1221 (by decide) p (sat_cons (step1216 p h) (sat_cons (step664 p h) (sat_nil p)))
def c1222 : List Lit := [(302, false)]
theorem step1222 (p : Nat → Bool) (h : Constraints p) : clause p c1222 = true :=
  Snake9.LocalRup.prove_clause [c1217, c621] c1222 (by decide) p (sat_cons (step1217 p h) (sat_cons (step621 p h) (sat_nil p)))
def c1223 : List Lit := [(272, false)]
theorem step1223 (p : Nat → Bool) (h : Constraints p) : clause p c1223 = true :=
  Snake9.LocalRup.prove_clause [c1218, c602] c1223 (by decide) p (sat_cons (step1218 p h) (sat_cons (step602 p h) (sat_nil p)))
def c1224 : List Lit := [(258, false)]
theorem step1224 (p : Nat → Bool) (h : Constraints p) : clause p c1224 = true :=
  Snake9.LocalRup.prove_clause [c1219, c584] c1224 (by decide) p (sat_cons (step1219 p h) (sat_cons (step584 p h) (sat_nil p)))
def c1225 : List Lit := [(246, false)]
theorem step1225 (p : Nat → Bool) (h : Constraints p) : clause p c1225 = true :=
  Snake9.LocalRup.prove_clause [c1219, c587] c1225 (by decide) p (sat_cons (step1219 p h) (sat_cons (step587 p h) (sat_nil p)))
def c1226 : List Lit := [(270, false)]
theorem step1226 (p : Nat → Bool) (h : Constraints p) : clause p c1226 = true :=
  Snake9.LocalRup.prove_clause [c1223, c594] c1226 (by decide) p (sat_cons (step1223 p h) (sat_cons (step594 p h) (sat_nil p)))
def c1227 : List Lit := [(244, false)]
theorem step1227 (p : Nat → Bool) (h : Constraints p) : clause p c1227 = true :=
  Snake9.LocalRup.prove_clause [c1225, c572] c1227 (by decide) p (sat_cons (step1225 p h) (sat_cons (step572 p h) (sat_nil p)))
def c1228 : List Lit := [(266, false)]
theorem step1228 (p : Nat → Bool) (h : Constraints p) : clause p c1228 = true :=
  Snake9.LocalRup.prove_clause [c1226, c592] c1228 (by decide) p (sat_cons (step1226 p h) (sat_cons (step592 p h) (sat_nil p)))
def c1229 : List Lit := [(240, false)]
theorem step1229 (p : Nat → Bool) (h : Constraints p) : clause p c1229 = true :=
  Snake9.LocalRup.prove_clause [c1227, c570] c1229 (by decide) p (sat_cons (step1227 p h) (sat_cons (step570 p h) (sat_nil p)))
def c1230 : List Lit := [(993, true)]
theorem step1230 (p : Nat → Bool) (h : Constraints p) : clause p c1230 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1082] c1230 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c1231 : List Lit := [(97, true), (994, true)]
theorem step1231 (p : Nat → Bool) (h : Constraints p) : clause p c1231 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1083] c1231 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1083 p h) (sat_nil p)))
def c1232 : List Lit := [(995, true)]
theorem step1232 (p : Nat → Bool) (h : Constraints p) : clause p c1232 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1084] c1232 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1084 p h) (sat_nil p)))
def c1233 : List Lit := [(100, true), (996, true)]
theorem step1233 (p : Nat → Bool) (h : Constraints p) : clause p c1233 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1085] c1233 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1085 p h) (sat_nil p)))
def c1234 : List Lit := [(997, true)]
theorem step1234 (p : Nat → Bool) (h : Constraints p) : clause p c1234 = true :=
  Snake9.LocalRup.prove_clause [c1232, c1086] c1234 (by decide) p (sat_cons (step1232 p h) (sat_cons (step1086 p h) (sat_nil p)))
def c1235 : List Lit := [(998, true)]
theorem step1235 (p : Nat → Bool) (h : Constraints p) : clause p c1235 = true :=
  Snake9.LocalRup.prove_clause [c1230, c1232, c1087] c1235 (by decide) p (sat_cons (step1230 p h) (sat_cons (step1232 p h) (sat_cons (step1087 p h) (sat_nil p))))
def c1236 : List Lit := [(996, false), (999, true)]
theorem step1236 (p : Nat → Bool) (h : Constraints p) : clause p c1236 = true :=
  Snake9.LocalRup.prove_clause [c1230, c1088] c1236 (by decide) p (sat_cons (step1230 p h) (sat_cons (step1088 p h) (sat_nil p)))
def c1237 : List Lit := [(994, false), (999, true)]
theorem step1237 (p : Nat → Bool) (h : Constraints p) : clause p c1237 = true :=
  Snake9.LocalRup.prove_clause [c1232, c1089] c1237 (by decide) p (sat_cons (step1232 p h) (sat_cons (step1089 p h) (sat_nil p)))
def c1238 : List Lit := [(1001, true)]
theorem step1238 (p : Nat → Bool) (h : Constraints p) : clause p c1238 = true :=
  Snake9.LocalRup.prove_clause [c1234, c1091] c1238 (by decide) p (sat_cons (step1234 p h) (sat_cons (step1091 p h) (sat_nil p)))
def c1239 : List Lit := [(1002, true)]
theorem step1239 (p : Nat → Bool) (h : Constraints p) : clause p c1239 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1092] c1239 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c1240 : List Lit := [(990, false), (1003, true)]
theorem step1240 (p : Nat → Bool) (h : Constraints p) : clause p c1240 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1095] c1240 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c1241 : List Lit := [(991, false), (1004, true)]
theorem step1241 (p : Nat → Bool) (h : Constraints p) : clause p c1241 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1098] c1241 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1098 p h) (sat_nil p)))
def c1242 : List Lit := [(1008, true)]
theorem step1242 (p : Nat → Bool) (h : Constraints p) : clause p c1242 = true :=
  Snake9.LocalRup.prove_clause [c1208, c1101] c1242 (by decide) p (sat_cons (step1208 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c1243 : List Lit := [(1012, true)]
theorem step1243 (p : Nat → Bool) (h : Constraints p) : clause p c1243 = true :=
  Snake9.LocalRup.prove_clause [c1242, c1103] c1243 (by decide) p (sat_cons (step1242 p h) (sat_cons (step1103 p h) (sat_nil p)))
def c1244 : List Lit := [(1010, false), (1013, true)]
theorem step1244 (p : Nat → Bool) (h : Constraints p) : clause p c1244 = true :=
  Snake9.LocalRup.prove_clause [c1242, c1104] c1244 (by decide) p (sat_cons (step1242 p h) (sat_cons (step1104 p h) (sat_nil p)))
def c1245 : List Lit := [(1024, true)]
theorem step1245 (p : Nat → Bool) (h : Constraints p) : clause p c1245 = true :=
  Snake9.LocalRup.prove_clause [c1243, c1111] c1245 (by decide) p (sat_cons (step1243 p h) (sat_cons (step1111 p h) (sat_nil p)))
def c1246 : List Lit := [(1020, false), (1025, true)]
theorem step1246 (p : Nat → Bool) (h : Constraints p) : clause p c1246 = true :=
  Snake9.LocalRup.prove_clause [c1243, c1112] c1246 (by decide) p (sat_cons (step1243 p h) (sat_cons (step1112 p h) (sat_nil p)))
def c1247 : List Lit := [(1021, false), (1026, true)]
theorem step1247 (p : Nat → Bool) (h : Constraints p) : clause p c1247 = true :=
  Snake9.LocalRup.prove_clause [c1243, c1113] c1247 (by decide) p (sat_cons (step1243 p h) (sat_cons (step1113 p h) (sat_nil p)))
def c1248 : List Lit := [(1033, true)]
theorem step1248 (p : Nat → Bool) (h : Constraints p) : clause p c1248 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1245, c1115] c1248 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1245 p h) (sat_cons (step1115 p h) (sat_nil p))))
def c1249 : List Lit := [(1034, true)]
theorem step1249 (p : Nat → Bool) (h : Constraints p) : clause p c1249 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1245, c1116] c1249 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1245 p h) (sat_cons (step1116 p h) (sat_nil p))))
def c1250 : List Lit := [(1026, false), (1036, true)]
theorem step1250 (p : Nat → Bool) (h : Constraints p) : clause p c1250 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1117] c1250 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c1251 : List Lit := [(1003, false), (1035, true)]
theorem step1251 (p : Nat → Bool) (h : Constraints p) : clause p c1251 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1118] c1251 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1118 p h) (sat_nil p)))
def c1252 : List Lit := [(1004, false), (1036, true)]
theorem step1252 (p : Nat → Bool) (h : Constraints p) : clause p c1252 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1121] c1252 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1121 p h) (sat_nil p)))
def c1253 : List Lit := [(1005, false), (1037, true)]
theorem step1253 (p : Nat → Bool) (h : Constraints p) : clause p c1253 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1123] c1253 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1123 p h) (sat_nil p)))
def c1254 : List Lit := [(1006, false), (1038, true)]
theorem step1254 (p : Nat → Bool) (h : Constraints p) : clause p c1254 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1125] c1254 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1125 p h) (sat_nil p)))
def c1255 : List Lit := [(973, false), (1050, true)]
theorem step1255 (p : Nat → Bool) (h : Constraints p) : clause p c1255 = true :=
  Snake9.LocalRup.prove_clause [c1249, c1130] c1255 (by decide) p (sat_cons (step1249 p h) (sat_cons (step1130 p h) (sat_nil p)))
def c1256 : List Lit := [(974, false), (1051, true)]
theorem step1256 (p : Nat → Bool) (h : Constraints p) : clause p c1256 = true :=
  Snake9.LocalRup.prove_clause [c1249, c1135] c1256 (by decide) p (sat_cons (step1249 p h) (sat_cons (step1135 p h) (sat_nil p)))
def c1257 : List Lit := [(975, false), (1052, true)]
theorem step1257 (p : Nat → Bool) (h : Constraints p) : clause p c1257 = true :=
  Snake9.LocalRup.prove_clause [c1249, c1141] c1257 (by decide) p (sat_cons (step1249 p h) (sat_cons (step1141 p h) (sat_nil p)))
def c1258 : List Lit := [(976, false), (1053, true)]
theorem step1258 (p : Nat → Bool) (h : Constraints p) : clause p c1258 = true :=
  Snake9.LocalRup.prove_clause [c1249, c1146] c1258 (by decide) p (sat_cons (step1249 p h) (sat_cons (step1146 p h) (sat_nil p)))
def c1259 : List Lit := [(977, false), (1054, true)]
theorem step1259 (p : Nat → Bool) (h : Constraints p) : clause p c1259 = true :=
  Snake9.LocalRup.prove_clause [c1249, c1151] c1259 (by decide) p (sat_cons (step1249 p h) (sat_cons (step1151 p h) (sat_nil p)))
def c1260 : List Lit := [(978, false), (1055, true)]
theorem step1260 (p : Nat → Bool) (h : Constraints p) : clause p c1260 = true :=
  Snake9.LocalRup.prove_clause [c1249, c1154] c1260 (by decide) p (sat_cons (step1249 p h) (sat_cons (step1154 p h) (sat_nil p)))
def c1261 : List Lit := [(979, false), (1055, true)]
theorem step1261 (p : Nat → Bool) (h : Constraints p) : clause p c1261 = true :=
  Snake9.LocalRup.prove_clause [c1248, c1157] c1261 (by decide) p (sat_cons (step1248 p h) (sat_cons (step1157 p h) (sat_nil p)))
def c1262 : List Lit := [(979, false), (1056, true)]
theorem step1262 (p : Nat → Bool) (h : Constraints p) : clause p c1262 = true :=
  Snake9.LocalRup.prove_clause [c1249, c1158] c1262 (by decide) p (sat_cons (step1249 p h) (sat_cons (step1158 p h) (sat_nil p)))
def c1263 : List Lit := [(825, false), (833, true), (21, true), (26, false), (37, false)]
theorem step1263 (p : Nat → Bool) (h : Constraints p) : clause p c1263 = true :=
  Snake9.LocalRup.prove_clause [c773, c758, c767, c770, c777, c759, c752, c149, c749] c1263 (by decide) p (sat_cons (step773 p h) (sat_cons (step758 p h) (sat_cons (step767 p h) (sat_cons (step770 p h) (sat_cons (step777 p h) (sat_cons (step759 p h) (sat_cons (step752 p h) (sat_cons (step149 p h) (sat_cons (step749 p h) (sat_nil p))))))))))
def c1264 : List Lit := [(807, true), (8, true), (34, true), (53, false)]
theorem step1264 (p : Nat → Bool) (h : Constraints p) : clause p c1264 = true :=
  Snake9.LocalRup.prove_clause [c515, c516, c723, c733, c731, c724, c725, c726, c26, c32, c29] c1264 (by decide) p (sat_cons (step515 p h) (sat_cons (step516 p h) (sat_cons (step723 p h) (sat_cons (step733 p h) (sat_cons (step731 p h) (sat_cons (step724 p h) (sat_cons (step725 p h) (sat_cons (step726 p h) (sat_cons (step26 p h) (sat_cons (step32 p h) (sat_cons (step29 p h) (sat_nil p))))))))))))
def c1265 : List Lit := [(804, true), (53, false), (9, false), (34, true)]
theorem step1265 (p : Nat → Bool) (h : Constraints p) : clause p c1265 = true :=
  Snake9.LocalRup.prove_clause [c516, c725, c726, c32, c29] c1265 (by decide) p (sat_cons (step516 p h) (sat_cons (step725 p h) (sat_cons (step726 p h) (sat_cons (step32 p h) (sat_cons (step29 p h) (sat_nil p))))))
def c1266 : List Lit := [(40, false), (39, false), (48, true)]
theorem step1266 (p : Nat → Bool) (h : Constraints p) : clause p c1266 = true :=
  Snake9.LocalRup.prove_clause [c526, c275, c274, c1193] c1266 (by decide) p (sat_cons (step526 p h) (sat_cons (step275 p h) (sat_cons (step274 p h) (sat_cons (step1193 p h) (sat_nil p)))))
def c1267 : List Lit := [(938, true), (71, false), (51, false)]
theorem step1267 (p : Nat → Bool) (h : Constraints p) : clause p c1267 = true :=
  Snake9.LocalRup.prove_clause [c999, c1001, c997, c994, c430] c1267 (by decide) p (sat_cons (step999 p h) (sat_cons (step1001 p h) (sat_cons (step997 p h) (sat_cons (step994 p h) (sat_cons (step430 p h) (sat_nil p))))))
end B112E213
