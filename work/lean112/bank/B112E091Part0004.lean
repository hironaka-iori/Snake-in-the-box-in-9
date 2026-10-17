import B112E091Part0003
namespace B112E091
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1175 : List Lit := [(69, false), (73, true)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true :=
  Snake9.LocalRup.prove_clause [c334, c232] c1175 (by decide) p (sat_cons (step334 p h) (sat_cons (step232 p h) (sat_nil p)))
def c1176 : List Lit := [(71, false), (70, true)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true :=
  Snake9.LocalRup.prove_clause [c335, c234] c1176 (by decide) p (sat_cons (step335 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1177 : List Lit := [(72, false), (68, true)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true :=
  Snake9.LocalRup.prove_clause [c336, c235] c1177 (by decide) p (sat_cons (step336 p h) (sat_cons (step235 p h) (sat_nil p)))
def c1178 : List Lit := [(84, false), (87, true), (76, true)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true :=
  Snake9.LocalRup.prove_clause [c341, c258] c1178 (by decide) p (sat_cons (step341 p h) (sat_cons (step258 p h) (sat_nil p)))
def c1179 : List Lit := [(85, true), (84, false), (76, true)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true :=
  Snake9.LocalRup.prove_clause [c341, c259] c1179 (by decide) p (sat_cons (step341 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1180 : List Lit := [(86, false), (85, true)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true :=
  Snake9.LocalRup.prove_clause [c342, c264] c1180 (by decide) p (sat_cons (step342 p h) (sat_cons (step264 p h) (sat_nil p)))
def c1181 : List Lit := [(86, false), (42, true)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true :=
  Snake9.LocalRup.prove_clause [c342, c265] c1181 (by decide) p (sat_cons (step342 p h) (sat_cons (step265 p h) (sat_nil p)))
def c1182 : List Lit := [(88, false), (87, true)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true :=
  Snake9.LocalRup.prove_clause [c343, c268] c1182 (by decide) p (sat_cons (step343 p h) (sat_cons (step268 p h) (sat_nil p)))
def c1183 : List Lit := [(92, false), (93, true), (91, true)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true :=
  Snake9.LocalRup.prove_clause [c345, c275] c1183 (by decide) p (sat_cons (step345 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1184 : List Lit := [(94, false), (98, true)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true :=
  Snake9.LocalRup.prove_clause [c346, c278] c1184 (by decide) p (sat_cons (step346 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1185 : List Lit := [(97, false), (98, true)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true :=
  Snake9.LocalRup.prove_clause [c348, c284] c1185 (by decide) p (sat_cons (step348 p h) (sat_cons (step284 p h) (sat_nil p)))
def c1186 : List Lit := [(102, true), (99, false), (91, true)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true :=
  Snake9.LocalRup.prove_clause [c349, c287] c1186 (by decide) p (sat_cons (step349 p h) (sat_cons (step287 p h) (sat_nil p)))
def c1187 : List Lit := [(101, false), (103, true)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true :=
  Snake9.LocalRup.prove_clause [c350, c291] c1187 (by decide) p (sat_cons (step350 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1188 : List Lit := [(101, false), (100, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true :=
  Snake9.LocalRup.prove_clause [c350, c292] c1188 (by decide) p (sat_cons (step350 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1189 : List Lit := [(104, false), (105, true)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true :=
  Snake9.LocalRup.prove_clause [c351, c297] c1189 (by decide) p (sat_cons (step351 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1190 : List Lit := [(104, false), (102, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true :=
  Snake9.LocalRup.prove_clause [c351, c298] c1190 (by decide) p (sat_cons (step351 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1191 : List Lit := [(116, false), (117, false)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true :=
  Snake9.LocalRup.prove_clause [c956, c364] c1191 (by decide) p (sat_cons (step956 p h) (sat_cons (step364 p h) (sat_nil p)))
def c1192 : List Lit := [(225, false), (231, false)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true :=
  Snake9.LocalRup.prove_clause [c945, c370] c1192 (by decide) p (sat_cons (step945 p h) (sat_cons (step370 p h) (sat_nil p)))
def c1193 : List Lit := [(221, false), (233, false)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true :=
  Snake9.LocalRup.prove_clause [c934, c374] c1193 (by decide) p (sat_cons (step934 p h) (sat_cons (step374 p h) (sat_nil p)))
def c1194 : List Lit := [(120, false), (237, false)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true :=
  Snake9.LocalRup.prove_clause [c953, c378] c1194 (by decide) p (sat_cons (step953 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1195 : List Lit := [(235, false), (259, false)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true :=
  Snake9.LocalRup.prove_clause [c926, c400] c1195 (by decide) p (sat_cons (step926 p h) (sat_cons (step400 p h) (sat_nil p)))
def c1196 : List Lit := [(271, false), (283, false)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true :=
  Snake9.LocalRup.prove_clause [c932, c420] c1196 (by decide) p (sat_cons (step932 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1197 : List Lit := [(150, false), (151, false)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true :=
  Snake9.LocalRup.prove_clause [c955, c429] c1197 (by decide) p (sat_cons (step955 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1198 : List Lit := [(285, false), (309, false)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true :=
  Snake9.LocalRup.prove_clause [c925, c452] c1198 (by decide) p (sat_cons (step925 p h) (sat_cons (step452 p h) (sat_nil p)))
def c1199 : List Lit := [(261, false), (311, false)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true :=
  Snake9.LocalRup.prove_clause [c922, c457] c1199 (by decide) p (sat_cons (step922 p h) (sat_cons (step457 p h) (sat_nil p)))
def c1200 : List Lit := [(159, false), (315, false)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true :=
  Snake9.LocalRup.prove_clause [c949, c462] c1200 (by decide) p (sat_cons (step949 p h) (sat_cons (step462 p h) (sat_nil p)))
def c1201 : List Lit := [(323, false), (335, false)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true :=
  Snake9.LocalRup.prove_clause [c930, c479] c1201 (by decide) p (sat_cons (step930 p h) (sat_cons (step479 p h) (sat_nil p)))
def c1202 : List Lit := [(341, false), (345, false)]
theorem step1202 (p : Nat → Bool) (h : Constraints p) : clause p c1202 = true :=
  Snake9.LocalRup.prove_clause [c939, c487] c1202 (by decide) p (sat_cons (step939 p h) (sat_cons (step487 p h) (sat_nil p)))
def c1203 : List Lit := [(351, false), (357, false)]
theorem step1203 (p : Nat → Bool) (h : Constraints p) : clause p c1203 = true :=
  Snake9.LocalRup.prove_clause [c938, c499] c1203 (by decide) p (sat_cons (step938 p h) (sat_cons (step499 p h) (sat_nil p)))
def c1204 : List Lit := [(347, false), (359, false)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true :=
  Snake9.LocalRup.prove_clause [c929, c503] c1204 (by decide) p (sat_cons (step929 p h) (sat_cons (step503 p h) (sat_nil p)))
def c1205 : List Lit := [(337, false), (361, false)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true :=
  Snake9.LocalRup.prove_clause [c924, c508] c1205 (by decide) p (sat_cons (step924 p h) (sat_cons (step508 p h) (sat_nil p)))
def c1206 : List Lit := [(367, false), (371, false)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true :=
  Snake9.LocalRup.prove_clause [c937, c519] c1206 (by decide) p (sat_cons (step937 p h) (sat_cons (step519 p h) (sat_nil p)))
def c1207 : List Lit := [(373, false), (385, false)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true :=
  Snake9.LocalRup.prove_clause [c928, c530] c1207 (by decide) p (sat_cons (step928 p h) (sat_cons (step530 p h) (sat_nil p)))
def c1208 : List Lit := [(387, false), (413, false)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true :=
  Snake9.LocalRup.prove_clause [c923, c559] c1208 (by decide) p (sat_cons (step923 p h) (sat_cons (step559 p h) (sat_nil p)))
def c1209 : List Lit := [(363, false), (415, false)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true :=
  Snake9.LocalRup.prove_clause [c921, c564] c1209 (by decide) p (sat_cons (step921 p h) (sat_cons (step564 p h) (sat_nil p)))
def c1210 : List Lit := [(313, false), (417, false)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true :=
  Snake9.LocalRup.prove_clause [c569, c567] c1210 (by decide) p (sat_cons (step569 p h) (sat_cons (step567 p h) (sat_nil p)))
def c1211 : List Lit := [(1353, true), (1338, false)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true :=
  Snake9.LocalRup.prove_clause [c1019, c715] c1211 (by decide) p (sat_cons (step1019 p h) (sat_cons (step715 p h) (sat_nil p)))
def c1212 : List Lit := [(1354, true), (1339, false)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true :=
  Snake9.LocalRup.prove_clause [c1019, c716] c1212 (by decide) p (sat_cons (step1019 p h) (sat_cons (step716 p h) (sat_nil p)))
def c1213 : List Lit := [(1355, true), (1340, false)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true :=
  Snake9.LocalRup.prove_clause [c1019, c717] c1213 (by decide) p (sat_cons (step1019 p h) (sat_cons (step717 p h) (sat_nil p)))
def c1214 : List Lit := [(1341, false), (1356, true)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true :=
  Snake9.LocalRup.prove_clause [c1019, c718] c1214 (by decide) p (sat_cons (step1019 p h) (sat_cons (step718 p h) (sat_nil p)))
def c1215 : List Lit := [(1342, false), (1357, true)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true :=
  Snake9.LocalRup.prove_clause [c1019, c719] c1215 (by decide) p (sat_cons (step1019 p h) (sat_cons (step719 p h) (sat_nil p)))
def c1216 : List Lit := [(1353, true), (1290, false)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true :=
  Snake9.LocalRup.prove_clause [c958, c720] c1216 (by decide) p (sat_cons (step958 p h) (sat_cons (step720 p h) (sat_nil p)))
def c1217 : List Lit := [(1354, true), (1291, false)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true :=
  Snake9.LocalRup.prove_clause [c958, c726] c1217 (by decide) p (sat_cons (step958 p h) (sat_cons (step726 p h) (sat_nil p)))
def c1218 : List Lit := [(1355, true), (1292, false)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true :=
  Snake9.LocalRup.prove_clause [c958, c732] c1218 (by decide) p (sat_cons (step958 p h) (sat_cons (step732 p h) (sat_nil p)))
def c1219 : List Lit := [(1365, false), (1374, true)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true :=
  Snake9.LocalRup.prove_clause [c961, c753] c1219 (by decide) p (sat_cons (step961 p h) (sat_cons (step753 p h) (sat_nil p)))
def c1220 : List Lit := [(1366, false), (1375, true)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true :=
  Snake9.LocalRup.prove_clause [c961, c756] c1220 (by decide) p (sat_cons (step961 p h) (sat_cons (step756 p h) (sat_nil p)))
def c1221 : List Lit := [(1367, false), (1376, true)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true :=
  Snake9.LocalRup.prove_clause [c961, c759] c1221 (by decide) p (sat_cons (step961 p h) (sat_cons (step759 p h) (sat_nil p)))
def c1222 : List Lit := [(1392, false), (1400, true)]
theorem step1222 (p : Nat → Bool) (h : Constraints p) : clause p c1222 = true :=
  Snake9.LocalRup.prove_clause [c962, c779] c1222 (by decide) p (sat_cons (step962 p h) (sat_cons (step779 p h) (sat_nil p)))
def c1223 : List Lit := [(1393, false), (1401, true)]
theorem step1223 (p : Nat → Bool) (h : Constraints p) : clause p c1223 = true :=
  Snake9.LocalRup.prove_clause [c962, c780] c1223 (by decide) p (sat_cons (step962 p h) (sat_cons (step780 p h) (sat_nil p)))
def c1224 : List Lit := [(1457, false), (1471, true)]
theorem step1224 (p : Nat → Bool) (h : Constraints p) : clause p c1224 = true :=
  Snake9.LocalRup.prove_clause [c963, c870] c1224 (by decide) p (sat_cons (step963 p h) (sat_cons (step870 p h) (sat_nil p)))
def c1225 : List Lit := [(1457, false), (1402, false)]
theorem step1225 (p : Nat → Bool) (h : Constraints p) : clause p c1225 = true :=
  Snake9.LocalRup.prove_clause [c1067, c888] c1225 (by decide) p (sat_cons (step1067 p h) (sat_cons (step888 p h) (sat_nil p)))
def c1226 : List Lit := [(1404, false), (1455, false)]
theorem step1226 (p : Nat → Bool) (h : Constraints p) : clause p c1226 = true :=
  Snake9.LocalRup.prove_clause [c1067, c897] c1226 (by decide) p (sat_cons (step1067 p h) (sat_cons (step897 p h) (sat_nil p)))
def c1227 : List Lit := [(1353, false), (1473, false)]
theorem step1227 (p : Nat → Bool) (h : Constraints p) : clause p c1227 = true :=
  Snake9.LocalRup.prove_clause [c910, c903] c1227 (by decide) p (sat_cons (step910 p h) (sat_cons (step903 p h) (sat_nil p)))
def c1228 : List Lit := [(1354, false), (1472, false)]
theorem step1228 (p : Nat → Bool) (h : Constraints p) : clause p c1228 = true :=
  Snake9.LocalRup.prove_clause [c910, c904] c1228 (by decide) p (sat_cons (step910 p h) (sat_cons (step904 p h) (sat_nil p)))
def c1229 : List Lit := [(1355, false), (1471, false)]
theorem step1229 (p : Nat → Bool) (h : Constraints p) : clause p c1229 = true :=
  Snake9.LocalRup.prove_clause [c910, c905] c1229 (by decide) p (sat_cons (step910 p h) (sat_cons (step905 p h) (sat_nil p)))
def c1230 : List Lit := [(1356, false), (1470, false)]
theorem step1230 (p : Nat → Bool) (h : Constraints p) : clause p c1230 = true :=
  Snake9.LocalRup.prove_clause [c910, c906] c1230 (by decide) p (sat_cons (step910 p h) (sat_cons (step906 p h) (sat_nil p)))
def c1231 : List Lit := [(1357, false), (1469, false)]
theorem step1231 (p : Nat → Bool) (h : Constraints p) : clause p c1231 = true :=
  Snake9.LocalRup.prove_clause [c910, c907] c1231 (by decide) p (sat_cons (step910 p h) (sat_cons (step907 p h) (sat_nil p)))
def c1232 : List Lit := [(1358, false), (1468, false)]
theorem step1232 (p : Nat → Bool) (h : Constraints p) : clause p c1232 = true :=
  Snake9.LocalRup.prove_clause [c910, c908] c1232 (by decide) p (sat_cons (step910 p h) (sat_cons (step908 p h) (sat_nil p)))
def c1233 : List Lit := [(1359, false), (1467, false)]
theorem step1233 (p : Nat → Bool) (h : Constraints p) : clause p c1233 = true :=
  Snake9.LocalRup.prove_clause [c910, c909] c1233 (by decide) p (sat_cons (step910 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1234 : List Lit := [(1290, false), (1404, false), (1446, false), (363, false)]
theorem step1234 (p : Nat → Bool) (h : Constraints p) : clause p c1234 = true :=
  Snake9.LocalRup.prove_clause [c1209, c558, c528, c526, c525, c522, c1226, c863, c818, c1038, c854, c895, c1228, c563, c1210, c454, c449, c446, c434, c425, c964, c432, c430, c427, c445, c443, c442, c439, c529, c516, c513, c512, c1216, c721, c1227, c694, c699, c896, c682, c690, c651, c859, c647, c817, c644, c810, c812, c965, c808, c805, c676, c993, c263, c262, c667, c668, c266, c1181, c147, c150] c1234 (by decide) p (sat_cons (step1209 p h) (sat_cons (step558 p h) (sat_cons (step528 p h) (sat_cons (step526 p h) (sat_cons (step525 p h) (sat_cons (step522 p h) (sat_cons (step1226 p h) (sat_cons (step863 p h) (sat_cons (step818 p h) (sat_cons (step1038 p h) (sat_cons (step854 p h) (sat_cons (step895 p h) (sat_cons (step1228 p h) (sat_cons (step563 p h) (sat_cons (step1210 p h) (sat_cons (step454 p h) (sat_cons (step449 p h) (sat_cons (step446 p h) (sat_cons (step434 p h) (sat_cons (step425 p h) (sat_cons (step964 p h) (sat_cons (step432 p h) (sat_cons (step430 p h) (sat_cons (step427 p h) (sat_cons (step445 p h) (sat_cons (step443 p h) (sat_cons (step442 p h) (sat_cons (step439 p h) (sat_cons (step529 p h) (sat_cons (step516 p h) (sat_cons (step513 p h) (sat_cons (step512 p h) (sat_cons (step1216 p h) (sat_cons (step721 p h) (sat_cons (step1227 p h) (sat_cons (step694 p h) (sat_cons (step699 p h) (sat_cons (step896 p h) (sat_cons (step682 p h) (sat_cons (step690 p h) (sat_cons (step651 p h) (sat_cons (step859 p h) (sat_cons (step647 p h) (sat_cons (step817 p h) (sat_cons (step644 p h) (sat_cons (step810 p h) (sat_cons (step812 p h) (sat_cons (step965 p h) (sat_cons (step808 p h) (sat_cons (step805 p h) (sat_cons (step676 p h) (sat_cons (step993 p h) (sat_cons (step263 p h) (sat_cons (step262 p h) (sat_cons (step667 p h) (sat_cons (step668 p h) (sat_cons (step266 p h) (sat_cons (step1181 p h) (sat_cons (step147 p h) (sat_cons (step150 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1235 : List Lit := [(1404, false), (1446, false), (363, false)]
theorem step1235 (p : Nat → Bool) (h : Constraints p) : clause p c1235 = true :=
  Snake9.LocalRup.prove_clause [c854, c563, c1210, c454, c449, c446, c434, c425, c964, c445, c443, c442, c439, c1209, c558, c528, c526, c525, c522, c1226, c895, c863, c1228, c818, c1212, c1038, c703, c1234, c967, c653, c654, c700, c647, c682, c690, c644, c645, c965, c673, c676, c686, c667, c663, c138, c998, c661, c106] c1235 (by decide) p (sat_cons (step854 p h) (sat_cons (step563 p h) (sat_cons (step1210 p h) (sat_cons (step454 p h) (sat_cons (step449 p h) (sat_cons (step446 p h) (sat_cons (step434 p h) (sat_cons (step425 p h) (sat_cons (step964 p h) (sat_cons (step445 p h) (sat_cons (step443 p h) (sat_cons (step442 p h) (sat_cons (step439 p h) (sat_cons (step1209 p h) (sat_cons (step558 p h) (sat_cons (step528 p h) (sat_cons (step526 p h) (sat_cons (step525 p h) (sat_cons (step522 p h) (sat_cons (step1226 p h) (sat_cons (step895 p h) (sat_cons (step863 p h) (sat_cons (step1228 p h) (sat_cons (step818 p h) (sat_cons (step1212 p h) (sat_cons (step1038 p h) (sat_cons (step703 p h) (sat_cons (step1234 p h) (sat_cons (step967 p h) (sat_cons (step653 p h) (sat_cons (step654 p h) (sat_cons (step700 p h) (sat_cons (step647 p h) (sat_cons (step682 p h) (sat_cons (step690 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step965 p h) (sat_cons (step673 p h) (sat_cons (step676 p h) (sat_cons (step686 p h) (sat_cons (step667 p h) (sat_cons (step663 p h) (sat_cons (step138 p h) (sat_cons (step998 p h) (sat_cons (step661 p h) (sat_cons (step106 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c1236 : List Lit := [(1331, true), (1306, true), (309, true)]
theorem step1236 (p : Nat → Bool) (h : Constraints p) : clause p c1236 = true :=
  Snake9.LocalRup.prove_clause [c645, c644, c446, c432, c430, c428, c445, c443, c442, c439, c682, c690, c965, c673, c676, c686, c667, c668, c663, c134, c146, c660, c1024] c1236 (by decide) p (sat_cons (step645 p h) (sat_cons (step644 p h) (sat_cons (step446 p h) (sat_cons (step432 p h) (sat_cons (step430 p h) (sat_cons (step428 p h) (sat_cons (step445 p h) (sat_cons (step443 p h) (sat_cons (step442 p h) (sat_cons (step439 p h) (sat_cons (step682 p h) (sat_cons (step690 p h) (sat_cons (step965 p h) (sat_cons (step673 p h) (sat_cons (step676 p h) (sat_cons (step686 p h) (sat_cons (step667 p h) (sat_cons (step668 p h) (sat_cons (step663 p h) (sat_cons (step134 p h) (sat_cons (step146 p h) (sat_cons (step660 p h) (sat_cons (step1024 p h) (sat_nil p))))))))))))))))))))))))
def c1237 : List Lit := [(1388, false), (52, true), (1472, true), (1404, true), (1379, false), (1375, false), (413, true)]
theorem step1237 (p : Nat → Bool) (h : Constraints p) : clause p c1237 = true :=
  Snake9.LocalRup.prove_clause [c1163, c788, c764, c774, c777, c787, c791, c766, c892, c1221, c855, c743, c997, c1080, c179, c184, c738] c1237 (by decide) p (sat_cons (step1163 p h) (sat_cons (step788 p h) (sat_cons (step764 p h) (sat_cons (step774 p h) (sat_cons (step777 p h) (sat_cons (step787 p h) (sat_cons (step791 p h) (sat_cons (step766 p h) (sat_cons (step892 p h) (sat_cons (step1221 p h) (sat_cons (step855 p h) (sat_cons (step743 p h) (sat_cons (step997 p h) (sat_cons (step1080 p h) (sat_cons (step179 p h) (sat_cons (step184 p h) (sat_cons (step738 p h) (sat_nil p))))))))))))))))))
def c1238 : List Lit := [(43, false), (87, false), (35, false), (37, false), (1333, true), (309, true)]
theorem step1238 (p : Nat → Bool) (h : Constraints p) : clause p c1238 = true :=
  Snake9.LocalRup.prove_clause [c684, c446, c434, c424, c422, c445, c443, c442, c439, c138, c136, c1046, c669, c680, c974, c663, c665, c660, c973, c133] c1238 (by decide) p (sat_cons (step684 p h) (sat_cons (step446 p h) (sat_cons (step434 p h) (sat_cons (step424 p h) (sat_cons (step422 p h) (sat_cons (step445 p h) (sat_cons (step443 p h) (sat_cons (step442 p h) (sat_cons (step439 p h) (sat_cons (step138 p h) (sat_cons (step136 p h) (sat_cons (step1046 p h) (sat_cons (step669 p h) (sat_cons (step680 p h) (sat_cons (step974 p h) (sat_cons (step663 p h) (sat_cons (step665 p h) (sat_cons (step660 p h) (sat_cons (step973 p h) (sat_cons (step133 p h) (sat_nil p)))))))))))))))))))))
end B112E091
