import B112E096Part0002
namespace B112E096
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1228 : List Lit := [(64, true), (63, false), (59, true)]
theorem step1228 (p : Nat → Bool) (h : Constraints p) : clause p c1228 = true :=
  Snake9.LocalRup.prove_clause [c476, c146] c1228 (by decide) p (sat_cons (step476 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1229 : List Lit := [(66, false), (105, true)]
theorem step1229 (p : Nat → Bool) (h : Constraints p) : clause p c1229 = true :=
  Snake9.LocalRup.prove_clause [c477, c151] c1229 (by decide) p (sat_cons (step477 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1230 : List Lit := [(66, false), (65, true)]
theorem step1230 (p : Nat → Bool) (h : Constraints p) : clause p c1230 = true :=
  Snake9.LocalRup.prove_clause [c477, c152] c1230 (by decide) p (sat_cons (step477 p h) (sat_cons (step152 p h) (sat_nil p)))
def c1231 : List Lit := [(68, true), (69, false), (71, true)]
theorem step1231 (p : Nat → Bool) (h : Constraints p) : clause p c1231 = true :=
  Snake9.LocalRup.prove_clause [c478, c158] c1231 (by decide) p (sat_cons (step478 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1232 : List Lit := [(64, true), (75, true), (73, false)]
theorem step1232 (p : Nat → Bool) (h : Constraints p) : clause p c1232 = true :=
  Snake9.LocalRup.prove_clause [c479, c163] c1232 (by decide) p (sat_cons (step479 p h) (sat_cons (step163 p h) (sat_nil p)))
def c1233 : List Lit := [(83, true), (98, true), (79, true), (77, false)]
theorem step1233 (p : Nat → Bool) (h : Constraints p) : clause p c1233 = true :=
  Snake9.LocalRup.prove_clause [c480, c169] c1233 (by decide) p (sat_cons (step480 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1234 : List Lit := [(83, true), (76, true), (77, false), (98, true)]
theorem step1234 (p : Nat → Bool) (h : Constraints p) : clause p c1234 = true :=
  Snake9.LocalRup.prove_clause [c480, c170] c1234 (by decide) p (sat_cons (step480 p h) (sat_cons (step170 p h) (sat_nil p)))
def c1235 : List Lit := [(76, true), (98, true), (79, true), (77, false)]
theorem step1235 (p : Nat → Bool) (h : Constraints p) : clause p c1235 = true :=
  Snake9.LocalRup.prove_clause [c480, c171] c1235 (by decide) p (sat_cons (step480 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1236 : List Lit := [(76, true), (83, true), (79, true), (77, false)]
theorem step1236 (p : Nat → Bool) (h : Constraints p) : clause p c1236 = true :=
  Snake9.LocalRup.prove_clause [c480, c172] c1236 (by decide) p (sat_cons (step480 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1237 : List Lit := [(89, true), (84, true), (78, false), (100, true), (79, true)]
theorem step1237 (p : Nat → Bool) (h : Constraints p) : clause p c1237 = true :=
  Snake9.LocalRup.prove_clause [c481, c175] c1237 (by decide) p (sat_cons (step481 p h) (sat_cons (step175 p h) (sat_nil p)))
def c1238 : List Lit := [(84, true), (76, true), (79, true), (78, false), (100, true)]
theorem step1238 (p : Nat → Bool) (h : Constraints p) : clause p c1238 = true :=
  Snake9.LocalRup.prove_clause [c481, c176] c1238 (by decide) p (sat_cons (step481 p h) (sat_cons (step176 p h) (sat_nil p)))
def c1239 : List Lit := [(91, true), (80, false), (79, true), (101, true)]
theorem step1239 (p : Nat → Bool) (h : Constraints p) : clause p c1239 = true :=
  Snake9.LocalRup.prove_clause [c482, c194] c1239 (by decide) p (sat_cons (step482 p h) (sat_cons (step194 p h) (sat_nil p)))
def c1240 : List Lit := [(91, true), (80, false), (101, true), (20, true)]
theorem step1240 (p : Nat → Bool) (h : Constraints p) : clause p c1240 = true :=
  Snake9.LocalRup.prove_clause [c482, c195] c1240 (by decide) p (sat_cons (step482 p h) (sat_cons (step195 p h) (sat_nil p)))
def c1241 : List Lit := [(79, true), (80, false), (101, true), (20, true)]
theorem step1241 (p : Nat → Bool) (h : Constraints p) : clause p c1241 = true :=
  Snake9.LocalRup.prove_clause [c482, c196] c1241 (by decide) p (sat_cons (step482 p h) (sat_cons (step196 p h) (sat_nil p)))
def c1242 : List Lit := [(91, true), (80, false), (79, true), (20, true)]
theorem step1242 (p : Nat → Bool) (h : Constraints p) : clause p c1242 = true :=
  Snake9.LocalRup.prove_clause [c482, c197] c1242 (by decide) p (sat_cons (step482 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1243 : List Lit := [(84, true), (83, true), (81, false), (82, true)]
theorem step1243 (p : Nat → Bool) (h : Constraints p) : clause p c1243 = true :=
  Snake9.LocalRup.prove_clause [c483, c198] c1243 (by decide) p (sat_cons (step483 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1244 : List Lit := [(83, true), (84, true), (81, false), (76, true)]
theorem step1244 (p : Nat → Bool) (h : Constraints p) : clause p c1244 = true :=
  Snake9.LocalRup.prove_clause [c483, c199] c1244 (by decide) p (sat_cons (step483 p h) (sat_cons (step199 p h) (sat_nil p)))
def c1245 : List Lit := [(84, true), (76, true), (81, false), (82, true)]
theorem step1245 (p : Nat → Bool) (h : Constraints p) : clause p c1245 = true :=
  Snake9.LocalRup.prove_clause [c483, c200] c1245 (by decide) p (sat_cons (step483 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1246 : List Lit := [(84, true), (105, true), (85, false)]
theorem step1246 (p : Nat → Bool) (h : Constraints p) : clause p c1246 = true :=
  Snake9.LocalRup.prove_clause [c484, c226] c1246 (by decide) p (sat_cons (step484 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1247 : List Lit := [(82, true), (105, true), (85, false)]
theorem step1247 (p : Nat → Bool) (h : Constraints p) : clause p c1247 = true :=
  Snake9.LocalRup.prove_clause [c484, c227] c1247 (by decide) p (sat_cons (step484 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1248 : List Lit := [(84, true), (82, true), (85, false)]
theorem step1248 (p : Nat → Bool) (h : Constraints p) : clause p c1248 = true :=
  Snake9.LocalRup.prove_clause [c484, c228] c1248 (by decide) p (sat_cons (step484 p h) (sat_cons (step228 p h) (sat_nil p)))
def c1249 : List Lit := [(89, true), (91, true), (90, false)]
theorem step1249 (p : Nat → Bool) (h : Constraints p) : clause p c1249 = true :=
  Snake9.LocalRup.prove_clause [c485, c238] c1249 (by decide) p (sat_cons (step485 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1250 : List Lit := [(87, true), (91, true), (90, false)]
theorem step1250 (p : Nat → Bool) (h : Constraints p) : clause p c1250 = true :=
  Snake9.LocalRup.prove_clause [c485, c239] c1250 (by decide) p (sat_cons (step485 p h) (sat_cons (step239 p h) (sat_nil p)))
def c1251 : List Lit := [(87, true), (89, true), (90, false)]
theorem step1251 (p : Nat → Bool) (h : Constraints p) : clause p c1251 = true :=
  Snake9.LocalRup.prove_clause [c485, c240] c1251 (by decide) p (sat_cons (step485 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1252 : List Lit := [(87, true), (94, true), (92, false)]
theorem step1252 (p : Nat → Bool) (h : Constraints p) : clause p c1252 = true :=
  Snake9.LocalRup.prove_clause [c486, c247] c1252 (by decide) p (sat_cons (step486 p h) (sat_cons (step247 p h) (sat_nil p)))
def c1253 : List Lit := [(94, true), (92, false), (82, true)]
theorem step1253 (p : Nat → Bool) (h : Constraints p) : clause p c1253 = true :=
  Snake9.LocalRup.prove_clause [c486, c248] c1253 (by decide) p (sat_cons (step486 p h) (sat_cons (step248 p h) (sat_nil p)))
def c1254 : List Lit := [(87, true), (92, false), (82, true)]
theorem step1254 (p : Nat → Bool) (h : Constraints p) : clause p c1254 = true :=
  Snake9.LocalRup.prove_clause [c486, c249] c1254 (by decide) p (sat_cons (step486 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1255 : List Lit := [(103, true), (110, true), (101, true), (98, true), (99, false)]
theorem step1255 (p : Nat → Bool) (h : Constraints p) : clause p c1255 = true :=
  Snake9.LocalRup.prove_clause [c488, c288] c1255 (by decide) p (sat_cons (step488 p h) (sat_cons (step288 p h) (sat_nil p)))
def c1256 : List Lit := [(103, true), (110, true), (97, true), (101, true), (99, false)]
theorem step1256 (p : Nat → Bool) (h : Constraints p) : clause p c1256 = true :=
  Snake9.LocalRup.prove_clause [c488, c289] c1256 (by decide) p (sat_cons (step488 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1257 : List Lit := [(110, true), (98, true), (97, true), (103, true), (99, false)]
theorem step1257 (p : Nat → Bool) (h : Constraints p) : clause p c1257 = true :=
  Snake9.LocalRup.prove_clause [c488, c290] c1257 (by decide) p (sat_cons (step488 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1258 : List Lit := [(97, true), (110, true), (101, true), (99, false), (98, true)]
theorem step1258 (p : Nat → Bool) (h : Constraints p) : clause p c1258 = true :=
  Snake9.LocalRup.prove_clause [c488, c291] c1258 (by decide) p (sat_cons (step488 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1259 : List Lit := [(103, true), (97, true), (98, true), (99, false), (101, true)]
theorem step1259 (p : Nat → Bool) (h : Constraints p) : clause p c1259 = true :=
  Snake9.LocalRup.prove_clause [c488, c292] c1259 (by decide) p (sat_cons (step488 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1260 : List Lit := [(103, true), (97, true), (102, false), (105, true)]
theorem step1260 (p : Nat → Bool) (h : Constraints p) : clause p c1260 = true :=
  Snake9.LocalRup.prove_clause [c489, c327] c1260 (by decide) p (sat_cons (step489 p h) (sat_cons (step327 p h) (sat_nil p)))
def c1261 : List Lit := [(82, true), (103, true), (102, false), (105, true)]
theorem step1261 (p : Nat → Bool) (h : Constraints p) : clause p c1261 = true :=
  Snake9.LocalRup.prove_clause [c489, c328] c1261 (by decide) p (sat_cons (step489 p h) (sat_cons (step328 p h) (sat_nil p)))
def c1262 : List Lit := [(82, true), (102, false), (105, true), (97, true)]
theorem step1262 (p : Nat → Bool) (h : Constraints p) : clause p c1262 = true :=
  Snake9.LocalRup.prove_clause [c489, c329] c1262 (by decide) p (sat_cons (step489 p h) (sat_cons (step329 p h) (sat_nil p)))
def c1263 : List Lit := [(103, true), (82, true), (102, false), (97, true)]
theorem step1263 (p : Nat → Bool) (h : Constraints p) : clause p c1263 = true :=
  Snake9.LocalRup.prove_clause [c489, c330] c1263 (by decide) p (sat_cons (step489 p h) (sat_cons (step330 p h) (sat_nil p)))
def c1264 : List Lit := [(103, true), (106, true), (107, false), (105, true), (118, true)]
theorem step1264 (p : Nat → Bool) (h : Constraints p) : clause p c1264 = true :=
  Snake9.LocalRup.prove_clause [c490, c380] c1264 (by decide) p (sat_cons (step490 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1265 : List Lit := [(118, true), (106, true), (101, true), (107, false), (105, true)]
theorem step1265 (p : Nat → Bool) (h : Constraints p) : clause p c1265 = true :=
  Snake9.LocalRup.prove_clause [c490, c381] c1265 (by decide) p (sat_cons (step490 p h) (sat_cons (step381 p h) (sat_nil p)))
def c1266 : List Lit := [(103, true), (106, true), (101, true), (107, false), (118, true)]
theorem step1266 (p : Nat → Bool) (h : Constraints p) : clause p c1266 = true :=
  Snake9.LocalRup.prove_clause [c490, c382] c1266 (by decide) p (sat_cons (step490 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1267 : List Lit := [(103, true), (101, true), (118, true), (107, false), (105, true)]
theorem step1267 (p : Nat → Bool) (h : Constraints p) : clause p c1267 = true :=
  Snake9.LocalRup.prove_clause [c490, c383] c1267 (by decide) p (sat_cons (step490 p h) (sat_cons (step383 p h) (sat_nil p)))
def c1268 : List Lit := [(103, true), (106, true), (101, true), (107, false), (105, true)]
theorem step1268 (p : Nat → Bool) (h : Constraints p) : clause p c1268 = true :=
  Snake9.LocalRup.prove_clause [c490, c384] c1268 (by decide) p (sat_cons (step490 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1269 : List Lit := [(108, true), (109, false), (112, true), (110, true)]
theorem step1269 (p : Nat → Bool) (h : Constraints p) : clause p c1269 = true :=
  Snake9.LocalRup.prove_clause [c491, c394] c1269 (by decide) p (sat_cons (step491 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1270 : List Lit := [(110, true), (112, true), (109, false), (98, true)]
theorem step1270 (p : Nat → Bool) (h : Constraints p) : clause p c1270 = true :=
  Snake9.LocalRup.prove_clause [c491, c395] c1270 (by decide) p (sat_cons (step491 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1271 : List Lit := [(108, true), (112, true), (98, true), (109, false)]
theorem step1271 (p : Nat → Bool) (h : Constraints p) : clause p c1271 = true :=
  Snake9.LocalRup.prove_clause [c491, c396] c1271 (by decide) p (sat_cons (step491 p h) (sat_cons (step396 p h) (sat_nil p)))
def c1272 : List Lit := [(108, true), (110, true), (109, false), (98, true)]
theorem step1272 (p : Nat → Bool) (h : Constraints p) : clause p c1272 = true :=
  Snake9.LocalRup.prove_clause [c491, c397] c1272 (by decide) p (sat_cons (step491 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1273 : List Lit := [(115, true), (112, true), (100, true), (108, true), (68, true), (111, false)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true :=
  Snake9.LocalRup.prove_clause [c492, c405] c1273 (by decide) p (sat_cons (step492 p h) (sat_cons (step405 p h) (sat_nil p)))
def c1274 : List Lit := [(89, true), (115, true), (112, true), (111, false), (68, true), (100, true)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true :=
  Snake9.LocalRup.prove_clause [c492, c406] c1274 (by decide) p (sat_cons (step492 p h) (sat_cons (step406 p h) (sat_nil p)))
def c1275 : List Lit := [(115, true), (114, false), (108, true)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true :=
  Snake9.LocalRup.prove_clause [c493, c425] c1275 (by decide) p (sat_cons (step493 p h) (sat_cons (step425 p h) (sat_nil p)))
def c1276 : List Lit := [(115, true), (114, false), (46, true)]
theorem step1276 (p : Nat → Bool) (h : Constraints p) : clause p c1276 = true :=
  Snake9.LocalRup.prove_clause [c493, c426] c1276 (by decide) p (sat_cons (step493 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1277 : List Lit := [(114, false), (46, true), (108, true)]
theorem step1277 (p : Nat → Bool) (h : Constraints p) : clause p c1277 = true :=
  Snake9.LocalRup.prove_clause [c493, c427] c1277 (by decide) p (sat_cons (step493 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1278 : List Lit := [(115, true), (118, true), (116, false)]
theorem step1278 (p : Nat → Bool) (h : Constraints p) : clause p c1278 = true :=
  Snake9.LocalRup.prove_clause [c494, c439] c1278 (by decide) p (sat_cons (step494 p h) (sat_cons (step439 p h) (sat_nil p)))
def c1279 : List Lit := [(118, true), (116, false), (105, true)]
theorem step1279 (p : Nat → Bool) (h : Constraints p) : clause p c1279 = true :=
  Snake9.LocalRup.prove_clause [c494, c440] c1279 (by decide) p (sat_cons (step494 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1280 : List Lit := [(115, true), (116, false), (105, true)]
theorem step1280 (p : Nat → Bool) (h : Constraints p) : clause p c1280 = true :=
  Snake9.LocalRup.prove_clause [c494, c441] c1280 (by decide) p (sat_cons (step494 p h) (sat_cons (step441 p h) (sat_nil p)))
def c1281 : List Lit := [(261, false), (289, false)]
theorem step1281 (p : Nat → Bool) (h : Constraints p) : clause p c1281 = true :=
  Snake9.LocalRup.prove_clause [c1042, c520] c1281 (by decide) p (sat_cons (step1042 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1282 : List Lit := [(295, false), (301, false)]
theorem step1282 (p : Nat → Bool) (h : Constraints p) : clause p c1282 = true :=
  Snake9.LocalRup.prove_clause [c1046, c528] c1282 (by decide) p (sat_cons (step1046 p h) (sat_cons (step528 p h) (sat_nil p)))
def c1283 : List Lit := [(303, false), (315, false)]
theorem step1283 (p : Nat → Bool) (h : Constraints p) : clause p c1283 = true :=
  Snake9.LocalRup.prove_clause [c1044, c536] c1283 (by decide) p (sat_cons (step1044 p h) (sat_cons (step536 p h) (sat_nil p)))
def c1284 : List Lit := [(291, false), (347, false)]
theorem step1284 (p : Nat → Bool) (h : Constraints p) : clause p c1284 = true :=
  Snake9.LocalRup.prove_clause [c1039, c548] c1284 (by decide) p (sat_cons (step1039 p h) (sat_cons (step548 p h) (sat_nil p)))
def c1285 : List Lit := [(445, false), (459, false)]
theorem step1285 (p : Nat → Bool) (h : Constraints p) : clause p c1285 = true :=
  Snake9.LocalRup.prove_clause [c1043, c576] c1285 (by decide) p (sat_cons (step1043 p h) (sat_cons (step576 p h) (sat_nil p)))
def c1286 : List Lit := [(433, false), (461, false)]
theorem step1286 (p : Nat → Bool) (h : Constraints p) : clause p c1286 = true :=
  Snake9.LocalRup.prove_clause [c1040, c580] c1286 (by decide) p (sat_cons (step1040 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1287 : List Lit := [(349, false), (465, false)]
theorem step1287 (p : Nat → Bool) (h : Constraints p) : clause p c1287 = true :=
  Snake9.LocalRup.prove_clause [c587, c585] c1287 (by decide) p (sat_cons (step587 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1288 : List Lit := [(1428, true), (1416, false)]
theorem step1288 (p : Nat → Bool) (h : Constraints p) : clause p c1288 = true :=
  Snake9.LocalRup.prove_clause [c1169, c608] c1288 (by decide) p (sat_cons (step1169 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1289 : List Lit := [(1417, false), (1429, true)]
theorem step1289 (p : Nat → Bool) (h : Constraints p) : clause p c1289 = true :=
  Snake9.LocalRup.prove_clause [c1169, c611] c1289 (by decide) p (sat_cons (step1169 p h) (sat_cons (step611 p h) (sat_nil p)))
def c1290 : List Lit := [(1437, false), (1450, true)]
theorem step1290 (p : Nat → Bool) (h : Constraints p) : clause p c1290 = true :=
  Snake9.LocalRup.prove_clause [c1065, c635] c1290 (by decide) p (sat_cons (step1065 p h) (sat_cons (step635 p h) (sat_nil p)))
def c1291 : List Lit := [(1438, false), (1451, true)]
theorem step1291 (p : Nat → Bool) (h : Constraints p) : clause p c1291 = true :=
  Snake9.LocalRup.prove_clause [c1065, c638] c1291 (by decide) p (sat_cons (step1065 p h) (sat_cons (step638 p h) (sat_nil p)))
end B112E096
