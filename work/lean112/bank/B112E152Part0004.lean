import B112E152Part0003
namespace B112E152
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1203 : List Lit := [(71, false), (72, false)]
theorem step1203 (p : Nat → Bool) (h : Constraints p) : clause p c1203 = true :=
  Snake9.LocalRup.prove_clause [c153, c146] c1203 (by decide) p (sat_cons (step153 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1204 : List Lit := [(71, false), (77, false)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true :=
  Snake9.LocalRup.prove_clause [c153, c147] c1204 (by decide) p (sat_cons (step153 p h) (sat_cons (step147 p h) (sat_nil p)))
def c1205 : List Lit := [(71, false), (115, false)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true :=
  Snake9.LocalRup.prove_clause [c153, c148] c1205 (by decide) p (sat_cons (step153 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1206 : List Lit := [(72, false), (77, false)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true :=
  Snake9.LocalRup.prove_clause [c153, c149] c1206 (by decide) p (sat_cons (step153 p h) (sat_cons (step149 p h) (sat_nil p)))
def c1207 : List Lit := [(72, false), (115, false)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true :=
  Snake9.LocalRup.prove_clause [c153, c150] c1207 (by decide) p (sat_cons (step153 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1208 : List Lit := [(74, false), (75, true)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true :=
  Snake9.LocalRup.prove_clause [c427, c154] c1208 (by decide) p (sat_cons (step427 p h) (sat_cons (step154 p h) (sat_nil p)))
def c1209 : List Lit := [(74, false), (69, true)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true :=
  Snake9.LocalRup.prove_clause [c427, c155] c1209 (by decide) p (sat_cons (step427 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1210 : List Lit := [(75, true), (76, false), (77, true)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true :=
  Snake9.LocalRup.prove_clause [c428, c158] c1210 (by decide) p (sat_cons (step428 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1211 : List Lit := [(76, false), (77, true), (66, true)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true :=
  Snake9.LocalRup.prove_clause [c428, c159] c1211 (by decide) p (sat_cons (step428 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1212 : List Lit := [(85, true), (79, false), (101, true), (82, true)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true :=
  Snake9.LocalRup.prove_clause [c429, c165] c1212 (by decide) p (sat_cons (step429 p h) (sat_cons (step165 p h) (sat_nil p)))
def c1213 : List Lit := [(78, true), (79, false), (82, true), (101, true)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true :=
  Snake9.LocalRup.prove_clause [c429, c166] c1213 (by decide) p (sat_cons (step429 p h) (sat_cons (step166 p h) (sat_nil p)))
def c1214 : List Lit := [(85, true), (78, true), (82, true), (79, false)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true :=
  Snake9.LocalRup.prove_clause [c429, c167] c1214 (by decide) p (sat_cons (step429 p h) (sat_cons (step167 p h) (sat_nil p)))
def c1215 : List Lit := [(92, true), (102, true), (82, true), (87, true), (80, false)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true :=
  Snake9.LocalRup.prove_clause [c430, c169] c1215 (by decide) p (sat_cons (step430 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1216 : List Lit := [(92, true), (87, true), (80, false), (78, true), (102, true)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true :=
  Snake9.LocalRup.prove_clause [c430, c170] c1216 (by decide) p (sat_cons (step430 p h) (sat_cons (step170 p h) (sat_nil p)))
def c1217 : List Lit := [(78, true), (102, true), (80, false), (82, true), (87, true)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true :=
  Snake9.LocalRup.prove_clause [c430, c171] c1217 (by decide) p (sat_cons (step430 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1218 : List Lit := [(92, true), (87, true), (80, false), (82, true), (78, true)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true :=
  Snake9.LocalRup.prove_clause [c430, c172] c1218 (by decide) p (sat_cons (step430 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1219 : List Lit := [(93, true), (103, true), (81, false), (82, true)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true :=
  Snake9.LocalRup.prove_clause [c431, c173] c1219 (by decide) p (sat_cons (step431 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1220 : List Lit := [(93, true), (103, true), (81, false), (28, true)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true :=
  Snake9.LocalRup.prove_clause [c431, c174] c1220 (by decide) p (sat_cons (step431 p h) (sat_cons (step174 p h) (sat_nil p)))
def c1221 : List Lit := [(103, true), (81, false), (82, true), (28, true)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true :=
  Snake9.LocalRup.prove_clause [c431, c175] c1221 (by decide) p (sat_cons (step431 p h) (sat_cons (step175 p h) (sat_nil p)))
def c1222 : List Lit := [(93, true), (81, false), (28, true), (82, true)]
theorem step1222 (p : Nat → Bool) (h : Constraints p) : clause p c1222 = true :=
  Snake9.LocalRup.prove_clause [c431, c176] c1222 (by decide) p (sat_cons (step431 p h) (sat_cons (step176 p h) (sat_nil p)))
def c1223 : List Lit := [(87, true), (86, false), (106, true)]
theorem step1223 (p : Nat → Bool) (h : Constraints p) : clause p c1223 = true :=
  Snake9.LocalRup.prove_clause [c432, c199] c1223 (by decide) p (sat_cons (step432 p h) (sat_cons (step199 p h) (sat_nil p)))
def c1224 : List Lit := [(83, true), (86, false), (106, true)]
theorem step1224 (p : Nat → Bool) (h : Constraints p) : clause p c1224 = true :=
  Snake9.LocalRup.prove_clause [c432, c200] c1224 (by decide) p (sat_cons (step432 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1225 : List Lit := [(86, false), (87, true), (83, true)]
theorem step1225 (p : Nat → Bool) (h : Constraints p) : clause p c1225 = true :=
  Snake9.LocalRup.prove_clause [c432, c201] c1225 (by decide) p (sat_cons (step432 p h) (sat_cons (step201 p h) (sat_nil p)))
def c1226 : List Lit := [(93, true), (92, true), (91, false)]
theorem step1226 (p : Nat → Bool) (h : Constraints p) : clause p c1226 = true :=
  Snake9.LocalRup.prove_clause [c433, c216] c1226 (by decide) p (sat_cons (step433 p h) (sat_cons (step216 p h) (sat_nil p)))
def c1227 : List Lit := [(93, true), (89, true), (91, false)]
theorem step1227 (p : Nat → Bool) (h : Constraints p) : clause p c1227 = true :=
  Snake9.LocalRup.prove_clause [c433, c217] c1227 (by decide) p (sat_cons (step433 p h) (sat_cons (step217 p h) (sat_nil p)))
def c1228 : List Lit := [(89, true), (95, true), (94, false)]
theorem step1228 (p : Nat → Bool) (h : Constraints p) : clause p c1228 = true :=
  Snake9.LocalRup.prove_clause [c434, c224] c1228 (by decide) p (sat_cons (step434 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1229 : List Lit := [(97, true), (95, true), (96, false)]
theorem step1229 (p : Nat → Bool) (h : Constraints p) : clause p c1229 = true :=
  Snake9.LocalRup.prove_clause [c435, c229] c1229 (by decide) p (sat_cons (step435 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1230 : List Lit := [(85, true), (95, true), (96, false)]
theorem step1230 (p : Nat → Bool) (h : Constraints p) : clause p c1230 = true :=
  Snake9.LocalRup.prove_clause [c435, c231] c1230 (by decide) p (sat_cons (step435 p h) (sat_cons (step231 p h) (sat_nil p)))
def c1231 : List Lit := [(111, true), (101, true), (100, false), (98, true), (105, true)]
theorem step1231 (p : Nat → Bool) (h : Constraints p) : clause p c1231 = true :=
  Snake9.LocalRup.prove_clause [c436, c246] c1231 (by decide) p (sat_cons (step436 p h) (sat_cons (step246 p h) (sat_nil p)))
def c1232 : List Lit := [(111, true), (101, true), (100, false), (103, true), (98, true)]
theorem step1232 (p : Nat → Bool) (h : Constraints p) : clause p c1232 = true :=
  Snake9.LocalRup.prove_clause [c436, c247] c1232 (by decide) p (sat_cons (step436 p h) (sat_cons (step247 p h) (sat_nil p)))
def c1233 : List Lit := [(101, true), (100, false), (103, true), (98, true), (105, true)]
theorem step1233 (p : Nat → Bool) (h : Constraints p) : clause p c1233 = true :=
  Snake9.LocalRup.prove_clause [c436, c248] c1233 (by decide) p (sat_cons (step436 p h) (sat_cons (step248 p h) (sat_nil p)))
def c1234 : List Lit := [(98, true), (105, true), (106, true), (104, false)]
theorem step1234 (p : Nat → Bool) (h : Constraints p) : clause p c1234 = true :=
  Snake9.LocalRup.prove_clause [c437, c296] c1234 (by decide) p (sat_cons (step437 p h) (sat_cons (step296 p h) (sat_nil p)))
def c1235 : List Lit := [(83, true), (106, true), (104, false), (105, true)]
theorem step1235 (p : Nat → Bool) (h : Constraints p) : clause p c1235 = true :=
  Snake9.LocalRup.prove_clause [c437, c297] c1235 (by decide) p (sat_cons (step437 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1236 : List Lit := [(83, true), (106, true), (98, true), (104, false)]
theorem step1236 (p : Nat → Bool) (h : Constraints p) : clause p c1236 = true :=
  Snake9.LocalRup.prove_clause [c437, c298] c1236 (by decide) p (sat_cons (step437 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1237 : List Lit := [(119, true), (109, true), (105, true), (106, true), (108, false)]
theorem step1237 (p : Nat → Bool) (h : Constraints p) : clause p c1237 = true :=
  Snake9.LocalRup.prove_clause [c438, c346] c1237 (by decide) p (sat_cons (step438 p h) (sat_cons (step346 p h) (sat_nil p)))
def c1238 : List Lit := [(103, true), (109, true), (108, false), (106, true), (119, true)]
theorem step1238 (p : Nat → Bool) (h : Constraints p) : clause p c1238 = true :=
  Snake9.LocalRup.prove_clause [c438, c347] c1238 (by decide) p (sat_cons (step438 p h) (sat_cons (step347 p h) (sat_nil p)))
def c1239 : List Lit := [(103, true), (109, true), (105, true), (108, false), (119, true)]
theorem step1239 (p : Nat → Bool) (h : Constraints p) : clause p c1239 = true :=
  Snake9.LocalRup.prove_clause [c438, c348] c1239 (by decide) p (sat_cons (step438 p h) (sat_cons (step348 p h) (sat_nil p)))
def c1240 : List Lit := [(103, true), (108, false), (105, true), (106, true), (119, true)]
theorem step1240 (p : Nat → Bool) (h : Constraints p) : clause p c1240 = true :=
  Snake9.LocalRup.prove_clause [c438, c349] c1240 (by decide) p (sat_cons (step438 p h) (sat_cons (step349 p h) (sat_nil p)))
def c1241 : List Lit := [(103, true), (108, false), (105, true), (106, true), (109, true)]
theorem step1241 (p : Nat → Bool) (h : Constraints p) : clause p c1241 = true :=
  Snake9.LocalRup.prove_clause [c438, c350] c1241 (by decide) p (sat_cons (step438 p h) (sat_cons (step350 p h) (sat_nil p)))
def c1242 : List Lit := [(111, true), (110, true), (112, false), (115, true)]
theorem step1242 (p : Nat → Bool) (h : Constraints p) : clause p c1242 = true :=
  Snake9.LocalRup.prove_clause [c439, c361] c1242 (by decide) p (sat_cons (step439 p h) (sat_cons (step361 p h) (sat_nil p)))
def c1243 : List Lit := [(111, true), (101, true), (115, true), (112, false)]
theorem step1243 (p : Nat → Bool) (h : Constraints p) : clause p c1243 = true :=
  Snake9.LocalRup.prove_clause [c439, c362] c1243 (by decide) p (sat_cons (step439 p h) (sat_cons (step362 p h) (sat_nil p)))
def c1244 : List Lit := [(110, true), (101, true), (112, false), (115, true)]
theorem step1244 (p : Nat → Bool) (h : Constraints p) : clause p c1244 = true :=
  Snake9.LocalRup.prove_clause [c439, c363] c1244 (by decide) p (sat_cons (step439 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1245 : List Lit := [(110, true), (102, true), (71, true), (113, false), (115, true), (118, true)]
theorem step1245 (p : Nat → Bool) (h : Constraints p) : clause p c1245 = true :=
  Snake9.LocalRup.prove_clause [c440, c365] c1245 (by decide) p (sat_cons (step440 p h) (sat_cons (step365 p h) (sat_nil p)))
def c1246 : List Lit := [(93, true), (72, true), (114, false), (103, true), (111, true), (115, true), (119, true)]
theorem step1246 (p : Nat → Bool) (h : Constraints p) : clause p c1246 = true :=
  Snake9.LocalRup.prove_clause [c441, c367] c1246 (by decide) p (sat_cons (step441 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1247 : List Lit := [(110, true), (118, true), (116, false)]
theorem step1247 (p : Nat → Bool) (h : Constraints p) : clause p c1247 = true :=
  Snake9.LocalRup.prove_clause [c442, c377] c1247 (by decide) p (sat_cons (step442 p h) (sat_cons (step377 p h) (sat_nil p)))
def c1248 : List Lit := [(57, true), (118, true), (116, false)]
theorem step1248 (p : Nat → Bool) (h : Constraints p) : clause p c1248 = true :=
  Snake9.LocalRup.prove_clause [c442, c378] c1248 (by decide) p (sat_cons (step442 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1249 : List Lit := [(57, true), (110, true), (116, false)]
theorem step1249 (p : Nat → Bool) (h : Constraints p) : clause p c1249 = true :=
  Snake9.LocalRup.prove_clause [c442, c379] c1249 (by decide) p (sat_cons (step442 p h) (sat_cons (step379 p h) (sat_nil p)))
def c1250 : List Lit := [(119, true), (118, true), (117, false)]
theorem step1250 (p : Nat → Bool) (h : Constraints p) : clause p c1250 = true :=
  Snake9.LocalRup.prove_clause [c443, c380] c1250 (by decide) p (sat_cons (step443 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1251 : List Lit := [(119, true), (117, false), (106, true)]
theorem step1251 (p : Nat → Bool) (h : Constraints p) : clause p c1251 = true :=
  Snake9.LocalRup.prove_clause [c443, c381] c1251 (by decide) p (sat_cons (step443 p h) (sat_cons (step381 p h) (sat_nil p)))
def c1252 : List Lit := [(118, true), (117, false), (106, true)]
theorem step1252 (p : Nat → Bool) (h : Constraints p) : clause p c1252 = true :=
  Snake9.LocalRup.prove_clause [c443, c382] c1252 (by decide) p (sat_cons (step443 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1253 : List Lit := [(121, false), (241, false)]
theorem step1253 (p : Nat → Bool) (h : Constraints p) : clause p c1253 = true :=
  Snake9.LocalRup.prove_clause [c962, c447] c1253 (by decide) p (sat_cons (step962 p h) (sat_cons (step447 p h) (sat_nil p)))
def c1254 : List Lit := [(243, false), (249, false)]
theorem step1254 (p : Nat → Bool) (h : Constraints p) : clause p c1254 = true :=
  Snake9.LocalRup.prove_clause [c961, c454] c1254 (by decide) p (sat_cons (step961 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1255 : List Lit := [(251, false), (263, false)]
theorem step1255 (p : Nat → Bool) (h : Constraints p) : clause p c1255 = true :=
  Snake9.LocalRup.prove_clause [c960, c460] c1255 (by decide) p (sat_cons (step960 p h) (sat_cons (step460 p h) (sat_nil p)))
def c1256 : List Lit := [(265, false), (293, false)]
theorem step1256 (p : Nat → Bool) (h : Constraints p) : clause p c1256 = true :=
  Snake9.LocalRup.prove_clause [c959, c476] c1256 (by decide) p (sat_cons (step959 p h) (sat_cons (step476 p h) (sat_nil p)))
def c1257 : List Lit := [(295, false), (353, false)]
theorem step1257 (p : Nat → Bool) (h : Constraints p) : clause p c1257 = true :=
  Snake9.LocalRup.prove_clause [c958, c493] c1257 (by decide) p (sat_cons (step958 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1258 : List Lit := [(355, false), (473, false)]
theorem step1258 (p : Nat → Bool) (h : Constraints p) : clause p c1258 = true :=
  Snake9.LocalRup.prove_clause [c546, c544] c1258 (by decide) p (sat_cons (step546 p h) (sat_cons (step544 p h) (sat_nil p)))
def c1259 : List Lit := [(1491, false), (1500, true)]
theorem step1259 (p : Nat → Bool) (h : Constraints p) : clause p c1259 = true :=
  Snake9.LocalRup.prove_clause [c974, c600] c1259 (by decide) p (sat_cons (step974 p h) (sat_cons (step600 p h) (sat_nil p)))
def c1260 : List Lit := [(1492, false), (1501, true)]
theorem step1260 (p : Nat → Bool) (h : Constraints p) : clause p c1260 = true :=
  Snake9.LocalRup.prove_clause [c974, c601] c1260 (by decide) p (sat_cons (step974 p h) (sat_cons (step601 p h) (sat_nil p)))
def c1261 : List Lit := [(1493, false), (1502, true)]
theorem step1261 (p : Nat → Bool) (h : Constraints p) : clause p c1261 = true :=
  Snake9.LocalRup.prove_clause [c974, c602] c1261 (by decide) p (sat_cons (step974 p h) (sat_cons (step602 p h) (sat_nil p)))
def c1262 : List Lit := [(1500, true), (1472, false)]
theorem step1262 (p : Nat → Bool) (h : Constraints p) : clause p c1262 = true :=
  Snake9.LocalRup.prove_clause [c971, c603] c1262 (by decide) p (sat_cons (step971 p h) (sat_cons (step603 p h) (sat_nil p)))
def c1263 : List Lit := [(1501, true), (1473, false)]
theorem step1263 (p : Nat → Bool) (h : Constraints p) : clause p c1263 = true :=
  Snake9.LocalRup.prove_clause [c971, c606] c1263 (by decide) p (sat_cons (step971 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1264 : List Lit := [(1513, false), (1525, true)]
theorem step1264 (p : Nat → Bool) (h : Constraints p) : clause p c1264 = true :=
  Snake9.LocalRup.prove_clause [c969, c629] c1264 (by decide) p (sat_cons (step969 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1265 : List Lit := [(1514, false), (1526, true)]
theorem step1265 (p : Nat → Bool) (h : Constraints p) : clause p c1265 = true :=
  Snake9.LocalRup.prove_clause [c969, c631] c1265 (by decide) p (sat_cons (step969 p h) (sat_cons (step631 p h) (sat_nil p)))
def c1266 : List Lit := [(1549, false), (1558, true)]
theorem step1266 (p : Nat → Bool) (h : Constraints p) : clause p c1266 = true :=
  Snake9.LocalRup.prove_clause [c970, c670] c1266 (by decide) p (sat_cons (step970 p h) (sat_cons (step670 p h) (sat_nil p)))
end B112E152
