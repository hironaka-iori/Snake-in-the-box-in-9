import ReplayCheck161_01280
import ReplayCheck161_01284
import ReplayCheck161_01288
import ReplayCheck161_01292
import ReplayCheck161_01296
import ReplayCheck161_01300
import ReplayCheck161_01304
import ReplayCheck161_01308
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps40 (τ : Nat → Bool) (h1280 : TreeTrue τ start1280) : TreeTrue τ start1312 := by
  have h1281 : TreeTrue τ start1281 := replay_true τ ok1280 h1280
  have h1282 : TreeTrue τ start1282 := replay_true τ ok1281 h1281
  have h1283 : TreeTrue τ start1283 := replay_true τ ok1282 h1282
  have h1284 : TreeTrue τ start1284 := replay_true τ ok1283 h1283
  have h1285 : TreeTrue τ start1285 := replay_true τ ok1284 h1284
  have h1286 : TreeTrue τ start1286 := replay_true τ ok1285 h1285
  have h1287 : TreeTrue τ start1287 := replay_true τ ok1286 h1286
  have h1288 : TreeTrue τ start1288 := replay_true τ ok1287 h1287
  have h1289 : TreeTrue τ start1289 := replay_true τ ok1288 h1288
  have h1290 : TreeTrue τ start1290 := replay_true τ ok1289 h1289
  have h1291 : TreeTrue τ start1291 := replay_true τ ok1290 h1290
  have h1292 : TreeTrue τ start1292 := replay_true τ ok1291 h1291
  have h1293 : TreeTrue τ start1293 := replay_true τ ok1292 h1292
  have h1294 : TreeTrue τ start1294 := replay_true τ ok1293 h1293
  have h1295 : TreeTrue τ start1295 := replay_true τ ok1294 h1294
  have h1296 : TreeTrue τ start1296 := replay_true τ ok1295 h1295
  have h1297 : TreeTrue τ start1297 := replay_true τ ok1296 h1296
  have h1298 : TreeTrue τ start1298 := replay_true τ ok1297 h1297
  have h1299 : TreeTrue τ start1299 := replay_true τ ok1298 h1298
  have h1300 : TreeTrue τ start1300 := replay_true τ ok1299 h1299
  have h1301 : TreeTrue τ start1301 := replay_true τ ok1300 h1300
  have h1302 : TreeTrue τ start1302 := replay_true τ ok1301 h1301
  have h1303 : TreeTrue τ start1303 := replay_true τ ok1302 h1302
  have h1304 : TreeTrue τ start1304 := replay_true τ ok1303 h1303
  have h1305 : TreeTrue τ start1305 := replay_true τ ok1304 h1304
  have h1306 : TreeTrue τ start1306 := replay_true τ ok1305 h1305
  have h1307 : TreeTrue τ start1307 := replay_true τ ok1306 h1306
  have h1308 : TreeTrue τ start1308 := replay_true τ ok1307 h1307
  have h1309 : TreeTrue τ start1309 := replay_true τ ok1308 h1308
  have h1310 : TreeTrue τ start1310 := replay_true τ ok1309 h1309
  have h1311 : TreeTrue τ start1311 := replay_true τ ok1310 h1310
  have h1312 : TreeTrue τ start1312 := cp_true τ ok1311 h1311
  exact h1312
#print axioms steps40
end Snake9.ReplayFull161
