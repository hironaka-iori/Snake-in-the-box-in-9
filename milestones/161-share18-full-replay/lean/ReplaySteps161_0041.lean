import ReplayCheck161_01312
import ReplayCheck161_01316
import ReplayCheck161_01320
import ReplayCheck161_01324
import ReplayCheck161_01328
import ReplayCheck161_01332
import ReplayCheck161_01336
import ReplayCheck161_01340
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps41 (τ : Nat → Bool) (h1312 : TreeTrue τ start1312) : TreeTrue τ start1344 := by
  have h1313 : TreeTrue τ start1313 := replay_true τ ok1312 h1312
  have h1314 : TreeTrue τ start1314 := replay_true τ ok1313 h1313
  have h1315 : TreeTrue τ start1315 := replay_true τ ok1314 h1314
  have h1316 : TreeTrue τ start1316 := replay_true τ ok1315 h1315
  have h1317 : TreeTrue τ start1317 := replay_true τ ok1316 h1316
  have h1318 : TreeTrue τ start1318 := replay_true τ ok1317 h1317
  have h1319 : TreeTrue τ start1319 := replay_true τ ok1318 h1318
  have h1320 : TreeTrue τ start1320 := replay_true τ ok1319 h1319
  have h1321 : TreeTrue τ start1321 := replay_true τ ok1320 h1320
  have h1322 : TreeTrue τ start1322 := replay_true τ ok1321 h1321
  have h1323 : TreeTrue τ start1323 := replay_true τ ok1322 h1322
  have h1324 : TreeTrue τ start1324 := replay_true τ ok1323 h1323
  have h1325 : TreeTrue τ start1325 := replay_true τ ok1324 h1324
  have h1326 : TreeTrue τ start1326 := replay_true τ ok1325 h1325
  have h1327 : TreeTrue τ start1327 := replay_true τ ok1326 h1326
  have h1328 : TreeTrue τ start1328 := replay_true τ ok1327 h1327
  have h1329 : TreeTrue τ start1329 := replay_true τ ok1328 h1328
  have h1330 : TreeTrue τ start1330 := replay_true τ ok1329 h1329
  have h1331 : TreeTrue τ start1331 := replay_true τ ok1330 h1330
  have h1332 : TreeTrue τ start1332 := replay_true τ ok1331 h1331
  have h1333 : TreeTrue τ start1333 := replay_true τ ok1332 h1332
  have h1334 : TreeTrue τ start1334 := replay_true τ ok1333 h1333
  have h1335 : TreeTrue τ start1335 := replay_true τ ok1334 h1334
  have h1336 : TreeTrue τ start1336 := replay_true τ ok1335 h1335
  have h1337 : TreeTrue τ start1337 := replay_true τ ok1336 h1336
  have h1338 : TreeTrue τ start1338 := replay_true τ ok1337 h1337
  have h1339 : TreeTrue τ start1339 := replay_true τ ok1338 h1338
  have h1340 : TreeTrue τ start1340 := replay_true τ ok1339 h1339
  have h1341 : TreeTrue τ start1341 := replay_true τ ok1340 h1340
  have h1342 : TreeTrue τ start1342 := replay_true τ ok1341 h1341
  have h1343 : TreeTrue τ start1343 := replay_true τ ok1342 h1342
  have h1344 : TreeTrue τ start1344 := cp_true τ ok1343 h1343
  exact h1344
#print axioms steps41
end Snake9.ReplayFull161
