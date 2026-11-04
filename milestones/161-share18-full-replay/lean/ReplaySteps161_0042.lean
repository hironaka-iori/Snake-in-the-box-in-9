import ReplayCheck161_01344
import ReplayCheck161_01348
import ReplayCheck161_01352
import ReplayCheck161_01356
import ReplayCheck161_01360
import ReplayCheck161_01364
import ReplayCheck161_01368
import ReplayCheck161_01372
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps42 (τ : Nat → Bool) (h1344 : TreeTrue τ start1344) : TreeTrue τ start1376 := by
  have h1345 : TreeTrue τ start1345 := replay_true τ ok1344 h1344
  have h1346 : TreeTrue τ start1346 := replay_true τ ok1345 h1345
  have h1347 : TreeTrue τ start1347 := replay_true τ ok1346 h1346
  have h1348 : TreeTrue τ start1348 := replay_true τ ok1347 h1347
  have h1349 : TreeTrue τ start1349 := replay_true τ ok1348 h1348
  have h1350 : TreeTrue τ start1350 := replay_true τ ok1349 h1349
  have h1351 : TreeTrue τ start1351 := replay_true τ ok1350 h1350
  have h1352 : TreeTrue τ start1352 := replay_true τ ok1351 h1351
  have h1353 : TreeTrue τ start1353 := replay_true τ ok1352 h1352
  have h1354 : TreeTrue τ start1354 := replay_true τ ok1353 h1353
  have h1355 : TreeTrue τ start1355 := replay_true τ ok1354 h1354
  have h1356 : TreeTrue τ start1356 := replay_true τ ok1355 h1355
  have h1357 : TreeTrue τ start1357 := replay_true τ ok1356 h1356
  have h1358 : TreeTrue τ start1358 := replay_true τ ok1357 h1357
  have h1359 : TreeTrue τ start1359 := replay_true τ ok1358 h1358
  have h1360 : TreeTrue τ start1360 := replay_true τ ok1359 h1359
  have h1361 : TreeTrue τ start1361 := replay_true τ ok1360 h1360
  have h1362 : TreeTrue τ start1362 := replay_true τ ok1361 h1361
  have h1363 : TreeTrue τ start1363 := replay_true τ ok1362 h1362
  have h1364 : TreeTrue τ start1364 := replay_true τ ok1363 h1363
  have h1365 : TreeTrue τ start1365 := replay_true τ ok1364 h1364
  have h1366 : TreeTrue τ start1366 := replay_true τ ok1365 h1365
  have h1367 : TreeTrue τ start1367 := replay_true τ ok1366 h1366
  have h1368 : TreeTrue τ start1368 := replay_true τ ok1367 h1367
  have h1369 : TreeTrue τ start1369 := replay_true τ ok1368 h1368
  have h1370 : TreeTrue τ start1370 := replay_true τ ok1369 h1369
  have h1371 : TreeTrue τ start1371 := replay_true τ ok1370 h1370
  have h1372 : TreeTrue τ start1372 := replay_true τ ok1371 h1371
  have h1373 : TreeTrue τ start1373 := replay_true τ ok1372 h1372
  have h1374 : TreeTrue τ start1374 := replay_true τ ok1373 h1373
  have h1375 : TreeTrue τ start1375 := replay_true τ ok1374 h1374
  have h1376 : TreeTrue τ start1376 := cp_true τ ok1375 h1375
  exact h1376
#print axioms steps42
end Snake9.ReplayFull161
