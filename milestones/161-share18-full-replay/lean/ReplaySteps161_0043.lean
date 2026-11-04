import ReplayCheck161_01376
import ReplayCheck161_01380
import ReplayCheck161_01384
import ReplayCheck161_01388
import ReplayCheck161_01392
import ReplayCheck161_01396
import ReplayCheck161_01400
import ReplayCheck161_01404
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps43 (τ : Nat → Bool) (h1376 : TreeTrue τ start1376) : TreeTrue τ start1408 := by
  have h1377 : TreeTrue τ start1377 := replay_true τ ok1376 h1376
  have h1378 : TreeTrue τ start1378 := replay_true τ ok1377 h1377
  have h1379 : TreeTrue τ start1379 := replay_true τ ok1378 h1378
  have h1380 : TreeTrue τ start1380 := replay_true τ ok1379 h1379
  have h1381 : TreeTrue τ start1381 := replay_true τ ok1380 h1380
  have h1382 : TreeTrue τ start1382 := replay_true τ ok1381 h1381
  have h1383 : TreeTrue τ start1383 := replay_true τ ok1382 h1382
  have h1384 : TreeTrue τ start1384 := replay_true τ ok1383 h1383
  have h1385 : TreeTrue τ start1385 := replay_true τ ok1384 h1384
  have h1386 : TreeTrue τ start1386 := replay_true τ ok1385 h1385
  have h1387 : TreeTrue τ start1387 := replay_true τ ok1386 h1386
  have h1388 : TreeTrue τ start1388 := replay_true τ ok1387 h1387
  have h1389 : TreeTrue τ start1389 := replay_true τ ok1388 h1388
  have h1390 : TreeTrue τ start1390 := replay_true τ ok1389 h1389
  have h1391 : TreeTrue τ start1391 := replay_true τ ok1390 h1390
  have h1392 : TreeTrue τ start1392 := replay_true τ ok1391 h1391
  have h1393 : TreeTrue τ start1393 := replay_true τ ok1392 h1392
  have h1394 : TreeTrue τ start1394 := replay_true τ ok1393 h1393
  have h1395 : TreeTrue τ start1395 := replay_true τ ok1394 h1394
  have h1396 : TreeTrue τ start1396 := replay_true τ ok1395 h1395
  have h1397 : TreeTrue τ start1397 := replay_true τ ok1396 h1396
  have h1398 : TreeTrue τ start1398 := replay_true τ ok1397 h1397
  have h1399 : TreeTrue τ start1399 := replay_true τ ok1398 h1398
  have h1400 : TreeTrue τ start1400 := replay_true τ ok1399 h1399
  have h1401 : TreeTrue τ start1401 := replay_true τ ok1400 h1400
  have h1402 : TreeTrue τ start1402 := replay_true τ ok1401 h1401
  have h1403 : TreeTrue τ start1403 := replay_true τ ok1402 h1402
  have h1404 : TreeTrue τ start1404 := replay_true τ ok1403 h1403
  have h1405 : TreeTrue τ start1405 := replay_true τ ok1404 h1404
  have h1406 : TreeTrue τ start1406 := replay_true τ ok1405 h1405
  have h1407 : TreeTrue τ start1407 := replay_true τ ok1406 h1406
  have h1408 : TreeTrue τ start1408 := cp_true τ ok1407 h1407
  exact h1408
#print axioms steps43
end Snake9.ReplayFull161
