import ReplayCheck161_01408
import ReplayCheck161_01412
import ReplayCheck161_01416
import ReplayCheck161_01420
import ReplayCheck161_01424
import ReplayCheck161_01428
import ReplayCheck161_01432
import ReplayCheck161_01436
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps44 (τ : Nat → Bool) (h1408 : TreeTrue τ start1408) : TreeTrue τ start1440 := by
  have h1409 : TreeTrue τ start1409 := replay_true τ ok1408 h1408
  have h1410 : TreeTrue τ start1410 := replay_true τ ok1409 h1409
  have h1411 : TreeTrue τ start1411 := replay_true τ ok1410 h1410
  have h1412 : TreeTrue τ start1412 := replay_true τ ok1411 h1411
  have h1413 : TreeTrue τ start1413 := replay_true τ ok1412 h1412
  have h1414 : TreeTrue τ start1414 := replay_true τ ok1413 h1413
  have h1415 : TreeTrue τ start1415 := replay_true τ ok1414 h1414
  have h1416 : TreeTrue τ start1416 := replay_true τ ok1415 h1415
  have h1417 : TreeTrue τ start1417 := replay_true τ ok1416 h1416
  have h1418 : TreeTrue τ start1418 := replay_true τ ok1417 h1417
  have h1419 : TreeTrue τ start1419 := replay_true τ ok1418 h1418
  have h1420 : TreeTrue τ start1420 := replay_true τ ok1419 h1419
  have h1421 : TreeTrue τ start1421 := replay_true τ ok1420 h1420
  have h1422 : TreeTrue τ start1422 := replay_true τ ok1421 h1421
  have h1423 : TreeTrue τ start1423 := replay_true τ ok1422 h1422
  have h1424 : TreeTrue τ start1424 := replay_true τ ok1423 h1423
  have h1425 : TreeTrue τ start1425 := replay_true τ ok1424 h1424
  have h1426 : TreeTrue τ start1426 := replay_true τ ok1425 h1425
  have h1427 : TreeTrue τ start1427 := replay_true τ ok1426 h1426
  have h1428 : TreeTrue τ start1428 := replay_true τ ok1427 h1427
  have h1429 : TreeTrue τ start1429 := replay_true τ ok1428 h1428
  have h1430 : TreeTrue τ start1430 := replay_true τ ok1429 h1429
  have h1431 : TreeTrue τ start1431 := replay_true τ ok1430 h1430
  have h1432 : TreeTrue τ start1432 := replay_true τ ok1431 h1431
  have h1433 : TreeTrue τ start1433 := replay_true τ ok1432 h1432
  have h1434 : TreeTrue τ start1434 := replay_true τ ok1433 h1433
  have h1435 : TreeTrue τ start1435 := replay_true τ ok1434 h1434
  have h1436 : TreeTrue τ start1436 := replay_true τ ok1435 h1435
  have h1437 : TreeTrue τ start1437 := replay_true τ ok1436 h1436
  have h1438 : TreeTrue τ start1438 := replay_true τ ok1437 h1437
  have h1439 : TreeTrue τ start1439 := replay_true τ ok1438 h1438
  have h1440 : TreeTrue τ start1440 := cp_true τ ok1439 h1439
  exact h1440
#print axioms steps44
end Snake9.ReplayFull161
