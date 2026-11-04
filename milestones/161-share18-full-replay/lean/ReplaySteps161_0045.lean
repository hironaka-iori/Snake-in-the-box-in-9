import ReplayCheck161_01440
import ReplayCheck161_01444
import ReplayCheck161_01448
import ReplayCheck161_01452
import ReplayCheck161_01456
import ReplayCheck161_01460
import ReplayCheck161_01464
import ReplayCheck161_01468
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps45 (τ : Nat → Bool) (h1440 : TreeTrue τ start1440) : TreeTrue τ start1472 := by
  have h1441 : TreeTrue τ start1441 := replay_true τ ok1440 h1440
  have h1442 : TreeTrue τ start1442 := replay_true τ ok1441 h1441
  have h1443 : TreeTrue τ start1443 := replay_true τ ok1442 h1442
  have h1444 : TreeTrue τ start1444 := replay_true τ ok1443 h1443
  have h1445 : TreeTrue τ start1445 := replay_true τ ok1444 h1444
  have h1446 : TreeTrue τ start1446 := replay_true τ ok1445 h1445
  have h1447 : TreeTrue τ start1447 := replay_true τ ok1446 h1446
  have h1448 : TreeTrue τ start1448 := replay_true τ ok1447 h1447
  have h1449 : TreeTrue τ start1449 := replay_true τ ok1448 h1448
  have h1450 : TreeTrue τ start1450 := replay_true τ ok1449 h1449
  have h1451 : TreeTrue τ start1451 := replay_true τ ok1450 h1450
  have h1452 : TreeTrue τ start1452 := replay_true τ ok1451 h1451
  have h1453 : TreeTrue τ start1453 := replay_true τ ok1452 h1452
  have h1454 : TreeTrue τ start1454 := replay_true τ ok1453 h1453
  have h1455 : TreeTrue τ start1455 := replay_true τ ok1454 h1454
  have h1456 : TreeTrue τ start1456 := replay_true τ ok1455 h1455
  have h1457 : TreeTrue τ start1457 := replay_true τ ok1456 h1456
  have h1458 : TreeTrue τ start1458 := replay_true τ ok1457 h1457
  have h1459 : TreeTrue τ start1459 := replay_true τ ok1458 h1458
  have h1460 : TreeTrue τ start1460 := replay_true τ ok1459 h1459
  have h1461 : TreeTrue τ start1461 := replay_true τ ok1460 h1460
  have h1462 : TreeTrue τ start1462 := replay_true τ ok1461 h1461
  have h1463 : TreeTrue τ start1463 := replay_true τ ok1462 h1462
  have h1464 : TreeTrue τ start1464 := replay_true τ ok1463 h1463
  have h1465 : TreeTrue τ start1465 := replay_true τ ok1464 h1464
  have h1466 : TreeTrue τ start1466 := replay_true τ ok1465 h1465
  have h1467 : TreeTrue τ start1467 := replay_true τ ok1466 h1466
  have h1468 : TreeTrue τ start1468 := replay_true τ ok1467 h1467
  have h1469 : TreeTrue τ start1469 := replay_true τ ok1468 h1468
  have h1470 : TreeTrue τ start1470 := replay_true τ ok1469 h1469
  have h1471 : TreeTrue τ start1471 := replay_true τ ok1470 h1470
  have h1472 : TreeTrue τ start1472 := cp_true τ ok1471 h1471
  exact h1472
#print axioms steps45
end Snake9.ReplayFull161
