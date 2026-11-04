import ReplayCheck161_01472
import ReplayCheck161_01476
import ReplayCheck161_01480
import ReplayCheck161_01484
import ReplayCheck161_01488
import ReplayCheck161_01492
import ReplayCheck161_01496
import ReplayCheck161_01500
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps46 (τ : Nat → Bool) (h1472 : TreeTrue τ start1472) : TreeTrue τ start1504 := by
  have h1473 : TreeTrue τ start1473 := replay_true τ ok1472 h1472
  have h1474 : TreeTrue τ start1474 := replay_true τ ok1473 h1473
  have h1475 : TreeTrue τ start1475 := replay_true τ ok1474 h1474
  have h1476 : TreeTrue τ start1476 := replay_true τ ok1475 h1475
  have h1477 : TreeTrue τ start1477 := replay_true τ ok1476 h1476
  have h1478 : TreeTrue τ start1478 := replay_true τ ok1477 h1477
  have h1479 : TreeTrue τ start1479 := replay_true τ ok1478 h1478
  have h1480 : TreeTrue τ start1480 := replay_true τ ok1479 h1479
  have h1481 : TreeTrue τ start1481 := replay_true τ ok1480 h1480
  have h1482 : TreeTrue τ start1482 := replay_true τ ok1481 h1481
  have h1483 : TreeTrue τ start1483 := replay_true τ ok1482 h1482
  have h1484 : TreeTrue τ start1484 := replay_true τ ok1483 h1483
  have h1485 : TreeTrue τ start1485 := replay_true τ ok1484 h1484
  have h1486 : TreeTrue τ start1486 := replay_true τ ok1485 h1485
  have h1487 : TreeTrue τ start1487 := replay_true τ ok1486 h1486
  have h1488 : TreeTrue τ start1488 := replay_true τ ok1487 h1487
  have h1489 : TreeTrue τ start1489 := replay_true τ ok1488 h1488
  have h1490 : TreeTrue τ start1490 := replay_true τ ok1489 h1489
  have h1491 : TreeTrue τ start1491 := replay_true τ ok1490 h1490
  have h1492 : TreeTrue τ start1492 := replay_true τ ok1491 h1491
  have h1493 : TreeTrue τ start1493 := replay_true τ ok1492 h1492
  have h1494 : TreeTrue τ start1494 := replay_true τ ok1493 h1493
  have h1495 : TreeTrue τ start1495 := replay_true τ ok1494 h1494
  have h1496 : TreeTrue τ start1496 := replay_true τ ok1495 h1495
  have h1497 : TreeTrue τ start1497 := replay_true τ ok1496 h1496
  have h1498 : TreeTrue τ start1498 := replay_true τ ok1497 h1497
  have h1499 : TreeTrue τ start1499 := replay_true τ ok1498 h1498
  have h1500 : TreeTrue τ start1500 := replay_true τ ok1499 h1499
  have h1501 : TreeTrue τ start1501 := replay_true τ ok1500 h1500
  have h1502 : TreeTrue τ start1502 := replay_true τ ok1501 h1501
  have h1503 : TreeTrue τ start1503 := replay_true τ ok1502 h1502
  have h1504 : TreeTrue τ start1504 := cp_true τ ok1503 h1503
  exact h1504
#print axioms steps46
end Snake9.ReplayFull161
