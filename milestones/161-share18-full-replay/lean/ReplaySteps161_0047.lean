import ReplayCheck161_01504
import ReplayCheck161_01508
import ReplayCheck161_01512
import ReplayCheck161_01516
import ReplayCheck161_01520
import ReplayCheck161_01524
import ReplayCheck161_01528
import ReplayCheck161_01532
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps47 (τ : Nat → Bool) (h1504 : TreeTrue τ start1504) : TreeTrue τ start1536 := by
  have h1505 : TreeTrue τ start1505 := replay_true τ ok1504 h1504
  have h1506 : TreeTrue τ start1506 := replay_true τ ok1505 h1505
  have h1507 : TreeTrue τ start1507 := replay_true τ ok1506 h1506
  have h1508 : TreeTrue τ start1508 := replay_true τ ok1507 h1507
  have h1509 : TreeTrue τ start1509 := replay_true τ ok1508 h1508
  have h1510 : TreeTrue τ start1510 := replay_true τ ok1509 h1509
  have h1511 : TreeTrue τ start1511 := replay_true τ ok1510 h1510
  have h1512 : TreeTrue τ start1512 := replay_true τ ok1511 h1511
  have h1513 : TreeTrue τ start1513 := replay_true τ ok1512 h1512
  have h1514 : TreeTrue τ start1514 := replay_true τ ok1513 h1513
  have h1515 : TreeTrue τ start1515 := replay_true τ ok1514 h1514
  have h1516 : TreeTrue τ start1516 := replay_true τ ok1515 h1515
  have h1517 : TreeTrue τ start1517 := replay_true τ ok1516 h1516
  have h1518 : TreeTrue τ start1518 := replay_true τ ok1517 h1517
  have h1519 : TreeTrue τ start1519 := replay_true τ ok1518 h1518
  have h1520 : TreeTrue τ start1520 := replay_true τ ok1519 h1519
  have h1521 : TreeTrue τ start1521 := replay_true τ ok1520 h1520
  have h1522 : TreeTrue τ start1522 := replay_true τ ok1521 h1521
  have h1523 : TreeTrue τ start1523 := replay_true τ ok1522 h1522
  have h1524 : TreeTrue τ start1524 := replay_true τ ok1523 h1523
  have h1525 : TreeTrue τ start1525 := replay_true τ ok1524 h1524
  have h1526 : TreeTrue τ start1526 := replay_true τ ok1525 h1525
  have h1527 : TreeTrue τ start1527 := replay_true τ ok1526 h1526
  have h1528 : TreeTrue τ start1528 := replay_true τ ok1527 h1527
  have h1529 : TreeTrue τ start1529 := replay_true τ ok1528 h1528
  have h1530 : TreeTrue τ start1530 := replay_true τ ok1529 h1529
  have h1531 : TreeTrue τ start1531 := replay_true τ ok1530 h1530
  have h1532 : TreeTrue τ start1532 := replay_true τ ok1531 h1531
  have h1533 : TreeTrue τ start1533 := replay_true τ ok1532 h1532
  have h1534 : TreeTrue τ start1534 := replay_true τ ok1533 h1533
  have h1535 : TreeTrue τ start1535 := replay_true τ ok1534 h1534
  have h1536 : TreeTrue τ start1536 := cp_true τ ok1535 h1535
  exact h1536
#print axioms steps47
end Snake9.ReplayFull161
