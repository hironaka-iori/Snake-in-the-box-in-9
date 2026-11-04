import ReplayCheck161_01536
import ReplayCheck161_01540
import ReplayCheck161_01544
import ReplayCheck161_01548
import ReplayCheck161_01552
import ReplayCheck161_01556
import ReplayCheck161_01560
import ReplayCheck161_01564
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps48 (τ : Nat → Bool) (h1536 : TreeTrue τ start1536) : TreeTrue τ start1568 := by
  have h1537 : TreeTrue τ start1537 := replay_true τ ok1536 h1536
  have h1538 : TreeTrue τ start1538 := replay_true τ ok1537 h1537
  have h1539 : TreeTrue τ start1539 := replay_true τ ok1538 h1538
  have h1540 : TreeTrue τ start1540 := replay_true τ ok1539 h1539
  have h1541 : TreeTrue τ start1541 := replay_true τ ok1540 h1540
  have h1542 : TreeTrue τ start1542 := replay_true τ ok1541 h1541
  have h1543 : TreeTrue τ start1543 := replay_true τ ok1542 h1542
  have h1544 : TreeTrue τ start1544 := replay_true τ ok1543 h1543
  have h1545 : TreeTrue τ start1545 := replay_true τ ok1544 h1544
  have h1546 : TreeTrue τ start1546 := replay_true τ ok1545 h1545
  have h1547 : TreeTrue τ start1547 := replay_true τ ok1546 h1546
  have h1548 : TreeTrue τ start1548 := replay_true τ ok1547 h1547
  have h1549 : TreeTrue τ start1549 := replay_true τ ok1548 h1548
  have h1550 : TreeTrue τ start1550 := replay_true τ ok1549 h1549
  have h1551 : TreeTrue τ start1551 := replay_true τ ok1550 h1550
  have h1552 : TreeTrue τ start1552 := replay_true τ ok1551 h1551
  have h1553 : TreeTrue τ start1553 := replay_true τ ok1552 h1552
  have h1554 : TreeTrue τ start1554 := replay_true τ ok1553 h1553
  have h1555 : TreeTrue τ start1555 := replay_true τ ok1554 h1554
  have h1556 : TreeTrue τ start1556 := replay_true τ ok1555 h1555
  have h1557 : TreeTrue τ start1557 := replay_true τ ok1556 h1556
  have h1558 : TreeTrue τ start1558 := replay_true τ ok1557 h1557
  have h1559 : TreeTrue τ start1559 := replay_true τ ok1558 h1558
  have h1560 : TreeTrue τ start1560 := replay_true τ ok1559 h1559
  have h1561 : TreeTrue τ start1561 := replay_true τ ok1560 h1560
  have h1562 : TreeTrue τ start1562 := replay_true τ ok1561 h1561
  have h1563 : TreeTrue τ start1563 := replay_true τ ok1562 h1562
  have h1564 : TreeTrue τ start1564 := replay_true τ ok1563 h1563
  have h1565 : TreeTrue τ start1565 := replay_true τ ok1564 h1564
  have h1566 : TreeTrue τ start1566 := replay_true τ ok1565 h1565
  have h1567 : TreeTrue τ start1567 := replay_true τ ok1566 h1566
  have h1568 : TreeTrue τ start1568 := cp_true τ ok1567 h1567
  exact h1568
#print axioms steps48
end Snake9.ReplayFull161
