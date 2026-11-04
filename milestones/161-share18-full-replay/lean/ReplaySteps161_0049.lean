import ReplayCheck161_01568
import ReplayCheck161_01572
import ReplayCheck161_01576
import ReplayCheck161_01580
import ReplayCheck161_01584
import ReplayCheck161_01588
import ReplayCheck161_01592
import ReplayCheck161_01596
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps49 (τ : Nat → Bool) (h1568 : TreeTrue τ start1568) : TreeTrue τ start1600 := by
  have h1569 : TreeTrue τ start1569 := replay_true τ ok1568 h1568
  have h1570 : TreeTrue τ start1570 := replay_true τ ok1569 h1569
  have h1571 : TreeTrue τ start1571 := replay_true τ ok1570 h1570
  have h1572 : TreeTrue τ start1572 := replay_true τ ok1571 h1571
  have h1573 : TreeTrue τ start1573 := replay_true τ ok1572 h1572
  have h1574 : TreeTrue τ start1574 := replay_true τ ok1573 h1573
  have h1575 : TreeTrue τ start1575 := replay_true τ ok1574 h1574
  have h1576 : TreeTrue τ start1576 := replay_true τ ok1575 h1575
  have h1577 : TreeTrue τ start1577 := replay_true τ ok1576 h1576
  have h1578 : TreeTrue τ start1578 := replay_true τ ok1577 h1577
  have h1579 : TreeTrue τ start1579 := replay_true τ ok1578 h1578
  have h1580 : TreeTrue τ start1580 := replay_true τ ok1579 h1579
  have h1581 : TreeTrue τ start1581 := replay_true τ ok1580 h1580
  have h1582 : TreeTrue τ start1582 := replay_true τ ok1581 h1581
  have h1583 : TreeTrue τ start1583 := replay_true τ ok1582 h1582
  have h1584 : TreeTrue τ start1584 := replay_true τ ok1583 h1583
  have h1585 : TreeTrue τ start1585 := replay_true τ ok1584 h1584
  have h1586 : TreeTrue τ start1586 := replay_true τ ok1585 h1585
  have h1587 : TreeTrue τ start1587 := replay_true τ ok1586 h1586
  have h1588 : TreeTrue τ start1588 := replay_true τ ok1587 h1587
  have h1589 : TreeTrue τ start1589 := replay_true τ ok1588 h1588
  have h1590 : TreeTrue τ start1590 := replay_true τ ok1589 h1589
  have h1591 : TreeTrue τ start1591 := replay_true τ ok1590 h1590
  have h1592 : TreeTrue τ start1592 := replay_true τ ok1591 h1591
  have h1593 : TreeTrue τ start1593 := replay_true τ ok1592 h1592
  have h1594 : TreeTrue τ start1594 := replay_true τ ok1593 h1593
  have h1595 : TreeTrue τ start1595 := replay_true τ ok1594 h1594
  have h1596 : TreeTrue τ start1596 := replay_true τ ok1595 h1595
  have h1597 : TreeTrue τ start1597 := replay_true τ ok1596 h1596
  have h1598 : TreeTrue τ start1598 := replay_true τ ok1597 h1597
  have h1599 : TreeTrue τ start1599 := replay_true τ ok1598 h1598
  have h1600 : TreeTrue τ start1600 := cp_true τ ok1599 h1599
  exact h1600
#print axioms steps49
end Snake9.ReplayFull161
