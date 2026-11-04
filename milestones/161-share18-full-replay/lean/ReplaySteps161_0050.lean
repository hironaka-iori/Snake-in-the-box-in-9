import ReplayCheck161_01600
import ReplayCheck161_01604
import ReplayCheck161_01608
import ReplayCheck161_01612
import ReplayCheck161_01616
import ReplayCheck161_01620
import ReplayCheck161_01624
import ReplayCheck161_01628
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps50 (τ : Nat → Bool) (h1600 : TreeTrue τ start1600) : TreeTrue τ start1632 := by
  have h1601 : TreeTrue τ start1601 := replay_true τ ok1600 h1600
  have h1602 : TreeTrue τ start1602 := replay_true τ ok1601 h1601
  have h1603 : TreeTrue τ start1603 := replay_true τ ok1602 h1602
  have h1604 : TreeTrue τ start1604 := replay_true τ ok1603 h1603
  have h1605 : TreeTrue τ start1605 := replay_true τ ok1604 h1604
  have h1606 : TreeTrue τ start1606 := replay_true τ ok1605 h1605
  have h1607 : TreeTrue τ start1607 := replay_true τ ok1606 h1606
  have h1608 : TreeTrue τ start1608 := replay_true τ ok1607 h1607
  have h1609 : TreeTrue τ start1609 := replay_true τ ok1608 h1608
  have h1610 : TreeTrue τ start1610 := replay_true τ ok1609 h1609
  have h1611 : TreeTrue τ start1611 := replay_true τ ok1610 h1610
  have h1612 : TreeTrue τ start1612 := replay_true τ ok1611 h1611
  have h1613 : TreeTrue τ start1613 := replay_true τ ok1612 h1612
  have h1614 : TreeTrue τ start1614 := replay_true τ ok1613 h1613
  have h1615 : TreeTrue τ start1615 := replay_true τ ok1614 h1614
  have h1616 : TreeTrue τ start1616 := replay_true τ ok1615 h1615
  have h1617 : TreeTrue τ start1617 := replay_true τ ok1616 h1616
  have h1618 : TreeTrue τ start1618 := replay_true τ ok1617 h1617
  have h1619 : TreeTrue τ start1619 := replay_true τ ok1618 h1618
  have h1620 : TreeTrue τ start1620 := replay_true τ ok1619 h1619
  have h1621 : TreeTrue τ start1621 := replay_true τ ok1620 h1620
  have h1622 : TreeTrue τ start1622 := replay_true τ ok1621 h1621
  have h1623 : TreeTrue τ start1623 := replay_true τ ok1622 h1622
  have h1624 : TreeTrue τ start1624 := replay_true τ ok1623 h1623
  have h1625 : TreeTrue τ start1625 := replay_true τ ok1624 h1624
  have h1626 : TreeTrue τ start1626 := replay_true τ ok1625 h1625
  have h1627 : TreeTrue τ start1627 := replay_true τ ok1626 h1626
  have h1628 : TreeTrue τ start1628 := replay_true τ ok1627 h1627
  have h1629 : TreeTrue τ start1629 := replay_true τ ok1628 h1628
  have h1630 : TreeTrue τ start1630 := replay_true τ ok1629 h1629
  have h1631 : TreeTrue τ start1631 := replay_true τ ok1630 h1630
  have h1632 : TreeTrue τ start1632 := cp_true τ ok1631 h1631
  exact h1632
#print axioms steps50
end Snake9.ReplayFull161
