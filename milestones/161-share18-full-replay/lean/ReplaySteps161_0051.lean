import ReplayCheck161_01632
import ReplayCheck161_01636
import ReplayCheck161_01640
import ReplayCheck161_01644
import ReplayCheck161_01648
import ReplayCheck161_01652
import ReplayCheck161_01656
import ReplayCheck161_01660
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps51 (τ : Nat → Bool) (h1632 : TreeTrue τ start1632) : TreeTrue τ start1664 := by
  have h1633 : TreeTrue τ start1633 := replay_true τ ok1632 h1632
  have h1634 : TreeTrue τ start1634 := replay_true τ ok1633 h1633
  have h1635 : TreeTrue τ start1635 := replay_true τ ok1634 h1634
  have h1636 : TreeTrue τ start1636 := replay_true τ ok1635 h1635
  have h1637 : TreeTrue τ start1637 := replay_true τ ok1636 h1636
  have h1638 : TreeTrue τ start1638 := replay_true τ ok1637 h1637
  have h1639 : TreeTrue τ start1639 := replay_true τ ok1638 h1638
  have h1640 : TreeTrue τ start1640 := replay_true τ ok1639 h1639
  have h1641 : TreeTrue τ start1641 := replay_true τ ok1640 h1640
  have h1642 : TreeTrue τ start1642 := replay_true τ ok1641 h1641
  have h1643 : TreeTrue τ start1643 := replay_true τ ok1642 h1642
  have h1644 : TreeTrue τ start1644 := replay_true τ ok1643 h1643
  have h1645 : TreeTrue τ start1645 := replay_true τ ok1644 h1644
  have h1646 : TreeTrue τ start1646 := replay_true τ ok1645 h1645
  have h1647 : TreeTrue τ start1647 := replay_true τ ok1646 h1646
  have h1648 : TreeTrue τ start1648 := replay_true τ ok1647 h1647
  have h1649 : TreeTrue τ start1649 := replay_true τ ok1648 h1648
  have h1650 : TreeTrue τ start1650 := replay_true τ ok1649 h1649
  have h1651 : TreeTrue τ start1651 := replay_true τ ok1650 h1650
  have h1652 : TreeTrue τ start1652 := replay_true τ ok1651 h1651
  have h1653 : TreeTrue τ start1653 := replay_true τ ok1652 h1652
  have h1654 : TreeTrue τ start1654 := replay_true τ ok1653 h1653
  have h1655 : TreeTrue τ start1655 := replay_true τ ok1654 h1654
  have h1656 : TreeTrue τ start1656 := replay_true τ ok1655 h1655
  have h1657 : TreeTrue τ start1657 := replay_true τ ok1656 h1656
  have h1658 : TreeTrue τ start1658 := replay_true τ ok1657 h1657
  have h1659 : TreeTrue τ start1659 := replay_true τ ok1658 h1658
  have h1660 : TreeTrue τ start1660 := replay_true τ ok1659 h1659
  have h1661 : TreeTrue τ start1661 := replay_true τ ok1660 h1660
  have h1662 : TreeTrue τ start1662 := replay_true τ ok1661 h1661
  have h1663 : TreeTrue τ start1663 := replay_true τ ok1662 h1662
  have h1664 : TreeTrue τ start1664 := cp_true τ ok1663 h1663
  exact h1664
#print axioms steps51
end Snake9.ReplayFull161
