import ReplayCheck161_01664
import ReplayCheck161_01668
import ReplayCheck161_01672
import ReplayCheck161_01676
import ReplayCheck161_01680
import ReplayCheck161_01684
import ReplayCheck161_01688
import ReplayCheck161_01692
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps52 (τ : Nat → Bool) (h1664 : TreeTrue τ start1664) : TreeTrue τ start1696 := by
  have h1665 : TreeTrue τ start1665 := replay_true τ ok1664 h1664
  have h1666 : TreeTrue τ start1666 := replay_true τ ok1665 h1665
  have h1667 : TreeTrue τ start1667 := replay_true τ ok1666 h1666
  have h1668 : TreeTrue τ start1668 := replay_true τ ok1667 h1667
  have h1669 : TreeTrue τ start1669 := replay_true τ ok1668 h1668
  have h1670 : TreeTrue τ start1670 := replay_true τ ok1669 h1669
  have h1671 : TreeTrue τ start1671 := replay_true τ ok1670 h1670
  have h1672 : TreeTrue τ start1672 := replay_true τ ok1671 h1671
  have h1673 : TreeTrue τ start1673 := replay_true τ ok1672 h1672
  have h1674 : TreeTrue τ start1674 := replay_true τ ok1673 h1673
  have h1675 : TreeTrue τ start1675 := replay_true τ ok1674 h1674
  have h1676 : TreeTrue τ start1676 := replay_true τ ok1675 h1675
  have h1677 : TreeTrue τ start1677 := replay_true τ ok1676 h1676
  have h1678 : TreeTrue τ start1678 := replay_true τ ok1677 h1677
  have h1679 : TreeTrue τ start1679 := replay_true τ ok1678 h1678
  have h1680 : TreeTrue τ start1680 := replay_true τ ok1679 h1679
  have h1681 : TreeTrue τ start1681 := replay_true τ ok1680 h1680
  have h1682 : TreeTrue τ start1682 := replay_true τ ok1681 h1681
  have h1683 : TreeTrue τ start1683 := replay_true τ ok1682 h1682
  have h1684 : TreeTrue τ start1684 := replay_true τ ok1683 h1683
  have h1685 : TreeTrue τ start1685 := replay_true τ ok1684 h1684
  have h1686 : TreeTrue τ start1686 := replay_true τ ok1685 h1685
  have h1687 : TreeTrue τ start1687 := replay_true τ ok1686 h1686
  have h1688 : TreeTrue τ start1688 := replay_true τ ok1687 h1687
  have h1689 : TreeTrue τ start1689 := replay_true τ ok1688 h1688
  have h1690 : TreeTrue τ start1690 := replay_true τ ok1689 h1689
  have h1691 : TreeTrue τ start1691 := replay_true τ ok1690 h1690
  have h1692 : TreeTrue τ start1692 := replay_true τ ok1691 h1691
  have h1693 : TreeTrue τ start1693 := replay_true τ ok1692 h1692
  have h1694 : TreeTrue τ start1694 := replay_true τ ok1693 h1693
  have h1695 : TreeTrue τ start1695 := replay_true τ ok1694 h1694
  have h1696 : TreeTrue τ start1696 := cp_true τ ok1695 h1695
  exact h1696
#print axioms steps52
end Snake9.ReplayFull161
