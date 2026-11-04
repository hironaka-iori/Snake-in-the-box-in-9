import ReplayCheck161_01696
import ReplayCheck161_01700
import ReplayCheck161_01704
import ReplayCheck161_01708
import ReplayCheck161_01712
import ReplayCheck161_01716
import ReplayCheck161_01720
import ReplayCheck161_01724
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps53 (τ : Nat → Bool) (h1696 : TreeTrue τ start1696) : TreeTrue τ start1728 := by
  have h1697 : TreeTrue τ start1697 := replay_true τ ok1696 h1696
  have h1698 : TreeTrue τ start1698 := replay_true τ ok1697 h1697
  have h1699 : TreeTrue τ start1699 := replay_true τ ok1698 h1698
  have h1700 : TreeTrue τ start1700 := replay_true τ ok1699 h1699
  have h1701 : TreeTrue τ start1701 := replay_true τ ok1700 h1700
  have h1702 : TreeTrue τ start1702 := replay_true τ ok1701 h1701
  have h1703 : TreeTrue τ start1703 := replay_true τ ok1702 h1702
  have h1704 : TreeTrue τ start1704 := replay_true τ ok1703 h1703
  have h1705 : TreeTrue τ start1705 := replay_true τ ok1704 h1704
  have h1706 : TreeTrue τ start1706 := replay_true τ ok1705 h1705
  have h1707 : TreeTrue τ start1707 := replay_true τ ok1706 h1706
  have h1708 : TreeTrue τ start1708 := replay_true τ ok1707 h1707
  have h1709 : TreeTrue τ start1709 := replay_true τ ok1708 h1708
  have h1710 : TreeTrue τ start1710 := replay_true τ ok1709 h1709
  have h1711 : TreeTrue τ start1711 := replay_true τ ok1710 h1710
  have h1712 : TreeTrue τ start1712 := replay_true τ ok1711 h1711
  have h1713 : TreeTrue τ start1713 := replay_true τ ok1712 h1712
  have h1714 : TreeTrue τ start1714 := replay_true τ ok1713 h1713
  have h1715 : TreeTrue τ start1715 := replay_true τ ok1714 h1714
  have h1716 : TreeTrue τ start1716 := replay_true τ ok1715 h1715
  have h1717 : TreeTrue τ start1717 := replay_true τ ok1716 h1716
  have h1718 : TreeTrue τ start1718 := replay_true τ ok1717 h1717
  have h1719 : TreeTrue τ start1719 := replay_true τ ok1718 h1718
  have h1720 : TreeTrue τ start1720 := replay_true τ ok1719 h1719
  have h1721 : TreeTrue τ start1721 := replay_true τ ok1720 h1720
  have h1722 : TreeTrue τ start1722 := replay_true τ ok1721 h1721
  have h1723 : TreeTrue τ start1723 := replay_true τ ok1722 h1722
  have h1724 : TreeTrue τ start1724 := replay_true τ ok1723 h1723
  have h1725 : TreeTrue τ start1725 := replay_true τ ok1724 h1724
  have h1726 : TreeTrue τ start1726 := replay_true τ ok1725 h1725
  have h1727 : TreeTrue τ start1727 := replay_true τ ok1726 h1726
  have h1728 : TreeTrue τ start1728 := cp_true τ ok1727 h1727
  exact h1728
#print axioms steps53
end Snake9.ReplayFull161
