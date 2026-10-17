import B112E047Part0064
namespace B112E047
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5703 : List Lit := [(172, false)]
theorem step5703 (p : Nat → Bool) (h : Constraints p) : clause p c5703 = true :=
  Snake9.LocalRup.prove_clause [c5689, c830] c5703 (by decide) p (sat_cons (step5689 p h) (sat_cons (step830 p h) (sat_nil p)))
def c5704 : List Lit := [(169, false)]
theorem step5704 (p : Nat → Bool) (h : Constraints p) : clause p c5704 = true :=
  Snake9.LocalRup.prove_clause [c5690, c828] c5704 (by decide) p (sat_cons (step5690 p h) (sat_cons (step828 p h) (sat_nil p)))
def c5705 : List Lit := [(1519, true)]
theorem step5705 (p : Nat → Bool) (h : Constraints p) : clause p c5705 = true :=
  Snake9.LocalRup.prove_clause [c5690, c5504] c5705 (by decide) p (sat_cons (step5690 p h) (sat_cons (step5504 p h) (sat_nil p)))
def c5706 : List Lit := [(165, false)]
theorem step5706 (p : Nat → Bool) (h : Constraints p) : clause p c5706 = true :=
  Snake9.LocalRup.prove_clause [c5691, c823] c5706 (by decide) p (sat_cons (step5691 p h) (sat_cons (step823 p h) (sat_nil p)))
def c5707 : List Lit := [(459, false)]
theorem step5707 (p : Nat → Bool) (h : Constraints p) : clause p c5707 = true :=
  Snake9.LocalRup.prove_clause [c5692, c971] c5707 (by decide) p (sat_cons (step5692 p h) (sat_cons (step971 p h) (sat_nil p)))
def c5708 : List Lit := [(445, false)]
theorem step5708 (p : Nat → Bool) (h : Constraints p) : clause p c5708 = true :=
  Snake9.LocalRup.prove_clause [c5692, c973] c5708 (by decide) p (sat_cons (step5692 p h) (sat_cons (step973 p h) (sat_nil p)))
def c5709 : List Lit := [(431, false)]
theorem step5709 (p : Nat → Bool) (h : Constraints p) : clause p c5709 = true :=
  Snake9.LocalRup.prove_clause [c5693, c941] c5709 (by decide) p (sat_cons (step5693 p h) (sat_cons (step941 p h) (sat_nil p)))
def c5710 : List Lit := [(417, false)]
theorem step5710 (p : Nat → Bool) (h : Constraints p) : clause p c5710 = true :=
  Snake9.LocalRup.prove_clause [c5693, c943] c5710 (by decide) p (sat_cons (step5693 p h) (sat_cons (step943 p h) (sat_nil p)))
def c5711 : List Lit := [(1559, false)]
theorem step5711 (p : Nat → Bool) (h : Constraints p) : clause p c5711 = true :=
  Snake9.LocalRup.prove_clause [c5694, c1919] c5711 (by decide) p (sat_cons (step5694 p h) (sat_cons (step1919 p h) (sat_nil p)))
def c5712 : List Lit := [(401, false)]
theorem step5712 (p : Nat → Bool) (h : Constraints p) : clause p c5712 = true :=
  Snake9.LocalRup.prove_clause [c5695, c904] c5712 (by decide) p (sat_cons (step5695 p h) (sat_cons (step904 p h) (sat_nil p)))
def c5713 : List Lit := [(387, false)]
theorem step5713 (p : Nat → Bool) (h : Constraints p) : clause p c5713 = true :=
  Snake9.LocalRup.prove_clause [c5695, c906] c5713 (by decide) p (sat_cons (step5695 p h) (sat_cons (step906 p h) (sat_nil p)))
def c5714 : List Lit := [(373, false)]
theorem step5714 (p : Nat → Bool) (h : Constraints p) : clause p c5714 = true :=
  Snake9.LocalRup.prove_clause [c5696, c879] c5714 (by decide) p (sat_cons (step5696 p h) (sat_cons (step879 p h) (sat_nil p)))
def c5715 : List Lit := [(361, false)]
theorem step5715 (p : Nat → Bool) (h : Constraints p) : clause p c5715 = true :=
  Snake9.LocalRup.prove_clause [c5696, c881] c5715 (by decide) p (sat_cons (step5696 p h) (sat_cons (step881 p h) (sat_nil p)))
def c5716 : List Lit := [(283, false)]
theorem step5716 (p : Nat → Bool) (h : Constraints p) : clause p c5716 = true :=
  Snake9.LocalRup.prove_clause [c5697, c781] c5716 (by decide) p (sat_cons (step5697 p h) (sat_cons (step781 p h) (sat_nil p)))
def c5717 : List Lit := [(277, false)]
theorem step5717 (p : Nat → Bool) (h : Constraints p) : clause p c5717 = true :=
  Snake9.LocalRup.prove_clause [c5698, c776] c5717 (by decide) p (sat_cons (step5698 p h) (sat_cons (step776 p h) (sat_nil p)))
def c5718 : List Lit := [(263, false)]
theorem step5718 (p : Nat → Bool) (h : Constraints p) : clause p c5718 = true :=
  Snake9.LocalRup.prove_clause [c5699, c764] c5718 (by decide) p (sat_cons (step5699 p h) (sat_cons (step764 p h) (sat_nil p)))
def c5719 : List Lit := [(253, false)]
theorem step5719 (p : Nat → Bool) (h : Constraints p) : clause p c5719 = true :=
  Snake9.LocalRup.prove_clause [c5700, c754] c5719 (by decide) p (sat_cons (step5700 p h) (sat_cons (step754 p h) (sat_nil p)))
def c5720 : List Lit := [(243, false)]
theorem step5720 (p : Nat → Bool) (h : Constraints p) : clause p c5720 = true :=
  Snake9.LocalRup.prove_clause [c5701, c742] c5720 (by decide) p (sat_cons (step5701 p h) (sat_cons (step742 p h) (sat_nil p)))
def c5721 : List Lit := [(241, false)]
theorem step5721 (p : Nat → Bool) (h : Constraints p) : clause p c5721 = true :=
  Snake9.LocalRup.prove_clause [c5701, c743] c5721 (by decide) p (sat_cons (step5701 p h) (sat_cons (step743 p h) (sat_nil p)))
def c5722 : List Lit := [(457, false)]
theorem step5722 (p : Nat → Bool) (h : Constraints p) : clause p c5722 = true :=
  Snake9.LocalRup.prove_clause [c5707, c967] c5722 (by decide) p (sat_cons (step5707 p h) (sat_cons (step967 p h) (sat_nil p)))
def c5723 : List Lit := [(443, false)]
theorem step5723 (p : Nat → Bool) (h : Constraints p) : clause p c5723 = true :=
  Snake9.LocalRup.prove_clause [c5708, c954] c5723 (by decide) p (sat_cons (step5708 p h) (sat_cons (step954 p h) (sat_nil p)))
def c5724 : List Lit := [(437, false)]
theorem step5724 (p : Nat → Bool) (h : Constraints p) : clause p c5724 = true :=
  Snake9.LocalRup.prove_clause [c5708, c956] c5724 (by decide) p (sat_cons (step5708 p h) (sat_cons (step956 p h) (sat_nil p)))
def c5725 : List Lit := [(429, false)]
theorem step5725 (p : Nat → Bool) (h : Constraints p) : clause p c5725 = true :=
  Snake9.LocalRup.prove_clause [c5709, c936] c5725 (by decide) p (sat_cons (step5709 p h) (sat_cons (step936 p h) (sat_nil p)))
def c5726 : List Lit := [(423, false)]
theorem step5726 (p : Nat → Bool) (h : Constraints p) : clause p c5726 = true :=
  Snake9.LocalRup.prove_clause [c5709, c938] c5726 (by decide) p (sat_cons (step5709 p h) (sat_cons (step938 p h) (sat_nil p)))
def c5727 : List Lit := [(409, false)]
theorem step5727 (p : Nat → Bool) (h : Constraints p) : clause p c5727 = true :=
  Snake9.LocalRup.prove_clause [c5710, c924] c5727 (by decide) p (sat_cons (step5710 p h) (sat_cons (step924 p h) (sat_nil p)))
def c5728 : List Lit := [(1489, false)]
theorem step5728 (p : Nat → Bool) (h : Constraints p) : clause p c5728 = true :=
  Snake9.LocalRup.prove_clause [c5711, c1876] c5728 (by decide) p (sat_cons (step5711 p h) (sat_cons (step1876 p h) (sat_nil p)))
def c5729 : List Lit := [(1544, false)]
theorem step5729 (p : Nat → Bool) (h : Constraints p) : clause p c5729 = true :=
  Snake9.LocalRup.prove_clause [c5711, c5247, c1188] c5729 (by decide) p (sat_cons (step5711 p h) (sat_cons (step5247 p h) (sat_cons (step1188 p h) (sat_nil p))))
def c5730 : List Lit := [(1488, false)]
theorem step5730 (p : Nat → Bool) (h : Constraints p) : clause p c5730 = true :=
  Snake9.LocalRup.prove_clause [c5711, c5518, c1206] c5730 (by decide) p (sat_cons (step5711 p h) (sat_cons (step5518 p h) (sat_cons (step1206 p h) (sat_nil p))))
def c5731 : List Lit := [(393, false)]
theorem step5731 (p : Nat → Bool) (h : Constraints p) : clause p c5731 = true :=
  Snake9.LocalRup.prove_clause [c5712, c902] c5731 (by decide) p (sat_cons (step5712 p h) (sat_cons (step902 p h) (sat_nil p)))
def c5732 : List Lit := [(379, false)]
theorem step5732 (p : Nat → Bool) (h : Constraints p) : clause p c5732 = true :=
  Snake9.LocalRup.prove_clause [c5713, c892] c5732 (by decide) p (sat_cons (step5713 p h) (sat_cons (step892 p h) (sat_nil p)))
def c5733 : List Lit := [(371, false)]
theorem step5733 (p : Nat → Bool) (h : Constraints p) : clause p c5733 = true :=
  Snake9.LocalRup.prove_clause [c5714, c875] c5733 (by decide) p (sat_cons (step5714 p h) (sat_cons (step875 p h) (sat_nil p)))
def c5734 : List Lit := [(365, false)]
theorem step5734 (p : Nat → Bool) (h : Constraints p) : clause p c5734 = true :=
  Snake9.LocalRup.prove_clause [c5714, c877] c5734 (by decide) p (sat_cons (step5714 p h) (sat_cons (step877 p h) (sat_nil p)))
def c5735 : List Lit := [(359, false)]
theorem step5735 (p : Nat → Bool) (h : Constraints p) : clause p c5735 = true :=
  Snake9.LocalRup.prove_clause [c5715, c866] c5735 (by decide) p (sat_cons (step5715 p h) (sat_cons (step866 p h) (sat_nil p)))
def c5736 : List Lit := [(353, false)]
theorem step5736 (p : Nat → Bool) (h : Constraints p) : clause p c5736 = true :=
  Snake9.LocalRup.prove_clause [c5715, c868] c5736 (by decide) p (sat_cons (step5715 p h) (sat_cons (step868 p h) (sat_nil p)))
def c5737 : List Lit := [(146, false)]
theorem step5737 (p : Nat → Bool) (h : Constraints p) : clause p c5737 = true :=
  Snake9.LocalRup.prove_clause [c5716, c780] c5737 (by decide) p (sat_cons (step5716 p h) (sat_cons (step780 p h) (sat_nil p)))
def c5738 : List Lit := [(143, false)]
theorem step5738 (p : Nat → Bool) (h : Constraints p) : clause p c5738 = true :=
  Snake9.LocalRup.prove_clause [c5717, c775] c5738 (by decide) p (sat_cons (step5717 p h) (sat_cons (step775 p h) (sat_nil p)))
def c5739 : List Lit := [(135, false)]
theorem step5739 (p : Nat → Bool) (h : Constraints p) : clause p c5739 = true :=
  Snake9.LocalRup.prove_clause [c5718, c763] c5739 (by decide) p (sat_cons (step5718 p h) (sat_cons (step763 p h) (sat_nil p)))
def c5740 : List Lit := [(129, false)]
theorem step5740 (p : Nat → Bool) (h : Constraints p) : clause p c5740 = true :=
  Snake9.LocalRup.prove_clause [c5719, c750] c5740 (by decide) p (sat_cons (step5719 p h) (sat_cons (step750 p h) (sat_nil p)))
def c5741 : List Lit := [(125, false)]
theorem step5741 (p : Nat → Bool) (h : Constraints p) : clause p c5741 = true :=
  Snake9.LocalRup.prove_clause [c5720, c741] c5741 (by decide) p (sat_cons (step5720 p h) (sat_cons (step741 p h) (sat_nil p)))
def c5742 : List Lit := [(123, false)]
theorem step5742 (p : Nat → Bool) (h : Constraints p) : clause p c5742 = true :=
  Snake9.LocalRup.prove_clause [c5721, c740] c5742 (by decide) p (sat_cons (step5721 p h) (sat_cons (step740 p h) (sat_nil p)))
def c5743 : List Lit := [(455, false)]
theorem step5743 (p : Nat → Bool) (h : Constraints p) : clause p c5743 = true :=
  Snake9.LocalRup.prove_clause [c5722, c964] c5743 (by decide) p (sat_cons (step5722 p h) (sat_cons (step964 p h) (sat_nil p)))
def c5744 : List Lit := [(441, false)]
theorem step5744 (p : Nat → Bool) (h : Constraints p) : clause p c5744 = true :=
  Snake9.LocalRup.prove_clause [c5723, c951] c5744 (by decide) p (sat_cons (step5723 p h) (sat_cons (step951 p h) (sat_nil p)))
def c5745 : List Lit := [(435, false)]
theorem step5745 (p : Nat → Bool) (h : Constraints p) : clause p c5745 = true :=
  Snake9.LocalRup.prove_clause [c5724, c947] c5745 (by decide) p (sat_cons (step5724 p h) (sat_cons (step947 p h) (sat_nil p)))
def c5746 : List Lit := [(427, false)]
theorem step5746 (p : Nat → Bool) (h : Constraints p) : clause p c5746 = true :=
  Snake9.LocalRup.prove_clause [c5725, c933] c5746 (by decide) p (sat_cons (step5725 p h) (sat_cons (step933 p h) (sat_nil p)))
def c5747 : List Lit := [(419, false)]
theorem step5747 (p : Nat → Bool) (h : Constraints p) : clause p c5747 = true :=
  Snake9.LocalRup.prove_clause [c5726, c929] c5747 (by decide) p (sat_cons (step5726 p h) (sat_cons (step929 p h) (sat_nil p)))
def c5748 : List Lit := [(207, false)]
theorem step5748 (p : Nat → Bool) (h : Constraints p) : clause p c5748 = true :=
  Snake9.LocalRup.prove_clause [c5727, c916] c5748 (by decide) p (sat_cons (step5727 p h) (sat_cons (step916 p h) (sat_nil p)))
def c5749 : List Lit := [(1461, false)]
theorem step5749 (p : Nat → Bool) (h : Constraints p) : clause p c5749 = true :=
  Snake9.LocalRup.prove_clause [c5728, c5246, c1089] c5749 (by decide) p (sat_cons (step5728 p h) (sat_cons (step5246 p h) (sat_cons (step1089 p h) (sat_nil p))))
def c5750 : List Lit := [(1460, false)]
theorem step5750 (p : Nat → Bool) (h : Constraints p) : clause p c5750 = true :=
  Snake9.LocalRup.prove_clause [c5730, c5246, c1084] c5750 (by decide) p (sat_cons (step5730 p h) (sat_cons (step5246 p h) (sat_cons (step1084 p h) (sat_nil p))))
def c5751 : List Lit := [(391, false)]
theorem step5751 (p : Nat → Bool) (h : Constraints p) : clause p c5751 = true :=
  Snake9.LocalRup.prove_clause [c5731, c897] c5751 (by decide) p (sat_cons (step5731 p h) (sat_cons (step897 p h) (sat_nil p)))
def c5752 : List Lit := [(377, false)]
theorem step5752 (p : Nat → Bool) (h : Constraints p) : clause p c5752 = true :=
  Snake9.LocalRup.prove_clause [c5732, c887] c5752 (by decide) p (sat_cons (step5732 p h) (sat_cons (step887 p h) (sat_nil p)))
def c5753 : List Lit := [(369, false)]
theorem step5753 (p : Nat → Bool) (h : Constraints p) : clause p c5753 = true :=
  Snake9.LocalRup.prove_clause [c5733, c872] c5753 (by decide) p (sat_cons (step5733 p h) (sat_cons (step872 p h) (sat_nil p)))
def c5754 : List Lit := [(367, false)]
theorem step5754 (p : Nat → Bool) (h : Constraints p) : clause p c5754 = true :=
  Snake9.LocalRup.prove_clause [c5733, c873] c5754 (by decide) p (sat_cons (step5733 p h) (sat_cons (step873 p h) (sat_nil p)))
def c5755 : List Lit := [(185, false)]
theorem step5755 (p : Nat → Bool) (h : Constraints p) : clause p c5755 = true :=
  Snake9.LocalRup.prove_clause [c5734, c869] c5755 (by decide) p (sat_cons (step5734 p h) (sat_cons (step869 p h) (sat_nil p)))
def c5756 : List Lit := [(357, false)]
theorem step5756 (p : Nat → Bool) (h : Constraints p) : clause p c5756 = true :=
  Snake9.LocalRup.prove_clause [c5735, c863] c5756 (by decide) p (sat_cons (step5735 p h) (sat_cons (step863 p h) (sat_nil p)))
def c5757 : List Lit := [(355, false)]
theorem step5757 (p : Nat → Bool) (h : Constraints p) : clause p c5757 = true :=
  Snake9.LocalRup.prove_clause [c5735, c864] c5757 (by decide) p (sat_cons (step5735 p h) (sat_cons (step864 p h) (sat_nil p)))
def c5758 : List Lit := [(351, false)]
theorem step5758 (p : Nat → Bool) (h : Constraints p) : clause p c5758 = true :=
  Snake9.LocalRup.prove_clause [c5736, c860] c5758 (by decide) p (sat_cons (step5736 p h) (sat_cons (step860 p h) (sat_nil p)))
def c5759 : List Lit := [(235, false)]
theorem step5759 (p : Nat → Bool) (h : Constraints p) : clause p c5759 = true :=
  Snake9.LocalRup.prove_clause [c5743, c963] c5759 (by decide) p (sat_cons (step5743 p h) (sat_cons (step963 p h) (sat_nil p)))
def c5760 : List Lit := [(228, false)]
theorem step5760 (p : Nat → Bool) (h : Constraints p) : clause p c5760 = true :=
  Snake9.LocalRup.prove_clause [c5744, c950] c5760 (by decide) p (sat_cons (step5744 p h) (sat_cons (step950 p h) (sat_nil p)))
def c5761 : List Lit := [(223, false)]
theorem step5761 (p : Nat → Bool) (h : Constraints p) : clause p c5761 = true :=
  Snake9.LocalRup.prove_clause [c5745, c946] c5761 (by decide) p (sat_cons (step5745 p h) (sat_cons (step946 p h) (sat_nil p)))
def c5762 : List Lit := [(221, false)]
theorem step5762 (p : Nat → Bool) (h : Constraints p) : clause p c5762 = true :=
  Snake9.LocalRup.prove_clause [c5746, c932] c5762 (by decide) p (sat_cons (step5746 p h) (sat_cons (step932 p h) (sat_nil p)))
def c5763 : List Lit := [(215, false)]
theorem step5763 (p : Nat → Bool) (h : Constraints p) : clause p c5763 = true :=
  Snake9.LocalRup.prove_clause [c5747, c926] c5763 (by decide) p (sat_cons (step5747 p h) (sat_cons (step926 p h) (sat_nil p)))
def c5764 : List Lit := [(1449, false)]
theorem step5764 (p : Nat → Bool) (h : Constraints p) : clause p c5764 = true :=
  Snake9.LocalRup.prove_clause [c5750, c1025] c5764 (by decide) p (sat_cons (step5750 p h) (sat_cons (step1025 p h) (sat_nil p)))
def c5765 : List Lit := [(202, false)]
theorem step5765 (p : Nat → Bool) (h : Constraints p) : clause p c5765 = true :=
  Snake9.LocalRup.prove_clause [c5751, c896] c5765 (by decide) p (sat_cons (step5751 p h) (sat_cons (step896 p h) (sat_nil p)))
def c5766 : List Lit := [(194, false)]
theorem step5766 (p : Nat → Bool) (h : Constraints p) : clause p c5766 = true :=
  Snake9.LocalRup.prove_clause [c5752, c884] c5766 (by decide) p (sat_cons (step5752 p h) (sat_cons (step884 p h) (sat_nil p)))
end B112E047
