import B112E057Part0138
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c10921 : List Lit := [(1064, false)]
theorem step10921 (p : Nat → Bool) (h : Constraints p) : clause p c10921 = true :=
  Snake9.LocalRup.prove_clause [c10920, c6643] c10921 (by decide) p (sat_cons (step10920 p h) (sat_cons (step6643 p h) (sat_nil p)))
def c10922 : List Lit := [(88, true)]
theorem step10922 (p : Nat → Bool) (h : Constraints p) : clause p c10922 = true :=
  Snake9.LocalRup.prove_clause [c10882, c10884, c10879, c10753, c10751, c10885, c10914, c10883, c3003, c3437, c1713, c1582, c1772, c1591, c5309, c1622, c6642, c6646, c1623, c5315, c1604, c1773, c1595, c1751, c5688, c1744, c1738, c1739, c1742, c1743, c1754, c1740, c1732, c8067, c1726] c10922 (by decide) p (sat_cons (step10882 p h) (sat_cons (step10884 p h) (sat_cons (step10879 p h) (sat_cons (step10753 p h) (sat_cons (step10751 p h) (sat_cons (step10885 p h) (sat_cons (step10914 p h) (sat_cons (step10883 p h) (sat_cons (step3003 p h) (sat_cons (step3437 p h) (sat_cons (step1713 p h) (sat_cons (step1582 p h) (sat_cons (step1772 p h) (sat_cons (step1591 p h) (sat_cons (step5309 p h) (sat_cons (step1622 p h) (sat_cons (step6642 p h) (sat_cons (step6646 p h) (sat_cons (step1623 p h) (sat_cons (step5315 p h) (sat_cons (step1604 p h) (sat_cons (step1773 p h) (sat_cons (step1595 p h) (sat_cons (step1751 p h) (sat_cons (step5688 p h) (sat_cons (step1744 p h) (sat_cons (step1738 p h) (sat_cons (step1739 p h) (sat_cons (step1742 p h) (sat_cons (step1743 p h) (sat_cons (step1754 p h) (sat_cons (step1740 p h) (sat_cons (step1732 p h) (sat_cons (step8067 p h) (sat_cons (step1726 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c10923 : List Lit := [(1027, true)]
theorem step10923 (p : Nat → Bool) (h : Constraints p) : clause p c10923 = true :=
  Snake9.LocalRup.prove_clause [c10917, c10885, c10922, c10879, c10751, c10914, c10884, c1550, c4788, c9406, c10727, c1591, c1689, c1595, c1697, c1604, c1713, c1623, c1772, c6642, c5309] c10923 (by decide) p (sat_cons (step10917 p h) (sat_cons (step10885 p h) (sat_cons (step10922 p h) (sat_cons (step10879 p h) (sat_cons (step10751 p h) (sat_cons (step10914 p h) (sat_cons (step10884 p h) (sat_cons (step1550 p h) (sat_cons (step4788 p h) (sat_cons (step9406 p h) (sat_cons (step10727 p h) (sat_cons (step1591 p h) (sat_cons (step1689 p h) (sat_cons (step1595 p h) (sat_cons (step1697 p h) (sat_cons (step1604 p h) (sat_cons (step1713 p h) (sat_cons (step1623 p h) (sat_cons (step1772 p h) (sat_cons (step6642 p h) (sat_cons (step5309 p h) (sat_nil p))))))))))))))))))))))
def c10924 : List Lit := [(1031, true)]
theorem step10924 (p : Nat → Bool) (h : Constraints p) : clause p c10924 = true :=
  Snake9.LocalRup.prove_clause [c10923, c1558] c10924 (by decide) p (sat_cons (step10923 p h) (sat_cons (step1558 p h) (sat_nil p)))
def c10925 : List Lit := [(1056, false), (1049, false), (1039, true)]
theorem step10925 (p : Nat → Bool) (h : Constraints p) : clause p c10925 = true :=
  Snake9.LocalRup.prove_clause [c10682, c10921, c10879, c10915, c10923, c10884, c10922, c10882, c10911, c10885, c10914, c9951, c1628, c1623, c1592, c6642, c5358, c5309, c1697, c1772, c1689, c1716, c6262, c6614, c6058, c1571, c1543, c2081] c10925 (by decide) p (sat_cons (step10682 p h) (sat_cons (step10921 p h) (sat_cons (step10879 p h) (sat_cons (step10915 p h) (sat_cons (step10923 p h) (sat_cons (step10884 p h) (sat_cons (step10922 p h) (sat_cons (step10882 p h) (sat_cons (step10911 p h) (sat_cons (step10885 p h) (sat_cons (step10914 p h) (sat_cons (step9951 p h) (sat_cons (step1628 p h) (sat_cons (step1623 p h) (sat_cons (step1592 p h) (sat_cons (step6642 p h) (sat_cons (step5358 p h) (sat_cons (step5309 p h) (sat_cons (step1697 p h) (sat_cons (step1772 p h) (sat_cons (step1689 p h) (sat_cons (step1716 p h) (sat_cons (step6262 p h) (sat_cons (step6614 p h) (sat_cons (step6058 p h) (sat_cons (step1571 p h) (sat_cons (step1543 p h) (sat_cons (step2081 p h) (sat_nil p)))))))))))))))))))))))))))))
def c10926 : List Lit := [(72, false), (90, false), (70, true)]
theorem step10926 (p : Nat → Bool) (h : Constraints p) : clause p c10926 = true :=
  Snake9.LocalRup.prove_clause [c10879, c10914, c10922, c10753, c10882, c10884, c10915, c10923, c10911, c6397, c2831, c1627, c5358] c10926 (by decide) p (sat_cons (step10879 p h) (sat_cons (step10914 p h) (sat_cons (step10922 p h) (sat_cons (step10753 p h) (sat_cons (step10882 p h) (sat_cons (step10884 p h) (sat_cons (step10915 p h) (sat_cons (step10923 p h) (sat_cons (step10911 p h) (sat_cons (step6397 p h) (sat_cons (step2831 p h) (sat_cons (step1627 p h) (sat_cons (step5358 p h) (sat_nil p))))))))))))))
def c10927 : List Lit := [(1049, false), (1039, true), (73, false)]
theorem step10927 (p : Nat → Bool) (h : Constraints p) : clause p c10927 = true :=
  Snake9.LocalRup.prove_clause [c10682, c10924, c10753, c10884, c10751, c10923, c10882, c10911, c10922, c1575, c2082, c9951, c1622, c6646, c5315, c1777, c10925, c1604, c1595, c10926, c1543, c1545, c2081, c1571, c1559, c1554, c2915, c549, c1716, c1717, c1773, c1697, c6363, c4637] c10927 (by decide) p (sat_cons (step10682 p h) (sat_cons (step10924 p h) (sat_cons (step10753 p h) (sat_cons (step10884 p h) (sat_cons (step10751 p h) (sat_cons (step10923 p h) (sat_cons (step10882 p h) (sat_cons (step10911 p h) (sat_cons (step10922 p h) (sat_cons (step1575 p h) (sat_cons (step2082 p h) (sat_cons (step9951 p h) (sat_cons (step1622 p h) (sat_cons (step6646 p h) (sat_cons (step5315 p h) (sat_cons (step1777 p h) (sat_cons (step10925 p h) (sat_cons (step1604 p h) (sat_cons (step1595 p h) (sat_cons (step10926 p h) (sat_cons (step1543 p h) (sat_cons (step1545 p h) (sat_cons (step2081 p h) (sat_cons (step1571 p h) (sat_cons (step1559 p h) (sat_cons (step1554 p h) (sat_cons (step2915 p h) (sat_cons (step549 p h) (sat_cons (step1716 p h) (sat_cons (step1717 p h) (sat_cons (step1773 p h) (sat_cons (step1697 p h) (sat_cons (step6363 p h) (sat_cons (step4637 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c10928 : List Lit := [(1039, true), (73, false)]
theorem step10928 (p : Nat → Bool) (h : Constraints p) : clause p c10928 = true :=
  Snake9.LocalRup.prove_clause [c10924, c10879, c10884, c10922, c10918, c10880, c10882, c1575, c2082, c10927, c1591, c1582, c1583, c5052, c4928, c1543, c1545, c2081, c4740, c1571] c10928 (by decide) p (sat_cons (step10924 p h) (sat_cons (step10879 p h) (sat_cons (step10884 p h) (sat_cons (step10922 p h) (sat_cons (step10918 p h) (sat_cons (step10880 p h) (sat_cons (step10882 p h) (sat_cons (step1575 p h) (sat_cons (step2082 p h) (sat_cons (step10927 p h) (sat_cons (step1591 p h) (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step5052 p h) (sat_cons (step4928 p h) (sat_cons (step1543 p h) (sat_cons (step1545 p h) (sat_cons (step2081 p h) (sat_cons (step4740 p h) (sat_cons (step1571 p h) (sat_nil p)))))))))))))))))))))
def c10929 : List Lit := [(1045, false), (1039, false)]
theorem step10929 (p : Nat → Bool) (h : Constraints p) : clause p c10929 = true :=
  Snake9.LocalRup.prove_clause [c10920, c10753, c10881, c10884, c10914, c10879, c10917, c10918, c10885, c10751, c10922, c1651, c5315, c1777, c1714, c1653, c1627, c1592, c1591, c8597, c1623, c1751, c1604, c1744, c1595, c6725] c10929 (by decide) p (sat_cons (step10920 p h) (sat_cons (step10753 p h) (sat_cons (step10881 p h) (sat_cons (step10884 p h) (sat_cons (step10914 p h) (sat_cons (step10879 p h) (sat_cons (step10917 p h) (sat_cons (step10918 p h) (sat_cons (step10885 p h) (sat_cons (step10751 p h) (sat_cons (step10922 p h) (sat_cons (step1651 p h) (sat_cons (step5315 p h) (sat_cons (step1777 p h) (sat_cons (step1714 p h) (sat_cons (step1653 p h) (sat_cons (step1627 p h) (sat_cons (step1592 p h) (sat_cons (step1591 p h) (sat_cons (step8597 p h) (sat_cons (step1623 p h) (sat_cons (step1751 p h) (sat_cons (step1604 p h) (sat_cons (step1744 p h) (sat_cons (step1595 p h) (sat_cons (step6725 p h) (sat_nil p)))))))))))))))))))))))))))
def c10930 : List Lit := [(1039, false)]
theorem step10930 (p : Nat → Bool) (h : Constraints p) : clause p c10930 = true :=
  Snake9.LocalRup.prove_clause [c10922, c10914, c10751, c10884, c10880, c10929, c2167, c6145, c1713, c1595, c1772, c1604, c5309, c1618, c1652] c10930 (by decide) p (sat_cons (step10922 p h) (sat_cons (step10914 p h) (sat_cons (step10751 p h) (sat_cons (step10884 p h) (sat_cons (step10880 p h) (sat_cons (step10929 p h) (sat_cons (step2167 p h) (sat_cons (step6145 p h) (sat_cons (step1713 p h) (sat_cons (step1595 p h) (sat_cons (step1772 p h) (sat_cons (step1604 p h) (sat_cons (step5309 p h) (sat_cons (step1618 p h) (sat_cons (step1652 p h) (sat_nil p))))))))))))))))
def c10931 : List Lit := [(1033, false)]
theorem step10931 (p : Nat → Bool) (h : Constraints p) : clause p c10931 = true :=
  Snake9.LocalRup.prove_clause [c10930, c2086] c10931 (by decide) p (sat_cons (step10930 p h) (sat_cons (step2086 p h) (sat_nil p)))
def c10932 : List Lit := [(70, false)]
theorem step10932 (p : Nat → Bool) (h : Constraints p) : clause p c10932 = true :=
  Snake9.LocalRup.prove_clause [c10930, c10923, c10682, c9951] c10932 (by decide) p (sat_cons (step10930 p h) (sat_cons (step10923 p h) (sat_cons (step10682 p h) (sat_cons (step9951 p h) (sat_nil p)))))
def c10933 : List Lit := [(73, false)]
theorem step10933 (p : Nat → Bool) (h : Constraints p) : clause p c10933 = true :=
  Snake9.LocalRup.prove_clause [c10930, c10928] c10933 (by decide) p (sat_cons (step10930 p h) (sat_cons (step10928 p h) (sat_nil p)))
def c10934 : List Lit := [(90, false)]
theorem step10934 (p : Nat → Bool) (h : Constraints p) : clause p c10934 = true :=
  Snake9.LocalRup.prove_clause [c10885, c10879, c10884, c10922, c10914, c10932, c10933, c10930, c10727, c10926, c1552, c1543, c1561, c2081, c1571] c10934 (by decide) p (sat_cons (step10885 p h) (sat_cons (step10879 p h) (sat_cons (step10884 p h) (sat_cons (step10922 p h) (sat_cons (step10914 p h) (sat_cons (step10932 p h) (sat_cons (step10933 p h) (sat_cons (step10930 p h) (sat_cons (step10727 p h) (sat_cons (step10926 p h) (sat_cons (step1552 p h) (sat_cons (step1543 p h) (sat_cons (step1561 p h) (sat_cons (step2081 p h) (sat_cons (step1571 p h) (sat_nil p))))))))))))))))
def c10935 : List Lit := [(1052, true)]
theorem step10935 (p : Nat → Bool) (h : Constraints p) : clause p c10935 = true :=
  Snake9.LocalRup.prove_clause [c10934, c10751, c1595] c10935 (by decide) p (sat_cons (step10934 p h) (sat_cons (step10751 p h) (sat_cons (step1595 p h) (sat_nil p))))
def c10936 : List Lit := [(1056, true)]
theorem step10936 (p : Nat → Bool) (h : Constraints p) : clause p c10936 = true :=
  Snake9.LocalRup.prove_clause [c10935, c1604] c10936 (by decide) p (sat_cons (step10935 p h) (sat_cons (step1604 p h) (sat_nil p)))
def c10937 : List Lit := [(1062, true)]
theorem step10937 (p : Nat → Bool) (h : Constraints p) : clause p c10937 = true :=
  Snake9.LocalRup.prove_clause [c10936, c10880, c1618] c10937 (by decide) p (sat_cons (step10936 p h) (sat_cons (step10880 p h) (sat_cons (step1618 p h) (sat_nil p))))
def c10938 : List Lit := [(1049, false)]
theorem step10938 (p : Nat → Bool) (h : Constraints p) : clause p c10938 = true :=
  Snake9.LocalRup.prove_clause [c10936, c10930, c10925] c10938 (by decide) p (sat_cons (step10936 p h) (sat_cons (step10930 p h) (sat_cons (step10925 p h) (sat_nil p))))
def c10939 : List Lit := [(1074, true)]
theorem step10939 (p : Nat → Bool) (h : Constraints p) : clause p c10939 = true :=
  Snake9.LocalRup.prove_clause [c10937, c6646] c10939 (by decide) p (sat_cons (step10937 p h) (sat_cons (step6646 p h) (sat_nil p)))
def c10940 : List Lit := [(1045, false)]
theorem step10940 (p : Nat → Bool) (h : Constraints p) : clause p c10940 = true :=
  Snake9.LocalRup.prove_clause [c10938, c10879, c1591] c10940 (by decide) p (sat_cons (step10938 p h) (sat_cons (step10879 p h) (sat_cons (step1591 p h) (sat_nil p))))
def c10941 : List Lit := [(1136, false)]
theorem step10941 (p : Nat → Bool) (h : Constraints p) : clause p c10941 = true :=
  Snake9.LocalRup.prove_clause [c10939, c5315] c10941 (by decide) p (sat_cons (step10939 p h) (sat_cons (step5315 p h) (sat_nil p)))
def c10942 : List Lit := [(1095, true)]
theorem step10942 (p : Nat → Bool) (h : Constraints p) : clause p c10942 = true :=
  Snake9.LocalRup.prove_clause [c10940, c2167] c10942 (by decide) p (sat_cons (step10940 p h) (sat_cons (step2167 p h) (sat_nil p)))
def c10943 : List Lit := [(75, false)]
theorem step10943 (p : Nat → Bool) (h : Constraints p) : clause p c10943 = true :=
  Snake9.LocalRup.prove_clause [c10940, c10922, c5052] c10943 (by decide) p (sat_cons (step10940 p h) (sat_cons (step10922 p h) (sat_cons (step5052 p h) (sat_nil p))))
def c10944 : List Lit := [(1102, false)]
theorem step10944 (p : Nat → Bool) (h : Constraints p) : clause p c10944 = true :=
  Snake9.LocalRup.prove_clause [c10941, c10884, c1777] c10944 (by decide) p (sat_cons (step10941 p h) (sat_cons (step10884 p h) (sat_cons (step1777 p h) (sat_nil p))))
def c10945 : List Lit := [(1089, false)]
theorem step10945 (p : Nat → Bool) (h : Constraints p) : clause p c10945 = true :=
  Snake9.LocalRup.prove_clause [c10942, c10944, c1717] c10945 (by decide) p (sat_cons (step10942 p h) (sat_cons (step10944 p h) (sat_cons (step1717 p h) (sat_nil p))))
def c10946 : List Lit := [(1028, true)]
theorem step10946 (p : Nat → Bool) (h : Constraints p) : clause p c10946 = true :=
  Snake9.LocalRup.prove_clause [c10943, c10933, c1552] c10946 (by decide) p (sat_cons (step10943 p h) (sat_cons (step10933 p h) (sat_cons (step1552 p h) (sat_nil p))))
def c10947 : List Lit := [(77, false)]
theorem step10947 (p : Nat → Bool) (h : Constraints p) : clause p c10947 = true :=
  Snake9.LocalRup.prove_clause [c10945, c10911, c10932, c10882, c2915] c10947 (by decide) p (sat_cons (step10945 p h) (sat_cons (step10911 p h) (sat_cons (step10932 p h) (sat_cons (step10882 p h) (sat_cons (step2915 p h) (sat_nil p))))))
def c10948 : List Lit := [(1029, false)]
theorem step10948 (p : Nat → Bool) (h : Constraints p) : clause p c10948 = true :=
  Snake9.LocalRup.prove_clause [c10946, c10931, c1562] c10948 (by decide) p (sat_cons (step10946 p h) (sat_cons (step10931 p h) (sat_cons (step1562 p h) (sat_nil p))))
def c10949 : List Lit := []
theorem step10949 (p : Nat → Bool) (h : Constraints p) : clause p c10949 = true :=
  Snake9.LocalRup.prove_clause [c10947, c10948, c1554] c10949 (by decide) p (sat_cons (step10947 p h) (sat_cons (step10948 p h) (sat_cons (step1554 p h) (sat_nil p))))
end B112E057
