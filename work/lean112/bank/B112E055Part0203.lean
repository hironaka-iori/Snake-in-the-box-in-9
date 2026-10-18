import B112E055Part0202
namespace B112E055
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c14934 : List Lit := [(75, false), (121, false), (123, true), (1789, true), (1619, false)]
theorem step14934 (p : Nat → Bool) (h : Constraints p) : clause p c14934 = true :=
  Snake9.LocalRup.prove_clause [c14907, c14573, c13776, c14799, c1758, c14931, c1277, c14465, c1816, c14933, c1705, c1737, c1738, c1811, c1715, c4887, c2449] c14934 (by decide) p (sat_cons (step14907 p h) (sat_cons (step14573 p h) (sat_cons (step13776 p h) (sat_cons (step14799 p h) (sat_cons (step1758 p h) (sat_cons (step14931 p h) (sat_cons (step1277 p h) (sat_cons (step14465 p h) (sat_cons (step1816 p h) (sat_cons (step14933 p h) (sat_cons (step1705 p h) (sat_cons (step1737 p h) (sat_cons (step1738 p h) (sat_cons (step1811 p h) (sat_cons (step1715 p h) (sat_cons (step4887 p h) (sat_cons (step2449 p h) (sat_nil p))))))))))))))))))
def c14935 : List Lit := [(1753, true), (1782, true), (1789, true)]
theorem step14935 (p : Nat → Bool) (h : Constraints p) : clause p c14935 = true :=
  Snake9.LocalRup.prove_clause [c12322, c1614, c3459, c1611, c6360] c14935 (by decide) p (sat_cons (step12322 p h) (sat_cons (step1614 p h) (sat_cons (step3459 p h) (sat_cons (step1611 p h) (sat_cons (step6360 p h) (sat_nil p))))))
def c14936 : List Lit := [(121, false), (123, true), (1789, true), (1619, false)]
theorem step14936 (p : Nat → Bool) (h : Constraints p) : clause p c14936 = true :=
  Snake9.LocalRup.prove_clause [c14573, c13777, c14907, c1758, c9228, c1708, c14935, c14930, c14934, c14835] c14936 (by decide) p (sat_cons (step14573 p h) (sat_cons (step13777 p h) (sat_cons (step14907 p h) (sat_cons (step1758 p h) (sat_cons (step9228 p h) (sat_cons (step1708 p h) (sat_cons (step14935 p h) (sat_cons (step14930 p h) (sat_cons (step14934 p h) (sat_cons (step14835 p h) (sat_nil p)))))))))))
def c14937 : List Lit := [(75, true), (123, true), (1789, true), (1619, false)]
theorem step14937 (p : Nat → Bool) (h : Constraints p) : clause p c14937 = true :=
  Snake9.LocalRup.prove_clause [c13777, c14573, c14907, c14756, c13776, c14829, c12322, c14502, c14936, c1760, c3853, c1705, c1696, c1695, c1758, c9228, c1708, c14935, c14930, c2765, c4845, c2319, c1856, c14841, c5948, c1563, c6143, c1633, c1637, c6024, c4388, c2290, c14840] c14937 (by decide) p (sat_cons (step13777 p h) (sat_cons (step14573 p h) (sat_cons (step14907 p h) (sat_cons (step14756 p h) (sat_cons (step13776 p h) (sat_cons (step14829 p h) (sat_cons (step12322 p h) (sat_cons (step14502 p h) (sat_cons (step14936 p h) (sat_cons (step1760 p h) (sat_cons (step3853 p h) (sat_cons (step1705 p h) (sat_cons (step1696 p h) (sat_cons (step1695 p h) (sat_cons (step1758 p h) (sat_cons (step9228 p h) (sat_cons (step1708 p h) (sat_cons (step14935 p h) (sat_cons (step14930 p h) (sat_cons (step2765 p h) (sat_cons (step4845 p h) (sat_cons (step2319 p h) (sat_cons (step1856 p h) (sat_cons (step14841 p h) (sat_cons (step5948 p h) (sat_cons (step1563 p h) (sat_cons (step6143 p h) (sat_cons (step1633 p h) (sat_cons (step1637 p h) (sat_cons (step6024 p h) (sat_cons (step4388 p h) (sat_cons (step2290 p h) (sat_cons (step14840 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c14938 : List Lit := [(77, false), (75, false), (1781, true), (123, true), (1789, true), (86, true)]
theorem step14938 (p : Nat → Bool) (h : Constraints p) : clause p c14938 = true :=
  Snake9.LocalRup.prove_clause [c12322, c13776, c1696, c2795, c486, c1212, c5009, c1215, c14897, c1224, c1284, c1247] c14938 (by decide) p (sat_cons (step12322 p h) (sat_cons (step13776 p h) (sat_cons (step1696 p h) (sat_cons (step2795 p h) (sat_cons (step486 p h) (sat_cons (step1212 p h) (sat_cons (step5009 p h) (sat_cons (step1215 p h) (sat_cons (step14897 p h) (sat_cons (step1224 p h) (sat_cons (step1284 p h) (sat_cons (step1247 p h) (sat_nil p)))))))))))))
def c14939 : List Lit := [(123, true), (1789, true), (1619, false)]
theorem step14939 (p : Nat → Bool) (h : Constraints p) : clause p c14939 = true :=
  Snake9.LocalRup.prove_clause [c13777, c14573, c14907, c12322, c14930, c1758, c9228, c1708, c14935, c14936, c1760, c3853, c1705, c1695, c1696, c6360, c2477, c1611, c14937, c14938, c14903, c14846, c1615, c1617, c1145, c1613, c1608, c2290, c726, c4011] c14939 (by decide) p (sat_cons (step13777 p h) (sat_cons (step14573 p h) (sat_cons (step14907 p h) (sat_cons (step12322 p h) (sat_cons (step14930 p h) (sat_cons (step1758 p h) (sat_cons (step9228 p h) (sat_cons (step1708 p h) (sat_cons (step14935 p h) (sat_cons (step14936 p h) (sat_cons (step1760 p h) (sat_cons (step3853 p h) (sat_cons (step1705 p h) (sat_cons (step1695 p h) (sat_cons (step1696 p h) (sat_cons (step6360 p h) (sat_cons (step2477 p h) (sat_cons (step1611 p h) (sat_cons (step14937 p h) (sat_cons (step14938 p h) (sat_cons (step14903 p h) (sat_cons (step14846 p h) (sat_cons (step1615 p h) (sat_cons (step1617 p h) (sat_cons (step1145 p h) (sat_cons (step1613 p h) (sat_cons (step1608 p h) (sat_cons (step2290 p h) (sat_cons (step726 p h) (sat_cons (step4011 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c14940 : List Lit := [(77, true), (1753, false), (87, true), (75, false), (1619, false)]
theorem step14940 (p : Nat → Bool) (h : Constraints p) : clause p c14940 = true :=
  Snake9.LocalRup.prove_clause [c14573, c13776, c14907, c14930, c14903, c14846, c14932, c1145, c7151, c2290] c14940 (by decide) p (sat_cons (step14573 p h) (sat_cons (step13776 p h) (sat_cons (step14907 p h) (sat_cons (step14930 p h) (sat_cons (step14903 p h) (sat_cons (step14846 p h) (sat_cons (step14932 p h) (sat_cons (step1145 p h) (sat_cons (step7151 p h) (sat_cons (step2290 p h) (sat_nil p)))))))))))
def c14941 : List Lit := [(99, false), (75, false), (1789, true), (1619, false)]
theorem step14941 (p : Nat → Bool) (h : Constraints p) : clause p c14941 = true :=
  Snake9.LocalRup.prove_clause [c13776, c12322, c14906, c14756, c14939, c637, c14930, c6360, c757, c1611, c13892, c14940, c2795, c1212, c1215, c1224, c1247, c1284, c2288, c2289, c14897, c1277, c1207, c1617, c14911, c1202, c1608, c1199, c8544] c14941 (by decide) p (sat_cons (step13776 p h) (sat_cons (step12322 p h) (sat_cons (step14906 p h) (sat_cons (step14756 p h) (sat_cons (step14939 p h) (sat_cons (step637 p h) (sat_cons (step14930 p h) (sat_cons (step6360 p h) (sat_cons (step757 p h) (sat_cons (step1611 p h) (sat_cons (step13892 p h) (sat_cons (step14940 p h) (sat_cons (step2795 p h) (sat_cons (step1212 p h) (sat_cons (step1215 p h) (sat_cons (step1224 p h) (sat_cons (step1247 p h) (sat_cons (step1284 p h) (sat_cons (step2288 p h) (sat_cons (step2289 p h) (sat_cons (step14897 p h) (sat_cons (step1277 p h) (sat_cons (step1207 p h) (sat_cons (step1617 p h) (sat_cons (step14911 p h) (sat_cons (step1202 p h) (sat_cons (step1608 p h) (sat_cons (step1199 p h) (sat_cons (step8544 p h) (sat_nil p))))))))))))))))))))))))))))))
def c14942 : List Lit := [(75, false), (1789, true), (1619, false)]
theorem step14942 (p : Nat → Bool) (h : Constraints p) : clause p c14942 = true :=
  Snake9.LocalRup.prove_clause [c13776, c13777, c14573, c14907, c14906, c14939, c14930, c637, c14941, c2211, c1696, c1705, c14911, c1277, c1282, c14931, c2289, c1759, c1207, c9228, c1202, c1708, c1199, c14935, c14189, c14940, c14897] c14942 (by decide) p (sat_cons (step13776 p h) (sat_cons (step13777 p h) (sat_cons (step14573 p h) (sat_cons (step14907 p h) (sat_cons (step14906 p h) (sat_cons (step14939 p h) (sat_cons (step14930 p h) (sat_cons (step637 p h) (sat_cons (step14941 p h) (sat_cons (step2211 p h) (sat_cons (step1696 p h) (sat_cons (step1705 p h) (sat_cons (step14911 p h) (sat_cons (step1277 p h) (sat_cons (step1282 p h) (sat_cons (step14931 p h) (sat_cons (step2289 p h) (sat_cons (step1759 p h) (sat_cons (step1207 p h) (sat_cons (step9228 p h) (sat_cons (step1202 p h) (sat_cons (step1708 p h) (sat_cons (step1199 p h) (sat_cons (step14935 p h) (sat_cons (step14189 p h) (sat_cons (step14940 p h) (sat_cons (step14897 p h) (sat_nil p))))))))))))))))))))))))))))
def c14943 : List Lit := [(1754, false), (75, true), (1619, false)]
theorem step14943 (p : Nat → Bool) (h : Constraints p) : clause p c14943 = true :=
  Snake9.LocalRup.prove_clause [c13776, c14829, c12322, c14502, c1561, c1569, c5853, c14930, c2765, c4845, c2319, c1856, c1633, c1638, c6143, c2829, c1563] c14943 (by decide) p (sat_cons (step13776 p h) (sat_cons (step14829 p h) (sat_cons (step12322 p h) (sat_cons (step14502 p h) (sat_cons (step1561 p h) (sat_cons (step1569 p h) (sat_cons (step5853 p h) (sat_cons (step14930 p h) (sat_cons (step2765 p h) (sat_cons (step4845 p h) (sat_cons (step2319 p h) (sat_cons (step1856 p h) (sat_cons (step1633 p h) (sat_cons (step1638 p h) (sat_cons (step6143 p h) (sat_cons (step2829 p h) (sat_cons (step1563 p h) (sat_nil p))))))))))))))))))
def c14944 : List Lit := [(505, true), (121, true), (77, false), (1754, true)]
theorem step14944 (p : Nat → Bool) (h : Constraints p) : clause p c14944 = true :=
  Snake9.LocalRup.prove_clause [c13777, c14907, c12322, c14756, c13776, c14573, c1759, c9228, c1708, c1287, c6024, c1284, c5693, c1247, c1212, c1224, c1215] c14944 (by decide) p (sat_cons (step13777 p h) (sat_cons (step14907 p h) (sat_cons (step12322 p h) (sat_cons (step14756 p h) (sat_cons (step13776 p h) (sat_cons (step14573 p h) (sat_cons (step1759 p h) (sat_cons (step9228 p h) (sat_cons (step1708 p h) (sat_cons (step1287 p h) (sat_cons (step6024 p h) (sat_cons (step1284 p h) (sat_cons (step5693 p h) (sat_cons (step1247 p h) (sat_cons (step1212 p h) (sat_cons (step1224 p h) (sat_cons (step1215 p h) (sat_nil p))))))))))))))))))
def c14945 : List Lit := [(77, false), (75, true), (1619, false)]
theorem step14945 (p : Nat → Bool) (h : Constraints p) : clause p c14945 = true :=
  Snake9.LocalRup.prove_clause [c13776, c14829, c12322, c14502, c14943, c1561, c1569, c5853, c14930, c4845, c2319, c1856, c4033, c14835, c1642, c14944, c2290, c14840, c4388, c1637, c6143, c1563, c552, c9092, c1599, c1607] c14945 (by decide) p (sat_cons (step13776 p h) (sat_cons (step14829 p h) (sat_cons (step12322 p h) (sat_cons (step14502 p h) (sat_cons (step14943 p h) (sat_cons (step1561 p h) (sat_cons (step1569 p h) (sat_cons (step5853 p h) (sat_cons (step14930 p h) (sat_cons (step4845 p h) (sat_cons (step2319 p h) (sat_cons (step1856 p h) (sat_cons (step4033 p h) (sat_cons (step14835 p h) (sat_cons (step1642 p h) (sat_cons (step14944 p h) (sat_cons (step2290 p h) (sat_cons (step14840 p h) (sat_cons (step4388 p h) (sat_cons (step1637 p h) (sat_cons (step6143 p h) (sat_cons (step1563 p h) (sat_cons (step552 p h) (sat_cons (step9092 p h) (sat_cons (step1599 p h) (sat_cons (step1607 p h) (sat_nil p)))))))))))))))))))))))))))
def c14946 : List Lit := [(1789, true), (1619, false)]
theorem step14946 (p : Nat → Bool) (h : Constraints p) : clause p c14946 = true :=
  Snake9.LocalRup.prove_clause [c14906, c12322, c14930, c14942, c14945, c14841, c1614, c5225, c7926, c1194, c1195, c2272] c14946 (by decide) p (sat_cons (step14906 p h) (sat_cons (step12322 p h) (sat_cons (step14930 p h) (sat_cons (step14942 p h) (sat_cons (step14945 p h) (sat_cons (step14841 p h) (sat_cons (step1614 p h) (sat_cons (step5225 p h) (sat_cons (step7926 p h) (sat_cons (step1194 p h) (sat_cons (step1195 p h) (sat_cons (step2272 p h) (sat_nil p)))))))))))))
def c14947 : List Lit := [(75, true), (1619, false)]
theorem step14947 (p : Nat → Bool) (h : Constraints p) : clause p c14947 = true :=
  Snake9.LocalRup.prove_clause [c14829, c12322, c14756, c14573, c13776, c14502, c14946, c14930, c4845, c2319, c1856, c14945, c14841, c8136, c14850, c1695, c1641, c5522, c4392, c3022, c1563, c1636, c14851] c14947 (by decide) p (sat_cons (step14829 p h) (sat_cons (step12322 p h) (sat_cons (step14756 p h) (sat_cons (step14573 p h) (sat_cons (step13776 p h) (sat_cons (step14502 p h) (sat_cons (step14946 p h) (sat_cons (step14930 p h) (sat_cons (step4845 p h) (sat_cons (step2319 p h) (sat_cons (step1856 p h) (sat_cons (step14945 p h) (sat_cons (step14841 p h) (sat_cons (step8136 p h) (sat_cons (step14850 p h) (sat_cons (step1695 p h) (sat_cons (step1641 p h) (sat_cons (step5522 p h) (sat_cons (step4392 p h) (sat_cons (step3022 p h) (sat_cons (step1563 p h) (sat_cons (step1636 p h) (sat_cons (step14851 p h) (sat_nil p))))))))))))))))))))))))
def c14948 : List Lit := [(1787, false), (1619, false)]
theorem step14948 (p : Nat → Bool) (h : Constraints p) : clause p c14948 = true :=
  Snake9.LocalRup.prove_clause [c14908, c14573, c13776, c14946, c14947, c5492, c3797, c10444, c1758, c637] c14948 (by decide) p (sat_cons (step14908 p h) (sat_cons (step14573 p h) (sat_cons (step13776 p h) (sat_cons (step14946 p h) (sat_cons (step14947 p h) (sat_cons (step5492 p h) (sat_cons (step3797 p h) (sat_cons (step10444 p h) (sat_cons (step1758 p h) (sat_cons (step637 p h) (sat_nil p)))))))))))
def c14949 : List Lit := [(1729, false), (1619, false)]
theorem step14949 (p : Nat → Bool) (h : Constraints p) : clause p c14949 = true :=
  Snake9.LocalRup.prove_clause [c14502, c14573, c14908, c13776, c14907, c14829, c14756, c12322, c14948, c1705, c1695, c8136, c14930, c14946, c14947, c5492, c14932, c14847, c3022, c1637, c5853, c8465, c1638, c14539, c6024, c1145, c2290] c14949 (by decide) p (sat_cons (step14502 p h) (sat_cons (step14573 p h) (sat_cons (step14908 p h) (sat_cons (step13776 p h) (sat_cons (step14907 p h) (sat_cons (step14829 p h) (sat_cons (step14756 p h) (sat_cons (step12322 p h) (sat_cons (step14948 p h) (sat_cons (step1705 p h) (sat_cons (step1695 p h) (sat_cons (step8136 p h) (sat_cons (step14930 p h) (sat_cons (step14946 p h) (sat_cons (step14947 p h) (sat_cons (step5492 p h) (sat_cons (step14932 p h) (sat_cons (step14847 p h) (sat_cons (step3022 p h) (sat_cons (step1637 p h) (sat_cons (step5853 p h) (sat_cons (step8465 p h) (sat_cons (step1638 p h) (sat_cons (step14539 p h) (sat_cons (step6024 p h) (sat_cons (step1145 p h) (sat_cons (step2290 p h) (sat_nil p))))))))))))))))))))))))))))
def c14950 : List Lit := [(1619, false)]
theorem step14950 (p : Nat → Bool) (h : Constraints p) : clause p c14950 = true :=
  Snake9.LocalRup.prove_clause [c14907, c12322, c13776, c14573, c14908, c14946, c14947, c5492, c14948, c1705, c1695, c8136, c14932, c14949, c1567, c2555, c1564, c1161, c1164, c2267, c1171, c1162, c1174, c13927, c1209, c637, c2289, c1758, c10754] c14950 (by decide) p (sat_cons (step14907 p h) (sat_cons (step12322 p h) (sat_cons (step13776 p h) (sat_cons (step14573 p h) (sat_cons (step14908 p h) (sat_cons (step14946 p h) (sat_cons (step14947 p h) (sat_cons (step5492 p h) (sat_cons (step14948 p h) (sat_cons (step1705 p h) (sat_cons (step1695 p h) (sat_cons (step8136 p h) (sat_cons (step14932 p h) (sat_cons (step14949 p h) (sat_cons (step1567 p h) (sat_cons (step2555 p h) (sat_cons (step1564 p h) (sat_cons (step1161 p h) (sat_cons (step1164 p h) (sat_cons (step2267 p h) (sat_cons (step1171 p h) (sat_cons (step1162 p h) (sat_cons (step1174 p h) (sat_cons (step13927 p h) (sat_cons (step1209 p h) (sat_cons (step637 p h) (sat_cons (step2289 p h) (sat_cons (step1758 p h) (sat_cons (step10754 p h) (sat_nil p))))))))))))))))))))))))))))))
def c14951 : List Lit := [(315, true)]
theorem step14951 (p : Nat → Bool) (h : Constraints p) : clause p c14951 = true :=
  Snake9.LocalRup.prove_clause [c14950, c11322] c14951 (by decide) p (sat_cons (step14950 p h) (sat_cons (step11322 p h) (sat_nil p)))
def c14952 : List Lit := [(14, true)]
theorem step14952 (p : Nat → Bool) (h : Constraints p) : clause p c14952 = true :=
  Snake9.LocalRup.prove_clause [c14950, c12068] c14952 (by decide) p (sat_cons (step14950 p h) (sat_cons (step12068 p h) (sat_nil p)))
def c14953 : List Lit := [(379, true)]
theorem step14953 (p : Nat → Bool) (h : Constraints p) : clause p c14953 = true :=
  Snake9.LocalRup.prove_clause [c14951, c1145] c14953 (by decide) p (sat_cons (step14951 p h) (sat_cons (step1145 p h) (sat_nil p)))
def c14954 : List Lit := [(1746, true)]
theorem step14954 (p : Nat → Bool) (h : Constraints p) : clause p c14954 = true :=
  Snake9.LocalRup.prove_clause [c14952, c14502, c2688] c14954 (by decide) p (sat_cons (step14952 p h) (sat_cons (step14502 p h) (sat_cons (step2688 p h) (sat_nil p))))
def c14955 : List Lit := [(505, false)]
theorem step14955 (p : Nat → Bool) (h : Constraints p) : clause p c14955 = true :=
  Snake9.LocalRup.prove_clause [c14953, c2290] c14955 (by decide) p (sat_cons (step14953 p h) (sat_cons (step2290 p h) (sat_nil p)))
def c14956 : List Lit := [(503, false)]
theorem step14956 (p : Nat → Bool) (h : Constraints p) : clause p c14956 = true :=
  Snake9.LocalRup.prove_clause [c14955, c1287] c14956 (by decide) p (sat_cons (step14955 p h) (sat_cons (step1287 p h) (sat_nil p)))
def c14957 : List Lit := [(441, false)]
theorem step14957 (p : Nat → Bool) (h : Constraints p) : clause p c14957 = true :=
  Snake9.LocalRup.prove_clause [c14955, c1289] c14957 (by decide) p (sat_cons (step14955 p h) (sat_cons (step1289 p h) (sat_nil p)))
def c14958 : List Lit := [(501, false)]
theorem step14958 (p : Nat → Bool) (h : Constraints p) : clause p c14958 = true :=
  Snake9.LocalRup.prove_clause [c14956, c1282] c14958 (by decide) p (sat_cons (step14956 p h) (sat_cons (step1282 p h) (sat_nil p)))
def c14959 : List Lit := [(471, false)]
theorem step14959 (p : Nat → Bool) (h : Constraints p) : clause p c14959 = true :=
  Snake9.LocalRup.prove_clause [c14956, c1284] c14959 (by decide) p (sat_cons (step14956 p h) (sat_cons (step1284 p h) (sat_nil p)))
def c14960 : List Lit := [(439, false)]
theorem step14960 (p : Nat → Bool) (h : Constraints p) : clause p c14960 = true :=
  Snake9.LocalRup.prove_clause [c14957, c1207] c14960 (by decide) p (sat_cons (step14957 p h) (sat_cons (step1207 p h) (sat_nil p)))
def c14961 : List Lit := [(409, false)]
theorem step14961 (p : Nat → Bool) (h : Constraints p) : clause p c14961 = true :=
  Snake9.LocalRup.prove_clause [c14957, c1209] c14961 (by decide) p (sat_cons (step14957 p h) (sat_cons (step1209 p h) (sat_nil p)))
def c14962 : List Lit := [(499, false)]
theorem step14962 (p : Nat → Bool) (h : Constraints p) : clause p c14962 = true :=
  Snake9.LocalRup.prove_clause [c14958, c1277] c14962 (by decide) p (sat_cons (step14958 p h) (sat_cons (step1277 p h) (sat_nil p)))
def c14963 : List Lit := [(469, false)]
theorem step14963 (p : Nat → Bool) (h : Constraints p) : clause p c14963 = true :=
  Snake9.LocalRup.prove_clause [c14959, c1245] c14963 (by decide) p (sat_cons (step14959 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c14964 : List Lit := [(455, false)]
theorem step14964 (p : Nat → Bool) (h : Constraints p) : clause p c14964 = true :=
  Snake9.LocalRup.prove_clause [c14959, c1247] c14964 (by decide) p (sat_cons (step14959 p h) (sat_cons (step1247 p h) (sat_nil p)))
def c14965 : List Lit := [(437, false)]
theorem step14965 (p : Nat → Bool) (h : Constraints p) : clause p c14965 = true :=
  Snake9.LocalRup.prove_clause [c14960, c1202] c14965 (by decide) p (sat_cons (step14960 p h) (sat_cons (step1202 p h) (sat_nil p)))
def c14966 : List Lit := [(407, false)]
theorem step14966 (p : Nat → Bool) (h : Constraints p) : clause p c14966 = true :=
  Snake9.LocalRup.prove_clause [c14961, c1174] c14966 (by decide) p (sat_cons (step14961 p h) (sat_cons (step1174 p h) (sat_nil p)))
def c14967 : List Lit := [(393, false)]
theorem step14967 (p : Nat → Bool) (h : Constraints p) : clause p c14967 = true :=
  Snake9.LocalRup.prove_clause [c14961, c1176] c14967 (by decide) p (sat_cons (step14961 p h) (sat_cons (step1176 p h) (sat_nil p)))
def c14968 : List Lit := [(497, false)]
theorem step14968 (p : Nat → Bool) (h : Constraints p) : clause p c14968 = true :=
  Snake9.LocalRup.prove_clause [c14962, c1272] c14968 (by decide) p (sat_cons (step14962 p h) (sat_cons (step1272 p h) (sat_nil p)))
def c14969 : List Lit := [(491, false)]
theorem step14969 (p : Nat → Bool) (h : Constraints p) : clause p c14969 = true :=
  Snake9.LocalRup.prove_clause [c14962, c1274] c14969 (by decide) p (sat_cons (step14962 p h) (sat_cons (step1274 p h) (sat_nil p)))
def c14970 : List Lit := [(467, false)]
theorem step14970 (p : Nat → Bool) (h : Constraints p) : clause p c14970 = true :=
  Snake9.LocalRup.prove_clause [c14963, c1240] c14970 (by decide) p (sat_cons (step14963 p h) (sat_cons (step1240 p h) (sat_nil p)))
def c14971 : List Lit := [(461, false)]
theorem step14971 (p : Nat → Bool) (h : Constraints p) : clause p c14971 = true :=
  Snake9.LocalRup.prove_clause [c14963, c1242] c14971 (by decide) p (sat_cons (step14963 p h) (sat_cons (step1242 p h) (sat_nil p)))
def c14972 : List Lit := [(447, false)]
theorem step14972 (p : Nat → Bool) (h : Constraints p) : clause p c14972 = true :=
  Snake9.LocalRup.prove_clause [c14964, c1224] c14972 (by decide) p (sat_cons (step14964 p h) (sat_cons (step1224 p h) (sat_nil p)))
def c14973 : List Lit := [(435, false)]
theorem step14973 (p : Nat → Bool) (h : Constraints p) : clause p c14973 = true :=
  Snake9.LocalRup.prove_clause [c14965, c1199] c14973 (by decide) p (sat_cons (step14965 p h) (sat_cons (step1199 p h) (sat_nil p)))
def c14974 : List Lit := [(399, false)]
theorem step14974 (p : Nat → Bool) (h : Constraints p) : clause p c14974 = true :=
  Snake9.LocalRup.prove_clause [c14966, c1171] c14974 (by decide) p (sat_cons (step14966 p h) (sat_cons (step1171 p h) (sat_nil p)))
def c14975 : List Lit := [(391, false)]
theorem step14975 (p : Nat → Bool) (h : Constraints p) : clause p c14975 = true :=
  Snake9.LocalRup.prove_clause [c14967, c1157] c14975 (by decide) p (sat_cons (step14967 p h) (sat_cons (step1157 p h) (sat_nil p)))
def c14976 : List Lit := [(493, false)]
theorem step14976 (p : Nat → Bool) (h : Constraints p) : clause p c14976 = true :=
  Snake9.LocalRup.prove_clause [c14968, c1270] c14976 (by decide) p (sat_cons (step14968 p h) (sat_cons (step1270 p h) (sat_nil p)))
def c14977 : List Lit := [(489, false)]
theorem step14977 (p : Nat → Bool) (h : Constraints p) : clause p c14977 = true :=
  Snake9.LocalRup.prove_clause [c14969, c1263] c14977 (by decide) p (sat_cons (step14969 p h) (sat_cons (step1263 p h) (sat_nil p)))
def c14978 : List Lit := [(487, false)]
theorem step14978 (p : Nat → Bool) (h : Constraints p) : clause p c14978 = true :=
  Snake9.LocalRup.prove_clause [c14969, c1264] c14978 (by decide) p (sat_cons (step14969 p h) (sat_cons (step1264 p h) (sat_nil p)))
def c14979 : List Lit := [(463, false)]
theorem step14979 (p : Nat → Bool) (h : Constraints p) : clause p c14979 = true :=
  Snake9.LocalRup.prove_clause [c14970, c1238] c14979 (by decide) p (sat_cons (step14970 p h) (sat_cons (step1238 p h) (sat_nil p)))
def c14980 : List Lit := [(459, false)]
theorem step14980 (p : Nat → Bool) (h : Constraints p) : clause p c14980 = true :=
  Snake9.LocalRup.prove_clause [c14971, c1229] c14980 (by decide) p (sat_cons (step14971 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c14981 : List Lit := [(445, false)]
theorem step14981 (p : Nat → Bool) (h : Constraints p) : clause p c14981 = true :=
  Snake9.LocalRup.prove_clause [c14972, c1215] c14981 (by decide) p (sat_cons (step14972 p h) (sat_cons (step1215 p h) (sat_nil p)))
def c14982 : List Lit := [(433, false)]
theorem step14982 (p : Nat → Bool) (h : Constraints p) : clause p c14982 = true :=
  Snake9.LocalRup.prove_clause [c14973, c1196] c14982 (by decide) p (sat_cons (step14973 p h) (sat_cons (step1196 p h) (sat_nil p)))
def c14983 : List Lit := [(431, false)]
theorem step14983 (p : Nat → Bool) (h : Constraints p) : clause p c14983 = true :=
  Snake9.LocalRup.prove_clause [c14973, c1197] c14983 (by decide) p (sat_cons (step14973 p h) (sat_cons (step1197 p h) (sat_nil p)))
def c14984 : List Lit := [(397, false)]
theorem step14984 (p : Nat → Bool) (h : Constraints p) : clause p c14984 = true :=
  Snake9.LocalRup.prove_clause [c14974, c1163] c14984 (by decide) p (sat_cons (step14974 p h) (sat_cons (step1163 p h) (sat_nil p)))
def c14985 : List Lit := [(395, false)]
theorem step14985 (p : Nat → Bool) (h : Constraints p) : clause p c14985 = true :=
  Snake9.LocalRup.prove_clause [c14974, c1164] c14985 (by decide) p (sat_cons (step14974 p h) (sat_cons (step1164 p h) (sat_nil p)))
def c14986 : List Lit := [(387, false)]
theorem step14986 (p : Nat → Bool) (h : Constraints p) : clause p c14986 = true :=
  Snake9.LocalRup.prove_clause [c14975, c1155] c14986 (by decide) p (sat_cons (step14975 p h) (sat_cons (step1155 p h) (sat_nil p)))
def c14987 : List Lit := [(253, false)]
theorem step14987 (p : Nat → Bool) (h : Constraints p) : clause p c14987 = true :=
  Snake9.LocalRup.prove_clause [c14976, c1267] c14987 (by decide) p (sat_cons (step14976 p h) (sat_cons (step1267 p h) (sat_nil p)))
def c14988 : List Lit := [(251, false)]
theorem step14988 (p : Nat → Bool) (h : Constraints p) : clause p c14988 = true :=
  Snake9.LocalRup.prove_clause [c14977, c1262] c14988 (by decide) p (sat_cons (step14977 p h) (sat_cons (step1262 p h) (sat_nil p)))
def c14989 : List Lit := [(248, false)]
theorem step14989 (p : Nat → Bool) (h : Constraints p) : clause p c14989 = true :=
  Snake9.LocalRup.prove_clause [c14978, c1260] c14989 (by decide) p (sat_cons (step14978 p h) (sat_cons (step1260 p h) (sat_nil p)))
def c14990 : List Lit := [(236, false)]
theorem step14990 (p : Nat → Bool) (h : Constraints p) : clause p c14990 = true :=
  Snake9.LocalRup.prove_clause [c14979, c1232] c14990 (by decide) p (sat_cons (step14979 p h) (sat_cons (step1232 p h) (sat_nil p)))
def c14991 : List Lit := [(234, false)]
theorem step14991 (p : Nat → Bool) (h : Constraints p) : clause p c14991 = true :=
  Snake9.LocalRup.prove_clause [c14980, c1228] c14991 (by decide) p (sat_cons (step14980 p h) (sat_cons (step1228 p h) (sat_nil p)))
def c14992 : List Lit := [(227, false)]
theorem step14992 (p : Nat → Bool) (h : Constraints p) : clause p c14992 = true :=
  Snake9.LocalRup.prove_clause [c14981, c1212] c14992 (by decide) p (sat_cons (step14981 p h) (sat_cons (step1212 p h) (sat_nil p)))
def c14993 : List Lit := [(222, false)]
theorem step14993 (p : Nat → Bool) (h : Constraints p) : clause p c14993 = true :=
  Snake9.LocalRup.prove_clause [c14982, c1195] c14993 (by decide) p (sat_cons (step14982 p h) (sat_cons (step1195 p h) (sat_nil p)))
def c14994 : List Lit := [(221, false)]
theorem step14994 (p : Nat → Bool) (h : Constraints p) : clause p c14994 = true :=
  Snake9.LocalRup.prove_clause [c14983, c1194] c14994 (by decide) p (sat_cons (step14983 p h) (sat_cons (step1194 p h) (sat_nil p)))
def c14995 : List Lit := [(203, false)]
theorem step14995 (p : Nat → Bool) (h : Constraints p) : clause p c14995 = true :=
  Snake9.LocalRup.prove_clause [c14984, c1162] c14995 (by decide) p (sat_cons (step14984 p h) (sat_cons (step1162 p h) (sat_nil p)))
def c14996 : List Lit := [(200, false)]
theorem step14996 (p : Nat → Bool) (h : Constraints p) : clause p c14996 = true :=
  Snake9.LocalRup.prove_clause [c14985, c1161] c14996 (by decide) p (sat_cons (step14985 p h) (sat_cons (step1161 p h) (sat_nil p)))
def c14997 : List Lit := [(197, false)]
theorem step14997 (p : Nat → Bool) (h : Constraints p) : clause p c14997 = true :=
  Snake9.LocalRup.prove_clause [c14986, c1152] c14997 (by decide) p (sat_cons (step14986 p h) (sat_cons (step1152 p h) (sat_nil p)))
end B112E055
