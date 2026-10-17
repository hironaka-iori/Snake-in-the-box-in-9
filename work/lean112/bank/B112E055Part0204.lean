import B112E055Part0203
namespace B112E055
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c14998 : List Lit := [(1753, true)]
theorem step14998 (p : Nat → Bool) (h : Constraints p) : clause p c14998 = true :=
  Snake9.LocalRup.prove_clause [c14994, c12322, c14906, c5225] c14998 (by decide) p (sat_cons (step14994 p h) (sat_cons (step12322 p h) (sat_cons (step14906 p h) (sat_cons (step5225 p h) (sat_nil p)))))
def c14999 : List Lit := [(1759, true)]
theorem step14999 (p : Nat → Bool) (h : Constraints p) : clause p c14999 = true :=
  Snake9.LocalRup.prove_clause [c14998, c14954, c1632] c14999 (by decide) p (sat_cons (step14998 p h) (sat_cons (step14954 p h) (sat_cons (step1632 p h) (sat_nil p))))
def c15000 : List Lit := [(1789, false), (75, false)]
theorem step15000 (p : Nat → Bool) (h : Constraints p) : clause p c15000 = true :=
  Snake9.LocalRup.prove_clause [c13776, c14962, c14989, c14987, c14573, c14908, c14854, c637, c14465, c14928, c1816, c1734] c15000 (by decide) p (sat_cons (step13776 p h) (sat_cons (step14962 p h) (sat_cons (step14989 p h) (sat_cons (step14987 p h) (sat_cons (step14573 p h) (sat_cons (step14908 p h) (sat_cons (step14854 p h) (sat_cons (step637 p h) (sat_cons (step14465 p h) (sat_cons (step14928 p h) (sat_cons (step1816 p h) (sat_cons (step1734 p h) (sat_nil p)))))))))))))
def c15001 : List Lit := [(1754, true), (77, false)]
theorem step15001 (p : Nat → Bool) (h : Constraints p) : clause p c15001 = true :=
  Snake9.LocalRup.prove_clause [c14988, c14573, c14756, c13776, c14987, c14989, c14962, c14574, c14992, c14907, c14973, c14906, c12322, c14955, c6024, c14189, c1695, c2211, c1705, c2795, c1739, c14911, c14928, c10772] c15001 (by decide) p (sat_cons (step14988 p h) (sat_cons (step14573 p h) (sat_cons (step14756 p h) (sat_cons (step13776 p h) (sat_cons (step14987 p h) (sat_cons (step14989 p h) (sat_cons (step14962 p h) (sat_cons (step14574 p h) (sat_cons (step14992 p h) (sat_cons (step14907 p h) (sat_cons (step14973 p h) (sat_cons (step14906 p h) (sat_cons (step12322 p h) (sat_cons (step14955 p h) (sat_cons (step6024 p h) (sat_cons (step14189 p h) (sat_cons (step1695 p h) (sat_cons (step2211 p h) (sat_cons (step1705 p h) (sat_cons (step2795 p h) (sat_cons (step1739 p h) (sat_cons (step14911 p h) (sat_cons (step14928 p h) (sat_cons (step10772 p h) (sat_nil p)))))))))))))))))))))))))
def c15002 : List Lit := [(1789, false), (77, false)]
theorem step15002 (p : Nat → Bool) (h : Constraints p) : clause p c15002 = true :=
  Snake9.LocalRup.prove_clause [c14996, c12322, c14952, c13776, c14962, c14989, c14987, c14573, c14908, c15001, c2555, c14854, c15000, c14901, c640, c14465, c14928, c1816, c1734] c15002 (by decide) p (sat_cons (step14996 p h) (sat_cons (step12322 p h) (sat_cons (step14952 p h) (sat_cons (step13776 p h) (sat_cons (step14962 p h) (sat_cons (step14989 p h) (sat_cons (step14987 p h) (sat_cons (step14573 p h) (sat_cons (step14908 p h) (sat_cons (step15001 p h) (sat_cons (step2555 p h) (sat_cons (step14854 p h) (sat_cons (step15000 p h) (sat_cons (step14901 p h) (sat_cons (step640 p h) (sat_cons (step14465 p h) (sat_cons (step14928 p h) (sat_cons (step1816 p h) (sat_cons (step1734 p h) (sat_nil p))))))))))))))))))))
def c15003 : List Lit := [(123, true), (1787, false)]
theorem step15003 (p : Nat → Bool) (h : Constraints p) : clause p c15003 = true :=
  Snake9.LocalRup.prove_clause [c14962, c13776, c14573, c14799, c1737, c1811, c3853, c1758, c1760, c14465, c4887, c1816, c2449, c1738, c1715] c15003 (by decide) p (sat_cons (step14962 p h) (sat_cons (step13776 p h) (sat_cons (step14573 p h) (sat_cons (step14799 p h) (sat_cons (step1737 p h) (sat_cons (step1811 p h) (sat_cons (step3853 p h) (sat_cons (step1758 p h) (sat_cons (step1760 p h) (sat_cons (step14465 p h) (sat_cons (step4887 p h) (sat_cons (step1816 p h) (sat_cons (step2449 p h) (sat_cons (step1738 p h) (sat_cons (step1715 p h) (sat_nil p))))))))))))))))
def c15004 : List Lit := [(77, false)]
theorem step15004 (p : Nat → Bool) (h : Constraints p) : clause p c15004 = true :=
  Snake9.LocalRup.prove_clause [c12322, c14996, c14992, c14907, c14962, c13776, c14952, c2555, c15001, c15002, c2795, c1696, c1705, c14911, c15003, c640, c637, c14901] c15004 (by decide) p (sat_cons (step12322 p h) (sat_cons (step14996 p h) (sat_cons (step14992 p h) (sat_cons (step14907 p h) (sat_cons (step14962 p h) (sat_cons (step13776 p h) (sat_cons (step14952 p h) (sat_cons (step2555 p h) (sat_cons (step15001 p h) (sat_cons (step15002 p h) (sat_cons (step2795 p h) (sat_cons (step1696 p h) (sat_cons (step1705 p h) (sat_cons (step14911 p h) (sat_cons (step15003 p h) (sat_cons (step640 p h) (sat_cons (step637 p h) (sat_cons (step14901 p h) (sat_nil p)))))))))))))))))))
def c15005 : List Lit := [(1727, true)]
theorem step15005 (p : Nat → Bool) (h : Constraints p) : clause p c15005 = true :=
  Snake9.LocalRup.prove_clause [c15004, c1565] c15005 (by decide) p (sat_cons (step15004 p h) (sat_cons (step1565 p h) (sat_nil p)))
def c15006 : List Lit := [(16, false)]
theorem step15006 (p : Nat → Bool) (h : Constraints p) : clause p c15006 = true :=
  Snake9.LocalRup.prove_clause [c15004, c14756, c8666] c15006 (by decide) p (sat_cons (step15004 p h) (sat_cons (step14756 p h) (sat_cons (step8666 p h) (sat_nil p))))
def c15007 : List Lit := [(1787, false), (1800, true), (123, false)]
theorem step15007 (p : Nat → Bool) (h : Constraints p) : clause p c15007 = true :=
  Snake9.LocalRup.prove_clause [c14962, c14573, c14988, c13776, c14998, c15005, c14502, c14952, c14829, c14997, c15004, c1737, c14911, c1738, c1811, c640, c637, c4263, c1715, c4388, c1561, c4497, c1637, c1570, c2604, c5206, c1759, c1666, c554, c6320, c1563] c15007 (by decide) p (sat_cons (step14962 p h) (sat_cons (step14573 p h) (sat_cons (step14988 p h) (sat_cons (step13776 p h) (sat_cons (step14998 p h) (sat_cons (step15005 p h) (sat_cons (step14502 p h) (sat_cons (step14952 p h) (sat_cons (step14829 p h) (sat_cons (step14997 p h) (sat_cons (step15004 p h) (sat_cons (step1737 p h) (sat_cons (step14911 p h) (sat_cons (step1738 p h) (sat_cons (step1811 p h) (sat_cons (step640 p h) (sat_cons (step637 p h) (sat_cons (step4263 p h) (sat_cons (step1715 p h) (sat_cons (step4388 p h) (sat_cons (step1561 p h) (sat_cons (step4497 p h) (sat_cons (step1637 p h) (sat_cons (step1570 p h) (sat_cons (step2604 p h) (sat_cons (step5206 p h) (sat_cons (step1759 p h) (sat_cons (step1666 p h) (sat_cons (step554 p h) (sat_cons (step6320 p h) (sat_cons (step1563 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c15008 : List Lit := [(121, false), (1781, true)]
theorem step15008 (p : Nat → Bool) (h : Constraints p) : clause p c15008 = true :=
  Snake9.LocalRup.prove_clause [c14502, c14952, c14998, c14829, c14997, c15004, c14993, c12322, c1696, c1695, c8201, c554, c1637, c2034, c5582, c1666, c1638, c6320, c5189, c1563, c6360, c15000] c15008 (by decide) p (sat_cons (step14502 p h) (sat_cons (step14952 p h) (sat_cons (step14998 p h) (sat_cons (step14829 p h) (sat_cons (step14997 p h) (sat_cons (step15004 p h) (sat_cons (step14993 p h) (sat_cons (step12322 p h) (sat_cons (step1696 p h) (sat_cons (step1695 p h) (sat_cons (step8201 p h) (sat_cons (step554 p h) (sat_cons (step1637 p h) (sat_cons (step2034 p h) (sat_cons (step5582 p h) (sat_cons (step1666 p h) (sat_cons (step1638 p h) (sat_cons (step6320 p h) (sat_cons (step5189 p h) (sat_cons (step1563 p h) (sat_cons (step6360 p h) (sat_cons (step15000 p h) (sat_nil p)))))))))))))))))))))))
def c15009 : List Lit := [(75, false), (1781, true), (123, false)]
theorem step15009 (p : Nat → Bool) (h : Constraints p) : clause p c15009 = true :=
  Snake9.LocalRup.prove_clause [c14955, c14573, c14907, c14990, c13776, c14954, c14756, c14502, c14952, c14995, c14997, c14829, c15004, c15008, c1696, c3442, c15000, c637, c1554, c1709, c2477, c7151, c13927, c4988, c1633, c1566, c2221, c1568, c552, c13989, c14138, c1666, c14326, c1849, c8629, c2320, c4819] c15009 (by decide) p (sat_cons (step14955 p h) (sat_cons (step14573 p h) (sat_cons (step14907 p h) (sat_cons (step14990 p h) (sat_cons (step13776 p h) (sat_cons (step14954 p h) (sat_cons (step14756 p h) (sat_cons (step14502 p h) (sat_cons (step14952 p h) (sat_cons (step14995 p h) (sat_cons (step14997 p h) (sat_cons (step14829 p h) (sat_cons (step15004 p h) (sat_cons (step15008 p h) (sat_cons (step1696 p h) (sat_cons (step3442 p h) (sat_cons (step15000 p h) (sat_cons (step637 p h) (sat_cons (step1554 p h) (sat_cons (step1709 p h) (sat_cons (step2477 p h) (sat_cons (step7151 p h) (sat_cons (step13927 p h) (sat_cons (step4988 p h) (sat_cons (step1633 p h) (sat_cons (step1566 p h) (sat_cons (step2221 p h) (sat_cons (step1568 p h) (sat_cons (step552 p h) (sat_cons (step13989 p h) (sat_cons (step14138 p h) (sat_cons (step1666 p h) (sat_cons (step14326 p h) (sat_cons (step1849 p h) (sat_cons (step8629 p h) (sat_cons (step2320 p h) (sat_cons (step4819 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c15010 : List Lit := [(1726, false), (1781, true), (123, false)]
theorem step15010 (p : Nat → Bool) (h : Constraints p) : clause p c15010 = true :=
  Snake9.LocalRup.prove_clause [c15005, c14997, c15004, c14907, c14829, c14999, c14955, c14954, c14998, c13776, c14952, c14502, c15009, c1561, c1570, c5206, c1665, c15008, c14694, c1673, c6320, c8639, c1637, c640, c4388] c15010 (by decide) p (sat_cons (step15005 p h) (sat_cons (step14997 p h) (sat_cons (step15004 p h) (sat_cons (step14907 p h) (sat_cons (step14829 p h) (sat_cons (step14999 p h) (sat_cons (step14955 p h) (sat_cons (step14954 p h) (sat_cons (step14998 p h) (sat_cons (step13776 p h) (sat_cons (step14952 p h) (sat_cons (step14502 p h) (sat_cons (step15009 p h) (sat_cons (step1561 p h) (sat_cons (step1570 p h) (sat_cons (step5206 p h) (sat_cons (step1665 p h) (sat_cons (step15008 p h) (sat_cons (step14694 p h) (sat_cons (step1673 p h) (sat_cons (step6320 p h) (sat_cons (step8639 p h) (sat_cons (step1637 p h) (sat_cons (step640 p h) (sat_cons (step4388 p h) (sat_nil p))))))))))))))))))))))))))
def c15011 : List Lit := [(1781, true), (123, false)]
theorem step15011 (p : Nat → Bool) (h : Constraints p) : clause p c15011 = true :=
  Snake9.LocalRup.prove_clause [c14952, c14997, c14756, c12322, c15004, c14830, c14829, c14502, c14998, c14955, c14573, c14907, c13776, c15008, c15009, c1561, c15010, c1563, c552, c2714, c9092, c2103, c1637, c1554, c1556, c8490, c1675, c8242, c1642, c7151, c1607, c640, c1599] c15011 (by decide) p (sat_cons (step14952 p h) (sat_cons (step14997 p h) (sat_cons (step14756 p h) (sat_cons (step12322 p h) (sat_cons (step15004 p h) (sat_cons (step14830 p h) (sat_cons (step14829 p h) (sat_cons (step14502 p h) (sat_cons (step14998 p h) (sat_cons (step14955 p h) (sat_cons (step14573 p h) (sat_cons (step14907 p h) (sat_cons (step13776 p h) (sat_cons (step15008 p h) (sat_cons (step15009 p h) (sat_cons (step1561 p h) (sat_cons (step15010 p h) (sat_cons (step1563 p h) (sat_cons (step552 p h) (sat_cons (step2714 p h) (sat_cons (step9092 p h) (sat_cons (step2103 p h) (sat_cons (step1637 p h) (sat_cons (step1554 p h) (sat_cons (step1556 p h) (sat_cons (step8490 p h) (sat_cons (step1675 p h) (sat_cons (step8242 p h) (sat_cons (step1642 p h) (sat_cons (step7151 p h) (sat_cons (step1607 p h) (sat_cons (step640 p h) (sat_cons (step1599 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c15012 : List Lit := [(123, false)]
theorem step15012 (p : Nat → Bool) (h : Constraints p) : clause p c15012 = true :=
  Snake9.LocalRup.prove_clause [c14907, c14962, c14988, c13776, c14573, c14998, c15005, c14502, c14952, c14829, c14997, c15004, c15011, c1705, c14911, c15007, c640, c637, c4263, c1816, c4388, c1561, c4528, c1637, c1570, c2450, c5206, c1759, c1666, c554, c6320, c1563] c15012 (by decide) p (sat_cons (step14907 p h) (sat_cons (step14962 p h) (sat_cons (step14988 p h) (sat_cons (step13776 p h) (sat_cons (step14573 p h) (sat_cons (step14998 p h) (sat_cons (step15005 p h) (sat_cons (step14502 p h) (sat_cons (step14952 p h) (sat_cons (step14829 p h) (sat_cons (step14997 p h) (sat_cons (step15004 p h) (sat_cons (step15011 p h) (sat_cons (step1705 p h) (sat_cons (step14911 p h) (sat_cons (step15007 p h) (sat_cons (step640 p h) (sat_cons (step637 p h) (sat_cons (step4263 p h) (sat_cons (step1816 p h) (sat_cons (step4388 p h) (sat_cons (step1561 p h) (sat_cons (step4528 p h) (sat_cons (step1637 p h) (sat_cons (step1570 p h) (sat_cons (step2450 p h) (sat_cons (step5206 p h) (sat_cons (step1759 p h) (sat_cons (step1666 p h) (sat_cons (step554 p h) (sat_cons (step6320 p h) (sat_cons (step1563 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c15013 : List Lit := [(1823, true)]
theorem step15013 (p : Nat → Bool) (h : Constraints p) : clause p c15013 = true :=
  Snake9.LocalRup.prove_clause [c15012, c14962, c14465] c15013 (by decide) p (sat_cons (step15012 p h) (sat_cons (step14962 p h) (sat_cons (step14465 p h) (sat_nil p))))
def c15014 : List Lit := [(1787, false)]
theorem step15014 (p : Nat → Bool) (h : Constraints p) : clause p c15014 = true :=
  Snake9.LocalRup.prove_clause [c15012, c15003] c15014 (by decide) p (sat_cons (step15012 p h) (sat_cons (step15003 p h) (sat_nil p)))
def c15015 : List Lit := [(1800, false)]
theorem step15015 (p : Nat → Bool) (h : Constraints p) : clause p c15015 = true :=
  Snake9.LocalRup.prove_clause [c15013, c14573, c1816] c15015 (by decide) p (sat_cons (step15013 p h) (sat_cons (step14573 p h) (sat_cons (step1816 p h) (sat_nil p))))
def c15016 : List Lit := [(1781, false)]
theorem step15016 (p : Nat → Bool) (h : Constraints p) : clause p c15016 = true :=
  Snake9.LocalRup.prove_clause [c15014, c14907, c1705] c15016 (by decide) p (sat_cons (step15014 p h) (sat_cons (step14907 p h) (sat_cons (step1705 p h) (sat_nil p))))
def c15017 : List Lit := [(1794, false)]
theorem step15017 (p : Nat → Bool) (h : Constraints p) : clause p c15017 = true :=
  Snake9.LocalRup.prove_clause [c15015, c14908, c1734] c15017 (by decide) p (sat_cons (step15015 p h) (sat_cons (step14908 p h) (sat_cons (step1734 p h) (sat_nil p))))
def c15018 : List Lit := [(100, true)]
theorem step15018 (p : Nat → Bool) (h : Constraints p) : clause p c15018 = true :=
  Snake9.LocalRup.prove_clause [c15016, c1695] c15018 (by decide) p (sat_cons (step15016 p h) (sat_cons (step1695 p h) (sat_nil p)))
def c15019 : List Lit := [(99, true)]
theorem step15019 (p : Nat → Bool) (h : Constraints p) : clause p c15019 = true :=
  Snake9.LocalRup.prove_clause [c15016, c1696] c15019 (by decide) p (sat_cons (step15016 p h) (sat_cons (step1696 p h) (sat_nil p)))
def c15020 : List Lit := [(1789, false)]
theorem step15020 (p : Nat → Bool) (h : Constraints p) : clause p c15020 = true :=
  Snake9.LocalRup.prove_clause [c15017, c15012, c14987, c14989, c14928] c15020 (by decide) p (sat_cons (step15017 p h) (sat_cons (step15012 p h) (sat_cons (step14987 p h) (sat_cons (step14989 p h) (sat_cons (step14928 p h) (sat_nil p))))))
def c15021 : List Lit := [(98, false)]
theorem step15021 (p : Nat → Bool) (h : Constraints p) : clause p c15021 = true :=
  Snake9.LocalRup.prove_clause [c15019, c12322, c15020, c6360] c15021 (by decide) p (sat_cons (step15019 p h) (sat_cons (step12322 p h) (sat_cons (step15020 p h) (sat_cons (step6360 p h) (sat_nil p)))))
def c15022 : List Lit := [(107, false)]
theorem step15022 (p : Nat → Bool) (h : Constraints p) : clause p c15022 = true :=
  Snake9.LocalRup.prove_clause [c15019, c15020, c2477] c15022 (by decide) p (sat_cons (step15019 p h) (sat_cons (step15020 p h) (sat_cons (step2477 p h) (sat_nil p))))
def c15023 : List Lit := [(108, true)]
theorem step15023 (p : Nat → Bool) (h : Constraints p) : clause p c15023 = true :=
  Snake9.LocalRup.prove_clause [c15020, c1709] c15023 (by decide) p (sat_cons (step15020 p h) (sat_cons (step1709 p h) (sat_nil p)))
def c15024 : List Lit := [(106, true)]
theorem step15024 (p : Nat → Bool) (h : Constraints p) : clause p c15024 = true :=
  Snake9.LocalRup.prove_clause [c15020, c1710] c15024 (by decide) p (sat_cons (step15020 p h) (sat_cons (step1710 p h) (sat_nil p)))
def c15025 : List Lit := [(1751, true)]
theorem step15025 (p : Nat → Bool) (h : Constraints p) : clause p c15025 = true :=
  Snake9.LocalRup.prove_clause [c15020, c14955, c3852] c15025 (by decide) p (sat_cons (step15020 p h) (sat_cons (step14955 p h) (sat_cons (step3852 p h) (sat_nil p))))
def c15026 : List Lit := [(1754, true)]
theorem step15026 (p : Nat → Bool) (h : Constraints p) : clause p c15026 = true :=
  Snake9.LocalRup.prove_clause [c15021, c15025, c15018, c14993, c3979] c15026 (by decide) p (sat_cons (step15021 p h) (sat_cons (step15025 p h) (sat_cons (step15018 p h) (sat_cons (step14993 p h) (sat_cons (step3979 p h) (sat_nil p))))))
def c15027 : List Lit := [(103, true)]
theorem step15027 (p : Nat → Bool) (h : Constraints p) : clause p c15027 = true :=
  Snake9.LocalRup.prove_clause [c15022, c13776, c14990, c15023, c4988] c15027 (by decide) p (sat_cons (step15022 p h) (sat_cons (step13776 p h) (sat_cons (step14990 p h) (sat_cons (step15023 p h) (sat_cons (step4988 p h) (sat_nil p))))))
def c15028 : List Lit := [(1760, true)]
theorem step15028 (p : Nat → Bool) (h : Constraints p) : clause p c15028 = true :=
  Snake9.LocalRup.prove_clause [c15026, c14954, c1633] c15028 (by decide) p (sat_cons (step15026 p h) (sat_cons (step14954 p h) (sat_cons (step1633 p h) (sat_nil p))))
def c15029 : List Lit := [(85, true)]
theorem step15029 (p : Nat → Bool) (h : Constraints p) : clause p c15029 = true :=
  Snake9.LocalRup.prove_clause [c15027, c14756, c2221] c15029 (by decide) p (sat_cons (step15027 p h) (sat_cons (step14756 p h) (sat_cons (step2221 p h) (sat_nil p))))
def c15030 : List Lit := [(1737, false)]
theorem step15030 (p : Nat → Bool) (h : Constraints p) : clause p c15030 = true :=
  Snake9.LocalRup.prove_clause [c15028, c14830, c1682] c15030 (by decide) p (sat_cons (step15028 p h) (sat_cons (step14830 p h) (sat_cons (step1682 p h) (sat_nil p))))
def c15031 : List Lit := [(72, false)]
theorem step15031 (p : Nat → Bool) (h : Constraints p) : clause p c15031 = true :=
  Snake9.LocalRup.prove_clause [c15029, c14952, c14502, c552] c15031 (by decide) p (sat_cons (step15029 p h) (sat_cons (step14952 p h) (sat_cons (step14502 p h) (sat_cons (step552 p h) (sat_nil p)))))
def c15032 : List Lit := [(1725, true)]
theorem step15032 (p : Nat → Bool) (h : Constraints p) : clause p c15032 = true :=
  Snake9.LocalRup.prove_clause [c15031, c1562] c15032 (by decide) p (sat_cons (step15031 p h) (sat_cons (step1562 p h) (sat_nil p)))
def c15033 : List Lit := [(1735, true)]
theorem step15033 (p : Nat → Bool) (h : Constraints p) : clause p c15033 = true :=
  Snake9.LocalRup.prove_clause [c15031, c15004, c2034] c15033 (by decide) p (sat_cons (step15031 p h) (sat_cons (step15004 p h) (sat_cons (step2034 p h) (sat_nil p))))
def c15034 : List Lit := [(1761, false)]
theorem step15034 (p : Nat → Bool) (h : Constraints p) : clause p c15034 = true :=
  Snake9.LocalRup.prove_clause [c15031, c14829, c15033, c15004, c5582] c15034 (by decide) p (sat_cons (step15031 p h) (sat_cons (step14829 p h) (sat_cons (step15033 p h) (sat_cons (step15004 p h) (sat_cons (step5582 p h) (sat_nil p))))))
def c15035 : List Lit := [(1771, true)]
theorem step15035 (p : Nat → Bool) (h : Constraints p) : clause p c15035 = true :=
  Snake9.LocalRup.prove_clause [c15033, c15028, c1666] c15035 (by decide) p (sat_cons (step15033 p h) (sat_cons (step15028 p h) (sat_cons (step1666 p h) (sat_nil p))))
def c15036 : List Lit := [(1747, false)]
theorem step15036 (p : Nat → Bool) (h : Constraints p) : clause p c15036 = true :=
  Snake9.LocalRup.prove_clause [c15034, c15026, c1638] c15036 (by decide) p (sat_cons (step15034 p h) (sat_cons (step15026 p h) (sat_cons (step1638 p h) (sat_nil p))))
def c15037 : List Lit := [(1857, true)]
theorem step15037 (p : Nat → Bool) (h : Constraints p) : clause p c15037 = true :=
  Snake9.LocalRup.prove_clause [c15035, c14829, c1849] c15037 (by decide) p (sat_cons (step15035 p h) (sat_cons (step14829 p h) (sat_cons (step1849 p h) (sat_nil p))))
def c15038 : List Lit := [(1726, false)]
theorem step15038 (p : Nat → Bool) (h : Constraints p) : clause p c15038 = true :=
  Snake9.LocalRup.prove_clause [c15035, c15004, c15028, c14997, c14829, c6320] c15038 (by decide) p (sat_cons (step15035 p h) (sat_cons (step15004 p h) (sat_cons (step15028 p h) (sat_cons (step14997 p h) (sat_cons (step14829 p h) (sat_cons (step6320 p h) (sat_nil p)))))))
def c15039 : List Lit := [(86, true)]
theorem step15039 (p : Nat → Bool) (h : Constraints p) : clause p c15039 = true :=
  Snake9.LocalRup.prove_clause [c15036, c14502, c14952, c4388] c15039 (by decide) p (sat_cons (step15036 p h) (sat_cons (step14502 p h) (sat_cons (step14952 p h) (sat_cons (step4388 p h) (sat_nil p)))))
def c15040 : List Lit := [(1703, false)]
theorem step15040 (p : Nat → Bool) (h : Constraints p) : clause p c15040 = true :=
  Snake9.LocalRup.prove_clause [c15037, c2320] c15040 (by decide) p (sat_cons (step15037 p h) (sat_cons (step2320 p h) (sat_nil p)))
def c15041 : List Lit := [(75, true)]
theorem step15041 (p : Nat → Bool) (h : Constraints p) : clause p c15041 = true :=
  Snake9.LocalRup.prove_clause [c15038, c15031, c1563] c15041 (by decide) p (sat_cons (step15038 p h) (sat_cons (step15031 p h) (sat_cons (step1563 p h) (sat_nil p))))
def c15042 : List Lit := [(1717, false)]
theorem step15042 (p : Nat → Bool) (h : Constraints p) : clause p c15042 = true :=
  Snake9.LocalRup.prove_clause [c15039, c15032, c15004, c15030, c15041, c14961, c13776, c5023] c15042 (by decide) p (sat_cons (step15039 p h) (sat_cons (step15032 p h) (sat_cons (step15004 p h) (sat_cons (step15030 p h) (sat_cons (step15041 p h) (sat_cons (step14961 p h) (sat_cons (step13776 p h) (sat_cons (step5023 p h) (sat_nil p)))))))))
def c15043 : List Lit := [(1682, false)]
theorem step15043 (p : Nat → Bool) (h : Constraints p) : clause p c15043 = true :=
  Snake9.LocalRup.prove_clause [c15039, c14991, c15024, c15006, c15040, c15019, c14887] c15043 (by decide) p (sat_cons (step15039 p h) (sat_cons (step14991 p h) (sat_cons (step15024 p h) (sat_cons (step15006 p h) (sat_cons (step15040 p h) (sat_cons (step15019 p h) (sat_cons (step14887 p h) (sat_nil p))))))))
def c15044 : List Lit := [(64, true)]
theorem step15044 (p : Nat → Bool) (h : Constraints p) : clause p c15044 = true :=
  Snake9.LocalRup.prove_clause [c15042, c1552] c15044 (by decide) p (sat_cons (step15042 p h) (sat_cons (step1552 p h) (sat_nil p)))
def c15045 : List Lit := []
theorem step15045 (p : Nat → Bool) (h : Constraints p) : clause p c15045 = true :=
  Snake9.LocalRup.prove_clause [c15044, c15043, c5352] c15045 (by decide) p (sat_cons (step15044 p h) (sat_cons (step15043 p h) (sat_cons (step5352 p h) (sat_nil p))))
end B112E055
