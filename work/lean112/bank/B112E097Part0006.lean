import B112E097Part0005
namespace B112E097
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1979 : List Lit := [(110, true), (119, true), (121, false), (123, true)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c741, c642] c1979 (by decide) p (sat_cons (step741 p h) (sat_cons (step642 p h) (sat_nil p)))
def c1980 : List Lit := [(249, false), (255, false)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c1627, c748] c1980 (by decide) p (sat_cons (step1627 p h) (sat_cons (step748 p h) (sat_nil p)))
def c1981 : List Lit := [(265, false), (267, false)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c1631, c758] c1981 (by decide) p (sat_cons (step1631 p h) (sat_cons (step758 p h) (sat_nil p)))
def c1982 : List Lit := [(257, false), (271, false)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1620, c765] c1982 (by decide) p (sat_cons (step1620 p h) (sat_cons (step765 p h) (sat_nil p)))
def c1983 : List Lit := [(273, false), (301, false)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c1613, c787] c1983 (by decide) p (sat_cons (step1613 p h) (sat_cons (step787 p h) (sat_nil p)))
def c1984 : List Lit := [(315, false), (329, false)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c1619, c807] c1984 (by decide) p (sat_cons (step1619 p h) (sat_cons (step807 p h) (sat_nil p)))
def c1985 : List Lit := [(353, false), (355, false)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c1630, c819] c1985 (by decide) p (sat_cons (step1630 p h) (sat_cons (step819 p h) (sat_nil p)))
def c1986 : List Lit := [(303, false), (363, false)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1609, c833] c1986 (by decide) p (sat_cons (step1609 p h) (sat_cons (step833 p h) (sat_nil p)))
def c1987 : List Lit := [(377, false), (391, false)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c1617, c851] c1987 (by decide) p (sat_cons (step1617 p h) (sat_cons (step851 p h) (sat_nil p)))
def c1988 : List Lit := [(397, false), (403, false)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c1623, c861] c1988 (by decide) p (sat_cons (step1623 p h) (sat_cons (step861 p h) (sat_nil p)))
def c1989 : List Lit := [(405, false), (419, false)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1616, c866] c1989 (by decide) p (sat_cons (step1616 p h) (sat_cons (step866 p h) (sat_nil p)))
def c1990 : List Lit := [(393, false), (421, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1611, c871] c1990 (by decide) p (sat_cons (step1611 p h) (sat_cons (step871 p h) (sat_nil p)))
def c1991 : List Lit := [(429, false), (431, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c1628, c879] c1991 (by decide) p (sat_cons (step1628 p h) (sat_cons (step879 p h) (sat_nil p)))
def c1992 : List Lit := [(427, false), (433, false)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1622, c883] c1992 (by decide) p (sat_cons (step1622 p h) (sat_cons (step883 p h) (sat_nil p)))
def c1993 : List Lit := [(471, false), (477, false)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1621, c903] c1993 (by decide) p (sat_cons (step1621 p h) (sat_cons (step903 p h) (sat_nil p)))
def c1994 : List Lit := [(451, false), (481, false)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c1610, c910] c1994 (by decide) p (sat_cons (step1610 p h) (sat_cons (step910 p h) (sat_nil p)))
def c1995 : List Lit := [(423, false), (483, false)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c1608, c915] c1995 (by decide) p (sat_cons (step1608 p h) (sat_cons (step915 p h) (sat_nil p)))
def c1996 : List Lit := [(365, false), (485, false)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c920, c918] c1996 (by decide) p (sat_cons (step920 p h) (sat_cons (step918 p h) (sat_nil p)))
def c1997 : List Lit := [(881, true), (849, false)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c1695, c984] c1997 (by decide) p (sat_cons (step1695 p h) (sat_cons (step984 p h) (sat_nil p)))
def c1998 : List Lit := [(882, true), (850, false)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c1695, c988] c1998 (by decide) p (sat_cons (step1695 p h) (sat_cons (step988 p h) (sat_nil p)))
def c1999 : List Lit := [(851, false), (883, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c1695, c991] c1999 (by decide) p (sat_cons (step1695 p h) (sat_cons (step991 p h) (sat_nil p)))
def c2000 : List Lit := [(906, true), (894, false)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1666, c1016] c2000 (by decide) p (sat_cons (step1666 p h) (sat_cons (step1016 p h) (sat_nil p)))
def c2001 : List Lit := [(895, false), (907, true)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c1666, c1020] c2001 (by decide) p (sat_cons (step1666 p h) (sat_cons (step1020 p h) (sat_nil p)))
def c2002 : List Lit := [(896, false), (908, true)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c1666, c1023] c2002 (by decide) p (sat_cons (step1666 p h) (sat_cons (step1023 p h) (sat_nil p)))
def c2003 : List Lit := [(938, true), (929, false)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c1667, c1075] c2003 (by decide) p (sat_cons (step1667 p h) (sat_cons (step1075 p h) (sat_nil p)))
def c2004 : List Lit := [(939, true), (930, false)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c1667, c1076] c2004 (by decide) p (sat_cons (step1667 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c2005 : List Lit := [(931, false), (940, true)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1667, c1077] c2005 (by decide) p (sat_cons (step1667 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c2006 : List Lit := [(932, false), (941, true)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c1667, c1078] c2006 (by decide) p (sat_cons (step1667 p h) (sat_cons (step1078 p h) (sat_nil p)))
def c2007 : List Lit := [(933, false), (942, true)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c1667, c1079] c2007 (by decide) p (sat_cons (step1667 p h) (sat_cons (step1079 p h) (sat_nil p)))
def c2008 : List Lit := [(938, true), (906, false)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1080] c2008 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c2009 : List Lit := [(907, false), (939, true)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1086] c2009 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1086 p h) (sat_nil p)))
def c2010 : List Lit := [(908, false), (940, true)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1092] c2010 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c2011 : List Lit := [(958, true), (939, false)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1105] c2011 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c2012 : List Lit := [(940, false), (959, true)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1106] c2012 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1106 p h) (sat_nil p)))
def c2013 : List Lit := [(941, false), (960, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1107] c2013 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1107 p h) (sat_nil p)))
def c2014 : List Lit := [(942, false), (961, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1108] c2014 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1108 p h) (sat_nil p)))
def c2015 : List Lit := [(943, false), (962, true)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1109] c2015 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1109 p h) (sat_nil p)))
def c2016 : List Lit := [(944, false), (963, true)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1110] c2016 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1110 p h) (sat_nil p)))
def c2017 : List Lit := [(945, false), (964, true)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1111] c2017 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1111 p h) (sat_nil p)))
def c2018 : List Lit := [(957, true), (881, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c1679, c1112] c2018 (by decide) p (sat_cons (step1679 p h) (sat_cons (step1112 p h) (sat_nil p)))
def c2019 : List Lit := [(882, false), (958, true)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c1679, c1119] c2019 (by decide) p (sat_cons (step1679 p h) (sat_cons (step1119 p h) (sat_nil p)))
def c2020 : List Lit := [(1059, false), (1072, true)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1338] c2020 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1338 p h) (sat_nil p)))
def c2021 : List Lit := [(1060, false), (1073, true)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1342] c2021 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1342 p h) (sat_nil p)))
def c2022 : List Lit := [(1061, false), (1074, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1346] c2022 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1346 p h) (sat_nil p)))
def c2023 : List Lit := [(1062, false), (1075, true)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1350] c2023 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1350 p h) (sat_nil p)))
def c2024 : List Lit := [(1048, false), (1081, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c1653, c1367] c2024 (by decide) p (sat_cons (step1653 p h) (sat_cons (step1367 p h) (sat_nil p)))
def c2025 : List Lit := [(1049, false), (1082, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c1653, c1375] c2025 (by decide) p (sat_cons (step1653 p h) (sat_cons (step1375 p h) (sat_nil p)))
def c2026 : List Lit := [(1050, false), (1083, true)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c1653, c1382] c2026 (by decide) p (sat_cons (step1653 p h) (sat_cons (step1382 p h) (sat_nil p)))
def c2027 : List Lit := [(1051, false), (1084, true)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c1653, c1390] c2027 (by decide) p (sat_cons (step1653 p h) (sat_cons (step1390 p h) (sat_nil p)))
def c2028 : List Lit := [(1089, false), (1019, false)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c1701, c1431] c2028 (by decide) p (sat_cons (step1701 p h) (sat_cons (step1431 p h) (sat_nil p)))
def c2029 : List Lit := [(957, false), (1108, false)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1456] c2029 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1456 p h) (sat_nil p)))
def c2030 : List Lit := [(958, false), (1107, false)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1457] c2030 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1457 p h) (sat_nil p)))
def c2031 : List Lit := [(959, false), (1106, false)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1458] c2031 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1458 p h) (sat_nil p)))
def c2032 : List Lit := [(960, false), (1105, false)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1459] c2032 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1459 p h) (sat_nil p)))
def c2033 : List Lit := [(961, false), (1104, false)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1460] c2033 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1460 p h) (sat_nil p)))
def c2034 : List Lit := [(962, false), (1103, false)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1461] c2034 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_nil p)))
def c2035 : List Lit := [(963, false), (1102, false)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1462] c2035 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1462 p h) (sat_nil p)))
def c2036 : List Lit := [(964, false), (1101, false)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1463] c2036 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1463 p h) (sat_nil p)))
def c2037 : List Lit := [(965, false), (1100, false)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1464] c2037 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1464 p h) (sat_nil p)))
def c2038 : List Lit := [(1669, false), (1678, true)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c1650, c1517] c2038 (by decide) p (sat_cons (step1650 p h) (sat_cons (step1517 p h) (sat_nil p)))
def c2039 : List Lit := [(1670, false), (1679, true)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c1650, c1518] c2039 (by decide) p (sat_cons (step1650 p h) (sat_cons (step1518 p h) (sat_nil p)))
def c2040 : List Lit := [(1620, false), (1765, false)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c1543, c1542] c2040 (by decide) p (sat_cons (step1543 p h) (sat_cons (step1542 p h) (sat_nil p)))
def c2041 : List Lit := [(853, false), (957, true)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1670] c2041 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1670 p h) (sat_nil p)))
def c2042 : List Lit := [(995, false), (979, false), (1021, true), (1005, false)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c1147, c1154, c1233, c1212, c1175, c1178, c1207, c1169, c1240, c1155, c1158, c1150, c1751, c1142] c2042 (by decide) p (sat_cons (step1147 p h) (sat_cons (step1154 p h) (sat_cons (step1233 p h) (sat_cons (step1212 p h) (sat_cons (step1175 p h) (sat_cons (step1178 p h) (sat_cons (step1207 p h) (sat_cons (step1169 p h) (sat_cons (step1240 p h) (sat_cons (step1155 p h) (sat_cons (step1158 p h) (sat_cons (step1150 p h) (sat_cons (step1751 p h) (sat_cons (step1142 p h) (sat_nil p)))))))))))))))
end B112E097
