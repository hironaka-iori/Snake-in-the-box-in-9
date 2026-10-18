import B112E186Part0059
namespace B112E186
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5240 : List Lit := [(1643, true), (112, false), (87, true), (1580, false), (85, true)]
theorem step5240 (p : Nat → Bool) (h : Constraints p) : clause p c5240 = true :=
  Snake9.LocalRup.prove_clause [c4970, c5222, c5218, c5129, c1112, c1121, c1725, c1167, c4313, c4107, c4379, c1749, c4184, c4115, c1054, c5223, c5230, c1067, c2625, c1313, c1315, c1751, c3991, c1032, c1982, c3197, c1124, c1122, c1114, c5234, c5235, c5239, c1199, c5238, c1652, c1653, c4421, c1757, c455, c450, c3992, c1289, c1197, c1187, c1314, c1736, c1192, c1750, c1223, c1031, c1206, c999, c1201, c1708, c1953, c5004] c5240 (by decide) p (sat_cons (step4970 p h) (sat_cons (step5222 p h) (sat_cons (step5218 p h) (sat_cons (step5129 p h) (sat_cons (step1112 p h) (sat_cons (step1121 p h) (sat_cons (step1725 p h) (sat_cons (step1167 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4379 p h) (sat_cons (step1749 p h) (sat_cons (step4184 p h) (sat_cons (step4115 p h) (sat_cons (step1054 p h) (sat_cons (step5223 p h) (sat_cons (step5230 p h) (sat_cons (step1067 p h) (sat_cons (step2625 p h) (sat_cons (step1313 p h) (sat_cons (step1315 p h) (sat_cons (step1751 p h) (sat_cons (step3991 p h) (sat_cons (step1032 p h) (sat_cons (step1982 p h) (sat_cons (step3197 p h) (sat_cons (step1124 p h) (sat_cons (step1122 p h) (sat_cons (step1114 p h) (sat_cons (step5234 p h) (sat_cons (step5235 p h) (sat_cons (step5239 p h) (sat_cons (step1199 p h) (sat_cons (step5238 p h) (sat_cons (step1652 p h) (sat_cons (step1653 p h) (sat_cons (step4421 p h) (sat_cons (step1757 p h) (sat_cons (step455 p h) (sat_cons (step450 p h) (sat_cons (step3992 p h) (sat_cons (step1289 p h) (sat_cons (step1197 p h) (sat_cons (step1187 p h) (sat_cons (step1314 p h) (sat_cons (step1736 p h) (sat_cons (step1192 p h) (sat_cons (step1750 p h) (sat_cons (step1223 p h) (sat_cons (step1031 p h) (sat_cons (step1206 p h) (sat_cons (step999 p h) (sat_cons (step1201 p h) (sat_cons (step1708 p h) (sat_cons (step1953 p h) (sat_cons (step5004 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5241 : List Lit := [(97, false), (1761, true), (84, false), (83, false), (1762, true), (67, true), (1580, false), (85, true)]
theorem step5241 (p : Nat → Bool) (h : Constraints p) : clause p c5241 = true :=
  Snake9.LocalRup.prove_clause [c3992, c1653, c4421, c450, c1199, c5220] c5241 (by decide) p (sat_cons (step3992 p h) (sat_cons (step1653 p h) (sat_cons (step4421 p h) (sat_cons (step450 p h) (sat_cons (step1199 p h) (sat_cons (step5220 p h) (sat_nil p)))))))
def c5242 : List Lit := [(107, false), (1761, true), (35, true), (84, false), (83, false), (1762, true), (67, true), (112, false), (1580, false), (85, true)]
theorem step5242 (p : Nat → Bool) (h : Constraints p) : clause p c5242 = true :=
  Snake9.LocalRup.prove_clause [c5137, c1667, c5220, c386, c1675, c4220, c636] c5242 (by decide) p (sat_cons (step5137 p h) (sat_cons (step1667 p h) (sat_cons (step5220 p h) (sat_cons (step386 p h) (sat_cons (step1675 p h) (sat_cons (step4220 p h) (sat_cons (step636 p h) (sat_nil p))))))))
def c5243 : List Lit := [(100, false), (97, true), (1727, true), (35, true), (84, false), (83, false), (112, false), (1661, true), (1750, true), (85, true)]
theorem step5243 (p : Nat → Bool) (h : Constraints p) : clause p c5243 = true :=
  Snake9.LocalRup.prove_clause [c2612, c386, c1675, c4073, c636, c635, c1538, c1184, c1247, c1218, c1249, c5057, c1266, c5015] c5243 (by decide) p (sat_cons (step2612 p h) (sat_cons (step386 p h) (sat_cons (step1675 p h) (sat_cons (step4073 p h) (sat_cons (step636 p h) (sat_cons (step635 p h) (sat_cons (step1538 p h) (sat_cons (step1184 p h) (sat_cons (step1247 p h) (sat_cons (step1218 p h) (sat_cons (step1249 p h) (sat_cons (step5057 p h) (sat_cons (step1266 p h) (sat_cons (step5015 p h) (sat_nil p)))))))))))))))
def c5244 : List Lit := [(112, false), (87, true), (1580, false), (85, true)]
theorem step5244 (p : Nat → Bool) (h : Constraints p) : clause p c5244 = true :=
  Snake9.LocalRup.prove_clause [c4972, c4970, c5218, c5129, c1112, c1121, c1725, c1167, c4313, c4107, c4379, c1749, c5137, c4115, c5240, c1061, c2726, c3034, c2243, c1087, c1313, c1315, c1124, c1122, c3157, c1078, c1751, c1114, c5134, c5234, c1750, c1314, c3992, c5241, c5242, c1199, c5243, c2093, c4991, c1284, c1201, c1736, c1827, c1676, c385, c1117, c4697, c2687, c1229, c1237] c5244 (by decide) p (sat_cons (step4972 p h) (sat_cons (step4970 p h) (sat_cons (step5218 p h) (sat_cons (step5129 p h) (sat_cons (step1112 p h) (sat_cons (step1121 p h) (sat_cons (step1725 p h) (sat_cons (step1167 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4379 p h) (sat_cons (step1749 p h) (sat_cons (step5137 p h) (sat_cons (step4115 p h) (sat_cons (step5240 p h) (sat_cons (step1061 p h) (sat_cons (step2726 p h) (sat_cons (step3034 p h) (sat_cons (step2243 p h) (sat_cons (step1087 p h) (sat_cons (step1313 p h) (sat_cons (step1315 p h) (sat_cons (step1124 p h) (sat_cons (step1122 p h) (sat_cons (step3157 p h) (sat_cons (step1078 p h) (sat_cons (step1751 p h) (sat_cons (step1114 p h) (sat_cons (step5134 p h) (sat_cons (step5234 p h) (sat_cons (step1750 p h) (sat_cons (step1314 p h) (sat_cons (step3992 p h) (sat_cons (step5241 p h) (sat_cons (step5242 p h) (sat_cons (step1199 p h) (sat_cons (step5243 p h) (sat_cons (step2093 p h) (sat_cons (step4991 p h) (sat_cons (step1284 p h) (sat_cons (step1201 p h) (sat_cons (step1736 p h) (sat_cons (step1827 p h) (sat_cons (step1676 p h) (sat_cons (step385 p h) (sat_cons (step1117 p h) (sat_cons (step4697 p h) (sat_cons (step2687 p h) (sat_cons (step1229 p h) (sat_cons (step1237 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c5245 : List Lit := [(1718, true), (88, false), (97, true), (1761, true), (1631, true), (107, true), (1678, true), (84, false), (83, false), (112, true), (1580, false), (85, true)]
theorem step5245 (p : Nat → Bool) (h : Constraints p) : clause p c5245 = true :=
  Snake9.LocalRup.prove_clause [c2637, c4313, c4107, c4184, c1032, c1199, c5137, c1737, c5002, c1201, c1284, c5112, c1981, c1000, c1039, c1953, c4992, c4473, c909] c5245 (by decide) p (sat_cons (step2637 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4184 p h) (sat_cons (step1032 p h) (sat_cons (step1199 p h) (sat_cons (step5137 p h) (sat_cons (step1737 p h) (sat_cons (step5002 p h) (sat_cons (step1201 p h) (sat_cons (step1284 p h) (sat_cons (step5112 p h) (sat_cons (step1981 p h) (sat_cons (step1000 p h) (sat_cons (step1039 p h) (sat_cons (step1953 p h) (sat_cons (step4992 p h) (sat_cons (step4473 p h) (sat_cons (step909 p h) (sat_nil p))))))))))))))))))))
def c5246 : List Lit := [(1749, true), (100, false), (84, false), (112, true)]
theorem step5246 (p : Nat → Bool) (h : Constraints p) : clause p c5246 = true :=
  Snake9.LocalRup.prove_clause [c1228, c1736, c1904, c1239, c1245, c1246, c1230, c637, c1841, c1691, c654] c5246 (by decide) p (sat_cons (step1228 p h) (sat_cons (step1736 p h) (sat_cons (step1904 p h) (sat_cons (step1239 p h) (sat_cons (step1245 p h) (sat_cons (step1246 p h) (sat_cons (step1230 p h) (sat_cons (step637 p h) (sat_cons (step1841 p h) (sat_cons (step1691 p h) (sat_cons (step654 p h) (sat_nil p))))))))))))
def c5247 : List Lit := [(1643, false), (84, false), (83, false), (87, true), (1580, false), (85, true)]
theorem step5247 (p : Nat → Bool) (h : Constraints p) : clause p c5247 = true :=
  Snake9.LocalRup.prove_clause [c4970, c4972, c5244, c5218, c5129, c1112, c1121, c1725, c1167, c4313, c4107, c4379, c1749, c5137, c1737, c1061, c2726, c3034, c2243, c1087, c1313, c1315, c1122, c5210, c1078, c1751, c1199, c5134, c1202, c1750, c1314, c5241, c2637, c5246, c1284, c1537, c1221, c1201, c5245, c4176, c1538, c1184, c4539, c1194, c1197, c1186, c457, c1763] c5247 (by decide) p (sat_cons (step4970 p h) (sat_cons (step4972 p h) (sat_cons (step5244 p h) (sat_cons (step5218 p h) (sat_cons (step5129 p h) (sat_cons (step1112 p h) (sat_cons (step1121 p h) (sat_cons (step1725 p h) (sat_cons (step1167 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4379 p h) (sat_cons (step1749 p h) (sat_cons (step5137 p h) (sat_cons (step1737 p h) (sat_cons (step1061 p h) (sat_cons (step2726 p h) (sat_cons (step3034 p h) (sat_cons (step2243 p h) (sat_cons (step1087 p h) (sat_cons (step1313 p h) (sat_cons (step1315 p h) (sat_cons (step1122 p h) (sat_cons (step5210 p h) (sat_cons (step1078 p h) (sat_cons (step1751 p h) (sat_cons (step1199 p h) (sat_cons (step5134 p h) (sat_cons (step1202 p h) (sat_cons (step1750 p h) (sat_cons (step1314 p h) (sat_cons (step5241 p h) (sat_cons (step2637 p h) (sat_cons (step5246 p h) (sat_cons (step1284 p h) (sat_cons (step1537 p h) (sat_cons (step1221 p h) (sat_cons (step1201 p h) (sat_cons (step5245 p h) (sat_cons (step4176 p h) (sat_cons (step1538 p h) (sat_cons (step1184 p h) (sat_cons (step4539 p h) (sat_cons (step1194 p h) (sat_cons (step1197 p h) (sat_cons (step1186 p h) (sat_cons (step457 p h) (sat_cons (step1763 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c5248 : List Lit := [(88, true), (1713, true), (107, true), (97, true), (100, false), (1761, true), (84, false), (83, false), (85, true)]
theorem step5248 (p : Nat → Bool) (h : Constraints p) : clause p c5248 = true :=
  Snake9.LocalRup.prove_clause [c4073, c1538, c1184, c4539, c1194, c1197, c1186, c457, c1763] c5248 (by decide) p (sat_cons (step4073 p h) (sat_cons (step1538 p h) (sat_cons (step1184 p h) (sat_cons (step4539 p h) (sat_cons (step1194 p h) (sat_cons (step1197 p h) (sat_cons (step1186 p h) (sat_cons (step457 p h) (sat_cons (step1763 p h) (sat_nil p))))))))))
def c5249 : List Lit := [(1631, true), (67, true), (88, false), (107, true), (97, true), (1718, true), (1761, true), (84, false), (83, false), (87, true), (1580, false), (85, true)]
theorem step5249 (p : Nat → Bool) (h : Constraints p) : clause p c5249 = true :=
  Snake9.LocalRup.prove_clause [c5247, c1054, c5244, c1112, c5218, c5129, c4313, c4107, c4184, c1032, c5224, c5245, c1982, c1067, c1122, c3197] c5249 (by decide) p (sat_cons (step5247 p h) (sat_cons (step1054 p h) (sat_cons (step5244 p h) (sat_cons (step1112 p h) (sat_cons (step5218 p h) (sat_cons (step5129 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4184 p h) (sat_cons (step1032 p h) (sat_cons (step5224 p h) (sat_cons (step5245 p h) (sat_cons (step1982 p h) (sat_cons (step1067 p h) (sat_cons (step1122 p h) (sat_cons (step3197 p h) (sat_nil p)))))))))))))))))
def c5250 : List Lit := [(67, true), (107, true), (97, true), (100, false), (1761, true), (84, false), (83, false), (87, true), (1580, false), (85, true)]
theorem step5250 (p : Nat → Bool) (h : Constraints p) : clause p c5250 = true :=
  Snake9.LocalRup.prove_clause [c4970, c5244, c5246, c1284, c1199, c1202, c1221, c5248, c1537, c5247, c4313, c1112, c1121, c1932, c1307, c1752, c5249, c1751, c1313, c1930, c2625, c1122, c5085, c5112, c1040, c4976, c1982, c2633] c5250 (by decide) p (sat_cons (step4970 p h) (sat_cons (step5244 p h) (sat_cons (step5246 p h) (sat_cons (step1284 p h) (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_cons (step1221 p h) (sat_cons (step5248 p h) (sat_cons (step1537 p h) (sat_cons (step5247 p h) (sat_cons (step4313 p h) (sat_cons (step1112 p h) (sat_cons (step1121 p h) (sat_cons (step1932 p h) (sat_cons (step1307 p h) (sat_cons (step1752 p h) (sat_cons (step5249 p h) (sat_cons (step1751 p h) (sat_cons (step1313 p h) (sat_cons (step1930 p h) (sat_cons (step2625 p h) (sat_cons (step1122 p h) (sat_cons (step5085 p h) (sat_cons (step5112 p h) (sat_cons (step1040 p h) (sat_cons (step4976 p h) (sat_cons (step1982 p h) (sat_cons (step2633 p h) (sat_nil p)))))))))))))))))))))))))))))
def c5251 : List Lit := [(107, true), (97, true), (100, false), (1761, true), (84, false), (83, false), (87, true), (1580, false), (85, true)]
theorem step5251 (p : Nat → Bool) (h : Constraints p) : clause p c5251 = true :=
  Snake9.LocalRup.prove_clause [c4970, c5244, c5246, c1284, c1537, c1112, c1121, c1725, c5218, c5129, c4313, c1199, c1202, c1221, c5248, c5250, c2168, c1161, c1160, c1726, c1313, c1122, c1751, c5245] c5251 (by decide) p (sat_cons (step4970 p h) (sat_cons (step5244 p h) (sat_cons (step5246 p h) (sat_cons (step1284 p h) (sat_cons (step1537 p h) (sat_cons (step1112 p h) (sat_cons (step1121 p h) (sat_cons (step1725 p h) (sat_cons (step5218 p h) (sat_cons (step5129 p h) (sat_cons (step4313 p h) (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_cons (step1221 p h) (sat_cons (step5248 p h) (sat_cons (step5250 p h) (sat_cons (step2168 p h) (sat_cons (step1161 p h) (sat_cons (step1160 p h) (sat_cons (step1726 p h) (sat_cons (step1313 p h) (sat_cons (step1122 p h) (sat_cons (step1751 p h) (sat_cons (step5245 p h) (sat_nil p)))))))))))))))))))))))))
def c5252 : List Lit := [(107, false), (84, false), (112, true), (1661, true), (1737, true), (85, true)]
theorem step5252 (p : Nat → Bool) (h : Constraints p) : clause p c5252 = true :=
  Snake9.LocalRup.prove_clause [c1486, c5210] c5252 (by decide) p (sat_cons (step1486 p h) (sat_cons (step5210 p h) (sat_nil p)))
def c5253 : List Lit := [(1761, true), (84, false), (83, false), (87, true), (1580, false), (85, true)]
theorem step5253 (p : Nat → Bool) (h : Constraints p) : clause p c5253 = true :=
  Snake9.LocalRup.prove_clause [c4970, c5137, c1737, c5218, c5129, c1112, c1121, c1725, c1167, c5244, c5252, c1199, c3992, c4421, c2637, c5251] c5253 (by decide) p (sat_cons (step4970 p h) (sat_cons (step5137 p h) (sat_cons (step1737 p h) (sat_cons (step5218 p h) (sat_cons (step5129 p h) (sat_cons (step1112 p h) (sat_cons (step1121 p h) (sat_cons (step1725 p h) (sat_cons (step1167 p h) (sat_cons (step5244 p h) (sat_cons (step5252 p h) (sat_cons (step1199 p h) (sat_cons (step3992 p h) (sat_cons (step4421 p h) (sat_cons (step2637 p h) (sat_cons (step5251 p h) (sat_nil p)))))))))))))))))
def c5254 : List Lit := [(1599, false), (105, false), (1631, true), (1737, true), (85, true)]
theorem step5254 (p : Nat → Bool) (h : Constraints p) : clause p c5254 = true :=
  Snake9.LocalRup.prove_clause [c4313, c4107, c4184, c1032, c1981, c1000, c1039, c1953, c4992, c4473, c909] c5254 (by decide) p (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4184 p h) (sat_cons (step1032 p h) (sat_cons (step1981 p h) (sat_cons (step1000 p h) (sat_cons (step1039 p h) (sat_cons (step1953 p h) (sat_cons (step4992 p h) (sat_cons (step4473 p h) (sat_cons (step909 p h) (sat_nil p))))))))))))
def c5255 : List Lit := [(88, true), (1727, true), (97, true), (100, false), (1761, false), (107, true), (1643, true), (84, false), (83, false), (1680, false), (1580, false), (85, true)]
theorem step5255 (p : Nat → Bool) (h : Constraints p) : clause p c5255 = true :=
  Snake9.LocalRup.prove_clause [c5069, c1932, c1308, c1751, c5218, c1980, c5137, c1737, c4313, c4107, c4184, c3116, c4073, c1538, c1184, c1218, c5057, c1201, c5254, c1903, c963, c5063, c1314, c1750, c1031, c1038, c999, c4473, c1953, c4992, c909] c5255 (by decide) p (sat_cons (step5069 p h) (sat_cons (step1932 p h) (sat_cons (step1308 p h) (sat_cons (step1751 p h) (sat_cons (step5218 p h) (sat_cons (step1980 p h) (sat_cons (step5137 p h) (sat_cons (step1737 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4184 p h) (sat_cons (step3116 p h) (sat_cons (step4073 p h) (sat_cons (step1538 p h) (sat_cons (step1184 p h) (sat_cons (step1218 p h) (sat_cons (step5057 p h) (sat_cons (step1201 p h) (sat_cons (step5254 p h) (sat_cons (step1903 p h) (sat_cons (step963 p h) (sat_cons (step5063 p h) (sat_cons (step1314 p h) (sat_cons (step1750 p h) (sat_cons (step1031 p h) (sat_cons (step1038 p h) (sat_cons (step999 p h) (sat_cons (step4473 p h) (sat_cons (step1953 p h) (sat_cons (step4992 p h) (sat_cons (step909 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c5256 : List Lit := [(1661, false), (1695, true)]
theorem step5256 (p : Nat → Bool) (h : Constraints p) : clause p c5256 = true :=
  Snake9.LocalRup.prove_clause [c4972, c1166] c5256 (by decide) p (sat_cons (step4972 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c5257 : List Lit := [(1694, true), (1660, false)]
theorem step5257 (p : Nat → Bool) (h : Constraints p) : clause p c5257 = true :=
  Snake9.LocalRup.prove_clause [c4972, c1159] c5257 (by decide) p (sat_cons (step4972 p h) (sat_cons (step1159 p h) (sat_nil p)))
def c5258 : List Lit := [(1675, false), (1680, true)]
theorem step5258 (p : Nat → Bool) (h : Constraints p) : clause p c5258 = true :=
  Snake9.LocalRup.prove_clause [c4970, c1121] c5258 (by decide) p (sat_cons (step4970 p h) (sat_cons (step1121 p h) (sat_nil p)))
def c5259 : List Lit := [(1672, false), (1685, true)]
theorem step5259 (p : Nat → Bool) (h : Constraints p) : clause p c5259 = true :=
  Snake9.LocalRup.prove_clause [c4971, c1132] c5259 (by decide) p (sat_cons (step4971 p h) (sat_cons (step1132 p h) (sat_nil p)))
def c5260 : List Lit := [(1676, false), (1681, true)]
theorem step5260 (p : Nat → Bool) (h : Constraints p) : clause p c5260 = true :=
  Snake9.LocalRup.prove_clause [c4970, c1124] c5260 (by decide) p (sat_cons (step4970 p h) (sat_cons (step1124 p h) (sat_nil p)))
def c5261 : List Lit := [(107, false), (1695, true), (87, true), (85, false)]
theorem step5261 (p : Nat → Bool) (h : Constraints p) : clause p c5261 = true :=
  Snake9.LocalRup.prove_clause [c4970, c1921] c5261 (by decide) p (sat_cons (step4970 p h) (sat_cons (step1921 p h) (sat_nil p)))
def c5262 : List Lit := [(1600, true), (85, false), (1660, true), (1574, false), (1588, false), (1761, false), (1544, false), (13, false), (51, true)]
theorem step5262 (p : Nat → Bool) (h : Constraints p) : clause p c5262 = true :=
  Snake9.LocalRup.prove_clause [c4970, c1914] c5262 (by decide) p (sat_cons (step4970 p h) (sat_cons (step1914 p h) (sat_nil p)))
def c5263 : List Lit := [(1663, false), (1697, true)]
theorem step5263 (p : Nat → Bool) (h : Constraints p) : clause p c5263 = true :=
  Snake9.LocalRup.prove_clause [c4972, c1178] c5263 (by decide) p (sat_cons (step4972 p h) (sat_cons (step1178 p h) (sat_nil p)))
def c5264 : List Lit := [(1574, false), (85, false), (51, true), (1588, false), (1680, false), (1761, false), (1545, false)]
theorem step5264 (p : Nat → Bool) (h : Constraints p) : clause p c5264 = true :=
  Snake9.LocalRup.prove_clause [c4970, c1936] c5264 (by decide) p (sat_cons (step4970 p h) (sat_cons (step1936 p h) (sat_nil p)))
def c5265 : List Lit := [(1673, false), (1686, true)]
theorem step5265 (p : Nat → Bool) (h : Constraints p) : clause p c5265 = true :=
  Snake9.LocalRup.prove_clause [c4971, c1137] c5265 (by decide) p (sat_cons (step4971 p h) (sat_cons (step1137 p h) (sat_nil p)))
def c5266 : List Lit := [(1662, false), (1696, true)]
theorem step5266 (p : Nat → Bool) (h : Constraints p) : clause p c5266 = true :=
  Snake9.LocalRup.prove_clause [c4972, c1173] c5266 (by decide) p (sat_cons (step4972 p h) (sat_cons (step1173 p h) (sat_nil p)))
def c5267 : List Lit := [(1781, true), (1762, false)]
theorem step5267 (p : Nat → Bool) (h : Constraints p) : clause p c5267 = true :=
  Snake9.LocalRup.prove_clause [c4973, c1303] c5267 (by decide) p (sat_cons (step4973 p h) (sat_cons (step1303 p h) (sat_nil p)))
def c5268 : List Lit := [(1695, true), (85, false), (13, false)]
theorem step5268 (p : Nat → Bool) (h : Constraints p) : clause p c5268 = true :=
  Snake9.LocalRup.prove_clause [c4970, c1906] c5268 (by decide) p (sat_cons (step4970 p h) (sat_cons (step1906 p h) (sat_nil p)))
def c5269 : List Lit := [(1780, true), (1761, false)]
theorem step5269 (p : Nat → Bool) (h : Constraints p) : clause p c5269 = true :=
  Snake9.LocalRup.prove_clause [c4973, c1302] c5269 (by decide) p (sat_cons (step4973 p h) (sat_cons (step1302 p h) (sat_nil p)))
def c5270 : List Lit := [(83, true), (1695, true), (51, false)]
theorem step5270 (p : Nat → Bool) (h : Constraints p) : clause p c5270 = true :=
  Snake9.LocalRup.prove_clause [c4971, c2820] c5270 (by decide) p (sat_cons (step4971 p h) (sat_cons (step2820 p h) (sat_nil p)))
def c5271 : List Lit := [(1695, true), (70, true), (83, true)]
theorem step5271 (p : Nat → Bool) (h : Constraints p) : clause p c5271 = true :=
  Snake9.LocalRup.prove_clause [c4971, c2803] c5271 (by decide) p (sat_cons (step4971 p h) (sat_cons (step2803 p h) (sat_nil p)))
def c5272 : List Lit := [(13, true), (1609, false), (1643, false), (1760, false), (1534, false), (34, false), (83, true)]
theorem step5272 (p : Nat → Bool) (h : Constraints p) : clause p c5272 = true :=
  Snake9.LocalRup.prove_clause [c4971, c2741] c5272 (by decide) p (sat_cons (step4971 p h) (sat_cons (step2741 p h) (sat_nil p)))
def c5273 : List Lit := [(1695, true), (1643, false), (1680, false)]
theorem step5273 (p : Nat → Bool) (h : Constraints p) : clause p c5273 = true :=
  Snake9.LocalRup.prove_clause [c4972, c2726] c5273 (by decide) p (sat_cons (step4972 p h) (sat_cons (step2726 p h) (sat_nil p)))
def c5274 : List Lit := [(83, true), (1695, true), (1643, false)]
theorem step5274 (p : Nat → Bool) (h : Constraints p) : clause p c5274 = true :=
  Snake9.LocalRup.prove_clause [c4971, c2744] c5274 (by decide) p (sat_cons (step4971 p h) (sat_cons (step2744 p h) (sat_nil p)))
def c5275 : List Lit := [(13, true), (1761, false), (1675, false), (1534, false), (83, true), (1631, true), (1580, false), (1599, true)]
theorem step5275 (p : Nat → Bool) (h : Constraints p) : clause p c5275 = true :=
  Snake9.LocalRup.prove_clause [c4970, c2762] c5275 (by decide) p (sat_cons (step4970 p h) (sat_cons (step2762 p h) (sat_nil p)))
def c5276 : List Lit := [(70, true), (60, false), (1694, true)]
theorem step5276 (p : Nat → Bool) (h : Constraints p) : clause p c5276 = true :=
  Snake9.LocalRup.prove_clause [c4971, c2647] c5276 (by decide) p (sat_cons (step4971 p h) (sat_cons (step2647 p h) (sat_nil p)))
def c5277 : List Lit := [(60, false), (70, true), (67, true), (83, true), (1643, false), (1696, true)]
theorem step5277 (p : Nat → Bool) (h : Constraints p) : clause p c5277 = true :=
  Snake9.LocalRup.prove_clause [c4971, c2276] c5277 (by decide) p (sat_cons (step4971 p h) (sat_cons (step2276 p h) (sat_nil p)))
def c5278 : List Lit := [(100, false), (34, false), (1631, true), (1546, false), (1761, false), (84, false), (1643, true), (83, true), (1580, false)]
theorem step5278 (p : Nat → Bool) (h : Constraints p) : clause p c5278 = true :=
  Snake9.LocalRup.prove_clause [c4971, c2702] c5278 (by decide) p (sat_cons (step4971 p h) (sat_cons (step2702 p h) (sat_nil p)))
def c5279 : List Lit := [(1782, true), (1762, false), (1545, false), (83, true), (67, true)]
theorem step5279 (p : Nat → Bool) (h : Constraints p) : clause p c5279 = true :=
  Snake9.LocalRup.prove_clause [c4971, c3401] c5279 (by decide) p (sat_cons (step4971 p h) (sat_cons (step3401 p h) (sat_nil p)))
def c5280 : List Lit := [(48, false), (13, false), (1597, false), (34, false), (1672, false), (51, false), (1761, false), (1534, false), (1643, false), (85, false)]
theorem step5280 (p : Nat → Bool) (h : Constraints p) : clause p c5280 = true :=
  Snake9.LocalRup.prove_clause [c4970, c3493] c5280 (by decide) p (sat_cons (step4970 p h) (sat_cons (step3493 p h) (sat_nil p)))
def c5281 : List Lit := [(48, false), (85, false), (13, false), (1609, false), (83, true), (1534, false), (1760, false)]
theorem step5281 (p : Nat → Bool) (h : Constraints p) : clause p c5281 = true :=
  Snake9.LocalRup.prove_clause [c4970, c3599] c5281 (by decide) p (sat_cons (step4970 p h) (sat_cons (step3599 p h) (sat_nil p)))
def c5282 : List Lit := [(13, true), (1574, false), (1534, false), (1580, false), (1695, true), (1680, false), (1631, true)]
theorem step5282 (p : Nat → Bool) (h : Constraints p) : clause p c5282 = true :=
  Snake9.LocalRup.prove_clause [c4972, c2830] c5282 (by decide) p (sat_cons (step4972 p h) (sat_cons (step2830 p h) (sat_nil p)))
def c5283 : List Lit := [(48, false), (53, true), (85, false), (87, true), (1659, false), (1696, true), (1672, false)]
theorem step5283 (p : Nat → Bool) (h : Constraints p) : clause p c5283 = true :=
  Snake9.LocalRup.prove_clause [c4970, c3680] c5283 (by decide) p (sat_cons (step4970 p h) (sat_cons (step3680 p h) (sat_nil p)))
def c5284 : List Lit := [(1687, false), (1659, false), (1534, false), (13, false), (85, false), (48, false), (1761, false), (1608, false)]
theorem step5284 (p : Nat → Bool) (h : Constraints p) : clause p c5284 = true :=
  Snake9.LocalRup.prove_clause [c4970, c3057] c5284 (by decide) p (sat_cons (step4970 p h) (sat_cons (step3057 p h) (sat_nil p)))
def c5285 : List Lit := [(1574, false), (1761, false), (1580, false), (83, true), (1600, true), (1546, false)]
theorem step5285 (p : Nat → Bool) (h : Constraints p) : clause p c5285 = true :=
  Snake9.LocalRup.prove_clause [c4971, c2838] c5285 (by decide) p (sat_cons (step4971 p h) (sat_cons (step2838 p h) (sat_nil p)))
def c5286 : List Lit := [(52, false), (1687, false), (85, false), (53, true), (1761, false), (13, false), (48, false), (1534, false), (1608, false)]
theorem step5286 (p : Nat → Bool) (h : Constraints p) : clause p c5286 = true :=
  Snake9.LocalRup.prove_clause [c4970, c3074] c5286 (by decide) p (sat_cons (step4970 p h) (sat_cons (step3074 p h) (sat_nil p)))
def c5287 : List Lit := [(1741, false), (84, true), (107, true), (37, false), (1661, false), (1784, true), (97, true), (1737, true), (1556, true), (34, false)]
theorem step5287 (p : Nat → Bool) (h : Constraints p) : clause p c5287 = true :=
  Snake9.LocalRup.prove_clause [c4970, c4381] c5287 (by decide) p (sat_cons (step4970 p h) (sat_cons (step4381 p h) (sat_nil p)))
def c5288 : List Lit := [(1643, true), (48, false), (1694, true), (85, true)]
theorem step5288 (p : Nat → Bool) (h : Constraints p) : clause p c5288 = true :=
  Snake9.LocalRup.prove_clause [c4971, c4413] c5288 (by decide) p (sat_cons (step4971 p h) (sat_cons (step4413 p h) (sat_nil p)))
def c5289 : List Lit := [(47, false), (48, false), (1695, true), (53, false), (1685, false), (70, true)]
theorem step5289 (p : Nat → Bool) (h : Constraints p) : clause p c5289 = true :=
  Snake9.LocalRup.prove_clause [c4970, c4481] c5289 (by decide) p (sat_cons (step4970 p h) (sat_cons (step4481 p h) (sat_nil p)))
def c5290 : List Lit := [(1574, false), (1546, false), (1760, false), (1588, false), (1580, false), (83, true)]
theorem step5290 (p : Nat → Bool) (h : Constraints p) : clause p c5290 = true :=
  Snake9.LocalRup.prove_clause [c4971, c4537] c5290 (by decide) p (sat_cons (step4971 p h) (sat_cons (step4537 p h) (sat_nil p)))
def c5291 : List Lit := [(1694, true), (83, true)]
theorem step5291 (p : Nat → Bool) (h : Constraints p) : clause p c5291 = true :=
  Snake9.LocalRup.prove_clause [c4971, c4570] c5291 (by decide) p (sat_cons (step4971 p h) (sat_cons (step4570 p h) (sat_nil p)))
def c5292 : List Lit := [(1599, true), (67, true), (91, true), (51, true), (61, true), (1761, false), (60, false), (62, false), (84, false), (1675, false), (1580, false), (85, true)]
theorem step5292 (p : Nat → Bool) (h : Constraints p) : clause p c5292 = true :=
  Snake9.LocalRup.prove_clause [c1613, c4313, c4107, c4184, c5258, c1932, c1308, c1751, c1032, c1982, c5218, c5129, c1725, c1167, c1903, c4045, c963, c190, c5063, c1067, c1314, c3197, c1750, c1122, c5134, c1117, c1078, c394, c194, c1087, c1597, c1059, c159, c1056] c5292 (by decide) p (sat_cons (step1613 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4184 p h) (sat_cons (step5258 p h) (sat_cons (step1932 p h) (sat_cons (step1308 p h) (sat_cons (step1751 p h) (sat_cons (step1032 p h) (sat_cons (step1982 p h) (sat_cons (step5218 p h) (sat_cons (step5129 p h) (sat_cons (step1725 p h) (sat_cons (step1167 p h) (sat_cons (step1903 p h) (sat_cons (step4045 p h) (sat_cons (step963 p h) (sat_cons (step190 p h) (sat_cons (step5063 p h) (sat_cons (step1067 p h) (sat_cons (step1314 p h) (sat_cons (step3197 p h) (sat_cons (step1750 p h) (sat_cons (step1122 p h) (sat_cons (step5134 p h) (sat_cons (step1117 p h) (sat_cons (step1078 p h) (sat_cons (step394 p h) (sat_cons (step194 p h) (sat_cons (step1087 p h) (sat_cons (step1597 p h) (sat_cons (step1059 p h) (sat_cons (step159 p h) (sat_cons (step1056 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c5293 : List Lit := [(67, true), (91, true), (51, true), (61, true), (1761, false), (1643, true), (84, false), (1675, false), (1580, false), (85, true)]
theorem step5293 (p : Nat → Bool) (h : Constraints p) : clause p c5293 = true :=
  Snake9.LocalRup.prove_clause [c5258, c1932, c1308, c1751, c1054, c1053, c4313, c4107, c4184, c5292, c1981, c1031, c1039, c1750, c5085, c1314, c2625] c5293 (by decide) p (sat_cons (step5258 p h) (sat_cons (step1932 p h) (sat_cons (step1308 p h) (sat_cons (step1751 p h) (sat_cons (step1054 p h) (sat_cons (step1053 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4184 p h) (sat_cons (step5292 p h) (sat_cons (step1981 p h) (sat_cons (step1031 p h) (sat_cons (step1039 p h) (sat_cons (step1750 p h) (sat_cons (step5085 p h) (sat_cons (step1314 p h) (sat_cons (step2625 p h) (sat_nil p))))))))))))))))))
def c5294 : List Lit := [(67, false), (1761, false), (1685, false), (1598, false), (85, true)]
theorem step5294 (p : Nat → Bool) (h : Constraints p) : clause p c5294 = true :=
  Snake9.LocalRup.prove_clause [c5129, c1167, c2168, c2372, c1160, c5134, c1314, c1750] c5294 (by decide) p (sat_cons (step5129 p h) (sat_cons (step1167 p h) (sat_cons (step2168 p h) (sat_cons (step2372 p h) (sat_cons (step1160 p h) (sat_cons (step5134 p h) (sat_cons (step1314 p h) (sat_cons (step1750 p h) (sat_nil p)))))))))
def c5295 : List Lit := [(1727, true), (88, true), (100, false), (1761, false), (107, true), (1643, true), (84, false), (83, false), (1680, false), (1580, false), (85, true)]
theorem step5295 (p : Nat → Bool) (h : Constraints p) : clause p c5295 = true :=
  Snake9.LocalRup.prove_clause [c1199, c4421, c5255] c5295 (by decide) p (sat_cons (step1199 p h) (sat_cons (step4421 p h) (sat_cons (step5255 p h) (sat_nil p))))
def c5296 : List Lit := [(1762, false), (67, true), (1643, true), (1680, false), (1598, false), (85, true)]
theorem step5296 (p : Nat → Bool) (h : Constraints p) : clause p c5296 = true :=
  Snake9.LocalRup.prove_clause [c1932, c4313, c4107, c4379, c1749, c1980, c1315, c1309, c2625, c1750, c5085, c1038] c5296 (by decide) p (sat_cons (step1932 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4379 p h) (sat_cons (step1749 p h) (sat_cons (step1980 p h) (sat_cons (step1315 p h) (sat_cons (step1309 p h) (sat_cons (step2625 p h) (sat_cons (step1750 p h) (sat_cons (step5085 p h) (sat_cons (step1038 p h) (sat_nil p)))))))))))))
def c5297 : List Lit := [(100, false), (84, false), (83, false), (87, true), (1580, false), (85, true)]
theorem step5297 (p : Nat → Bool) (h : Constraints p) : clause p c5297 = true :=
  Snake9.LocalRup.prove_clause [c5218, c1112, c5258, c5247, c1725, c5253, c5294, c5296, c5137, c1737, c5129, c1167, c5244, c5252, c5069, c5246, c1289, c5295, c379, c384, c5293] c5297 (by decide) p (sat_cons (step5218 p h) (sat_cons (step1112 p h) (sat_cons (step5258 p h) (sat_cons (step5247 p h) (sat_cons (step1725 p h) (sat_cons (step5253 p h) (sat_cons (step5294 p h) (sat_cons (step5296 p h) (sat_cons (step5137 p h) (sat_cons (step1737 p h) (sat_cons (step5129 p h) (sat_cons (step1167 p h) (sat_cons (step5244 p h) (sat_cons (step5252 p h) (sat_cons (step5069 p h) (sat_cons (step5246 p h) (sat_cons (step1289 p h) (sat_cons (step5295 p h) (sat_cons (step379 p h) (sat_cons (step384 p h) (sat_cons (step5293 p h) (sat_nil p))))))))))))))))))))))
def c5298 : List Lit := [(1681, false), (1761, false), (1598, false), (85, true)]
theorem step5298 (p : Nat → Bool) (h : Constraints p) : clause p c5298 = true :=
  Snake9.LocalRup.prove_clause [c5129, c1726, c1930, c1161, c1314, c1082, c1750, c1078, c5134] c5298 (by decide) p (sat_cons (step5129 p h) (sat_cons (step1726 p h) (sat_cons (step1930 p h) (sat_cons (step1161 p h) (sat_cons (step1314 p h) (sat_cons (step1082 p h) (sat_cons (step1750 p h) (sat_cons (step1078 p h) (sat_cons (step5134 p h) (sat_nil p))))))))))
def c5299 : List Lit := [(1630, true), (105, false), (1580, false), (85, true)]
theorem step5299 (p : Nat → Bool) (h : Constraints p) : clause p c5299 = true :=
  Snake9.LocalRup.prove_clause [c5218, c1980, c5137, c1737, c4313, c4107, c4184, c1031, c1038, c999, c4473, c1953, c4992, c909] c5299 (by decide) p (sat_cons (step5218 p h) (sat_cons (step1980 p h) (sat_cons (step5137 p h) (sat_cons (step1737 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4184 p h) (sat_cons (step1031 p h) (sat_cons (step1038 p h) (sat_cons (step999 p h) (sat_cons (step4473 p h) (sat_cons (step1953 p h) (sat_cons (step4992 p h) (sat_cons (step909 p h) (sat_nil p)))))))))))))))
def c5300 : List Lit := [(105, false), (1761, false), (1643, true), (1680, false), (1580, false), (85, true)]
theorem step5300 (p : Nat → Bool) (h : Constraints p) : clause p c5300 = true :=
  Snake9.LocalRup.prove_clause [c5218, c1725, c5294, c1980, c1932, c1308, c1751, c1045, c5137, c1737, c5254, c5299, c1750, c1314, c2625, c5085, c4472, c1039, c909, c999, c1953, c4992] c5300 (by decide) p (sat_cons (step5218 p h) (sat_cons (step1725 p h) (sat_cons (step5294 p h) (sat_cons (step1980 p h) (sat_cons (step1932 p h) (sat_cons (step1308 p h) (sat_cons (step1751 p h) (sat_cons (step1045 p h) (sat_cons (step5137 p h) (sat_cons (step1737 p h) (sat_cons (step5254 p h) (sat_cons (step5299 p h) (sat_cons (step1750 p h) (sat_cons (step1314 p h) (sat_cons (step2625 p h) (sat_cons (step5085 p h) (sat_cons (step4472 p h) (sat_cons (step1039 p h) (sat_cons (step909 p h) (sat_cons (step999 p h) (sat_cons (step1953 p h) (sat_cons (step4992 p h) (sat_nil p)))))))))))))))))))))))
def c5301 : List Lit := [(84, false), (83, false), (87, true), (1580, false), (85, true)]
theorem step5301 (p : Nat → Bool) (h : Constraints p) : clause p c5301 = true :=
  Snake9.TreeRup.prove_clause [c5244, c1228, c5218, c5129, c1112, c5258, c1725, c1167, c1932, c5137, c1737, c4313, c4107, c4184, c4115, c5247, c1054, c5252, c5253, c1308, c1751, c1032, c1982, c5294, c5296, c5297, c3991, c1948, c1219, c5298, c1122, c5300, c1201, c4991, c1209, c1289, c1736, c1904, c2987, c1239, c1237, c1246, c1833, c1230, c1231, c1232, c641, c1841, c1197, c1198, c576, c4657, c906, c1117, c5096, c420, c1750, c1926, c1314, c1068, c1806] c5301 (by decide) p (sat_cons (step5244 p h) (sat_cons (step1228 p h) (sat_cons (step5218 p h) (sat_cons (step5129 p h) (sat_cons (step1112 p h) (sat_cons (step5258 p h) (sat_cons (step1725 p h) (sat_cons (step1167 p h) (sat_cons (step1932 p h) (sat_cons (step5137 p h) (sat_cons (step1737 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4184 p h) (sat_cons (step4115 p h) (sat_cons (step5247 p h) (sat_cons (step1054 p h) (sat_cons (step5252 p h) (sat_cons (step5253 p h) (sat_cons (step1308 p h) (sat_cons (step1751 p h) (sat_cons (step1032 p h) (sat_cons (step1982 p h) (sat_cons (step5294 p h) (sat_cons (step5296 p h) (sat_cons (step5297 p h) (sat_cons (step3991 p h) (sat_cons (step1948 p h) (sat_cons (step1219 p h) (sat_cons (step5298 p h) (sat_cons (step1122 p h) (sat_cons (step5300 p h) (sat_cons (step1201 p h) (sat_cons (step4991 p h) (sat_cons (step1209 p h) (sat_cons (step1289 p h) (sat_cons (step1736 p h) (sat_cons (step1904 p h) (sat_cons (step2987 p h) (sat_cons (step1239 p h) (sat_cons (step1237 p h) (sat_cons (step1246 p h) (sat_cons (step1833 p h) (sat_cons (step1230 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step641 p h) (sat_cons (step1841 p h) (sat_cons (step1197 p h) (sat_cons (step1198 p h) (sat_cons (step576 p h) (sat_cons (step4657 p h) (sat_cons (step906 p h) (sat_cons (step1117 p h) (sat_cons (step5096 p h) (sat_cons (step420 p h) (sat_cons (step1750 p h) (sat_cons (step1926 p h) (sat_cons (step1314 p h) (sat_cons (step1068 p h) (sat_cons (step1806 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5302 : List Lit := [(1681, false), (1685, false), (1598, false), (85, true)]
theorem step5302 (p : Nat → Bool) (h : Constraints p) : clause p c5302 = true :=
  Snake9.LocalRup.prove_clause [c5129, c4313, c4107, c4184, c1726, c1930, c3034, c5298, c1161, c1313, c1054, c2168, c1751, c1032, c5224, c1982, c1067, c3197] c5302 (by decide) p (sat_cons (step5129 p h) (sat_cons (step4313 p h) (sat_cons (step4107 p h) (sat_cons (step4184 p h) (sat_cons (step1726 p h) (sat_cons (step1930 p h) (sat_cons (step3034 p h) (sat_cons (step5298 p h) (sat_cons (step1161 p h) (sat_cons (step1313 p h) (sat_cons (step1054 p h) (sat_cons (step2168 p h) (sat_cons (step1751 p h) (sat_cons (step1032 p h) (sat_cons (step5224 p h) (sat_cons (step1982 p h) (sat_cons (step1067 p h) (sat_cons (step3197 p h) (sat_nil p)))))))))))))))))))
def c5303 : List Lit := [(87, true), (1580, false), (85, true)]
theorem step5303 (p : Nat → Bool) (h : Constraints p) : clause p c5303 = true :=
  Snake9.LocalRup.prove_clause [c5218, c5129, c1112, c5258, c1725, c1167, c5302, c5260, c1114, c5301, c5223, c2243, c3157] c5303 (by decide) p (sat_cons (step5218 p h) (sat_cons (step5129 p h) (sat_cons (step1112 p h) (sat_cons (step5258 p h) (sat_cons (step1725 p h) (sat_cons (step1167 p h) (sat_cons (step5302 p h) (sat_cons (step5260 p h) (sat_cons (step1114 p h) (sat_cons (step5301 p h) (sat_cons (step5223 p h) (sat_cons (step2243 p h) (sat_cons (step3157 p h) (sat_nil p))))))))))))))
end B112E186
