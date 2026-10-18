import B112E064Part0043
namespace B112E064
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4235 : List Lit := [(1489, true), (1545, true)]
theorem step4235 (p : Nat → Bool) (h : Constraints p) : clause p c4235 = true :=
  Snake9.LocalRup.prove_clause [c4152, c2036] c4235 (by decide) p (sat_cons (step4152 p h) (sat_cons (step2036 p h) (sat_nil p)))
def c4236 : List Lit := [(70, false), (72, false)]
theorem step4236 (p : Nat → Bool) (h : Constraints p) : clause p c4236 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3851, c340] c4236 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3851 p h) (sat_cons (step340 p h) (sat_nil p))))
def c4237 : List Lit := [(65, false), (70, false)]
theorem step4237 (p : Nat → Bool) (h : Constraints p) : clause p c4237 = true :=
  Snake9.LocalRup.prove_clause [c3851, c4152, c335] c4237 (by decide) p (sat_cons (step3851 p h) (sat_cons (step4152 p h) (sat_cons (step335 p h) (sat_nil p))))
def c4238 : List Lit := [(65, false), (51, false)]
theorem step4238 (p : Nat → Bool) (h : Constraints p) : clause p c4238 = true :=
  Snake9.LocalRup.prove_clause [c3851, c4152, c326] c4238 (by decide) p (sat_cons (step3851 p h) (sat_cons (step4152 p h) (sat_cons (step326 p h) (sat_nil p))))
def c4239 : List Lit := [(73, false), (53, false), (70, false)]
theorem step4239 (p : Nat → Bool) (h : Constraints p) : clause p c4239 = true :=
  Snake9.LocalRup.prove_clause [c3851, c348] c4239 (by decide) p (sat_cons (step3851 p h) (sat_cons (step348 p h) (sat_nil p)))
def c4240 : List Lit := [(79, false), (1568, false), (68, false), (1584, false), (1555, false), (1618, false), (1660, true)]
theorem step4240 (p : Nat → Bool) (h : Constraints p) : clause p c4240 = true :=
  Snake9.LocalRup.prove_clause [c4153, c1847] c4240 (by decide) p (sat_cons (step4153 p h) (sat_cons (step1847 p h) (sat_nil p)))
def c4241 : List Lit := [(74, false), (1626, true), (80, true)]
theorem step4241 (p : Nat → Bool) (h : Constraints p) : clause p c4241 = true :=
  Snake9.LocalRup.prove_clause [c4152, c1546] c4241 (by decide) p (sat_cons (step4152 p h) (sat_cons (step1546 p h) (sat_nil p)))
def c4242 : List Lit := [(86, false), (1543, true), (1558, true), (72, false)]
theorem step4242 (p : Nat → Bool) (h : Constraints p) : clause p c4242 = true :=
  Snake9.LocalRup.prove_clause [c4152, c2114] c4242 (by decide) p (sat_cons (step4152 p h) (sat_cons (step2114 p h) (sat_nil p)))
def c4243 : List Lit := [(80, false), (74, false), (60, false)]
theorem step4243 (p : Nat → Bool) (h : Constraints p) : clause p c4243 = true :=
  Snake9.LocalRup.prove_clause [c4152, c449] c4243 (by decide) p (sat_cons (step4152 p h) (sat_cons (step449 p h) (sat_nil p)))
def c4244 : List Lit := [(74, false), (110, false), (114, false)]
theorem step4244 (p : Nat → Bool) (h : Constraints p) : clause p c4244 = true :=
  Snake9.LocalRup.prove_clause [c4152, c2454] c4244 (by decide) p (sat_cons (step4152 p h) (sat_cons (step2454 p h) (sat_nil p)))
def c4245 : List Lit := [(1575, false), (1584, true)]
theorem step4245 (p : Nat → Bool) (h : Constraints p) : clause p c4245 = true :=
  Snake9.LocalRup.prove_clause [c4154, c1223] c4245 (by decide) p (sat_cons (step4154 p h) (sat_cons (step1223 p h) (sat_nil p)))
def c4246 : List Lit := [(115, false), (1632, true), (114, false), (1624, false)]
theorem step4246 (p : Nat → Bool) (h : Constraints p) : clause p c4246 = true :=
  Snake9.LocalRup.prove_clause [c4152, c1986] c4246 (by decide) p (sat_cons (step4152 p h) (sat_cons (step1986 p h) (sat_nil p)))
def c4247 : List Lit := [(1403, false), (1417, true)]
theorem step4247 (p : Nat → Bool) (h : Constraints p) : clause p c4247 = true :=
  Snake9.LocalRup.prove_clause [c4152, c2047] c4247 (by decide) p (sat_cons (step4152 p h) (sat_cons (step2047 p h) (sat_nil p)))
def c4248 : List Lit := [(72, false), (1489, true)]
theorem step4248 (p : Nat → Bool) (h : Constraints p) : clause p c4248 = true :=
  Snake9.LocalRup.prove_clause [c4152, c1640] c4248 (by decide) p (sat_cons (step4152 p h) (sat_cons (step1640 p h) (sat_nil p)))
def c4249 : List Lit := [(72, false), (1540, true)]
theorem step4249 (p : Nat → Bool) (h : Constraints p) : clause p c4249 = true :=
  Snake9.LocalRup.prove_clause [c4152, c1974] c4249 (by decide) p (sat_cons (step4152 p h) (sat_cons (step1974 p h) (sat_nil p)))
def c4250 : List Lit := [(72, false), (1545, true)]
theorem step4250 (p : Nat → Bool) (h : Constraints p) : clause p c4250 = true :=
  Snake9.LocalRup.prove_clause [c4152, c2153] c4250 (by decide) p (sat_cons (step4152 p h) (sat_cons (step2153 p h) (sat_nil p)))
def c4251 : List Lit := [(65, false), (72, false)]
theorem step4251 (p : Nat → Bool) (h : Constraints p) : clause p c4251 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3851, c337] c4251 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3851 p h) (sat_cons (step337 p h) (sat_nil p))))
def c4252 : List Lit := [(72, false), (5, false)]
theorem step4252 (p : Nat → Bool) (h : Constraints p) : clause p c4252 = true :=
  Snake9.LocalRup.prove_clause [c3851, c4152, c321] c4252 (by decide) p (sat_cons (step3851 p h) (sat_cons (step4152 p h) (sat_cons (step321 p h) (sat_nil p))))
def c4253 : List Lit := [(51, false), (72, false)]
theorem step4253 (p : Nat → Bool) (h : Constraints p) : clause p c4253 = true :=
  Snake9.LocalRup.prove_clause [c3851, c4152, c331] c4253 (by decide) p (sat_cons (step3851 p h) (sat_cons (step4152 p h) (sat_cons (step331 p h) (sat_nil p))))
def c4254 : List Lit := [(83, false), (80, false), (74, false)]
theorem step4254 (p : Nat → Bool) (h : Constraints p) : clause p c4254 = true :=
  Snake9.LocalRup.prove_clause [c4152, c460] c4254 (by decide) p (sat_cons (step4152 p h) (sat_cons (step460 p h) (sat_nil p)))
def c4255 : List Lit := [(105, false), (70, false)]
theorem step4255 (p : Nat → Bool) (h : Constraints p) : clause p c4255 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3851, c342] c4255 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3851 p h) (sat_cons (step342 p h) (sat_nil p))))
def c4256 : List Lit := [(65, false), (105, false)]
theorem step4256 (p : Nat → Bool) (h : Constraints p) : clause p c4256 = true :=
  Snake9.LocalRup.prove_clause [c3851, c4152, c339] c4256 (by decide) p (sat_cons (step3851 p h) (sat_cons (step4152 p h) (sat_cons (step339 p h) (sat_nil p))))
def c4257 : List Lit := [(51, false), (105, false)]
theorem step4257 (p : Nat → Bool) (h : Constraints p) : clause p c4257 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3851, c333] c4257 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3851 p h) (sat_cons (step333 p h) (sat_nil p))))
def c4258 : List Lit := [(72, false), (105, false)]
theorem step4258 (p : Nat → Bool) (h : Constraints p) : clause p c4258 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3851, c343] c4258 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3851 p h) (sat_cons (step343 p h) (sat_nil p))))
def c4259 : List Lit := [(51, false), (70, false)]
theorem step4259 (p : Nat → Bool) (h : Constraints p) : clause p c4259 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3851, c329] c4259 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3851 p h) (sat_cons (step329 p h) (sat_nil p))))
def c4260 : List Lit := [(53, false), (70, false), (107, false)]
theorem step4260 (p : Nat → Bool) (h : Constraints p) : clause p c4260 = true :=
  Snake9.LocalRup.prove_clause [c3851, c349] c4260 (by decide) p (sat_cons (step3851 p h) (sat_cons (step349 p h) (sat_nil p)))
def c4261 : List Lit := [(60, false), (80, true), (1490, true)]
theorem step4261 (p : Nat → Bool) (h : Constraints p) : clause p c4261 = true :=
  Snake9.LocalRup.prove_clause [c4152, c2071] c4261 (by decide) p (sat_cons (step4152 p h) (sat_cons (step2071 p h) (sat_nil p)))
def c4262 : List Lit := [(83, false), (80, false), (60, false)]
theorem step4262 (p : Nat → Bool) (h : Constraints p) : clause p c4262 = true :=
  Snake9.LocalRup.prove_clause [c4152, c454] c4262 (by decide) p (sat_cons (step4152 p h) (sat_cons (step454 p h) (sat_nil p)))
def c4263 : List Lit := [(80, false), (83, false), (114, false)]
theorem step4263 (p : Nat → Bool) (h : Constraints p) : clause p c4263 = true :=
  Snake9.LocalRup.prove_clause [c4152, c467] c4263 (by decide) p (sat_cons (step4152 p h) (sat_cons (step467 p h) (sat_nil p)))
def c4264 : List Lit := [(70, false), (5, false)]
theorem step4264 (p : Nat → Bool) (h : Constraints p) : clause p c4264 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3851, c319] c4264 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3851 p h) (sat_cons (step319 p h) (sat_nil p))))
def c4265 : List Lit := [(105, false), (5, false)]
theorem step4265 (p : Nat → Bool) (h : Constraints p) : clause p c4265 = true :=
  Snake9.LocalRup.prove_clause [c3851, c4152, c323] c4265 (by decide) p (sat_cons (step3851 p h) (sat_cons (step4152 p h) (sat_cons (step323 p h) (sat_nil p))))
def c4266 : List Lit := [(61, false), (60, false), (56, false)]
theorem step4266 (p : Nat → Bool) (h : Constraints p) : clause p c4266 = true :=
  Snake9.LocalRup.prove_clause [c4152, c276] c4266 (by decide) p (sat_cons (step4152 p h) (sat_cons (step276 p h) (sat_nil p)))
def c4267 : List Lit := [(65, false), (5, false)]
theorem step4267 (p : Nat → Bool) (h : Constraints p) : clause p c4267 = true :=
  Snake9.LocalRup.prove_clause [c3851, c4152, c316] c4267 (by decide) p (sat_cons (step3851 p h) (sat_cons (step4152 p h) (sat_cons (step316 p h) (sat_nil p))))
def c4268 : List Lit := [(51, false), (5, false)]
theorem step4268 (p : Nat → Bool) (h : Constraints p) : clause p c4268 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3851, c312] c4268 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3851 p h) (sat_cons (step312 p h) (sat_nil p))))
def c4269 : List Lit := [(1574, false), (1639, false), (114, false), (1447, false), (1585, true), (1545, false)]
theorem step4269 (p : Nat → Bool) (h : Constraints p) : clause p c4269 = true :=
  Snake9.LocalRup.prove_clause [c4152, c2918] c4269 (by decide) p (sat_cons (step4152 p h) (sat_cons (step2918 p h) (sat_nil p)))
def c4270 : List Lit := [(60, false), (1490, true), (114, false)]
theorem step4270 (p : Nat → Bool) (h : Constraints p) : clause p c4270 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3150] c4270 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3150 p h) (sat_nil p)))
def c4271 : List Lit := [(2, false), (1413, true), (13, true)]
theorem step4271 (p : Nat → Bool) (h : Constraints p) : clause p c4271 = true :=
  Snake9.LocalRup.prove_clause [c4152, c3812] c4271 (by decide) p (sat_cons (step4152 p h) (sat_cons (step3812 p h) (sat_nil p)))
def c4272 : List Lit := [(1545, true), (86, false), (1661, true)]
theorem step4272 (p : Nat → Bool) (h : Constraints p) : clause p c4272 = true :=
  Snake9.LocalRup.prove_clause [c3915, c2258, c4237, c1134] c4272 (by decide) p (sat_cons (step3915 p h) (sat_cons (step2258 p h) (sat_cons (step4237 p h) (sat_cons (step1134 p h) (sat_nil p)))))
def c4273 : List Lit := [(25, false), (1491, false), (1527, true), (5, true), (49, true)]
theorem step4273 (p : Nat → Bool) (h : Constraints p) : clause p c4273 = true :=
  Snake9.LocalRup.prove_clause [c1024, c1027, c1053, c1803, c1797, c1061, c3086, c1613, c1076, c1075, c1057, c1106, c1514, c2552, c920, c2216] c4273 (by decide) p (sat_cons (step1024 p h) (sat_cons (step1027 p h) (sat_cons (step1053 p h) (sat_cons (step1803 p h) (sat_cons (step1797 p h) (sat_cons (step1061 p h) (sat_cons (step3086 p h) (sat_cons (step1613 p h) (sat_cons (step1076 p h) (sat_cons (step1075 p h) (sat_cons (step1057 p h) (sat_cons (step1106 p h) (sat_cons (step1514 p h) (sat_cons (step2552 p h) (sat_cons (step920 p h) (sat_cons (step2216 p h) (sat_nil p)))))))))))))))))
def c4274 : List Lit := [(1491, false), (1474, true), (1448, true), (1527, true), (5, true), (49, true)]
theorem step4274 (p : Nat → Bool) (h : Constraints p) : clause p c4274 = true :=
  Snake9.LocalRup.prove_clause [c908, c4247, c979, c1803, c1797, c1024, c1061, c1033, c4273, c1454, c1456, c960, c963, c983, c946, c948, c3794, c3787, c944, c2056, c3056] c4274 (by decide) p (sat_cons (step908 p h) (sat_cons (step4247 p h) (sat_cons (step979 p h) (sat_cons (step1803 p h) (sat_cons (step1797 p h) (sat_cons (step1024 p h) (sat_cons (step1061 p h) (sat_cons (step1033 p h) (sat_cons (step4273 p h) (sat_cons (step1454 p h) (sat_cons (step1456 p h) (sat_cons (step960 p h) (sat_cons (step963 p h) (sat_cons (step983 p h) (sat_cons (step946 p h) (sat_cons (step948 p h) (sat_cons (step3794 p h) (sat_cons (step3787 p h) (sat_cons (step944 p h) (sat_cons (step2056 p h) (sat_cons (step3056 p h) (sat_nil p))))))))))))))))))))))
def c4275 : List Lit := [(1438, false), (16, false), (1472, false), (1490, false), (1448, true), (1527, true), (5, true), (49, true)]
theorem step4275 (p : Nat → Bool) (h : Constraints p) : clause p c4275 = true :=
  Snake9.LocalRup.prove_clause [c908, c4247, c911, c978, c983, c1106, c3787, c936, c1075, c4271, c1056, c1514] c4275 (by decide) p (sat_cons (step908 p h) (sat_cons (step4247 p h) (sat_cons (step911 p h) (sat_cons (step978 p h) (sat_cons (step983 p h) (sat_cons (step1106 p h) (sat_cons (step3787 p h) (sat_cons (step936 p h) (sat_cons (step1075 p h) (sat_cons (step4271 p h) (sat_cons (step1056 p h) (sat_cons (step1514 p h) (sat_nil p)))))))))))))
def c4276 : List Lit := [(1418, true), (19, false), (16, false), (1464, false), (1474, true), (5, true)]
theorem step4276 (p : Nat → Bool) (h : Constraints p) : clause p c4276 = true :=
  Snake9.LocalRup.prove_clause [c3794, c3787, c3056] c4276 (by decide) p (sat_cons (step3794 p h) (sat_cons (step3787 p h) (sat_cons (step3056 p h) (sat_nil p))))
def c4277 : List Lit := [(1464, false), (1490, false), (1448, true), (1527, true), (1489, false), (5, true), (72, true), (66, false), (1545, false), (86, false), (49, true)]
theorem step4277 (p : Nat → Bool) (h : Constraints p) : clause p c4277 = true :=
  Snake9.LocalRup.prove_clause [c1803, c1024, c1027, c1052, c1086, c4175, c1613, c4234, c1076, c1060, c4110, c1282, c4275, c1459, c946, c944, c4276, c1464, c1106, c2061, c2137, c4197, c1663, c507] c4277 (by decide) p (sat_cons (step1803 p h) (sat_cons (step1024 p h) (sat_cons (step1027 p h) (sat_cons (step1052 p h) (sat_cons (step1086 p h) (sat_cons (step4175 p h) (sat_cons (step1613 p h) (sat_cons (step4234 p h) (sat_cons (step1076 p h) (sat_cons (step1060 p h) (sat_cons (step4110 p h) (sat_cons (step1282 p h) (sat_cons (step4275 p h) (sat_cons (step1459 p h) (sat_cons (step946 p h) (sat_cons (step944 p h) (sat_cons (step4276 p h) (sat_cons (step1464 p h) (sat_cons (step1106 p h) (sat_cons (step2061 p h) (sat_cons (step2137 p h) (sat_cons (step4197 p h) (sat_cons (step1663 p h) (sat_cons (step507 p h) (sat_nil p)))))))))))))))))))))))))
def c4278 : List Lit := [(1490, false), (1448, true), (1527, true), (1489, false), (5, true), (72, true), (66, false), (1545, false), (86, false), (49, true)]
theorem step4278 (p : Nat → Bool) (h : Constraints p) : clause p c4278 = true :=
  Snake9.LocalRup.prove_clause [c908, c4247, c1024, c4277, c997, c1495, c1999, c2057, c978, c1106, c1796, c1060, c1033, c1031, c2084, c1026] c4278 (by decide) p (sat_cons (step908 p h) (sat_cons (step4247 p h) (sat_cons (step1024 p h) (sat_cons (step4277 p h) (sat_cons (step997 p h) (sat_cons (step1495 p h) (sat_cons (step1999 p h) (sat_cons (step2057 p h) (sat_cons (step978 p h) (sat_cons (step1106 p h) (sat_cons (step1796 p h) (sat_cons (step1060 p h) (sat_cons (step1033 p h) (sat_cons (step1031 p h) (sat_cons (step2084 p h) (sat_cons (step1026 p h) (sat_nil p)))))))))))))))))
def c4279 : List Lit := [(1540, true), (86, false), (1506, false), (49, true)]
theorem step4279 (p : Nat → Bool) (h : Constraints p) : clause p c4279 = true :=
  Snake9.LocalRup.prove_clause [c1801, c1819, c4272, c2365, c1133, c1134, c4249, c4267, c4256, c4238, c4237, c2259, c1035, c1309, c1043, c1333, c1821, c1112, c4278, c1046, c3859, c1498, c1037, c790, c249, c2408, c791, c235, c798, c784, c1783, c786, c787] c4279 (by decide) p (sat_cons (step1801 p h) (sat_cons (step1819 p h) (sat_cons (step4272 p h) (sat_cons (step2365 p h) (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step4249 p h) (sat_cons (step4267 p h) (sat_cons (step4256 p h) (sat_cons (step4238 p h) (sat_cons (step4237 p h) (sat_cons (step2259 p h) (sat_cons (step1035 p h) (sat_cons (step1309 p h) (sat_cons (step1043 p h) (sat_cons (step1333 p h) (sat_cons (step1821 p h) (sat_cons (step1112 p h) (sat_cons (step4278 p h) (sat_cons (step1046 p h) (sat_cons (step3859 p h) (sat_cons (step1498 p h) (sat_cons (step1037 p h) (sat_cons (step790 p h) (sat_cons (step249 p h) (sat_cons (step2408 p h) (sat_cons (step791 p h) (sat_cons (step235 p h) (sat_cons (step798 p h) (sat_cons (step784 p h) (sat_cons (step1783 p h) (sat_cons (step786 p h) (sat_cons (step787 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c4280 : List Lit := [(1490, true), (65, false), (49, true)]
theorem step4280 (p : Nat → Bool) (h : Constraints p) : clause p c4280 = true :=
  Snake9.LocalRup.prove_clause [c4237, c4238, c1046, c3859, c1498, c1037, c790, c249, c2408, c791, c235, c798, c784, c1783, c786, c787] c4280 (by decide) p (sat_cons (step4237 p h) (sat_cons (step4238 p h) (sat_cons (step1046 p h) (sat_cons (step3859 p h) (sat_cons (step1498 p h) (sat_cons (step1037 p h) (sat_cons (step790 p h) (sat_cons (step249 p h) (sat_cons (step2408 p h) (sat_cons (step791 p h) (sat_cons (step235 p h) (sat_cons (step798 p h) (sat_cons (step784 p h) (sat_cons (step1783 p h) (sat_cons (step786 p h) (sat_cons (step787 p h) (sat_nil p)))))))))))))))))
def c4281 : List Lit := [(53, true), (52, false), (50, false)]
theorem step4281 (p : Nat → Bool) (h : Constraints p) : clause p c4281 = true :=
  Snake9.LocalRup.prove_clause [c255, c1530, c1703, c254] c4281 (by decide) p (sat_cons (step255 p h) (sat_cons (step1530 p h) (sat_cons (step1703 p h) (sat_cons (step254 p h) (sat_nil p)))))
def c4282 : List Lit := [(52, false), (50, false), (65, false), (49, true)]
theorem step4282 (p : Nat → Bool) (h : Constraints p) : clause p c4282 = true :=
  Snake9.LocalRup.prove_clause [c4237, c4238, c4281, c253, c2408, c790, c235, c791, c784, c798, c786, c1783, c787] c4282 (by decide) p (sat_cons (step4237 p h) (sat_cons (step4238 p h) (sat_cons (step4281 p h) (sat_cons (step253 p h) (sat_cons (step2408 p h) (sat_cons (step790 p h) (sat_cons (step235 p h) (sat_cons (step791 p h) (sat_cons (step784 p h) (sat_cons (step798 p h) (sat_cons (step786 p h) (sat_cons (step1783 p h) (sat_cons (step787 p h) (sat_nil p))))))))))))))
def c4283 : List Lit := [(345, false), (1496, false), (1604, true), (1632, true), (1584, false), (70, true), (105, true)]
theorem step4283 (p : Nat → Bool) (h : Constraints p) : clause p c4283 = true :=
  Snake9.LocalRup.prove_clause [c1270, c809, c1568, c1791, c898, c894, c892, c880, c879, c875, c596, c3157, c4145, c4109, c1285, c997, c1495, c1282, c210] c4283 (by decide) p (sat_cons (step1270 p h) (sat_cons (step809 p h) (sat_cons (step1568 p h) (sat_cons (step1791 p h) (sat_cons (step898 p h) (sat_cons (step894 p h) (sat_cons (step892 p h) (sat_cons (step880 p h) (sat_cons (step879 p h) (sat_cons (step875 p h) (sat_cons (step596 p h) (sat_cons (step3157 p h) (sat_cons (step4145 p h) (sat_cons (step4109 p h) (sat_cons (step1285 p h) (sat_cons (step997 p h) (sat_cons (step1495 p h) (sat_cons (step1282 p h) (sat_cons (step210 p h) (sat_nil p))))))))))))))))))))
def c4284 : List Lit := [(50, false), (48, true), (164, true), (66, true), (65, false), (49, true)]
theorem step4284 (p : Nat → Bool) (h : Constraints p) : clause p c4284 = true :=
  Snake9.LocalRup.prove_clause [c4282, c231, c1700] c4284 (by decide) p (sat_cons (step4282 p h) (sat_cons (step231 p h) (sat_cons (step1700 p h) (sat_nil p))))
def c4285 : List Lit := [(65, false), (68, true), (86, false), (1506, false), (49, true)]
theorem step4285 (p : Nat → Bool) (h : Constraints p) : clause p c4285 = true :=
  Snake9.LocalRup.prove_clause [c4279, c1801, c1819, c4272, c4267, c4251, c4256, c4238, c4237, c1166, c1270, c1035, c1138, c1173, c1272, c1043, c1143, c1297, c3101, c1308, c1339, c1341, c1821, c1310, c1317, c1803, c1112, c1299, c1262, c2214, c1055, c1086, c4274, c4280, c4278, c1056, c4283, c804, c800, c802, c798, c787, c791, c786, c784, c785, c235, c4284, c790, c1037, c232, c253, c1047, c1705, c1039] c4285 (by decide) p (sat_cons (step4279 p h) (sat_cons (step1801 p h) (sat_cons (step1819 p h) (sat_cons (step4272 p h) (sat_cons (step4267 p h) (sat_cons (step4251 p h) (sat_cons (step4256 p h) (sat_cons (step4238 p h) (sat_cons (step4237 p h) (sat_cons (step1166 p h) (sat_cons (step1270 p h) (sat_cons (step1035 p h) (sat_cons (step1138 p h) (sat_cons (step1173 p h) (sat_cons (step1272 p h) (sat_cons (step1043 p h) (sat_cons (step1143 p h) (sat_cons (step1297 p h) (sat_cons (step3101 p h) (sat_cons (step1308 p h) (sat_cons (step1339 p h) (sat_cons (step1341 p h) (sat_cons (step1821 p h) (sat_cons (step1310 p h) (sat_cons (step1317 p h) (sat_cons (step1803 p h) (sat_cons (step1112 p h) (sat_cons (step1299 p h) (sat_cons (step1262 p h) (sat_cons (step2214 p h) (sat_cons (step1055 p h) (sat_cons (step1086 p h) (sat_cons (step4274 p h) (sat_cons (step4280 p h) (sat_cons (step4278 p h) (sat_cons (step1056 p h) (sat_cons (step4283 p h) (sat_cons (step804 p h) (sat_cons (step800 p h) (sat_cons (step802 p h) (sat_cons (step798 p h) (sat_cons (step787 p h) (sat_cons (step791 p h) (sat_cons (step786 p h) (sat_cons (step784 p h) (sat_cons (step785 p h) (sat_cons (step235 p h) (sat_cons (step4284 p h) (sat_cons (step790 p h) (sat_cons (step1037 p h) (sat_cons (step232 p h) (sat_cons (step253 p h) (sat_cons (step1047 p h) (sat_cons (step1705 p h) (sat_cons (step1039 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c4286 : List Lit := [(1527, true), (5, true), (1491, false), (1495, false), (1506, false), (49, true)]
theorem step4286 (p : Nat → Bool) (h : Constraints p) : clause p c4286 = true :=
  Snake9.LocalRup.prove_clause [c1803, c1112, c1086, c4274] c4286 (by decide) p (sat_cons (step1803 p h) (sat_cons (step1112 p h) (sat_cons (step1086 p h) (sat_cons (step4274 p h) (sat_nil p)))))
def c4287 : List Lit := [(1658, true), (1545, false)]
theorem step4287 (p : Nat → Bool) (h : Constraints p) : clause p c4287 = true :=
  Snake9.LocalRup.prove_clause [c2365, c1338, c1332, c4199, c1308, c1270, c1297, c1272] c4287 (by decide) p (sat_cons (step2365 p h) (sat_cons (step1338 p h) (sat_cons (step1332 p h) (sat_cons (step4199 p h) (sat_cons (step1308 p h) (sat_cons (step1270 p h) (sat_cons (step1297 p h) (sat_cons (step1272 p h) (sat_nil p)))))))))
def c4288 : List Lit := [(1631, true), (1551, true), (105, true), (65, true), (1542, false), (86, false)]
theorem step4288 (p : Nat → Bool) (h : Constraints p) : clause p c4288 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1272, c2259, c1298, c1135, c1285, c1145, c1282, c1154, c1552] c4288 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1272 p h) (sat_cons (step2259 p h) (sat_cons (step1298 p h) (sat_cons (step1135 p h) (sat_cons (step1285 p h) (sat_cons (step1145 p h) (sat_cons (step1282 p h) (sat_cons (step1154 p h) (sat_cons (step1552 p h) (sat_nil p)))))))))))
def c4289 : List Lit := [(1546, false), (1584, true)]
theorem step4289 (p : Nat → Bool) (h : Constraints p) : clause p c4289 = true :=
  Snake9.LocalRup.prove_clause [c3101, c2931, c1173, c1165] c4289 (by decide) p (sat_cons (step3101 p h) (sat_cons (step2931 p h) (sat_cons (step1173 p h) (sat_cons (step1165 p h) (sat_nil p)))))
def c4290 : List Lit := [(1584, true), (105, true), (68, true), (86, false), (1506, false), (49, true)]
theorem step4290 (p : Nat → Bool) (h : Constraints p) : clause p c4290 = true :=
  Snake9.LocalRup.prove_clause [c4285, c1137, c4279, c1801, c1819, c4272, c2365, c1810, c4228, c4288, c1309, c1333, c1821, c1112, c4289, c1143, c1145, c1138, c1135, c1517, c4236, c4259, c4278, c4197, c1035, c1046, c1044, c1037, c1039, c230, c254, c1699] c4290 (by decide) p (sat_cons (step4285 p h) (sat_cons (step1137 p h) (sat_cons (step4279 p h) (sat_cons (step1801 p h) (sat_cons (step1819 p h) (sat_cons (step4272 p h) (sat_cons (step2365 p h) (sat_cons (step1810 p h) (sat_cons (step4228 p h) (sat_cons (step4288 p h) (sat_cons (step1309 p h) (sat_cons (step1333 p h) (sat_cons (step1821 p h) (sat_cons (step1112 p h) (sat_cons (step4289 p h) (sat_cons (step1143 p h) (sat_cons (step1145 p h) (sat_cons (step1138 p h) (sat_cons (step1135 p h) (sat_cons (step1517 p h) (sat_cons (step4236 p h) (sat_cons (step4259 p h) (sat_cons (step4278 p h) (sat_cons (step4197 p h) (sat_cons (step1035 p h) (sat_cons (step1046 p h) (sat_cons (step1044 p h) (sat_cons (step1037 p h) (sat_cons (step1039 p h) (sat_cons (step230 p h) (sat_cons (step254 p h) (sat_cons (step1699 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c4291 : List Lit := [(1546, true), (105, true), (68, true), (86, false), (1506, false), (49, true)]
theorem step4291 (p : Nat → Bool) (h : Constraints p) : clause p c4291 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1272, c1801, c1819, c4290, c1341, c1310, c1299, c2214, c1306, c1297, c1308, c1339, c1821, c1112, c4285, c1137, c4279, c4272, c1143, c1145, c1138, c1135, c1517, c4236, c4264, c4259, c2259, c1055, c4278, c908, c1309, c1498, c4247, c1340, c4260, c1820, c3157, c1523, c1802, c1105, c1080, c978, c3940, c1999] c4291 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1272 p h) (sat_cons (step1801 p h) (sat_cons (step1819 p h) (sat_cons (step4290 p h) (sat_cons (step1341 p h) (sat_cons (step1310 p h) (sat_cons (step1299 p h) (sat_cons (step2214 p h) (sat_cons (step1306 p h) (sat_cons (step1297 p h) (sat_cons (step1308 p h) (sat_cons (step1339 p h) (sat_cons (step1821 p h) (sat_cons (step1112 p h) (sat_cons (step4285 p h) (sat_cons (step1137 p h) (sat_cons (step4279 p h) (sat_cons (step4272 p h) (sat_cons (step1143 p h) (sat_cons (step1145 p h) (sat_cons (step1138 p h) (sat_cons (step1135 p h) (sat_cons (step1517 p h) (sat_cons (step4236 p h) (sat_cons (step4264 p h) (sat_cons (step4259 p h) (sat_cons (step2259 p h) (sat_cons (step1055 p h) (sat_cons (step4278 p h) (sat_cons (step908 p h) (sat_cons (step1309 p h) (sat_cons (step1498 p h) (sat_cons (step4247 p h) (sat_cons (step1340 p h) (sat_cons (step4260 p h) (sat_cons (step1820 p h) (sat_cons (step3157 p h) (sat_cons (step1523 p h) (sat_cons (step1802 p h) (sat_cons (step1105 p h) (sat_cons (step1080 p h) (sat_cons (step978 p h) (sat_cons (step3940 p h) (sat_cons (step1999 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c4292 : List Lit := [(5, true), (1474, true), (1447, true)]
theorem step4292 (p : Nat → Bool) (h : Constraints p) : clause p c4292 = true :=
  Snake9.LocalRup.prove_clause [c1464, c908, c4247, c978, c1459, c1999, c946, c948, c944, c4276] c4292 (by decide) p (sat_cons (step1464 p h) (sat_cons (step908 p h) (sat_cons (step4247 p h) (sat_cons (step978 p h) (sat_cons (step1459 p h) (sat_cons (step1999 p h) (sat_cons (step946 p h) (sat_cons (step948 p h) (sat_cons (step944 p h) (sat_cons (step4276 p h) (sat_nil p)))))))))))
def c4293 : List Lit := [(1490, true), (70, true), (72, true), (51, true), (66, false), (1546, false), (1625, true), (1539, true), (1585, true), (86, false)]
theorem step4293 (p : Nat → Bool) (h : Constraints p) : clause p c4293 = true :=
  Snake9.LocalRup.prove_clause [c4219, c4270, c1920, c1284, c1239, c1552, c1154] c4293 (by decide) p (sat_cons (step4219 p h) (sat_cons (step4270 p h) (sat_cons (step1920 p h) (sat_cons (step1284 p h) (sat_cons (step1239 p h) (sat_cons (step1552 p h) (sat_cons (step1154 p h) (sat_nil p))))))))
def c4294 : List Lit := [(66, false), (1546, false), (1482, false), (1584, false), (105, true), (86, false), (1506, false), (1479, false)]
theorem step4294 (p : Nat → Bool) (h : Constraints p) : clause p c4294 = true :=
  Snake9.LocalRup.prove_clause [c1054, c1270, c1272, c1801, c1819, c1341, c1310, c1299, c1286, c4272, c4175, c1811, c1163, c2259, c1309, c1340, c1820, c1802, c1105, c1796, c1085, c2240, c4292, c4268, c4252, c4264, c4293, c1056, c1060, c1075, c1033, c1613, c2056, c2054, c948, c1454, c963, c1456] c4294 (by decide) p (sat_cons (step1054 p h) (sat_cons (step1270 p h) (sat_cons (step1272 p h) (sat_cons (step1801 p h) (sat_cons (step1819 p h) (sat_cons (step1341 p h) (sat_cons (step1310 p h) (sat_cons (step1299 p h) (sat_cons (step1286 p h) (sat_cons (step4272 p h) (sat_cons (step4175 p h) (sat_cons (step1811 p h) (sat_cons (step1163 p h) (sat_cons (step2259 p h) (sat_cons (step1309 p h) (sat_cons (step1340 p h) (sat_cons (step1820 p h) (sat_cons (step1802 p h) (sat_cons (step1105 p h) (sat_cons (step1796 p h) (sat_cons (step1085 p h) (sat_cons (step2240 p h) (sat_cons (step4292 p h) (sat_cons (step4268 p h) (sat_cons (step4252 p h) (sat_cons (step4264 p h) (sat_cons (step4293 p h) (sat_cons (step1056 p h) (sat_cons (step1060 p h) (sat_cons (step1075 p h) (sat_cons (step1033 p h) (sat_cons (step1613 p h) (sat_cons (step2056 p h) (sat_cons (step2054 p h) (sat_cons (step948 p h) (sat_cons (step1454 p h) (sat_cons (step963 p h) (sat_cons (step1456 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c4295 : List Lit := [(5, false), (1541, false), (68, true), (1585, true)]
theorem step4295 (p : Nat → Bool) (h : Constraints p) : clause p c4295 = true :=
  Snake9.LocalRup.prove_clause [c1811, c4252, c4264, c1166, c1138, c1173, c1146, c1150, c1155, c1239, c1946] c4295 (by decide) p (sat_cons (step1811 p h) (sat_cons (step4252 p h) (sat_cons (step4264 p h) (sat_cons (step1166 p h) (sat_cons (step1138 p h) (sat_cons (step1173 p h) (sat_cons (step1146 p h) (sat_cons (step1150 p h) (sat_cons (step1155 p h) (sat_cons (step1239 p h) (sat_cons (step1946 p h) (sat_nil p))))))))))))
def c4296 : List Lit := [(1547, false), (1559, false), (1585, true)]
theorem step4296 (p : Nat → Bool) (h : Constraints p) : clause p c4296 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1150, c1155, c1239, c1946] c4296 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1150 p h) (sat_cons (step1155 p h) (sat_cons (step1239 p h) (sat_cons (step1946 p h) (sat_nil p))))))
def c4297 : List Lit := [(70, false), (5, true), (1482, false), (1584, false), (105, true), (1506, false)]
theorem step4297 (p : Nat → Bool) (h : Constraints p) : clause p c4297 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1272, c1297, c1308, c1339, c1821, c1803, c1517, c4259, c1055, c1086, c4292, c1105, c1106, c1820, c1080, c1340, c1309, c1302, c2854, c1298, c1275, c1285, c1267, c1282, c3940, c4025, c1873, c1498, c4260] c4297 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1272 p h) (sat_cons (step1297 p h) (sat_cons (step1308 p h) (sat_cons (step1339 p h) (sat_cons (step1821 p h) (sat_cons (step1803 p h) (sat_cons (step1517 p h) (sat_cons (step4259 p h) (sat_cons (step1055 p h) (sat_cons (step1086 p h) (sat_cons (step4292 p h) (sat_cons (step1105 p h) (sat_cons (step1106 p h) (sat_cons (step1820 p h) (sat_cons (step1080 p h) (sat_cons (step1340 p h) (sat_cons (step1309 p h) (sat_cons (step1302 p h) (sat_cons (step2854 p h) (sat_cons (step1298 p h) (sat_cons (step1275 p h) (sat_cons (step1285 p h) (sat_cons (step1267 p h) (sat_cons (step1282 p h) (sat_cons (step3940 p h) (sat_cons (step4025 p h) (sat_cons (step1873 p h) (sat_cons (step1498 p h) (sat_cons (step4260 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c4298 : List Lit := [(1547, false), (1585, true)]
theorem step4298 (p : Nat → Bool) (h : Constraints p) : clause p c4298 = true :=
  Snake9.LocalRup.prove_clause [c2484, c4296, c1165, c1173] c4298 (by decide) p (sat_cons (step2484 p h) (sat_cons (step4296 p h) (sat_cons (step1165 p h) (sat_cons (step1173 p h) (sat_nil p)))))
end B112E064
