import B112E064Part0045
namespace B112E064
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4363 : List Lit := [(116, true), (74, false), (1627, true)]
theorem step4363 (p : Nat → Bool) (h : Constraints p) : clause p c4363 = true :=
  Snake9.LocalRup.prove_clause [c1286, c1282, c1284, c1288, c4244, c1280] c4363 (by decide) p (sat_cons (step1286 p h) (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_cons (step1288 p h) (sat_cons (step4244 p h) (sat_cons (step1280 p h) (sat_nil p)))))))
def c4364 : List Lit := [(74, false), (1660, true), (1546, true), (70, true)]
theorem step4364 (p : Nat → Bool) (h : Constraints p) : clause p c4364 = true :=
  Snake9.LocalRup.prove_clause [c4356, c4355, c1801, c1819, c3915, c4361, c4322, c1136, c1145, c4362, c1135, c1340, c1309, c2259, c4265, c4359, c1269, c1294, c1134, c4360, c4337, c1166, c4363, c1552, c1545, c4357, c1266, c2249, c1274, c1183, c1298, c4254, c4241] c4364 (by decide) p (sat_cons (step4356 p h) (sat_cons (step4355 p h) (sat_cons (step1801 p h) (sat_cons (step1819 p h) (sat_cons (step3915 p h) (sat_cons (step4361 p h) (sat_cons (step4322 p h) (sat_cons (step1136 p h) (sat_cons (step1145 p h) (sat_cons (step4362 p h) (sat_cons (step1135 p h) (sat_cons (step1340 p h) (sat_cons (step1309 p h) (sat_cons (step2259 p h) (sat_cons (step4265 p h) (sat_cons (step4359 p h) (sat_cons (step1269 p h) (sat_cons (step1294 p h) (sat_cons (step1134 p h) (sat_cons (step4360 p h) (sat_cons (step4337 p h) (sat_cons (step1166 p h) (sat_cons (step4363 p h) (sat_cons (step1552 p h) (sat_cons (step1545 p h) (sat_cons (step4357 p h) (sat_cons (step1266 p h) (sat_cons (step2249 p h) (sat_cons (step1274 p h) (sat_cons (step1183 p h) (sat_cons (step1298 p h) (sat_cons (step4254 p h) (sat_cons (step4241 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c4365 : List Lit := [(1561, false), (1545, false)]
theorem step4365 (p : Nat → Bool) (h : Constraints p) : clause p c4365 = true :=
  Snake9.LocalRup.prove_clause [c4175, c1148, c1229, c1806, c1208, c1234, c2249, c1153, c1945] c4365 (by decide) p (sat_cons (step4175 p h) (sat_cons (step1148 p h) (sat_cons (step1229 p h) (sat_cons (step1806 p h) (sat_cons (step1208 p h) (sat_cons (step1234 p h) (sat_cons (step2249 p h) (sat_cons (step1153 p h) (sat_cons (step1945 p h) (sat_nil p))))))))))
def c4366 : List Lit := [(41, false), (116, false), (45, false), (1483, true)]
theorem step4366 (p : Nat → Bool) (h : Constraints p) : clause p c4366 = true :=
  Snake9.LocalRup.prove_clause [c3623, c219] c4366 (by decide) p (sat_cons (step3623 p h) (sat_cons (step219 p h) (sat_nil p)))
def c4367 : List Lit := [(116, false), (1483, true), (1585, true), (1545, false)]
theorem step4367 (p : Nat → Bool) (h : Constraints p) : clause p c4367 = true :=
  Snake9.LocalRup.prove_clause [c4110, c4234, c997, c1495, c4366] c4367 (by decide) p (sat_cons (step4110 p h) (sat_cons (step4234 p h) (sat_cons (step997 p h) (sat_cons (step1495 p h) (sat_cons (step4366 p h) (sat_nil p))))))
def c4368 : List Lit := [(1546, true), (70, true)]
theorem step4368 (p : Nat → Bool) (h : Constraints p) : clause p c4368 = true :=
  Snake9.LocalRup.prove_clause [c4355, c1801, c1819, c3915, c4365, c4360, c4356, c1049, c4175, c4361, c4322, c1341, c1310, c4362, c1134, c4331, c1177, c1167, c4364, c1820, c1802, c4314, c1796, c4265, c1060, c1270, c1272, c1299, c4363, c4367] c4368 (by decide) p (sat_cons (step4355 p h) (sat_cons (step1801 p h) (sat_cons (step1819 p h) (sat_cons (step3915 p h) (sat_cons (step4365 p h) (sat_cons (step4360 p h) (sat_cons (step4356 p h) (sat_cons (step1049 p h) (sat_cons (step4175 p h) (sat_cons (step4361 p h) (sat_cons (step4322 p h) (sat_cons (step1341 p h) (sat_cons (step1310 p h) (sat_cons (step4362 p h) (sat_cons (step1134 p h) (sat_cons (step4331 p h) (sat_cons (step1177 p h) (sat_cons (step1167 p h) (sat_cons (step4364 p h) (sat_cons (step1820 p h) (sat_cons (step1802 p h) (sat_cons (step4314 p h) (sat_cons (step1796 p h) (sat_cons (step4265 p h) (sat_cons (step1060 p h) (sat_cons (step1270 p h) (sat_cons (step1272 p h) (sat_cons (step1299 p h) (sat_cons (step4363 p h) (sat_cons (step4367 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c4369 : List Lit := [(1546, false), (1585, true), (72, true)]
theorem step4369 (p : Nat → Bool) (h : Constraints p) : clause p c4369 = true :=
  Snake9.LocalRup.prove_clause [c4332, c2249, c1945, c4349, c1154, c1239] c4369 (by decide) p (sat_cons (step4332 p h) (sat_cons (step2249 p h) (sat_cons (step1945 p h) (sat_cons (step4349 p h) (sat_cons (step1154 p h) (sat_cons (step1239 p h) (sat_nil p)))))))
def c4370 : List Lit := [(1661, true), (70, true)]
theorem step4370 (p : Nat → Bool) (h : Constraints p) : clause p c4370 = true :=
  Snake9.LocalRup.prove_clause [c3915, c4175, c4360, c4368, c4369] c4370 (by decide) p (sat_cons (step3915 p h) (sat_cons (step4175 p h) (sat_cons (step4360 p h) (sat_cons (step4368 p h) (sat_cons (step4369 p h) (sat_nil p))))))
def c4371 : List Lit := [(70, true)]
theorem step4371 (p : Nat → Bool) (h : Constraints p) : clause p c4371 = true :=
  Snake9.LocalRup.prove_clause [c4355, c1801, c1819, c4370] c4371 (by decide) p (sat_cons (step4355 p h) (sat_cons (step1801 p h) (sat_cons (step1819 p h) (sat_cons (step4370 p h) (sat_nil p)))))
def c4372 : List Lit := [(1489, true)]
theorem step4372 (p : Nat → Bool) (h : Constraints p) : clause p c4372 = true :=
  Snake9.LocalRup.prove_clause [c4371, c1517] c4372 (by decide) p (sat_cons (step4371 p h) (sat_cons (step1517 p h) (sat_nil p)))
def c4373 : List Lit := [(72, false)]
theorem step4373 (p : Nat → Bool) (h : Constraints p) : clause p c4373 = true :=
  Snake9.LocalRup.prove_clause [c4371, c4236] c4373 (by decide) p (sat_cons (step4371 p h) (sat_cons (step4236 p h) (sat_nil p)))
def c4374 : List Lit := [(5, false)]
theorem step4374 (p : Nat → Bool) (h : Constraints p) : clause p c4374 = true :=
  Snake9.LocalRup.prove_clause [c4371, c4264] c4374 (by decide) p (sat_cons (step4371 p h) (sat_cons (step4264 p h) (sat_nil p)))
def c4375 : List Lit := [(105, false)]
theorem step4375 (p : Nat → Bool) (h : Constraints p) : clause p c4375 = true :=
  Snake9.LocalRup.prove_clause [c4371, c4255] c4375 (by decide) p (sat_cons (step4371 p h) (sat_cons (step4255 p h) (sat_nil p)))
def c4376 : List Lit := [(65, false)]
theorem step4376 (p : Nat → Bool) (h : Constraints p) : clause p c4376 = true :=
  Snake9.LocalRup.prove_clause [c4371, c4237] c4376 (by decide) p (sat_cons (step4371 p h) (sat_cons (step4237 p h) (sat_nil p)))
def c4377 : List Lit := [(51, false)]
theorem step4377 (p : Nat → Bool) (h : Constraints p) : clause p c4377 = true :=
  Snake9.LocalRup.prove_clause [c4371, c4259] c4377 (by decide) p (sat_cons (step4371 p h) (sat_cons (step4259 p h) (sat_nil p)))
def c4378 : List Lit := [(1493, true)]
theorem step4378 (p : Nat → Bool) (h : Constraints p) : clause p c4378 = true :=
  Snake9.LocalRup.prove_clause [c4372, c1048] c4378 (by decide) p (sat_cons (step4372 p h) (sat_cons (step1048 p h) (sat_nil p)))
def c4379 : List Lit := [(1505, true)]
theorem step4379 (p : Nat → Bool) (h : Constraints p) : clause p c4379 = true :=
  Snake9.LocalRup.prove_clause [c4372, c3440] c4379 (by decide) p (sat_cons (step4372 p h) (sat_cons (step3440 p h) (sat_nil p)))
def c4380 : List Lit := [(1555, true)]
theorem step4380 (p : Nat → Bool) (h : Constraints p) : clause p c4380 = true :=
  Snake9.LocalRup.prove_clause [c4373, c1166] c4380 (by decide) p (sat_cons (step4373 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c4381 : List Lit := [(1403, true)]
theorem step4381 (p : Nat → Bool) (h : Constraints p) : clause p c4381 = true :=
  Snake9.LocalRup.prove_clause [c4374, c908] c4381 (by decide) p (sat_cons (step4374 p h) (sat_cons (step908 p h) (sat_nil p)))
def c4382 : List Lit := [(1616, true)]
theorem step4382 (p : Nat → Bool) (h : Constraints p) : clause p c4382 = true :=
  Snake9.LocalRup.prove_clause [c4375, c1270] c4382 (by decide) p (sat_cons (step4375 p h) (sat_cons (step1270 p h) (sat_nil p)))
def c4383 : List Lit := [(1540, true)]
theorem step4383 (p : Nat → Bool) (h : Constraints p) : clause p c4383 = true :=
  Snake9.LocalRup.prove_clause [c4376, c1134] c4383 (by decide) p (sat_cons (step4376 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c4384 : List Lit := [(1559, true)]
theorem step4384 (p : Nat → Bool) (h : Constraints p) : clause p c4384 = true :=
  Snake9.LocalRup.prove_clause [c4380, c1173] c4384 (by decide) p (sat_cons (step4380 p h) (sat_cons (step1173 p h) (sat_nil p)))
def c4385 : List Lit := [(1417, true)]
theorem step4385 (p : Nat → Bool) (h : Constraints p) : clause p c4385 = true :=
  Snake9.LocalRup.prove_clause [c4381, c4247] c4385 (by decide) p (sat_cons (step4381 p h) (sat_cons (step4247 p h) (sat_nil p)))
def c4386 : List Lit := [(1618, true)]
theorem step4386 (p : Nat → Bool) (h : Constraints p) : clause p c4386 = true :=
  Snake9.LocalRup.prove_clause [c4382, c1272] c4386 (by decide) p (sat_cons (step4382 p h) (sat_cons (step1272 p h) (sat_nil p)))
def c4387 : List Lit := [(1630, true)]
theorem step4387 (p : Nat → Bool) (h : Constraints p) : clause p c4387 = true :=
  Snake9.LocalRup.prove_clause [c4386, c1297] c4387 (by decide) p (sat_cons (step4386 p h) (sat_cons (step1297 p h) (sat_nil p)))
def c4388 : List Lit := [(1638, true)]
theorem step4388 (p : Nat → Bool) (h : Constraints p) : clause p c4388 = true :=
  Snake9.LocalRup.prove_clause [c4387, c1308] c4388 (by decide) p (sat_cons (step4387 p h) (sat_cons (step1308 p h) (sat_nil p)))
def c4389 : List Lit := [(116, true), (1632, true), (1584, false), (83, false)]
theorem step4389 (p : Nat → Bool) (h : Constraints p) : clause p c4389 = true :=
  Snake9.LocalRup.prove_clause [c4386, c4382, c4372, c4374, c1299, c1286, c1282, c1284, c1285, c2979, c1979, c4246, c4263, c1996, c1298, c1051, c998, c1309, c4138, c1340, c4314, c1820] c4389 (by decide) p (sat_cons (step4386 p h) (sat_cons (step4382 p h) (sat_cons (step4372 p h) (sat_cons (step4374 p h) (sat_cons (step1299 p h) (sat_cons (step1286 p h) (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_cons (step1285 p h) (sat_cons (step2979 p h) (sat_cons (step1979 p h) (sat_cons (step4246 p h) (sat_cons (step4263 p h) (sat_cons (step1996 p h) (sat_cons (step1298 p h) (sat_cons (step1051 p h) (sat_cons (step998 p h) (sat_cons (step1309 p h) (sat_cons (step4138 p h) (sat_cons (step1340 p h) (sat_cons (step4314 p h) (sat_cons (step1820 p h) (sat_nil p)))))))))))))))))))))))
def c4390 : List Lit := [(1565, true), (1661, true), (1545, false), (1585, true)]
theorem step4390 (p : Nat → Bool) (h : Constraints p) : clause p c4390 = true :=
  Snake9.LocalRup.prove_clause [c4373, c4388, c4372, c4385, c4374, c4371, c4375, c1182, c1183, c1945, c4349, c1153, c1233, c1341, c1339, c1310, c1821, c4389, c4367, c538, c1059, c1867, c1795, c978, c4297, c1106, c2213, c1075, c1613] c4390 (by decide) p (sat_cons (step4373 p h) (sat_cons (step4388 p h) (sat_cons (step4372 p h) (sat_cons (step4385 p h) (sat_cons (step4374 p h) (sat_cons (step4371 p h) (sat_cons (step4375 p h) (sat_cons (step1182 p h) (sat_cons (step1183 p h) (sat_cons (step1945 p h) (sat_cons (step4349 p h) (sat_cons (step1153 p h) (sat_cons (step1233 p h) (sat_cons (step1341 p h) (sat_cons (step1339 p h) (sat_cons (step1310 p h) (sat_cons (step1821 p h) (sat_cons (step4389 p h) (sat_cons (step4367 p h) (sat_cons (step538 p h) (sat_cons (step1059 p h) (sat_cons (step1867 p h) (sat_cons (step1795 p h) (sat_cons (step978 p h) (sat_cons (step4297 p h) (sat_cons (step1106 p h) (sat_cons (step2213 p h) (sat_cons (step1075 p h) (sat_cons (step1613 p h) (sat_nil p))))))))))))))))))))))))))))))
def c4391 : List Lit := [(1584, false), (1660, true), (1496, false)]
theorem step4391 (p : Nat → Bool) (h : Constraints p) : clause p c4391 = true :=
  Snake9.LocalRup.prove_clause [c4374, c4371, c4375, c4382, c1795, c4297, c1340, c2213, c1309, c4109, c2854] c4391 (by decide) p (sat_cons (step4374 p h) (sat_cons (step4371 p h) (sat_cons (step4375 p h) (sat_cons (step4382 p h) (sat_cons (step1795 p h) (sat_cons (step4297 p h) (sat_cons (step1340 p h) (sat_cons (step2213 p h) (sat_cons (step1309 p h) (sat_cons (step4109 p h) (sat_cons (step2854 p h) (sat_nil p))))))))))))
def c4392 : List Lit := [(116, false), (1545, false), (1585, true)]
theorem step4392 (p : Nat → Bool) (h : Constraints p) : clause p c4392 = true :=
  Snake9.LocalRup.prove_clause [c4383, c4372, c4374, c4380, c4384, c4373, c4287, c1822, c1804, c1148, c4369, c1143, c4367, c1059, c1795, c1087, c4292, c1105, c1820, c4391, c4322, c1228, c4320, c1174, c1200, c1828, c1168, c2250, c533, c1184] c4392 (by decide) p (sat_cons (step4383 p h) (sat_cons (step4372 p h) (sat_cons (step4374 p h) (sat_cons (step4380 p h) (sat_cons (step4384 p h) (sat_cons (step4373 p h) (sat_cons (step4287 p h) (sat_cons (step1822 p h) (sat_cons (step1804 p h) (sat_cons (step1148 p h) (sat_cons (step4369 p h) (sat_cons (step1143 p h) (sat_cons (step4367 p h) (sat_cons (step1059 p h) (sat_cons (step1795 p h) (sat_cons (step1087 p h) (sat_cons (step4292 p h) (sat_cons (step1105 p h) (sat_cons (step1820 p h) (sat_cons (step4391 p h) (sat_cons (step4322 p h) (sat_cons (step1228 p h) (sat_cons (step4320 p h) (sat_cons (step1174 p h) (sat_cons (step1200 p h) (sat_cons (step1828 p h) (sat_cons (step1168 p h) (sat_cons (step2250 p h) (sat_cons (step533 p h) (sat_cons (step1184 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c4393 : List Lit := [(1584, true), (1573, false), (1545, false)]
theorem step4393 (p : Nat → Bool) (h : Constraints p) : clause p c4393 = true :=
  Snake9.LocalRup.prove_clause [c4384, c4373, c1148, c4322, c1228, c1233, c1200, c1153, c2250, c1128, c1130, c1125, c4224] c4393 (by decide) p (sat_cons (step4384 p h) (sat_cons (step4373 p h) (sat_cons (step1148 p h) (sat_cons (step4322 p h) (sat_cons (step1228 p h) (sat_cons (step1233 p h) (sat_cons (step1200 p h) (sat_cons (step1153 p h) (sat_cons (step2250 p h) (sat_cons (step1128 p h) (sat_cons (step1130 p h) (sat_cons (step1125 p h) (sat_cons (step4224 p h) (sat_nil p))))))))))))))
def c4394 : List Lit := [(1661, true), (1545, false), (1585, true)]
theorem step4394 (p : Nat → Bool) (h : Constraints p) : clause p c4394 = true :=
  Snake9.LocalRup.prove_clause [c4384, c4386, c4373, c4372, c4374, c4392, c1282, c1285, c1298, c1309, c4390, c2249, c1199, c4393, c1341, c1340, c1310, c1820, c1299, c1802, c1286, c4363, c1284, c1167, c1979, c1176, c1051, c1204, c1085, c4269, c4292] c4394 (by decide) p (sat_cons (step4384 p h) (sat_cons (step4386 p h) (sat_cons (step4373 p h) (sat_cons (step4372 p h) (sat_cons (step4374 p h) (sat_cons (step4392 p h) (sat_cons (step1282 p h) (sat_cons (step1285 p h) (sat_cons (step1298 p h) (sat_cons (step1309 p h) (sat_cons (step4390 p h) (sat_cons (step2249 p h) (sat_cons (step1199 p h) (sat_cons (step4393 p h) (sat_cons (step1341 p h) (sat_cons (step1340 p h) (sat_cons (step1310 p h) (sat_cons (step1820 p h) (sat_cons (step1299 p h) (sat_cons (step1802 p h) (sat_cons (step1286 p h) (sat_cons (step4363 p h) (sat_cons (step1284 p h) (sat_cons (step1167 p h) (sat_cons (step1979 p h) (sat_cons (step1176 p h) (sat_cons (step1051 p h) (sat_cons (step1204 p h) (sat_cons (step1085 p h) (sat_cons (step4269 p h) (sat_cons (step4292 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c4395 : List Lit := [(1525, true)]
theorem step4395 (p : Nat → Bool) (h : Constraints p) : clause p c4395 = true :=
  Snake9.LocalRup.prove_clause [c4379, c4378, c4374, c1801, c1104, c1084, c4292] c4395 (by decide) p (sat_cons (step4379 p h) (sat_cons (step4378 p h) (sat_cons (step4374 p h) (sat_cons (step1801 p h) (sat_cons (step1104 p h) (sat_cons (step1084 p h) (sat_cons (step4292 p h) (sat_nil p))))))))
def c4396 : List Lit := [(1661, false)]
theorem step4396 (p : Nat → Bool) (h : Constraints p) : clause p c4396 = true :=
  Snake9.LocalRup.prove_clause [c4395, c1819] c4396 (by decide) p (sat_cons (step4395 p h) (sat_cons (step1819 p h) (sat_nil p)))
def c4397 : List Lit := [(1545, true)]
theorem step4397 (p : Nat → Bool) (h : Constraints p) : clause p c4397 = true :=
  Snake9.LocalRup.prove_clause [c4396, c4383, c4386, c4380, c4371, c4377, c4374, c4272, c1142, c1872, c3917, c1182, c1137, c1720, c1721, c2249, c4240, c4239, c1820, c1498, c1049, c2308, c4314] c4397 (by decide) p (sat_cons (step4396 p h) (sat_cons (step4383 p h) (sat_cons (step4386 p h) (sat_cons (step4380 p h) (sat_cons (step4371 p h) (sat_cons (step4377 p h) (sat_cons (step4374 p h) (sat_cons (step4272 p h) (sat_cons (step1142 p h) (sat_cons (step1872 p h) (sat_cons (step3917 p h) (sat_cons (step1182 p h) (sat_cons (step1137 p h) (sat_cons (step1720 p h) (sat_cons (step1721 p h) (sat_cons (step2249 p h) (sat_cons (step4240 p h) (sat_cons (step4239 p h) (sat_cons (step1820 p h) (sat_cons (step1498 p h) (sat_cons (step1049 p h) (sat_cons (step2308 p h) (sat_cons (step4314 p h) (sat_nil p))))))))))))))))))))))))
def c4398 : List Lit := [(1585, false)]
theorem step4398 (p : Nat → Bool) (h : Constraints p) : clause p c4398 = true :=
  Snake9.LocalRup.prove_clause [c4397, c4175] c4398 (by decide) p (sat_cons (step4397 p h) (sat_cons (step4175 p h) (sat_nil p)))
def c4399 : List Lit := []
theorem step4399 (p : Nat → Bool) (h : Constraints p) : clause p c4399 = true :=
  Snake9.LocalRup.prove_clause [c4397, c4398, c4396, c4394] c4399 (by decide) p (sat_cons (step4397 p h) (sat_cons (step4398 p h) (sat_cons (step4396 p h) (sat_cons (step4394 p h) (sat_nil p)))))
end B112E064
