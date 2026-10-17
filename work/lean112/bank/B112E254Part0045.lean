import B112E254Part0044
namespace B112E254
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4295 : List Lit := [(1622, true), (81, false), (69, true), (31, false), (15, false), (10, true)]
theorem step4295 (p : Nat → Bool) (h : Constraints p) : clause p c4295 = true :=
  Snake9.LocalRup.prove_clause [c3478, c4131, c131, c1002, c1010, c4271, c926, c375, c128, c4294, c900, c914, c1866, c4226, c978, c2843, c4237, c977, c2166, c1097] c4295 (by decide) p (sat_cons (step3478 p h) (sat_cons (step4131 p h) (sat_cons (step131 p h) (sat_cons (step1002 p h) (sat_cons (step1010 p h) (sat_cons (step4271 p h) (sat_cons (step926 p h) (sat_cons (step375 p h) (sat_cons (step128 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step914 p h) (sat_cons (step1866 p h) (sat_cons (step4226 p h) (sat_cons (step978 p h) (sat_cons (step2843 p h) (sat_cons (step4237 p h) (sat_cons (step977 p h) (sat_cons (step2166 p h) (sat_cons (step1097 p h) (sat_nil p)))))))))))))))))))))
def c4296 : List Lit := [(81, false), (69, true), (31, false), (15, false), (10, true)]
theorem step4296 (p : Nat → Bool) (h : Constraints p) : clause p c4296 = true :=
  Snake9.LocalRup.prove_clause [c4131, c3478, c1114, c4294, c131, c4271, c1002, c926, c1010, c953, c4295, c1890, c4291, c3815, c896, c906, c916, c2260, c988, c957, c2265, c929, c2166] c4296 (by decide) p (sat_cons (step4131 p h) (sat_cons (step3478 p h) (sat_cons (step1114 p h) (sat_cons (step4294 p h) (sat_cons (step131 p h) (sat_cons (step4271 p h) (sat_cons (step1002 p h) (sat_cons (step926 p h) (sat_cons (step1010 p h) (sat_cons (step953 p h) (sat_cons (step4295 p h) (sat_cons (step1890 p h) (sat_cons (step4291 p h) (sat_cons (step3815 p h) (sat_cons (step896 p h) (sat_cons (step906 p h) (sat_cons (step916 p h) (sat_cons (step2260 p h) (sat_cons (step988 p h) (sat_cons (step957 p h) (sat_cons (step2265 p h) (sat_cons (step929 p h) (sat_cons (step2166 p h) (sat_nil p))))))))))))))))))))))))
def c4297 : List Lit := [(1545, false), (1560, false), (41, true), (12, false), (18, false), (1622, true), (1652, false), (69, true), (31, false)]
theorem step4297 (p : Nat → Bool) (h : Constraints p) : clause p c4297 = true :=
  Snake9.LocalRup.prove_clause [c1010, c2166, c1093, c1092, c4177, c1889] c4297 (by decide) p (sat_cons (step1010 p h) (sat_cons (step2166 p h) (sat_cons (step1093 p h) (sat_cons (step1092 p h) (sat_cons (step4177 p h) (sat_cons (step1889 p h) (sat_nil p)))))))
def c4298 : List Lit := [(1524, true), (69, true), (31, false), (15, false), (10, true)]
theorem step4298 (p : Nat → Bool) (h : Constraints p) : clause p c4298 = true :=
  Snake9.LocalRup.prove_clause [c3478, c4296, c3993, c1890, c1146, c4294, c900, c914, c4132, c925, c948, c975, c926, c928, c4169, c4267, c4153, c1010, c2166, c1087, c1888, c4297, c981, c976, c915, c949, c903, c936, c938, c895, c934, c930, c4270, c1714, c1889, c4145, c1088, c1005, c1855, c2595] c4298 (by decide) p (sat_cons (step3478 p h) (sat_cons (step4296 p h) (sat_cons (step3993 p h) (sat_cons (step1890 p h) (sat_cons (step1146 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step914 p h) (sat_cons (step4132 p h) (sat_cons (step925 p h) (sat_cons (step948 p h) (sat_cons (step975 p h) (sat_cons (step926 p h) (sat_cons (step928 p h) (sat_cons (step4169 p h) (sat_cons (step4267 p h) (sat_cons (step4153 p h) (sat_cons (step1010 p h) (sat_cons (step2166 p h) (sat_cons (step1087 p h) (sat_cons (step1888 p h) (sat_cons (step4297 p h) (sat_cons (step981 p h) (sat_cons (step976 p h) (sat_cons (step915 p h) (sat_cons (step949 p h) (sat_cons (step903 p h) (sat_cons (step936 p h) (sat_cons (step938 p h) (sat_cons (step895 p h) (sat_cons (step934 p h) (sat_cons (step930 p h) (sat_cons (step4270 p h) (sat_cons (step1714 p h) (sat_cons (step1889 p h) (sat_cons (step4145 p h) (sat_cons (step1088 p h) (sat_cons (step1005 p h) (sat_cons (step1855 p h) (sat_cons (step2595 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c4299 : List Lit := [(1601, false), (12, false), (1524, false), (81, true), (69, true), (15, false), (10, true)]
theorem step4299 (p : Nat → Bool) (h : Constraints p) : clause p c4299 = true :=
  Snake9.LocalRup.prove_clause [c3478, c4294, c900, c914, c953, c976, c3993, c1890, c1097, c4117, c1092, c977, c915, c1889, c954, c903, c936, c895, c934, c4179] c4299 (by decide) p (sat_cons (step3478 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step914 p h) (sat_cons (step953 p h) (sat_cons (step976 p h) (sat_cons (step3993 p h) (sat_cons (step1890 p h) (sat_cons (step1097 p h) (sat_cons (step4117 p h) (sat_cons (step1092 p h) (sat_cons (step977 p h) (sat_cons (step915 p h) (sat_cons (step1889 p h) (sat_cons (step954 p h) (sat_cons (step903 p h) (sat_cons (step936 p h) (sat_cons (step895 p h) (sat_cons (step934 p h) (sat_cons (step4179 p h) (sat_nil p)))))))))))))))))))))
def c4300 : List Lit := [(101, false), (99, true), (98, false), (1735, true), (1648, true), (69, true), (31, false), (15, false), (10, true)]
theorem step4300 (p : Nat → Bool) (h : Constraints p) : clause p c4300 = true :=
  Snake9.LocalRup.prove_clause [c3478, c1877, c4296, c4298, c3993, c1890, c4226, c4299, c1854, c1016, c1013, c2214, c1235, c1022, c1866, c4294, c1972, c1719, c538, c1725, c994, c997, c1000, c1018, c1019, c1060, c1008, c1010, c1048, c1852, c1006, c1003, c4153, c1031, c1736, c2207, c508, c1029, c4155, c1225, c2807, c4211, c929, c1227, c1137, c915, c2142, c1256, c1109, c903, c1238, c1107, c895, c1236, c1943] c4300 (by decide) p (sat_cons (step3478 p h) (sat_cons (step1877 p h) (sat_cons (step4296 p h) (sat_cons (step4298 p h) (sat_cons (step3993 p h) (sat_cons (step1890 p h) (sat_cons (step4226 p h) (sat_cons (step4299 p h) (sat_cons (step1854 p h) (sat_cons (step1016 p h) (sat_cons (step1013 p h) (sat_cons (step2214 p h) (sat_cons (step1235 p h) (sat_cons (step1022 p h) (sat_cons (step1866 p h) (sat_cons (step4294 p h) (sat_cons (step1972 p h) (sat_cons (step1719 p h) (sat_cons (step538 p h) (sat_cons (step1725 p h) (sat_cons (step994 p h) (sat_cons (step997 p h) (sat_cons (step1000 p h) (sat_cons (step1018 p h) (sat_cons (step1019 p h) (sat_cons (step1060 p h) (sat_cons (step1008 p h) (sat_cons (step1010 p h) (sat_cons (step1048 p h) (sat_cons (step1852 p h) (sat_cons (step1006 p h) (sat_cons (step1003 p h) (sat_cons (step4153 p h) (sat_cons (step1031 p h) (sat_cons (step1736 p h) (sat_cons (step2207 p h) (sat_cons (step508 p h) (sat_cons (step1029 p h) (sat_cons (step4155 p h) (sat_cons (step1225 p h) (sat_cons (step2807 p h) (sat_cons (step4211 p h) (sat_cons (step929 p h) (sat_cons (step1227 p h) (sat_cons (step1137 p h) (sat_cons (step915 p h) (sat_cons (step2142 p h) (sat_cons (step1256 p h) (sat_cons (step1109 p h) (sat_cons (step903 p h) (sat_cons (step1238 p h) (sat_cons (step1107 p h) (sat_cons (step895 p h) (sat_cons (step1236 p h) (sat_cons (step1943 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c4301 : List Lit := [(1621, true), (1646, false), (69, true), (31, false), (15, false), (10, true)]
theorem step4301 (p : Nat → Bool) (h : Constraints p) : clause p c4301 = true :=
  Snake9.LocalRup.prove_clause [c3478, c4296, c3993, c1890, c4298, c4226, c953, c1146, c1148, c4294, c900, c914, c1865, c4227, c982, c1010, c915, c1002, c1003, c4153, c903, c211, c4233, c895, c1691] c4301 (by decide) p (sat_cons (step3478 p h) (sat_cons (step4296 p h) (sat_cons (step3993 p h) (sat_cons (step1890 p h) (sat_cons (step4298 p h) (sat_cons (step4226 p h) (sat_cons (step953 p h) (sat_cons (step1146 p h) (sat_cons (step1148 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step914 p h) (sat_cons (step1865 p h) (sat_cons (step4227 p h) (sat_cons (step982 p h) (sat_cons (step1010 p h) (sat_cons (step915 p h) (sat_cons (step1002 p h) (sat_cons (step1003 p h) (sat_cons (step4153 p h) (sat_cons (step903 p h) (sat_cons (step211 p h) (sat_cons (step4233 p h) (sat_cons (step895 p h) (sat_cons (step1691 p h) (sat_nil p))))))))))))))))))))))))))
def c4302 : List Lit := [(98, false), (38, false), (101, false), (1735, true), (1648, true), (69, true), (31, false), (15, false), (10, true)]
theorem step4302 (p : Nat → Bool) (h : Constraints p) : clause p c4302 = true :=
  Snake9.LocalRup.prove_clause [c509, c4300] c4302 (by decide) p (sat_cons (step509 p h) (sat_cons (step4300 p h) (sat_nil p)))
def c4303 : List Lit := [(1667, false), (1646, false), (1686, false), (69, true), (31, false), (15, false), (10, true)]
theorem step4303 (p : Nat → Bool) (h : Constraints p) : clause p c4303 = true :=
  Snake9.LocalRup.prove_clause [c3478, c4301, c1889, c4294, c900, c914, c4298, c953, c976, c1863, c1888, c4296, c3993, c1890, c4226, c4299, c2214, c1235, c1237, c1226, c1250, c1875, c1354, c1854, c1016, c1013, c1022, c1208, c1195, c1342, c1341, c1876, c1255, c2030, c1251, c1229, c1018, c1019, c1240, c1060, c1010, c1231, c1048, c1003, c1972, c4302, c1850, c1940, c1800, c1035, c276, c493, c1728, c994, c194, c1000] c4303 (by decide) p (sat_cons (step3478 p h) (sat_cons (step4301 p h) (sat_cons (step1889 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step914 p h) (sat_cons (step4298 p h) (sat_cons (step953 p h) (sat_cons (step976 p h) (sat_cons (step1863 p h) (sat_cons (step1888 p h) (sat_cons (step4296 p h) (sat_cons (step3993 p h) (sat_cons (step1890 p h) (sat_cons (step4226 p h) (sat_cons (step4299 p h) (sat_cons (step2214 p h) (sat_cons (step1235 p h) (sat_cons (step1237 p h) (sat_cons (step1226 p h) (sat_cons (step1250 p h) (sat_cons (step1875 p h) (sat_cons (step1354 p h) (sat_cons (step1854 p h) (sat_cons (step1016 p h) (sat_cons (step1013 p h) (sat_cons (step1022 p h) (sat_cons (step1208 p h) (sat_cons (step1195 p h) (sat_cons (step1342 p h) (sat_cons (step1341 p h) (sat_cons (step1876 p h) (sat_cons (step1255 p h) (sat_cons (step2030 p h) (sat_cons (step1251 p h) (sat_cons (step1229 p h) (sat_cons (step1018 p h) (sat_cons (step1019 p h) (sat_cons (step1240 p h) (sat_cons (step1060 p h) (sat_cons (step1010 p h) (sat_cons (step1231 p h) (sat_cons (step1048 p h) (sat_cons (step1003 p h) (sat_cons (step1972 p h) (sat_cons (step4302 p h) (sat_cons (step1850 p h) (sat_cons (step1940 p h) (sat_cons (step1800 p h) (sat_cons (step1035 p h) (sat_cons (step276 p h) (sat_cons (step493 p h) (sat_cons (step1728 p h) (sat_cons (step994 p h) (sat_cons (step194 p h) (sat_cons (step1000 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c4304 : List Lit := [(1646, false), (1686, false), (69, true), (31, false), (15, false), (10, true)]
theorem step4304 (p : Nat → Bool) (h : Constraints p) : clause p c4304 = true :=
  Snake9.LocalRup.prove_clause [c3478, c4296, c3993, c1890, c4298, c4226, c1146, c1148, c4294, c900, c914, c4301, c1889, c4303, c1173, c1529, c934, c936, c954, c4240, c1002, c1003, c4153, c211, c4245] c4304 (by decide) p (sat_cons (step3478 p h) (sat_cons (step4296 p h) (sat_cons (step3993 p h) (sat_cons (step1890 p h) (sat_cons (step4298 p h) (sat_cons (step4226 p h) (sat_cons (step1146 p h) (sat_cons (step1148 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step914 p h) (sat_cons (step4301 p h) (sat_cons (step1889 p h) (sat_cons (step4303 p h) (sat_cons (step1173 p h) (sat_cons (step1529 p h) (sat_cons (step934 p h) (sat_cons (step936 p h) (sat_cons (step954 p h) (sat_cons (step4240 p h) (sat_cons (step1002 p h) (sat_cons (step1003 p h) (sat_cons (step4153 p h) (sat_cons (step211 p h) (sat_cons (step4245 p h) (sat_nil p))))))))))))))))))))))))))
def c4305 : List Lit := [(1646, true), (69, true)]
theorem step4305 (p : Nat → Bool) (h : Constraints p) : clause p c4305 = true :=
  Snake9.LocalRup.prove_clause [c1114, c1121, c1128, c1131, c4159] c4305 (by decide) p (sat_cons (step1114 p h) (sat_cons (step1121 p h) (sat_cons (step1128 p h) (sat_cons (step1131 p h) (sat_cons (step4159 p h) (sat_nil p))))))
def c4306 : List Lit := [(41, false), (22, false), (19, false)]
theorem step4306 (p : Nat → Bool) (h : Constraints p) : clause p c4306 = true :=
  Snake9.LocalRup.prove_clause [c4131, c132] c4306 (by decide) p (sat_cons (step4131 p h) (sat_cons (step132 p h) (sat_nil p)))
def c4307 : List Lit := [(81, false), (22, false), (19, false)]
theorem step4307 (p : Nat → Bool) (h : Constraints p) : clause p c4307 = true :=
  Snake9.LocalRup.prove_clause [c4131, c133] c4307 (by decide) p (sat_cons (step4131 p h) (sat_cons (step133 p h) (sat_nil p)))
def c4308 : List Lit := [(41, false), (22, false), (81, false)]
theorem step4308 (p : Nat → Bool) (h : Constraints p) : clause p c4308 = true :=
  Snake9.LocalRup.prove_clause [c4131, c135] c4308 (by decide) p (sat_cons (step4131 p h) (sat_cons (step135 p h) (sat_nil p)))
def c4309 : List Lit := [(41, false), (81, false), (19, false)]
theorem step4309 (p : Nat → Bool) (h : Constraints p) : clause p c4309 = true :=
  Snake9.LocalRup.prove_clause [c4131, c134] c4309 (by decide) p (sat_cons (step4131 p h) (sat_cons (step134 p h) (sat_nil p)))
def c4310 : List Lit := [(76, false), (81, false), (19, false)]
theorem step4310 (p : Nat → Bool) (h : Constraints p) : clause p c4310 = true :=
  Snake9.LocalRup.prove_clause [c4131, c1387] c4310 (by decide) p (sat_cons (step4131 p h) (sat_cons (step1387 p h) (sat_nil p)))
def c4311 : List Lit := [(39, false), (41, false), (22, false)]
theorem step4311 (p : Nat → Bool) (h : Constraints p) : clause p c4311 = true :=
  Snake9.LocalRup.prove_clause [c4131, c1390] c4311 (by decide) p (sat_cons (step4131 p h) (sat_cons (step1390 p h) (sat_nil p)))
def c4312 : List Lit := [(41, false), (19, false), (15, false)]
theorem step4312 (p : Nat → Bool) (h : Constraints p) : clause p c4312 = true :=
  Snake9.LocalRup.prove_clause [c4131, c127] c4312 (by decide) p (sat_cons (step4131 p h) (sat_cons (step127 p h) (sat_nil p)))
def c4313 : List Lit := [(9, true), (69, false), (10, false), (1524, false), (1508, false)]
theorem step4313 (p : Nat → Bool) (h : Constraints p) : clause p c4313 = true :=
  Snake9.LocalRup.prove_clause [c3478, c2062] c4313 (by decide) p (sat_cons (step3478 p h) (sat_cons (step2062 p h) (sat_nil p)))
def c4314 : List Lit := [(1544, true), (1535, false)]
theorem step4314 (p : Nat → Bool) (h : Constraints p) : clause p c4314 = true :=
  Snake9.LocalRup.prove_clause [c3480, c969] c4314 (by decide) p (sat_cons (step3480 p h) (sat_cons (step969 p h) (sat_nil p)))
def c4315 : List Lit := [(80, false), (22, false), (81, false)]
theorem step4315 (p : Nat → Bool) (h : Constraints p) : clause p c4315 = true :=
  Snake9.LocalRup.prove_clause [c4131, c1391] c4315 (by decide) p (sat_cons (step4131 p h) (sat_cons (step1391 p h) (sat_nil p)))
def c4316 : List Lit := [(13, false), (15, false), (10, false)]
theorem step4316 (p : Nat → Bool) (h : Constraints p) : clause p c4316 = true :=
  Snake9.LocalRup.prove_clause [c4131, c91] c4316 (by decide) p (sat_cons (step4131 p h) (sat_cons (step91 p h) (sat_nil p)))
def c4317 : List Lit := [(1516, true), (1510, false)]
theorem step4317 (p : Nat → Bool) (h : Constraints p) : clause p c4317 = true :=
  Snake9.LocalRup.prove_clause [c3478, c914] c4317 (by decide) p (sat_cons (step3478 p h) (sat_cons (step914 p h) (sat_nil p)))
def c4318 : List Lit := [(73, false), (81, false), (15, false)]
theorem step4318 (p : Nat → Bool) (h : Constraints p) : clause p c4318 = true :=
  Snake9.LocalRup.prove_clause [c4131, c1384] c4318 (by decide) p (sat_cons (step4131 p h) (sat_cons (step1384 p h) (sat_nil p)))
def c4319 : List Lit := [(123, true), (1, false)]
theorem step4319 (p : Nat → Bool) (h : Constraints p) : clause p c4319 = true :=
  Snake9.LocalRup.prove_clause [c3477, c2] c4319 (by decide) p (sat_cons (step3477 p h) (sat_cons (step2 p h) (sat_nil p)))
def c4320 : List Lit := [(45, false), (69, false), (1506, false), (10, false), (1528, false)]
theorem step4320 (p : Nat → Bool) (h : Constraints p) : clause p c4320 = true :=
  Snake9.LocalRup.prove_clause [c3477, c2226] c4320 (by decide) p (sat_cons (step3477 p h) (sat_cons (step2226 p h) (sat_nil p)))
def c4321 : List Lit := [(1619, true), (1601, false)]
theorem step4321 (p : Nat → Bool) (h : Constraints p) : clause p c4321 = true :=
  Snake9.LocalRup.prove_clause [c3479, c1082] c4321 (by decide) p (sat_cons (step3479 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c4322 : List Lit := [(1621, true), (1603, false)]
theorem step4322 (p : Nat → Bool) (h : Constraints p) : clause p c4322 = true :=
  Snake9.LocalRup.prove_clause [c3479, c1084] c4322 (by decide) p (sat_cons (step3479 p h) (sat_cons (step1084 p h) (sat_nil p)))
def c4323 : List Lit := [(41, true), (22, true), (145, true), (15, true), (19, true)]
theorem step4323 (p : Nat → Bool) (h : Constraints p) : clause p c4323 = true :=
  Snake9.LocalRup.prove_clause [c4131, c139] c4323 (by decide) p (sat_cons (step4131 p h) (sat_cons (step139 p h) (sat_nil p)))
def c4324 : List Lit := [(15, false), (19, false), (10, false)]
theorem step4324 (p : Nat → Bool) (h : Constraints p) : clause p c4324 = true :=
  Snake9.LocalRup.prove_clause [c4131, c1376] c4324 (by decide) p (sat_cons (step4131 p h) (sat_cons (step1376 p h) (sat_nil p)))
def c4325 : List Lit := [(41, false), (81, false), (15, false)]
theorem step4325 (p : Nat → Bool) (h : Constraints p) : clause p c4325 = true :=
  Snake9.LocalRup.prove_clause [c4131, c131] c4325 (by decide) p (sat_cons (step4131 p h) (sat_cons (step131 p h) (sat_nil p)))
def c4326 : List Lit := [(1620, true), (1602, false)]
theorem step4326 (p : Nat → Bool) (h : Constraints p) : clause p c4326 = true :=
  Snake9.LocalRup.prove_clause [c3479, c1083] c4326 (by decide) p (sat_cons (step3479 p h) (sat_cons (step1083 p h) (sat_nil p)))
def c4327 : List Lit := [(1525, false), (1532, false)]
theorem step4327 (p : Nat → Bool) (h : Constraints p) : clause p c4327 = true :=
  Snake9.LocalRup.prove_clause [c3481, c960] c4327 (by decide) p (sat_cons (step3481 p h) (sat_cons (step960 p h) (sat_nil p)))
def c4328 : List Lit := [(1513, false), (1519, true)]
theorem step4328 (p : Nat → Bool) (h : Constraints p) : clause p c4328 = true :=
  Snake9.LocalRup.prove_clause [c3478, c917] c4328 (by decide) p (sat_cons (step3478 p h) (sat_cons (step917 p h) (sat_nil p)))
def c4329 : List Lit := [(1512, false), (1518, true)]
theorem step4329 (p : Nat → Bool) (h : Constraints p) : clause p c4329 = true :=
  Snake9.LocalRup.prove_clause [c3478, c916] c4329 (by decide) p (sat_cons (step3478 p h) (sat_cons (step916 p h) (sat_nil p)))
def c4330 : List Lit := [(1511, false), (1517, true)]
theorem step4330 (p : Nat → Bool) (h : Constraints p) : clause p c4330 = true :=
  Snake9.LocalRup.prove_clause [c3478, c915] c4330 (by decide) p (sat_cons (step3478 p h) (sat_cons (step915 p h) (sat_nil p)))
def c4331 : List Lit := [(6, true), (1511, false), (1547, true), (1536, true), (1528, false), (22, true)]
theorem step4331 (p : Nat → Bool) (h : Constraints p) : clause p c4331 = true :=
  Snake9.LocalRup.prove_clause [c3477, c2005] c4331 (by decide) p (sat_cons (step3477 p h) (sat_cons (step2005 p h) (sat_nil p)))
def c4332 : List Lit := [(1502, false), (1505, true)]
theorem step4332 (p : Nat → Bool) (h : Constraints p) : clause p c4332 = true :=
  Snake9.LocalRup.prove_clause [c3477, c893] c4332 (by decide) p (sat_cons (step3477 p h) (sat_cons (step893 p h) (sat_nil p)))
def c4333 : List Lit := [(22, false), (81, false), (76, true), (73, true)]
theorem step4333 (p : Nat → Bool) (h : Constraints p) : clause p c4333 = true :=
  Snake9.LocalRup.prove_clause [c4131, c3000] c4333 (by decide) p (sat_cons (step4131 p h) (sat_cons (step3000 p h) (sat_nil p)))
def c4334 : List Lit := [(1531, false), (1622, true), (1521, false), (15, false), (1516, false)]
theorem step4334 (p : Nat → Bool) (h : Constraints p) : clause p c4334 = true :=
  Snake9.LocalRup.prove_clause [c4131, c3392] c4334 (by decide) p (sat_cons (step4131 p h) (sat_cons (step3392 p h) (sat_nil p)))
def c4335 : List Lit := [(255, false), (15, true), (12, true), (1547, true), (1526, false), (1523, false)]
theorem step4335 (p : Nat → Bool) (h : Constraints p) : clause p c4335 = true :=
  Snake9.LocalRup.prove_clause [c3478, c3395] c4335 (by decide) p (sat_cons (step3478 p h) (sat_cons (step3395 p h) (sat_nil p)))
def c4336 : List Lit := [(1560, true), (22, false), (31, false)]
theorem step4336 (p : Nat → Bool) (h : Constraints p) : clause p c4336 = true :=
  Snake9.LocalRup.prove_clause [c4131, c3455] c4336 (by decide) p (sat_cons (step4131 p h) (sat_cons (step3455 p h) (sat_nil p)))
def c4337 : List Lit := [(1546, true), (1536, true), (1528, false), (10, false), (1508, false)]
theorem step4337 (p : Nat → Bool) (h : Constraints p) : clause p c4337 = true :=
  Snake9.LocalRup.prove_clause [c936, c3990, c923, c925, c949, c950, c982, c939, c4113, c930] c4337 (by decide) p (sat_cons (step936 p h) (sat_cons (step3990 p h) (sat_cons (step923 p h) (sat_cons (step925 p h) (sat_cons (step949 p h) (sat_cons (step950 p h) (sat_cons (step982 p h) (sat_cons (step939 p h) (sat_cons (step4113 p h) (sat_cons (step930 p h) (sat_nil p)))))))))))
def c4338 : List Lit := [(1521, false), (1536, true), (1524, true), (1564, false), (31, true), (10, false), (1508, false)]
theorem step4338 (p : Nat → Bool) (h : Constraints p) : clause p c4338 = true :=
  Snake9.LocalRup.prove_clause [c933, c4337, c936, c925, c928, c949, c950, c2166, c937, c939, c2265, c1097, c935, c930, c988, c1890, c4107, c2342, c1529] c4338 (by decide) p (sat_cons (step933 p h) (sat_cons (step4337 p h) (sat_cons (step936 p h) (sat_cons (step925 p h) (sat_cons (step928 p h) (sat_cons (step949 p h) (sat_cons (step950 p h) (sat_cons (step2166 p h) (sat_cons (step937 p h) (sat_cons (step939 p h) (sat_cons (step2265 p h) (sat_cons (step1097 p h) (sat_cons (step935 p h) (sat_cons (step930 p h) (sat_cons (step988 p h) (sat_cons (step1890 p h) (sat_cons (step4107 p h) (sat_cons (step2342 p h) (sat_cons (step1529 p h) (sat_nil p))))))))))))))))))))
def c4339 : List Lit := [(19, false), (1518, true), (69, false), (10, false), (1508, false)]
theorem step4339 (p : Nat → Bool) (h : Constraints p) : clause p c4339 = true :=
  Snake9.LocalRup.prove_clause [c48, c38, c895, c1450, c903, c4332, c920] c4339 (by decide) p (sat_cons (step48 p h) (sat_cons (step38 p h) (sat_cons (step895 p h) (sat_cons (step1450 p h) (sat_cons (step903 p h) (sat_cons (step4332 p h) (sat_cons (step920 p h) (sat_nil p))))))))
def c4340 : List Lit := [(1517, true), (69, false), (10, false), (1510, false)]
theorem step4340 (p : Nat → Bool) (h : Constraints p) : clause p c4340 = true :=
  Snake9.LocalRup.prove_clause [c4330, c919, c2067, c4332, c1450] c4340 (by decide) p (sat_cons (step4330 p h) (sat_cons (step919 p h) (sat_cons (step2067 p h) (sat_cons (step4332 p h) (sat_cons (step1450 p h) (sat_nil p))))))
def c4341 : List Lit := [(1524, false), (1528, false), (69, false), (10, false), (1508, false)]
theorem step4341 (p : Nat → Bool) (h : Constraints p) : clause p c4341 = true :=
  Snake9.LocalRup.prove_clause [c900, c4340, c2259, c4313, c955, c50, c939, c930] c4341 (by decide) p (sat_cons (step900 p h) (sat_cons (step4340 p h) (sat_cons (step2259 p h) (sat_cons (step4313 p h) (sat_cons (step955 p h) (sat_cons (step50 p h) (sat_cons (step939 p h) (sat_cons (step930 p h) (sat_nil p)))))))))
def c4342 : List Lit := [(45, false), (1528, false), (69, false), (10, false)]
theorem step4342 (p : Nat → Bool) (h : Constraints p) : clause p c4342 = true :=
  Snake9.LocalRup.prove_clause [c51, c4320, c895] c4342 (by decide) p (sat_cons (step51 p h) (sat_cons (step4320 p h) (sat_cons (step895 p h) (sat_nil p))))
def c4343 : List Lit := [(31, true), (69, false), (10, false), (1508, false)]
theorem step4343 (p : Nat → Bool) (h : Constraints p) : clause p c4343 = true :=
  Snake9.LocalRup.prove_clause [c900, c4340, c933, c4341, c4342, c1005, c1008, c3968, c2265, c983, c4338, c923, c59, c4339, c930, c988, c939, c945] c4343 (by decide) p (sat_cons (step900 p h) (sat_cons (step4340 p h) (sat_cons (step933 p h) (sat_cons (step4341 p h) (sat_cons (step4342 p h) (sat_cons (step1005 p h) (sat_cons (step1008 p h) (sat_cons (step3968 p h) (sat_cons (step2265 p h) (sat_cons (step983 p h) (sat_cons (step4338 p h) (sat_cons (step923 p h) (sat_cons (step59 p h) (sat_cons (step4339 p h) (sat_cons (step930 p h) (sat_cons (step988 p h) (sat_cons (step939 p h) (sat_cons (step945 p h) (sat_nil p)))))))))))))))))))
def c4344 : List Lit := [(1531, false), (1547, true), (69, false), (10, false), (1508, false)]
theorem step4344 (p : Nat → Bool) (h : Constraints p) : clause p c4344 = true :=
  Snake9.LocalRup.prove_clause [c900, c4340, c983, c945, c950, c988, c925, c4339, c923] c4344 (by decide) p (sat_cons (step900 p h) (sat_cons (step4340 p h) (sat_cons (step983 p h) (sat_cons (step945 p h) (sat_cons (step950 p h) (sat_cons (step988 p h) (sat_cons (step925 p h) (sat_cons (step4339 p h) (sat_cons (step923 p h) (sat_nil p))))))))))
def c4345 : List Lit := [(1528, false), (69, false), (10, false), (1508, false)]
theorem step4345 (p : Nat → Bool) (h : Constraints p) : clause p c4345 = true :=
  Snake9.LocalRup.prove_clause [c4343, c900, c4340, c4341, c4342, c926, c1005, c3968, c2265, c983, c4337, c2264, c1855, c4344, c939, c930, c59, c923, c924, c928, c4336, c2595] c4345 (by decide) p (sat_cons (step4343 p h) (sat_cons (step900 p h) (sat_cons (step4340 p h) (sat_cons (step4341 p h) (sat_cons (step4342 p h) (sat_cons (step926 p h) (sat_cons (step1005 p h) (sat_cons (step3968 p h) (sat_cons (step2265 p h) (sat_cons (step983 p h) (sat_cons (step4337 p h) (sat_cons (step2264 p h) (sat_cons (step1855 p h) (sat_cons (step4344 p h) (sat_cons (step939 p h) (sat_cons (step930 p h) (sat_cons (step59 p h) (sat_cons (step923 p h) (sat_cons (step924 p h) (sat_cons (step928 p h) (sat_cons (step4336 p h) (sat_cons (step2595 p h) (sat_nil p)))))))))))))))))))))))
def c4346 : List Lit := [(1546, true), (1523, false), (1517, false), (69, false), (10, false)]
theorem step4346 (p : Nat → Bool) (h : Constraints p) : clause p c4346 = true :=
  Snake9.LocalRup.prove_clause [c982, c2072, c949, c4332, c938, c1450, c930, c40] c4346 (by decide) p (sat_cons (step982 p h) (sat_cons (step2072 p h) (sat_cons (step949 p h) (sat_cons (step4332 p h) (sat_cons (step938 p h) (sat_cons (step1450 p h) (sat_cons (step930 p h) (sat_cons (step40 p h) (sat_nil p)))))))))
def c4347 : List Lit := [(13, true), (1662, true), (29, false)]
theorem step4347 (p : Nat → Bool) (h : Constraints p) : clause p c4347 = true :=
  Snake9.LocalRup.prove_clause [c1529, c1164, c2369, c1717, c153, c1528, c1155] c4347 (by decide) p (sat_cons (step1529 p h) (sat_cons (step1164 p h) (sat_cons (step2369 p h) (sat_cons (step1717 p h) (sat_cons (step153 p h) (sat_cons (step1528 p h) (sat_cons (step1155 p h) (sat_nil p))))))))
def c4348 : List Lit := [(19, true), (1601, false), (1547, true), (1527, true), (69, false), (10, false), (15, true)]
theorem step4348 (p : Nat → Bool) (h : Constraints p) : clause p c4348 = true :=
  Snake9.LocalRup.prove_clause [c897, c4345, c934, c4343, c900, c4340, c923, c925, c4346, c2264, c1097, c1855, c1890, c2342, c1529, c894, c903, c2058, c926, c928, c924, c4347, c4336, c86, c1010, c2595, c684, c2069, c1005, c685, c41, c686, c2071, c689] c4348 (by decide) p (sat_cons (step897 p h) (sat_cons (step4345 p h) (sat_cons (step934 p h) (sat_cons (step4343 p h) (sat_cons (step900 p h) (sat_cons (step4340 p h) (sat_cons (step923 p h) (sat_cons (step925 p h) (sat_cons (step4346 p h) (sat_cons (step2264 p h) (sat_cons (step1097 p h) (sat_cons (step1855 p h) (sat_cons (step1890 p h) (sat_cons (step2342 p h) (sat_cons (step1529 p h) (sat_cons (step894 p h) (sat_cons (step903 p h) (sat_cons (step2058 p h) (sat_cons (step926 p h) (sat_cons (step928 p h) (sat_cons (step924 p h) (sat_cons (step4347 p h) (sat_cons (step4336 p h) (sat_cons (step86 p h) (sat_cons (step1010 p h) (sat_cons (step2595 p h) (sat_cons (step684 p h) (sat_cons (step2069 p h) (sat_cons (step1005 p h) (sat_cons (step685 p h) (sat_cons (step41 p h) (sat_cons (step686 p h) (sat_cons (step2071 p h) (sat_cons (step689 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c4349 : List Lit := [(19, false), (1547, true), (69, false), (10, false), (1508, false)]
theorem step4349 (p : Nat → Bool) (h : Constraints p) : clause p c4349 = true :=
  Snake9.LocalRup.prove_clause [c4343, c59, c60, c4339, c930, c1005, c988, c938, c944, c949, c987, c925, c927, c2264, c922, c1855, c4336, c2595] c4349 (by decide) p (sat_cons (step4343 p h) (sat_cons (step59 p h) (sat_cons (step60 p h) (sat_cons (step4339 p h) (sat_cons (step930 p h) (sat_cons (step1005 p h) (sat_cons (step988 p h) (sat_cons (step938 p h) (sat_cons (step944 p h) (sat_cons (step949 p h) (sat_cons (step987 p h) (sat_cons (step925 p h) (sat_cons (step927 p h) (sat_cons (step2264 p h) (sat_cons (step922 p h) (sat_cons (step1855 p h) (sat_cons (step4336 p h) (sat_cons (step2595 p h) (sat_nil p)))))))))))))))))))
def c4350 : List Lit := [(1562, false), (1601, true), (19, true), (1525, true)]
theorem step4350 (p : Nat → Bool) (h : Constraints p) : clause p c4350 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1008, c3953, c2166, c924, c929] c4350 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1008 p h) (sat_cons (step3953 p h) (sat_cons (step2166 p h) (sat_cons (step924 p h) (sat_cons (step929 p h) (sat_nil p)))))))
def c4351 : List Lit := [(1547, true), (1525, true), (1527, true), (69, false), (10, false), (15, true)]
theorem step4351 (p : Nat → Bool) (h : Constraints p) : clause p c4351 = true :=
  Snake9.LocalRup.prove_clause [c897, c4349, c923, c4348, c925, c4350, c1005, c61, c51, c41, c930, c895, c1450, c938, c903, c4332, c949, c920, c988] c4351 (by decide) p (sat_cons (step897 p h) (sat_cons (step4349 p h) (sat_cons (step923 p h) (sat_cons (step4348 p h) (sat_cons (step925 p h) (sat_cons (step4350 p h) (sat_cons (step1005 p h) (sat_cons (step61 p h) (sat_cons (step51 p h) (sat_cons (step41 p h) (sat_cons (step930 p h) (sat_cons (step895 p h) (sat_cons (step1450 p h) (sat_cons (step938 p h) (sat_cons (step903 p h) (sat_cons (step4332 p h) (sat_cons (step949 p h) (sat_cons (step920 p h) (sat_cons (step988 p h) (sat_nil p))))))))))))))))))))
def c4352 : List Lit := [(1547, false), (1527, true), (69, false), (10, false), (15, true)]
theorem step4352 (p : Nat → Bool) (h : Constraints p) : clause p c4352 = true :=
  Snake9.LocalRup.prove_clause [c897, c4345, c934, c1866, c2265, c1890, c2342, c1529, c4347, c1563, c86, c1838, c684, c771, c685, c748, c750, c686, c744, c734, c689, c742, c728, c1833, c739, c727, c719, c2006, c699, c61, c51, c60, c695, c932, c4313, c923, c694, c1711, c928, c101, c2876] c4352 (by decide) p (sat_cons (step897 p h) (sat_cons (step4345 p h) (sat_cons (step934 p h) (sat_cons (step1866 p h) (sat_cons (step2265 p h) (sat_cons (step1890 p h) (sat_cons (step2342 p h) (sat_cons (step1529 p h) (sat_cons (step4347 p h) (sat_cons (step1563 p h) (sat_cons (step86 p h) (sat_cons (step1838 p h) (sat_cons (step684 p h) (sat_cons (step771 p h) (sat_cons (step685 p h) (sat_cons (step748 p h) (sat_cons (step750 p h) (sat_cons (step686 p h) (sat_cons (step744 p h) (sat_cons (step734 p h) (sat_cons (step689 p h) (sat_cons (step742 p h) (sat_cons (step728 p h) (sat_cons (step1833 p h) (sat_cons (step739 p h) (sat_cons (step727 p h) (sat_cons (step719 p h) (sat_cons (step2006 p h) (sat_cons (step699 p h) (sat_cons (step61 p h) (sat_cons (step51 p h) (sat_cons (step60 p h) (sat_cons (step695 p h) (sat_cons (step932 p h) (sat_cons (step4313 p h) (sat_cons (step923 p h) (sat_cons (step694 p h) (sat_cons (step1711 p h) (sat_cons (step928 p h) (sat_cons (step101 p h) (sat_cons (step2876 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c4353 : List Lit := [(1527, true), (69, false), (10, false), (15, true)]
theorem step4353 (p : Nat → Bool) (h : Constraints p) : clause p c4353 = true :=
  Snake9.LocalRup.prove_clause [c897, c900, c4340, c4352, c983, c4351, c957] c4353 (by decide) p (sat_cons (step897 p h) (sat_cons (step900 p h) (sat_cons (step4340 p h) (sat_cons (step4352 p h) (sat_cons (step983 p h) (sat_cons (step4351 p h) (sat_cons (step957 p h) (sat_nil p))))))))
def c4354 : List Lit := [(69, false), (10, false), (15, true)]
theorem step4354 (p : Nat → Bool) (h : Constraints p) : clause p c4354 = true :=
  Snake9.LocalRup.prove_clause [c897, c900, c4340, c2259, c4345, c934, c4353, c941, c945, c955, c4344, c2261, c1866, c2265, c1890, c3968, c2342, c1005, c1529, c51, c41, c896, c1450, c906, c4332, c921] c4354 (by decide) p (sat_cons (step897 p h) (sat_cons (step900 p h) (sat_cons (step4340 p h) (sat_cons (step2259 p h) (sat_cons (step4345 p h) (sat_cons (step934 p h) (sat_cons (step4353 p h) (sat_cons (step941 p h) (sat_cons (step945 p h) (sat_cons (step955 p h) (sat_cons (step4344 p h) (sat_cons (step2261 p h) (sat_cons (step1866 p h) (sat_cons (step2265 p h) (sat_cons (step1890 p h) (sat_cons (step3968 p h) (sat_cons (step2342 p h) (sat_cons (step1005 p h) (sat_cons (step1529 p h) (sat_cons (step51 p h) (sat_cons (step41 p h) (sat_cons (step896 p h) (sat_cons (step1450 p h) (sat_cons (step906 p h) (sat_cons (step4332 p h) (sat_cons (step921 p h) (sat_nil p)))))))))))))))))))))))))))
def c4355 : List Lit := [(1512, false), (45, false), (1531, false), (10, false)]
theorem step4355 (p : Nat → Bool) (h : Constraints p) : clause p c4355 = true :=
  Snake9.LocalRup.prove_clause [c945, c2261, c4329, c921, c2260, c4332, c950, c1450, c925, c37, c923] c4355 (by decide) p (sat_cons (step945 p h) (sat_cons (step2261 p h) (sat_cons (step4329 p h) (sat_cons (step921 p h) (sat_cons (step2260 p h) (sat_cons (step4332 p h) (sat_cons (step950 p h) (sat_cons (step1450 p h) (sat_cons (step925 p h) (sat_cons (step37 p h) (sat_cons (step923 p h) (sat_nil p))))))))))))
def c4356 : List Lit := [(1531, false), (12, true), (1601, true), (10, false), (1508, false)]
theorem step4356 (p : Nat → Bool) (h : Constraints p) : clause p c4356 = true :=
  Snake9.LocalRup.prove_clause [c894, c903, c4330, c2259, c955, c3968, c1005, c4355, c906, c896, c47, c30, c923, c1450, c925, c4332, c950, c920, c2260] c4356 (by decide) p (sat_cons (step894 p h) (sat_cons (step903 p h) (sat_cons (step4330 p h) (sat_cons (step2259 p h) (sat_cons (step955 p h) (sat_cons (step3968 p h) (sat_cons (step1005 p h) (sat_cons (step4355 p h) (sat_cons (step906 p h) (sat_cons (step896 p h) (sat_cons (step47 p h) (sat_cons (step30 p h) (sat_cons (step923 p h) (sat_cons (step1450 p h) (sat_cons (step925 p h) (sat_cons (step4332 p h) (sat_cons (step950 p h) (sat_cons (step920 p h) (sat_cons (step2260 p h) (sat_nil p))))))))))))))))))))
def c4357 : List Lit := [(9, false), (1536, true), (45, false), (1531, true), (1601, true), (10, false)]
theorem step4357 (p : Nat → Bool) (h : Constraints p) : clause p c4357 = true :=
  Snake9.LocalRup.prove_clause [c47, c49, c923, c930, c938, c939, c954, c933, c926, c928, c924, c2166, c4336, c1010] c4357 (by decide) p (sat_cons (step47 p h) (sat_cons (step49 p h) (sat_cons (step923 p h) (sat_cons (step930 p h) (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step954 p h) (sat_cons (step933 p h) (sat_cons (step926 p h) (sat_cons (step928 p h) (sat_cons (step924 p h) (sat_cons (step2166 p h) (sat_cons (step4336 p h) (sat_cons (step1010 p h) (sat_nil p)))))))))))))))
def c4358 : List Lit := [(19, true), (1524, true), (81, false), (1601, true)]
theorem step4358 (p : Nat → Bool) (h : Constraints p) : clause p c4358 = true :=
  Snake9.LocalRup.prove_clause [c926, c923, c924, c928, c4308, c2166, c1002, c1010] c4358 (by decide) p (sat_cons (step926 p h) (sat_cons (step923 p h) (sat_cons (step924 p h) (sat_cons (step928 p h) (sat_cons (step4308 p h) (sat_cons (step2166 p h) (sat_cons (step1002 p h) (sat_cons (step1010 p h) (sat_nil p)))))))))
end B112E254
