import B112E158Part0071
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6178 : List Lit := [(63, true)]
theorem step6178 (p : Nat → Bool) (h : Constraints p) : clause p c6178 = true :=
  Snake9.LocalRup.prove_clause [c6177, c1271] c6178 (by decide) p (sat_cons (step6177 p h) (sat_cons (step1271 p h) (sat_nil p)))
def c6179 : List Lit := [(61, true)]
theorem step6179 (p : Nat → Bool) (h : Constraints p) : clause p c6179 = true :=
  Snake9.LocalRup.prove_clause [c6177, c1272] c6179 (by decide) p (sat_cons (step6177 p h) (sat_cons (step1272 p h) (sat_nil p)))
def c6180 : List Lit := [(69, true), (1568, false)]
theorem step6180 (p : Nat → Bool) (h : Constraints p) : clause p c6180 = true :=
  Snake9.LocalRup.prove_clause [c6095, c6158, c6171, c6094, c6166, c6169, c5784, c6178, c6160, c4979, c1461, c1984, c1392, c1957, c1945, c6105, c1921, c5917, c2291, c2222, c2225, c4275, c391, c631, c5332, c4890, c1859, c1256, c4186, c317, c307, c1084, c4991, c4650] c6180 (by decide) p (sat_cons (step6095 p h) (sat_cons (step6158 p h) (sat_cons (step6171 p h) (sat_cons (step6094 p h) (sat_cons (step6166 p h) (sat_cons (step6169 p h) (sat_cons (step5784 p h) (sat_cons (step6178 p h) (sat_cons (step6160 p h) (sat_cons (step4979 p h) (sat_cons (step1461 p h) (sat_cons (step1984 p h) (sat_cons (step1392 p h) (sat_cons (step1957 p h) (sat_cons (step1945 p h) (sat_cons (step6105 p h) (sat_cons (step1921 p h) (sat_cons (step5917 p h) (sat_cons (step2291 p h) (sat_cons (step2222 p h) (sat_cons (step2225 p h) (sat_cons (step4275 p h) (sat_cons (step391 p h) (sat_cons (step631 p h) (sat_cons (step5332 p h) (sat_cons (step4890 p h) (sat_cons (step1859 p h) (sat_cons (step1256 p h) (sat_cons (step4186 p h) (sat_cons (step317 p h) (sat_cons (step307 p h) (sat_cons (step1084 p h) (sat_cons (step4991 p h) (sat_cons (step4650 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c6181 : List Lit := [(1555, false), (1583, false)]
theorem step6181 (p : Nat → Bool) (h : Constraints p) : clause p c6181 = true :=
  Snake9.LocalRup.prove_clause [c6094, c6168, c5784, c6095, c6172, c6176, c6166, c6171, c6158, c5964, c6178, c6159, c6179, c1299, c1300, c4979, c3599, c1957, c1362, c1921, c1461, c1382, c1945, c1668, c1984, c6150, c6105, c1392, c1139, c5847, c1148, c6180, c5851, c1952, c5365, c6138, c2160, c408, c1859, c1158, c326, c2168, c5530, c5444, c1249] c6181 (by decide) p (sat_cons (step6094 p h) (sat_cons (step6168 p h) (sat_cons (step5784 p h) (sat_cons (step6095 p h) (sat_cons (step6172 p h) (sat_cons (step6176 p h) (sat_cons (step6166 p h) (sat_cons (step6171 p h) (sat_cons (step6158 p h) (sat_cons (step5964 p h) (sat_cons (step6178 p h) (sat_cons (step6159 p h) (sat_cons (step6179 p h) (sat_cons (step1299 p h) (sat_cons (step1300 p h) (sat_cons (step4979 p h) (sat_cons (step3599 p h) (sat_cons (step1957 p h) (sat_cons (step1362 p h) (sat_cons (step1921 p h) (sat_cons (step1461 p h) (sat_cons (step1382 p h) (sat_cons (step1945 p h) (sat_cons (step1668 p h) (sat_cons (step1984 p h) (sat_cons (step6150 p h) (sat_cons (step6105 p h) (sat_cons (step1392 p h) (sat_cons (step1139 p h) (sat_cons (step5847 p h) (sat_cons (step1148 p h) (sat_cons (step6180 p h) (sat_cons (step5851 p h) (sat_cons (step1952 p h) (sat_cons (step5365 p h) (sat_cons (step6138 p h) (sat_cons (step2160 p h) (sat_cons (step408 p h) (sat_cons (step1859 p h) (sat_cons (step1158 p h) (sat_cons (step326 p h) (sat_cons (step2168 p h) (sat_cons (step5530 p h) (sat_cons (step5444 p h) (sat_cons (step1249 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c6182 : List Lit := [(52, false), (37, true), (28, true), (102, false), (1544, true)]
theorem step6182 (p : Nat → Bool) (h : Constraints p) : clause p c6182 = true :=
  Snake9.LocalRup.prove_clause [c6178, c5966, c323, c317, c326, c307, c1047, c1144, c1009, c2047, c4545, c4756, c1256, c1089] c6182 (by decide) p (sat_cons (step6178 p h) (sat_cons (step5966 p h) (sat_cons (step323 p h) (sat_cons (step317 p h) (sat_cons (step326 p h) (sat_cons (step307 p h) (sat_cons (step1047 p h) (sat_cons (step1144 p h) (sat_cons (step1009 p h) (sat_cons (step2047 p h) (sat_cons (step4545 p h) (sat_cons (step4756 p h) (sat_cons (step1256 p h) (sat_cons (step1089 p h) (sat_nil p)))))))))))))))
def c6183 : List Lit := [(1498, false), (51, true), (1495, false), (37, true), (28, true), (92, false), (102, false), (24, true), (1544, true), (59, false)]
theorem step6183 (p : Nat → Bool) (h : Constraints p) : clause p c6183 = true :=
  Snake9.LocalRup.prove_clause [c6171, c5966, c6158, c6178, c6160, c5964, c6179, c1046, c1656, c1082, c1241, c1148, c4545, c1149, c1256, c1183, c1084, c1214, c5527, c5866, c1047, c2047, c4650, c1083, c5553, c1249, c5444] c6183 (by decide) p (sat_cons (step6171 p h) (sat_cons (step5966 p h) (sat_cons (step6158 p h) (sat_cons (step6178 p h) (sat_cons (step6160 p h) (sat_cons (step5964 p h) (sat_cons (step6179 p h) (sat_cons (step1046 p h) (sat_cons (step1656 p h) (sat_cons (step1082 p h) (sat_cons (step1241 p h) (sat_cons (step1148 p h) (sat_cons (step4545 p h) (sat_cons (step1149 p h) (sat_cons (step1256 p h) (sat_cons (step1183 p h) (sat_cons (step1084 p h) (sat_cons (step1214 p h) (sat_cons (step5527 p h) (sat_cons (step5866 p h) (sat_cons (step1047 p h) (sat_cons (step2047 p h) (sat_cons (step4650 p h) (sat_cons (step1083 p h) (sat_cons (step5553 p h) (sat_cons (step1249 p h) (sat_cons (step5444 p h) (sat_nil p))))))))))))))))))))))))))))
def c6184 : List Lit := [(51, true), (37, true), (28, true), (48, true), (92, false), (102, false), (24, true), (1544, true), (59, false)]
theorem step6184 (p : Nat → Bool) (h : Constraints p) : clause p c6184 = true :=
  Snake9.LocalRup.prove_clause [c6171, c6178, c5965, c6179, c5964, c6182, c1139, c1148, c1046, c6183, c1144, c5385, c5568, c4586, c4756, c1256, c1249, c1089, c5444, c1637, c5553] c6184 (by decide) p (sat_cons (step6171 p h) (sat_cons (step6178 p h) (sat_cons (step5965 p h) (sat_cons (step6179 p h) (sat_cons (step5964 p h) (sat_cons (step6182 p h) (sat_cons (step1139 p h) (sat_cons (step1148 p h) (sat_cons (step1046 p h) (sat_cons (step6183 p h) (sat_cons (step1144 p h) (sat_cons (step5385 p h) (sat_cons (step5568 p h) (sat_cons (step4586 p h) (sat_cons (step4756 p h) (sat_cons (step1256 p h) (sat_cons (step1249 p h) (sat_cons (step1089 p h) (sat_cons (step5444 p h) (sat_cons (step1637 p h) (sat_cons (step5553 p h) (sat_nil p))))))))))))))))))))))
def c6185 : List Lit := [(102, false), (69, false), (24, true), (118, true), (59, false)]
theorem step6185 (p : Nat → Bool) (h : Constraints p) : clause p c6185 = true :=
  Snake9.LocalRup.prove_clause [c5784, c6166, c6095, c6171, c6179, c5965, c6158, c6178, c6160, c2161, c4110, c1945, c4979, c1295, c1495, c1355, c2162, c5944, c6128, c1381, c1382, c2149, c1952, c6022, c1139, c1046, c1148, c1656, c1082, c1241, c6182, c6184, c5099, c2108, c5533, c1101, c1165, c1104, c1179, c5521, c1214, c1207, c5527, c1249, c5866, c1083, c1047, c2047] c6185 (by decide) p (sat_cons (step5784 p h) (sat_cons (step6166 p h) (sat_cons (step6095 p h) (sat_cons (step6171 p h) (sat_cons (step6179 p h) (sat_cons (step5965 p h) (sat_cons (step6158 p h) (sat_cons (step6178 p h) (sat_cons (step6160 p h) (sat_cons (step2161 p h) (sat_cons (step4110 p h) (sat_cons (step1945 p h) (sat_cons (step4979 p h) (sat_cons (step1295 p h) (sat_cons (step1495 p h) (sat_cons (step1355 p h) (sat_cons (step2162 p h) (sat_cons (step5944 p h) (sat_cons (step6128 p h) (sat_cons (step1381 p h) (sat_cons (step1382 p h) (sat_cons (step2149 p h) (sat_cons (step1952 p h) (sat_cons (step6022 p h) (sat_cons (step1139 p h) (sat_cons (step1046 p h) (sat_cons (step1148 p h) (sat_cons (step1656 p h) (sat_cons (step1082 p h) (sat_cons (step1241 p h) (sat_cons (step6182 p h) (sat_cons (step6184 p h) (sat_cons (step5099 p h) (sat_cons (step2108 p h) (sat_cons (step5533 p h) (sat_cons (step1101 p h) (sat_cons (step1165 p h) (sat_cons (step1104 p h) (sat_cons (step1179 p h) (sat_cons (step5521 p h) (sat_cons (step1214 p h) (sat_cons (step1207 p h) (sat_cons (step5527 p h) (sat_cons (step1249 p h) (sat_cons (step5866 p h) (sat_cons (step1083 p h) (sat_cons (step1047 p h) (sat_cons (step2047 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c6186 : List Lit := [(1650, true), (118, true), (59, false)]
theorem step6186 (p : Nat → Bool) (h : Constraints p) : clause p c6186 = true :=
  Snake9.LocalRup.prove_clause [c6158, c5365, c6138, c410] c6186 (by decide) p (sat_cons (step6158 p h) (sat_cons (step5365 p h) (sat_cons (step6138 p h) (sat_cons (step410 p h) (sat_nil p)))))
def c6187 : List Lit := [(28, true), (1506, false), (48, true), (37, true), (102, false), (92, false), (24, true), (1544, true), (59, false)]
theorem step6187 (p : Nat → Bool) (h : Constraints p) : clause p c6187 = true :=
  Snake9.LocalRup.prove_clause [c6177, c6160, c6178, c6179, c1139, c1046, c6182, c6184, c1656, c2155, c2108, c1082, c6109, c1101, c1241, c1208, c1104, c5521] c6187 (by decide) p (sat_cons (step6177 p h) (sat_cons (step6160 p h) (sat_cons (step6178 p h) (sat_cons (step6179 p h) (sat_cons (step1139 p h) (sat_cons (step1046 p h) (sat_cons (step6182 p h) (sat_cons (step6184 p h) (sat_cons (step1656 p h) (sat_cons (step2155 p h) (sat_cons (step2108 p h) (sat_cons (step1082 p h) (sat_cons (step6109 p h) (sat_cons (step1101 p h) (sat_cons (step1241 p h) (sat_cons (step1208 p h) (sat_cons (step1104 p h) (sat_cons (step5521 p h) (sat_nil p)))))))))))))))))))
def c6188 : List Lit := [(70, true), (71, false), (69, true), (60, true)]
theorem step6188 (p : Nat → Bool) (h : Constraints p) : clause p c6188 = true :=
  Snake9.LocalRup.prove_clause [c6178, c1834, c1833, c1560] c6188 (by decide) p (sat_cons (step6178 p h) (sat_cons (step1834 p h) (sat_cons (step1833 p h) (sat_cons (step1560 p h) (sat_nil p)))))
def c6189 : List Lit := [(118, true), (1583, false)]
theorem step6189 (p : Nat → Bool) (h : Constraints p) : clause p c6189 = true :=
  Snake9.LocalRup.prove_clause [c5784, c6166, c6095, c5964, c6171, c6158, c6177, c6178, c6179, c6159, c6181, c1276, c1726, c1354, c1490, c2161, c1495, c4979, c4110, c1355, c1295, c1945, c1668, c6186, c5944, c6128, c1462, c1381, c1382, c1282, c1984, c1291, c1392, c6185, c6022, c5969, c3622, c1808, c1289, c1158, c1139, c1284, c5530, c1148, c409, c6188, c534, c1281, c488, c5125, c323, c326, c307, c5444, c5220, c1249] c6189 (by decide) p (sat_cons (step5784 p h) (sat_cons (step6166 p h) (sat_cons (step6095 p h) (sat_cons (step5964 p h) (sat_cons (step6171 p h) (sat_cons (step6158 p h) (sat_cons (step6177 p h) (sat_cons (step6178 p h) (sat_cons (step6179 p h) (sat_cons (step6159 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step1726 p h) (sat_cons (step1354 p h) (sat_cons (step1490 p h) (sat_cons (step2161 p h) (sat_cons (step1495 p h) (sat_cons (step4979 p h) (sat_cons (step4110 p h) (sat_cons (step1355 p h) (sat_cons (step1295 p h) (sat_cons (step1945 p h) (sat_cons (step1668 p h) (sat_cons (step6186 p h) (sat_cons (step5944 p h) (sat_cons (step6128 p h) (sat_cons (step1462 p h) (sat_cons (step1381 p h) (sat_cons (step1382 p h) (sat_cons (step1282 p h) (sat_cons (step1984 p h) (sat_cons (step1291 p h) (sat_cons (step1392 p h) (sat_cons (step6185 p h) (sat_cons (step6022 p h) (sat_cons (step5969 p h) (sat_cons (step3622 p h) (sat_cons (step1808 p h) (sat_cons (step1289 p h) (sat_cons (step1158 p h) (sat_cons (step1139 p h) (sat_cons (step1284 p h) (sat_cons (step5530 p h) (sat_cons (step1148 p h) (sat_cons (step409 p h) (sat_cons (step6188 p h) (sat_cons (step534 p h) (sat_cons (step1281 p h) (sat_cons (step488 p h) (sat_cons (step5125 p h) (sat_cons (step323 p h) (sat_cons (step326 p h) (sat_cons (step307 p h) (sat_cons (step5444 p h) (sat_cons (step5220 p h) (sat_cons (step1249 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c6190 : List Lit := [(52, false), (1544, true), (37, true), (102, false)]
theorem step6190 (p : Nat → Bool) (h : Constraints p) : clause p c6190 = true :=
  Snake9.LocalRup.prove_clause [c6178, c5966, c323, c317, c326, c307, c1144, c1045, c1009, c4545, c1656, c4756, c1256, c4991, c1089, c2047] c6190 (by decide) p (sat_cons (step6178 p h) (sat_cons (step5966 p h) (sat_cons (step323 p h) (sat_cons (step317 p h) (sat_cons (step326 p h) (sat_cons (step307 p h) (sat_cons (step1144 p h) (sat_cons (step1045 p h) (sat_cons (step1009 p h) (sat_cons (step4545 p h) (sat_cons (step1656 p h) (sat_cons (step4756 p h) (sat_cons (step1256 p h) (sat_cons (step4991 p h) (sat_cons (step1089 p h) (sat_cons (step2047 p h) (sat_nil p)))))))))))))))))
def c6191 : List Lit := [(58, false), (73, true), (37, true), (1583, false)]
theorem step6191 (p : Nat → Bool) (h : Constraints p) : clause p c6191 = true :=
  Snake9.LocalRup.prove_clause [c6173, c6189, c6181, c1276, c3622, c5868] c6191 (by decide) p (sat_cons (step6173 p h) (sat_cons (step6189 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step3622 p h) (sat_cons (step5868 p h) (sat_nil p)))))))
def c6192 : List Lit := [(1516, false), (28, false), (73, true), (92, false), (1544, true), (24, true), (102, false), (1583, false)]
theorem step6192 (p : Nat → Bool) (h : Constraints p) : clause p c6192 = true :=
  Snake9.LocalRup.prove_clause [c6160, c6178, c6158, c6173, c1907, c6189, c6181, c1276, c5526, c1215, c1249, c5527, c1083, c5866, c1045, c1656, c1637, c1088, c389, c2302, c2218, c6099, c1292, c1284] c6192 (by decide) p (sat_cons (step6160 p h) (sat_cons (step6178 p h) (sat_cons (step6158 p h) (sat_cons (step6173 p h) (sat_cons (step1907 p h) (sat_cons (step6189 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step5526 p h) (sat_cons (step1215 p h) (sat_cons (step1249 p h) (sat_cons (step5527 p h) (sat_cons (step1083 p h) (sat_cons (step5866 p h) (sat_cons (step1045 p h) (sat_cons (step1656 p h) (sat_cons (step1637 p h) (sat_cons (step1088 p h) (sat_cons (step389 p h) (sat_cons (step2302 p h) (sat_cons (step2218 p h) (sat_cons (step6099 p h) (sat_cons (step1292 p h) (sat_cons (step1284 p h) (sat_nil p)))))))))))))))))))))))))
def c6193 : List Lit := [(92, false), (1544, true), (37, true), (24, true), (102, false), (1583, false)]
theorem step6193 (p : Nat → Bool) (h : Constraints p) : clause p c6193 = true :=
  Snake9.LocalRup.prove_clause [c6171, c5964, c6178, c5784, c6166, c6177, c6179, c6190, c6181, c1276, c5847, c1282, c5831, c1139, c1148, c6191, c1158, c6187, c6192, c6109, c1180, c4157, c1166, c4979, c5533, c1295, c2489, c1291, c2640] c6193 (by decide) p (sat_cons (step6171 p h) (sat_cons (step5964 p h) (sat_cons (step6178 p h) (sat_cons (step5784 p h) (sat_cons (step6166 p h) (sat_cons (step6177 p h) (sat_cons (step6179 p h) (sat_cons (step6190 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step5847 p h) (sat_cons (step1282 p h) (sat_cons (step5831 p h) (sat_cons (step1139 p h) (sat_cons (step1148 p h) (sat_cons (step6191 p h) (sat_cons (step1158 p h) (sat_cons (step6187 p h) (sat_cons (step6192 p h) (sat_cons (step6109 p h) (sat_cons (step1180 p h) (sat_cons (step4157 p h) (sat_cons (step1166 p h) (sat_cons (step4979 p h) (sat_cons (step5533 p h) (sat_cons (step1295 p h) (sat_cons (step2489 p h) (sat_cons (step1291 p h) (sat_cons (step2640 p h) (sat_nil p))))))))))))))))))))))))))))))
def c6194 : List Lit := [(69, true), (1650, true), (59, false)]
theorem step6194 (p : Nat → Bool) (h : Constraints p) : clause p c6194 = true :=
  Snake9.LocalRup.prove_clause [c6158, c2291, c2222, c410] c6194 (by decide) p (sat_cons (step6158 p h) (sat_cons (step2291 p h) (sat_cons (step2222 p h) (sat_cons (step410 p h) (sat_nil p)))))
def c6195 : List Lit := [(60, false), (28, true), (58, true), (48, true), (1564, true), (1544, true), (59, false)]
theorem step6195 (p : Nat → Bool) (h : Constraints p) : clause p c6195 = true :=
  Snake9.LocalRup.prove_clause [c5964, c6158, c6160, c6179, c6171, c5493, c1256, c1084, c1046, c1158, c409, c389, c1283, c1637, c4650, c1291, c1083, c1047, c1249, c5443] c6195 (by decide) p (sat_cons (step5964 p h) (sat_cons (step6158 p h) (sat_cons (step6160 p h) (sat_cons (step6179 p h) (sat_cons (step6171 p h) (sat_cons (step5493 p h) (sat_cons (step1256 p h) (sat_cons (step1084 p h) (sat_cons (step1046 p h) (sat_cons (step1158 p h) (sat_cons (step409 p h) (sat_cons (step389 p h) (sat_cons (step1283 p h) (sat_cons (step1637 p h) (sat_cons (step4650 p h) (sat_cons (step1291 p h) (sat_cons (step1083 p h) (sat_cons (step1047 p h) (sat_cons (step1249 p h) (sat_cons (step5443 p h) (sat_nil p)))))))))))))))))))))
def c6196 : List Lit := [(30, false), (1476, true), (52, true), (32, false)]
theorem step6196 (p : Nat → Bool) (h : Constraints p) : clause p c6196 = true :=
  Snake9.LocalRup.prove_clause [c6158, c149, c1731] c6196 (by decide) p (sat_cons (step6158 p h) (sat_cons (step149 p h) (sat_cons (step1731 p h) (sat_nil p))))
def c6197 : List Lit := [(1544, true), (37, true), (24, true), (102, false), (1583, false)]
theorem step6197 (p : Nat → Bool) (h : Constraints p) : clause p c6197 = true :=
  Snake9.LocalRup.prove_clause [c6095, c6166, c5784, c5964, c6171, c6160, c6178, c6179, c5557, c6189, c6181, c1276, c6190, c6193, c1382, c5944, c3599, c1295, c3615, c1139, c6194, c2055, c4322, c1158, c5493, c1046, c5515, c1256, c1656, c1082, c1241, c1214, c5527, c1105, c6196, c1047, c2047, c1083, c1089, c1249, c4756, c5526, c5385, c6109] c6197 (by decide) p (sat_cons (step6095 p h) (sat_cons (step6166 p h) (sat_cons (step5784 p h) (sat_cons (step5964 p h) (sat_cons (step6171 p h) (sat_cons (step6160 p h) (sat_cons (step6178 p h) (sat_cons (step6179 p h) (sat_cons (step5557 p h) (sat_cons (step6189 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step6190 p h) (sat_cons (step6193 p h) (sat_cons (step1382 p h) (sat_cons (step5944 p h) (sat_cons (step3599 p h) (sat_cons (step1295 p h) (sat_cons (step3615 p h) (sat_cons (step1139 p h) (sat_cons (step6194 p h) (sat_cons (step2055 p h) (sat_cons (step4322 p h) (sat_cons (step1158 p h) (sat_cons (step5493 p h) (sat_cons (step1046 p h) (sat_cons (step5515 p h) (sat_cons (step1256 p h) (sat_cons (step1656 p h) (sat_cons (step1082 p h) (sat_cons (step1241 p h) (sat_cons (step1214 p h) (sat_cons (step5527 p h) (sat_cons (step1105 p h) (sat_cons (step6196 p h) (sat_cons (step1047 p h) (sat_cons (step2047 p h) (sat_cons (step1083 p h) (sat_cons (step1089 p h) (sat_cons (step1249 p h) (sat_cons (step4756 p h) (sat_cons (step5526 p h) (sat_cons (step5385 p h) (sat_cons (step6109 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c6198 : List Lit := [(37, true), (24, true), (102, false), (1583, false)]
theorem step6198 (p : Nat → Bool) (h : Constraints p) : clause p c6198 = true :=
  Snake9.LocalRup.prove_clause [c6095, c6166, c6181, c1276, c1726, c1354, c5557, c6197, c1945, c1489, c6120, c5917] c6198 (by decide) p (sat_cons (step6095 p h) (sat_cons (step6166 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step1726 p h) (sat_cons (step1354 p h) (sat_cons (step5557 p h) (sat_cons (step6197 p h) (sat_cons (step1945 p h) (sat_cons (step1489 p h) (sat_cons (step6120 p h) (sat_cons (step5917 p h) (sat_nil p)))))))))))))
def c6199 : List Lit := [(1678, true), (37, false), (102, false), (1583, false)]
theorem step6199 (p : Nat → Bool) (h : Constraints p) : clause p c6199 = true :=
  Snake9.LocalRup.prove_clause [c6095, c6171, c5964, c6159, c6175, c6158, c6166, c6178, c6179, c6189, c6181, c1276, c1726, c1354, c1957, c2529, c1489, c1295, c1382, c5917, c212, c6074, c190, c211, c4322, c1158, c1250, c5818, c1139, c2168, c6068, c4157, c6109] c6199 (by decide) p (sat_cons (step6095 p h) (sat_cons (step6171 p h) (sat_cons (step5964 p h) (sat_cons (step6159 p h) (sat_cons (step6175 p h) (sat_cons (step6158 p h) (sat_cons (step6166 p h) (sat_cons (step6178 p h) (sat_cons (step6179 p h) (sat_cons (step6189 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step1726 p h) (sat_cons (step1354 p h) (sat_cons (step1957 p h) (sat_cons (step2529 p h) (sat_cons (step1489 p h) (sat_cons (step1295 p h) (sat_cons (step1382 p h) (sat_cons (step5917 p h) (sat_cons (step212 p h) (sat_cons (step6074 p h) (sat_cons (step190 p h) (sat_cons (step211 p h) (sat_cons (step4322 p h) (sat_cons (step1158 p h) (sat_cons (step1250 p h) (sat_cons (step5818 p h) (sat_cons (step1139 p h) (sat_cons (step2168 p h) (sat_cons (step6068 p h) (sat_cons (step4157 p h) (sat_cons (step6109 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c6200 : List Lit := [(69, false), (1544, true), (37, false), (102, false), (118, false)]
theorem step6200 (p : Nat → Bool) (h : Constraints p) : clause p c6200 = true :=
  Snake9.LocalRup.prove_clause [c6166, c5964, c6171, c6179, c6178, c6159, c6105, c1295, c5390, c2113, c2055, c4322, c1139, c1158, c1046, c1148, c5530, c1656, c1179, c6089, c1207, c6109, c1249, c5385, c1088, c1011, c1024] c6200 (by decide) p (sat_cons (step6166 p h) (sat_cons (step5964 p h) (sat_cons (step6171 p h) (sat_cons (step6179 p h) (sat_cons (step6178 p h) (sat_cons (step6159 p h) (sat_cons (step6105 p h) (sat_cons (step1295 p h) (sat_cons (step5390 p h) (sat_cons (step2113 p h) (sat_cons (step2055 p h) (sat_cons (step4322 p h) (sat_cons (step1139 p h) (sat_cons (step1158 p h) (sat_cons (step1046 p h) (sat_cons (step1148 p h) (sat_cons (step5530 p h) (sat_cons (step1656 p h) (sat_cons (step1179 p h) (sat_cons (step6089 p h) (sat_cons (step1207 p h) (sat_cons (step6109 p h) (sat_cons (step1249 p h) (sat_cons (step5385 p h) (sat_cons (step1088 p h) (sat_cons (step1011 p h) (sat_cons (step1024 p h) (sat_nil p))))))))))))))))))))))))))))
def c6201 : List Lit := [(37, false), (102, false), (1583, false)]
theorem step6201 (p : Nat → Bool) (h : Constraints p) : clause p c6201 = true :=
  Snake9.LocalRup.prove_clause [c6095, c6171, c6189, c6181, c1276, c6199, c1945, c6200, c6194, c5944, c1381, c1382, c6022] c6201 (by decide) p (sat_cons (step6095 p h) (sat_cons (step6171 p h) (sat_cons (step6189 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step6199 p h) (sat_cons (step1945 p h) (sat_cons (step6200 p h) (sat_cons (step6194 p h) (sat_cons (step5944 p h) (sat_cons (step1381 p h) (sat_cons (step1382 p h) (sat_cons (step6022 p h) (sat_nil p))))))))))))))
def c6202 : List Lit := [(102, false), (1583, false)]
theorem step6202 (p : Nat → Bool) (h : Constraints p) : clause p c6202 = true :=
  Snake9.LocalRup.prove_clause [c6172, c6095, c5784, c6166, c5964, c6178, c6179, c6160, c6189, c6181, c1276, c6201, c6198, c1668, c1362, c3688, c1355, c1295, c1945, c1495, c3615, c1907, c6190, c5917, c1139, c4157, c2055, c4322, c1158, c1046, c6109, c1656, c5526, c1215, c1082, c1249, c5527, c1241, c1083, c1105, c5541, c2047, c6196, c1047] c6202 (by decide) p (sat_cons (step6172 p h) (sat_cons (step6095 p h) (sat_cons (step5784 p h) (sat_cons (step6166 p h) (sat_cons (step5964 p h) (sat_cons (step6178 p h) (sat_cons (step6179 p h) (sat_cons (step6160 p h) (sat_cons (step6189 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step6201 p h) (sat_cons (step6198 p h) (sat_cons (step1668 p h) (sat_cons (step1362 p h) (sat_cons (step3688 p h) (sat_cons (step1355 p h) (sat_cons (step1295 p h) (sat_cons (step1945 p h) (sat_cons (step1495 p h) (sat_cons (step3615 p h) (sat_cons (step1907 p h) (sat_cons (step6190 p h) (sat_cons (step5917 p h) (sat_cons (step1139 p h) (sat_cons (step4157 p h) (sat_cons (step2055 p h) (sat_cons (step4322 p h) (sat_cons (step1158 p h) (sat_cons (step1046 p h) (sat_cons (step6109 p h) (sat_cons (step1656 p h) (sat_cons (step5526 p h) (sat_cons (step1215 p h) (sat_cons (step1082 p h) (sat_cons (step1249 p h) (sat_cons (step5527 p h) (sat_cons (step1241 p h) (sat_cons (step1083 p h) (sat_cons (step1105 p h) (sat_cons (step5541 p h) (sat_cons (step2047 p h) (sat_cons (step6196 p h) (sat_cons (step1047 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c6203 : List Lit := [(1612, false), (1583, false)]
theorem step6203 (p : Nat → Bool) (h : Constraints p) : clause p c6203 = true :=
  Snake9.LocalRup.prove_clause [c5964, c6179, c6171, c6095, c5784, c6166, c1726, c1354, c1490, c1466, c6202, c1392, c1395, c2058, c1984, c1461, c4979, c1295, c6189, c6181, c1276, c1462, c6194, c2113, c4110, c1945, c2055, c1158, c5530, c4322, c1046, c1656, c6041, c1853, c1495, c1355, c1410, c1384, c1387, c1407, c2191, c577, c1398, c1326, c1389, c1328, c1856, c592, c1338, c1313, c1317] c6203 (by decide) p (sat_cons (step5964 p h) (sat_cons (step6179 p h) (sat_cons (step6171 p h) (sat_cons (step6095 p h) (sat_cons (step5784 p h) (sat_cons (step6166 p h) (sat_cons (step1726 p h) (sat_cons (step1354 p h) (sat_cons (step1490 p h) (sat_cons (step1466 p h) (sat_cons (step6202 p h) (sat_cons (step1392 p h) (sat_cons (step1395 p h) (sat_cons (step2058 p h) (sat_cons (step1984 p h) (sat_cons (step1461 p h) (sat_cons (step4979 p h) (sat_cons (step1295 p h) (sat_cons (step6189 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step1462 p h) (sat_cons (step6194 p h) (sat_cons (step2113 p h) (sat_cons (step4110 p h) (sat_cons (step1945 p h) (sat_cons (step2055 p h) (sat_cons (step1158 p h) (sat_cons (step5530 p h) (sat_cons (step4322 p h) (sat_cons (step1046 p h) (sat_cons (step1656 p h) (sat_cons (step6041 p h) (sat_cons (step1853 p h) (sat_cons (step1495 p h) (sat_cons (step1355 p h) (sat_cons (step1410 p h) (sat_cons (step1384 p h) (sat_cons (step1387 p h) (sat_cons (step1407 p h) (sat_cons (step2191 p h) (sat_cons (step577 p h) (sat_cons (step1398 p h) (sat_cons (step1326 p h) (sat_cons (step1389 p h) (sat_cons (step1328 p h) (sat_cons (step1856 p h) (sat_cons (step592 p h) (sat_cons (step1338 p h) (sat_cons (step1313 p h) (sat_cons (step1317 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))
def c6204 : List Lit := [(1583, false)]
theorem step6204 (p : Nat → Bool) (h : Constraints p) : clause p c6204 = true :=
  Snake9.LocalRup.prove_clause [c5784, c6166, c6095, c5964, c6171, c6160, c6179, c1726, c1354, c1490, c6181, c1276, c6189, c6202, c1392, c1984, c1461, c1462, c1495, c4979, c4110, c6194, c1355, c1295, c1945, c2113, c5851, c2055, c4322, c1668, c1139, c1158, c1046, c1148, c5530, c1656, c1179, c1082, c1241, c1214, c6203, c1382, c5847, c5970] c6204 (by decide) p (sat_cons (step5784 p h) (sat_cons (step6166 p h) (sat_cons (step6095 p h) (sat_cons (step5964 p h) (sat_cons (step6171 p h) (sat_cons (step6160 p h) (sat_cons (step6179 p h) (sat_cons (step1726 p h) (sat_cons (step1354 p h) (sat_cons (step1490 p h) (sat_cons (step6181 p h) (sat_cons (step1276 p h) (sat_cons (step6189 p h) (sat_cons (step6202 p h) (sat_cons (step1392 p h) (sat_cons (step1984 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step1495 p h) (sat_cons (step4979 p h) (sat_cons (step4110 p h) (sat_cons (step6194 p h) (sat_cons (step1355 p h) (sat_cons (step1295 p h) (sat_cons (step1945 p h) (sat_cons (step2113 p h) (sat_cons (step5851 p h) (sat_cons (step2055 p h) (sat_cons (step4322 p h) (sat_cons (step1668 p h) (sat_cons (step1139 p h) (sat_cons (step1158 p h) (sat_cons (step1046 p h) (sat_cons (step1148 p h) (sat_cons (step5530 p h) (sat_cons (step1656 p h) (sat_cons (step1179 p h) (sat_cons (step1082 p h) (sat_cons (step1241 p h) (sat_cons (step1214 p h) (sat_cons (step6203 p h) (sat_cons (step1382 p h) (sat_cons (step5847 p h) (sat_cons (step5970 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c6205 : List Lit := [(87, true)]
theorem step6205 (p : Nat → Bool) (h : Constraints p) : clause p c6205 = true :=
  Snake9.LocalRup.prove_clause [c6204, c1324] c6205 (by decide) p (sat_cons (step6204 p h) (sat_cons (step1324 p h) (sat_nil p)))
def c6206 : List Lit := [(93, false)]
theorem step6206 (p : Nat → Bool) (h : Constraints p) : clause p c6206 = true :=
  Snake9.LocalRup.prove_clause [c6204, c1665] c6206 (by decide) p (sat_cons (step6204 p h) (sat_cons (step1665 p h) (sat_nil p)))
def c6207 : List Lit := [(1621, false)]
theorem step6207 (p : Nat → Bool) (h : Constraints p) : clause p c6207 = true :=
  Snake9.LocalRup.prove_clause [c6204, c6169, c1958] c6207 (by decide) p (sat_cons (step6204 p h) (sat_cons (step6169 p h) (sat_cons (step1958 p h) (sat_nil p))))
def c6208 : List Lit := [(1616, true)]
theorem step6208 (p : Nat → Bool) (h : Constraints p) : clause p c6208 = true :=
  Snake9.LocalRup.prove_clause [c6204, c6169, c2114] c6208 (by decide) p (sat_cons (step6204 p h) (sat_cons (step6169 p h) (sat_cons (step2114 p h) (sat_nil p))))
def c6209 : List Lit := [(212, true)]
theorem step6209 (p : Nat → Bool) (h : Constraints p) : clause p c6209 = true :=
  Snake9.LocalRup.prove_clause [c6204, c6169, c3278] c6209 (by decide) p (sat_cons (step6204 p h) (sat_cons (step6169 p h) (sat_cons (step3278 p h) (sat_nil p))))
def c6210 : List Lit := [(1612, true)]
theorem step6210 (p : Nat → Bool) (h : Constraints p) : clause p c6210 = true :=
  Snake9.LocalRup.prove_clause [c6206, c1381] c6210 (by decide) p (sat_cons (step6206 p h) (sat_cons (step1381 p h) (sat_nil p)))
def c6211 : List Lit := [(1619, false)]
theorem step6211 (p : Nat → Bool) (h : Constraints p) : clause p c6211 = true :=
  Snake9.LocalRup.prove_clause [c6207, c1395] c6211 (by decide) p (sat_cons (step6207 p h) (sat_cons (step1395 p h) (sat_nil p)))
def c6212 : List Lit := [(1617, false)]
theorem step6212 (p : Nat → Bool) (h : Constraints p) : clause p c6212 = true :=
  Snake9.LocalRup.prove_clause [c6207, c1397] c6212 (by decide) p (sat_cons (step6207 p h) (sat_cons (step1397 p h) (sat_nil p)))
def c6213 : List Lit := [(1627, true)]
theorem step6213 (p : Nat → Bool) (h : Constraints p) : clause p c6213 = true :=
  Snake9.LocalRup.prove_clause [c6208, c1412] c6213 (by decide) p (sat_cons (step6208 p h) (sat_cons (step1412 p h) (sat_nil p)))
def c6214 : List Lit := [(413, true)]
theorem step6214 (p : Nat → Bool) (h : Constraints p) : clause p c6214 = true :=
  Snake9.LocalRup.prove_clause [c6209, c866] c6214 (by decide) p (sat_cons (step6209 p h) (sat_cons (step866 p h) (sat_nil p)))
def c6215 : List Lit := [(1650, false)]
theorem step6215 (p : Nat → Bool) (h : Constraints p) : clause p c6215 = true :=
  Snake9.LocalRup.prove_clause [c6210, c6095, c5944] c6215 (by decide) p (sat_cons (step6210 p h) (sat_cons (step6095 p h) (sat_cons (step5944 p h) (sat_nil p))))
def c6216 : List Lit := [(1568, false)]
theorem step6216 (p : Nat → Bool) (h : Constraints p) : clause p c6216 = true :=
  Snake9.LocalRup.prove_clause [c6210, c5784, c6166, c3599] c6216 (by decide) p (sat_cons (step6210 p h) (sat_cons (step5784 p h) (sat_cons (step6166 p h) (sat_cons (step3599 p h) (sat_nil p)))))
def c6217 : List Lit := [(1678, true)]
theorem step6217 (p : Nat → Bool) (h : Constraints p) : clause p c6217 = true :=
  Snake9.LocalRup.prove_clause [c6210, c6095, c6166, c2529] c6217 (by decide) p (sat_cons (step6210 p h) (sat_cons (step6095 p h) (sat_cons (step6166 p h) (sat_cons (step2529 p h) (sat_nil p)))))
def c6218 : List Lit := [(102, true)]
theorem step6218 (p : Nat → Bool) (h : Constraints p) : clause p c6218 = true :=
  Snake9.LocalRup.prove_clause [c6211, c1392] c6218 (by decide) p (sat_cons (step6211 p h) (sat_cons (step1392 p h) (sat_nil p)))
def c6219 : List Lit := [(98, true)]
theorem step6219 (p : Nat → Bool) (h : Constraints p) : clause p c6219 = true :=
  Snake9.LocalRup.prove_clause [c6212, c1389] c6219 (by decide) p (sat_cons (step6212 p h) (sat_cons (step1389 p h) (sat_nil p)))
def c6220 : List Lit := [(1659, true)]
theorem step6220 (p : Nat → Bool) (h : Constraints p) : clause p c6220 = true :=
  Snake9.LocalRup.prove_clause [c6213, c1924] c6220 (by decide) p (sat_cons (step6213 p h) (sat_cons (step1924 p h) (sat_nil p)))
def c6221 : List Lit := [(1660, true)]
theorem step6221 (p : Nat → Bool) (h : Constraints p) : clause p c6221 = true :=
  Snake9.LocalRup.prove_clause [c6213, c6166, c1466] c6221 (by decide) p (sat_cons (step6213 p h) (sat_cons (step6166 p h) (sat_cons (step1466 p h) (sat_nil p))))
def c6222 : List Lit := [(415, true)]
theorem step6222 (p : Nat → Bool) (h : Constraints p) : clause p c6222 = true :=
  Snake9.LocalRup.prove_clause [c6214, c867] c6222 (by decide) p (sat_cons (step6214 p h) (sat_cons (step867 p h) (sat_nil p)))
def c6223 : List Lit := [(1564, false)]
theorem step6223 (p : Nat → Bool) (h : Constraints p) : clause p c6223 = true :=
  Snake9.LocalRup.prove_clause [c6216, c1295] c6223 (by decide) p (sat_cons (step6216 p h) (sat_cons (step1295 p h) (sat_nil p)))
def c6224 : List Lit := [(1555, false)]
theorem step6224 (p : Nat → Bool) (h : Constraints p) : clause p c6224 = true :=
  Snake9.LocalRup.prove_clause [c6216, c6094, c1299] c6224 (by decide) p (sat_cons (step6216 p h) (sat_cons (step6094 p h) (sat_cons (step1299 p h) (sat_nil p))))
def c6225 : List Lit := [(1544, false)]
theorem step6225 (p : Nat → Bool) (h : Constraints p) : clause p c6225 = true :=
  Snake9.LocalRup.prove_clause [c6217, c1945] c6225 (by decide) p (sat_cons (step6217 p h) (sat_cons (step1945 p h) (sat_nil p)))
def c6226 : List Lit := [(74, false)]
theorem step6226 (p : Nat → Bool) (h : Constraints p) : clause p c6226 = true :=
  Snake9.LocalRup.prove_clause [c6219, c6205, c1640] c6226 (by decide) p (sat_cons (step6219 p h) (sat_cons (step6205 p h) (sat_cons (step1640 p h) (sat_nil p))))
def c6227 : List Lit := [(1601, false)]
theorem step6227 (p : Nat → Bool) (h : Constraints p) : clause p c6227 = true :=
  Snake9.LocalRup.prove_clause [c6220, c5784, c1495] c6227 (by decide) p (sat_cons (step6220 p h) (sat_cons (step5784 p h) (sat_cons (step1495 p h) (sat_nil p))))
def c6228 : List Lit := [(1600, false)]
theorem step6228 (p : Nat → Bool) (h : Constraints p) : clause p c6228 = true :=
  Snake9.LocalRup.prove_clause [c6221, c5784, c1490] c6228 (by decide) p (sat_cons (step6221 p h) (sat_cons (step5784 p h) (sat_cons (step1490 p h) (sat_nil p))))
def c6229 : List Lit := [(409, false)]
theorem step6229 (p : Nat → Bool) (h : Constraints p) : clause p c6229 = true :=
  Snake9.LocalRup.prove_clause [c6222, c1895] c6229 (by decide) p (sat_cons (step6222 p h) (sat_cons (step1895 p h) (sat_nil p)))
def c6230 : List Lit := [(59, true)]
theorem step6230 (p : Nat → Bool) (h : Constraints p) : clause p c6230 = true :=
  Snake9.LocalRup.prove_clause [c6224, c1276] c6230 (by decide) p (sat_cons (step6224 p h) (sat_cons (step1276 p h) (sat_nil p)))
def c6231 : List Lit := [(1573, true)]
theorem step6231 (p : Nat → Bool) (h : Constraints p) : clause p c6231 = true :=
  Snake9.LocalRup.prove_clause [c6226, c1313] c6231 (by decide) p (sat_cons (step6226 p h) (sat_cons (step1313 p h) (sat_nil p)))
def c6232 : List Lit := [(1578, false)]
theorem step6232 (p : Nat → Bool) (h : Constraints p) : clause p c6232 = true :=
  Snake9.LocalRup.prove_clause [c6227, c6166, c6095, c5784, c3277] c6232 (by decide) p (sat_cons (step6227 p h) (sat_cons (step6166 p h) (sat_cons (step6095 p h) (sat_cons (step5784 p h) (sat_cons (step3277 p h) (sat_nil p))))))
def c6233 : List Lit := [(1590, false)]
theorem step6233 (p : Nat → Bool) (h : Constraints p) : clause p c6233 = true :=
  Snake9.LocalRup.prove_clause [c6228, c6095, c1354] c6233 (by decide) p (sat_cons (step6228 p h) (sat_cons (step6095 p h) (sat_cons (step1354 p h) (sat_nil p))))
def c6234 : List Lit := [(407, false)]
theorem step6234 (p : Nat → Bool) (h : Constraints p) : clause p c6234 = true :=
  Snake9.LocalRup.prove_clause [c6229, c865] c6234 (by decide) p (sat_cons (step6229 p h) (sat_cons (step865 p h) (sat_nil p)))
def c6235 : List Lit := [(118, true)]
theorem step6235 (p : Nat → Bool) (h : Constraints p) : clause p c6235 = true :=
  Snake9.LocalRup.prove_clause [c6230, c6215, c6186] c6235 (by decide) p (sat_cons (step6230 p h) (sat_cons (step6215 p h) (sat_cons (step6186 p h) (sat_nil p))))
def c6236 : List Lit := [(69, true)]
theorem step6236 (p : Nat → Bool) (h : Constraints p) : clause p c6236 = true :=
  Snake9.LocalRup.prove_clause [c6230, c6215, c6194] c6236 (by decide) p (sat_cons (step6230 p h) (sat_cons (step6215 p h) (sat_cons (step6194 p h) (sat_nil p))))
def c6237 : List Lit := [(1577, true)]
theorem step6237 (p : Nat → Bool) (h : Constraints p) : clause p c6237 = true :=
  Snake9.LocalRup.prove_clause [c6231, c1317] c6237 (by decide) p (sat_cons (step6231 p h) (sat_cons (step1317 p h) (sat_nil p)))
def c6238 : List Lit := [(1575, false)]
theorem step6238 (p : Nat → Bool) (h : Constraints p) : clause p c6238 = true :=
  Snake9.LocalRup.prove_clause [c6231, c6232, c1318] c6238 (by decide) p (sat_cons (step6231 p h) (sat_cons (step6232 p h) (sat_cons (step1318 p h) (sat_nil p))))
def c6239 : List Lit := [(208, false)]
theorem step6239 (p : Nat → Bool) (h : Constraints p) : clause p c6239 = true :=
  Snake9.LocalRup.prove_clause [c6234, c864] c6239 (by decide) p (sat_cons (step6234 p h) (sat_cons (step864 p h) (sat_nil p)))
def c6240 : List Lit := [(37, false)]
theorem step6240 (p : Nat → Bool) (h : Constraints p) : clause p c6240 = true :=
  Snake9.LocalRup.prove_clause [c6235, c6236, c6218, c6225, c6200] c6240 (by decide) p (sat_cons (step6235 p h) (sat_cons (step6236 p h) (sat_cons (step6218 p h) (sat_cons (step6225 p h) (sat_cons (step6200 p h) (sat_nil p))))))
def c6241 : List Lit := [(48, false)]
theorem step6241 (p : Nat → Bool) (h : Constraints p) : clause p c6241 = true :=
  Snake9.LocalRup.prove_clause [c6236, c6235, c6223, c2113] c6241 (by decide) p (sat_cons (step6236 p h) (sat_cons (step6235 p h) (sat_cons (step6223 p h) (sat_cons (step2113 p h) (sat_nil p)))))
end B112E158
