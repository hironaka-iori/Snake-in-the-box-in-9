import B112E089Part0269
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c19292 : List Lit := [(67, false)]
theorem step19292 (p : Nat → Bool) (h : Constraints p) : clause p c19292 = true :=
  Snake9.LocalRup.prove_clause [c19287, c19276, c13751] c19292 (by decide) p (sat_cons (step19287 p h) (sat_cons (step19276 p h) (sat_cons (step13751 p h) (sat_nil p))))
def c19293 : List Lit := [(1653, true)]
theorem step19293 (p : Nat → Bool) (h : Constraints p) : clause p c19293 = true :=
  Snake9.LocalRup.prove_clause [c19289, c1610] c19293 (by decide) p (sat_cons (step19289 p h) (sat_cons (step1610 p h) (sat_nil p)))
def c19294 : List Lit := [(1656, true)]
theorem step19294 (p : Nat → Bool) (h : Constraints p) : clause p c19294 = true :=
  Snake9.LocalRup.prove_clause [c19292, c19268, c1616] c19294 (by decide) p (sat_cons (step19292 p h) (sat_cons (step19268 p h) (sat_cons (step1616 p h) (sat_nil p))))
def c19295 : List Lit := [(305, true), (1616, false), (1593, false), (1580, false), (489, true)]
theorem step19295 (p : Nat → Bool) (h : Constraints p) : clause p c19295 = true :=
  Snake9.LocalRup.prove_clause [c19269, c19276, c18870, c19288, c19291, c19294, c19264, c19270, c19292, c19293, c19266, c19290, c1294, c1577, c2383, c18639, c1913, c1296, c1222, c1195, c1190, c1188, c1182, c1291, c1252, c1289, c18233, c18470, c1521, c3025, c4141, c6035, c1501, c711, c1475, c1649, c2264, c1485, c17219, c4125, c1480] c19295 (by decide) p (sat_cons (step19269 p h) (sat_cons (step19276 p h) (sat_cons (step18870 p h) (sat_cons (step19288 p h) (sat_cons (step19291 p h) (sat_cons (step19294 p h) (sat_cons (step19264 p h) (sat_cons (step19270 p h) (sat_cons (step19292 p h) (sat_cons (step19293 p h) (sat_cons (step19266 p h) (sat_cons (step19290 p h) (sat_cons (step1294 p h) (sat_cons (step1577 p h) (sat_cons (step2383 p h) (sat_cons (step18639 p h) (sat_cons (step1913 p h) (sat_cons (step1296 p h) (sat_cons (step1222 p h) (sat_cons (step1195 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1289 p h) (sat_cons (step18233 p h) (sat_cons (step18470 p h) (sat_cons (step1521 p h) (sat_cons (step3025 p h) (sat_cons (step4141 p h) (sat_cons (step6035 p h) (sat_cons (step1501 p h) (sat_cons (step711 p h) (sat_cons (step1475 p h) (sat_cons (step1649 p h) (sat_cons (step2264 p h) (sat_cons (step1485 p h) (sat_cons (step17219 p h) (sat_cons (step4125 p h) (sat_cons (step1480 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c19296 : List Lit := [(51, true), (32, true), (489, true)]
theorem step19296 (p : Nat → Bool) (h : Constraints p) : clause p c19296 = true :=
  Snake9.LocalRup.prove_clause [c19050, c19266, c19293, c19292, c19288, c18870, c19270, c19264, c1413, c1421, c1445, c1294, c1291, c1252, c5198, c17840, c16619, c19295, c2338, c1157, c1123, c1099, c1098, c1097, c2074, c19047, c19045, c1618, c18621, c18833, c18790] c19296 (by decide) p (sat_cons (step19050 p h) (sat_cons (step19266 p h) (sat_cons (step19293 p h) (sat_cons (step19292 p h) (sat_cons (step19288 p h) (sat_cons (step18870 p h) (sat_cons (step19270 p h) (sat_cons (step19264 p h) (sat_cons (step1413 p h) (sat_cons (step1421 p h) (sat_cons (step1445 p h) (sat_cons (step1294 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step5198 p h) (sat_cons (step17840 p h) (sat_cons (step16619 p h) (sat_cons (step19295 p h) (sat_cons (step2338 p h) (sat_cons (step1157 p h) (sat_cons (step1123 p h) (sat_cons (step1099 p h) (sat_cons (step1098 p h) (sat_cons (step1097 p h) (sat_cons (step2074 p h) (sat_cons (step19047 p h) (sat_cons (step19045 p h) (sat_cons (step1618 p h) (sat_cons (step18621 p h) (sat_cons (step18833 p h) (sat_cons (step18790 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c19297 : List Lit := [(32, true), (489, true)]
theorem step19297 (p : Nat → Bool) (h : Constraints p) : clause p c19297 = true :=
  Snake9.LocalRup.prove_clause [c19266, c19270, c19292, c19264, c19288, c19052, c19274, c18870, c19051, c19290, c19050, c1296, c1222, c1195, c1190, c1188, c1182, c1294, c1291, c1252, c1413, c1421, c1445, c19296, c699, c698, c3025, c2312, c1649, c2264, c19043, c2161, c18601, c1618, c1723, c1520, c17822, c17663, c16354, c1496, c1485, c4701, c1480, c678, c651] c19297 (by decide) p (sat_cons (step19266 p h) (sat_cons (step19270 p h) (sat_cons (step19292 p h) (sat_cons (step19264 p h) (sat_cons (step19288 p h) (sat_cons (step19052 p h) (sat_cons (step19274 p h) (sat_cons (step18870 p h) (sat_cons (step19051 p h) (sat_cons (step19290 p h) (sat_cons (step19050 p h) (sat_cons (step1296 p h) (sat_cons (step1222 p h) (sat_cons (step1195 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step1294 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1413 p h) (sat_cons (step1421 p h) (sat_cons (step1445 p h) (sat_cons (step19296 p h) (sat_cons (step699 p h) (sat_cons (step698 p h) (sat_cons (step3025 p h) (sat_cons (step2312 p h) (sat_cons (step1649 p h) (sat_cons (step2264 p h) (sat_cons (step19043 p h) (sat_cons (step2161 p h) (sat_cons (step18601 p h) (sat_cons (step1618 p h) (sat_cons (step1723 p h) (sat_cons (step1520 p h) (sat_cons (step17822 p h) (sat_cons (step17663 p h) (sat_cons (step16354 p h) (sat_cons (step1496 p h) (sat_cons (step1485 p h) (sat_cons (step4701 p h) (sat_cons (step1480 p h) (sat_cons (step678 p h) (sat_cons (step651 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c19298 : List Lit := [(489, true)]
theorem step19298 (p : Nat → Bool) (h : Constraints p) : clause p c19298 = true :=
  Snake9.LocalRup.prove_clause [c19270, c19292, c19288, c18870, c19050, c19290, c19264, c19274, c19266, c1294, c1296, c1291, c1222, c1252, c1195, c1190, c1188, c1182, c19297, c16137, c689, c688, c3025, c2312, c1649, c2264, c2161, c18601, c1723, c1515, c14631, c16354, c17683, c679, c678, c1987, c1480, c1482, c1485, c1505, c14620] c19298 (by decide) p (sat_cons (step19270 p h) (sat_cons (step19292 p h) (sat_cons (step19288 p h) (sat_cons (step18870 p h) (sat_cons (step19050 p h) (sat_cons (step19290 p h) (sat_cons (step19264 p h) (sat_cons (step19274 p h) (sat_cons (step19266 p h) (sat_cons (step1294 p h) (sat_cons (step1296 p h) (sat_cons (step1291 p h) (sat_cons (step1222 p h) (sat_cons (step1252 p h) (sat_cons (step1195 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step19297 p h) (sat_cons (step16137 p h) (sat_cons (step689 p h) (sat_cons (step688 p h) (sat_cons (step3025 p h) (sat_cons (step2312 p h) (sat_cons (step1649 p h) (sat_cons (step2264 p h) (sat_cons (step2161 p h) (sat_cons (step18601 p h) (sat_cons (step1723 p h) (sat_cons (step1515 p h) (sat_cons (step14631 p h) (sat_cons (step16354 p h) (sat_cons (step17683 p h) (sat_cons (step679 p h) (sat_cons (step678 p h) (sat_cons (step1987 p h) (sat_cons (step1480 p h) (sat_cons (step1482 p h) (sat_cons (step1485 p h) (sat_cons (step1505 p h) (sat_cons (step14620 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c19299 : List Lit := [(367, false)]
theorem step19299 (p : Nat → Bool) (h : Constraints p) : clause p c19299 = true :=
  Snake9.LocalRup.prove_clause [c19298, c2361] c19299 (by decide) p (sat_cons (step19298 p h) (sat_cons (step2361 p h) (sat_nil p)))
def c19300 : List Lit := [(365, false)]
theorem step19300 (p : Nat → Bool) (h : Constraints p) : clause p c19300 = true :=
  Snake9.LocalRup.prove_clause [c19299, c1160] c19300 (by decide) p (sat_cons (step19299 p h) (sat_cons (step1160 p h) (sat_nil p)))
def c19301 : List Lit := [(305, false)]
theorem step19301 (p : Nat → Bool) (h : Constraints p) : clause p c19301 = true :=
  Snake9.LocalRup.prove_clause [c19299, c1162] c19301 (by decide) p (sat_cons (step19299 p h) (sat_cons (step1162 p h) (sat_nil p)))
def c19302 : List Lit := [(333, false)]
theorem step19302 (p : Nat → Bool) (h : Constraints p) : clause p c19302 = true :=
  Snake9.LocalRup.prove_clause [c19300, c1157] c19302 (by decide) p (sat_cons (step19300 p h) (sat_cons (step1157 p h) (sat_nil p)))
def c19303 : List Lit := [(275, false)]
theorem step19303 (p : Nat → Bool) (h : Constraints p) : clause p c19303 = true :=
  Snake9.LocalRup.prove_clause [c19301, c1090] c19303 (by decide) p (sat_cons (step19301 p h) (sat_cons (step1090 p h) (sat_nil p)))
def c19304 : List Lit := [(1617, false)]
theorem step19304 (p : Nat → Bool) (h : Constraints p) : clause p c19304 = true :=
  Snake9.LocalRup.prove_clause [c19301, c19291, c19288, c18870, c18233] c19304 (by decide) p (sat_cons (step19301 p h) (sat_cons (step19291 p h) (sat_cons (step19288 p h) (sat_cons (step18870 p h) (sat_cons (step18233 p h) (sat_nil p))))))
def c19305 : List Lit := [(331, false)]
theorem step19305 (p : Nat → Bool) (h : Constraints p) : clause p c19305 = true :=
  Snake9.LocalRup.prove_clause [c19302, c1121] c19305 (by decide) p (sat_cons (step19302 p h) (sat_cons (step1121 p h) (sat_nil p)))
def c19306 : List Lit := [(317, false)]
theorem step19306 (p : Nat → Bool) (h : Constraints p) : clause p c19306 = true :=
  Snake9.LocalRup.prove_clause [c19302, c1123] c19306 (by decide) p (sat_cons (step19302 p h) (sat_cons (step1123 p h) (sat_nil p)))
def c19307 : List Lit := [(1519, true)]
theorem step19307 (p : Nat → Bool) (h : Constraints p) : clause p c19307 = true :=
  Snake9.LocalRup.prove_clause [c19303, c19304, c19051, c17634] c19307 (by decide) p (sat_cons (step19303 p h) (sat_cons (step19304 p h) (sat_cons (step19051 p h) (sat_cons (step17634 p h) (sat_nil p)))))
def c19308 : List Lit := [(315, false)]
theorem step19308 (p : Nat → Bool) (h : Constraints p) : clause p c19308 = true :=
  Snake9.LocalRup.prove_clause [c19306, c1099] c19308 (by decide) p (sat_cons (step19306 p h) (sat_cons (step1099 p h) (sat_nil p)))
def c19309 : List Lit := [(309, false)]
theorem step19309 (p : Nat → Bool) (h : Constraints p) : clause p c19309 = true :=
  Snake9.LocalRup.prove_clause [c19306, c1100] c19309 (by decide) p (sat_cons (step19306 p h) (sat_cons (step1100 p h) (sat_nil p)))
def c19310 : List Lit := [(311, false)]
theorem step19310 (p : Nat → Bool) (h : Constraints p) : clause p c19310 = true :=
  Snake9.LocalRup.prove_clause [c19308, c1098] c19310 (by decide) p (sat_cons (step19308 p h) (sat_cons (step1098 p h) (sat_nil p)))
def c19311 : List Lit := [(307, false)]
theorem step19311 (p : Nat → Bool) (h : Constraints p) : clause p c19311 = true :=
  Snake9.LocalRup.prove_clause [c19309, c1094] c19311 (by decide) p (sat_cons (step19309 p h) (sat_cons (step1094 p h) (sat_nil p)))
def c19312 : List Lit := [(155, false)]
theorem step19312 (p : Nat → Bool) (h : Constraints p) : clause p c19312 = true :=
  Snake9.LocalRup.prove_clause [c19309, c1095] c19312 (by decide) p (sat_cons (step19309 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c19313 : List Lit := [(158, false)]
theorem step19313 (p : Nat → Bool) (h : Constraints p) : clause p c19313 = true :=
  Snake9.LocalRup.prove_clause [c19310, c1097] c19313 (by decide) p (sat_cons (step19310 p h) (sat_cons (step1097 p h) (sat_nil p)))
def c19314 : List Lit := [(156, false)]
theorem step19314 (p : Nat → Bool) (h : Constraints p) : clause p c19314 = true :=
  Snake9.LocalRup.prove_clause [c19311, c1093] c19314 (by decide) p (sat_cons (step19311 p h) (sat_cons (step1093 p h) (sat_nil p)))
def c19315 : List Lit := [(1616, true), (32, false)]
theorem step19315 (p : Nat → Bool) (h : Constraints p) : clause p c19315 = true :=
  Snake9.LocalRup.prove_clause [c19314, c19270, c19266, c19290, c19305, c19264, c19312, c19301, c19291, c19307, c18345, c19288, c18870, c688, c1649, c2161, c1723, c689, c3025, c1962, c2137, c16137, c18877, c15764, c1414, c2422, c2207, c4735, c1585, c2383, c1913, c1906, c1724, c1858, c2576, c4992, c19022, c1664] c19315 (by decide) p (sat_cons (step19314 p h) (sat_cons (step19270 p h) (sat_cons (step19266 p h) (sat_cons (step19290 p h) (sat_cons (step19305 p h) (sat_cons (step19264 p h) (sat_cons (step19312 p h) (sat_cons (step19301 p h) (sat_cons (step19291 p h) (sat_cons (step19307 p h) (sat_cons (step18345 p h) (sat_cons (step19288 p h) (sat_cons (step18870 p h) (sat_cons (step688 p h) (sat_cons (step1649 p h) (sat_cons (step2161 p h) (sat_cons (step1723 p h) (sat_cons (step689 p h) (sat_cons (step3025 p h) (sat_cons (step1962 p h) (sat_cons (step2137 p h) (sat_cons (step16137 p h) (sat_cons (step18877 p h) (sat_cons (step15764 p h) (sat_cons (step1414 p h) (sat_cons (step2422 p h) (sat_cons (step2207 p h) (sat_cons (step4735 p h) (sat_cons (step1585 p h) (sat_cons (step2383 p h) (sat_cons (step1913 p h) (sat_cons (step1906 p h) (sat_cons (step1724 p h) (sat_cons (step1858 p h) (sat_cons (step2576 p h) (sat_cons (step4992 p h) (sat_cons (step19022 p h) (sat_cons (step1664 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c19316 : List Lit := [(1616, false), (1638, true), (1671, false), (1750, false)]
theorem step19316 (p : Nat → Bool) (h : Constraints p) : clause p c19316 = true :=
  Snake9.LocalRup.prove_clause [c19288, c18870, c19291, c19293, c19294, c19266, c19264, c16223, c18601, c1252] c19316 (by decide) p (sat_cons (step19288 p h) (sat_cons (step18870 p h) (sat_cons (step19291 p h) (sat_cons (step19293 p h) (sat_cons (step19294 p h) (sat_cons (step19266 p h) (sat_cons (step19264 p h) (sat_cons (step16223 p h) (sat_cons (step18601 p h) (sat_cons (step1252 p h) (sat_nil p)))))))))))
def c19317 : List Lit := [(32, false)]
theorem step19317 (p : Nat → Bool) (h : Constraints p) : clause p c19317 = true :=
  Snake9.LocalRup.prove_clause [c19266, c19264, c19270, c19275, c18870, c689, c688, c3025, c1649, c1846, c7632, c2384, c19315, c19316] c19317 (by decide) p (sat_cons (step19266 p h) (sat_cons (step19264 p h) (sat_cons (step19270 p h) (sat_cons (step19275 p h) (sat_cons (step18870 p h) (sat_cons (step689 p h) (sat_cons (step688 p h) (sat_cons (step3025 p h) (sat_cons (step1649 p h) (sat_cons (step1846 p h) (sat_cons (step7632 p h) (sat_cons (step2384 p h) (sat_cons (step19315 p h) (sat_cons (step19316 p h) (sat_nil p)))))))))))))))
def c19318 : List Lit := [(1554, true)]
theorem step19318 (p : Nat → Bool) (h : Constraints p) : clause p c19318 = true :=
  Snake9.LocalRup.prove_clause [c19317, c19304, c19312, c19264, c19051, c19291, c19301, c17911] c19318 (by decide) p (sat_cons (step19317 p h) (sat_cons (step19304 p h) (sat_cons (step19312 p h) (sat_cons (step19264 p h) (sat_cons (step19051 p h) (sat_cons (step19291 p h) (sat_cons (step19301 p h) (sat_cons (step17911 p h) (sat_nil p)))))))))
def c19319 : List Lit := [(1577, false)]
theorem step19319 (p : Nat → Bool) (h : Constraints p) : clause p c19319 = true :=
  Snake9.LocalRup.prove_clause [c19317, c19304, c19313, c19270, c17758] c19319 (by decide) p (sat_cons (step19317 p h) (sat_cons (step19304 p h) (sat_cons (step19313 p h) (sat_cons (step19270 p h) (sat_cons (step17758 p h) (sat_nil p))))))
def c19320 : List Lit := [(1637, true)]
theorem step19320 (p : Nat → Bool) (h : Constraints p) : clause p c19320 = true :=
  Snake9.LocalRup.prove_clause [c19318, c18345, c1585] c19320 (by decide) p (sat_cons (step19318 p h) (sat_cons (step18345 p h) (sat_cons (step1585 p h) (sat_nil p))))
def c19321 : List Lit := [(1784, false)]
theorem step19321 (p : Nat → Bool) (h : Constraints p) : clause p c19321 = true :=
  Snake9.LocalRup.prove_clause [c19320, c2383] c19321 (by decide) p (sat_cons (step19320 p h) (sat_cons (step2383 p h) (sat_nil p)))
def c19322 : List Lit := [(1616, false), (1750, false)]
theorem step19322 (p : Nat → Bool) (h : Constraints p) : clause p c19322 = true :=
  Snake9.LocalRup.prove_clause [c19288, c19301, c19319, c19321, c18870, c19294, c19291, c19293, c19270, c19304, c19313, c19317, c19266, c19264, c16681, c17637, c1858, c16029, c6486, c16221, c6293, c1649, c18790, c698] c19322 (by decide) p (sat_cons (step19288 p h) (sat_cons (step19301 p h) (sat_cons (step19319 p h) (sat_cons (step19321 p h) (sat_cons (step18870 p h) (sat_cons (step19294 p h) (sat_cons (step19291 p h) (sat_cons (step19293 p h) (sat_cons (step19270 p h) (sat_cons (step19304 p h) (sat_cons (step19313 p h) (sat_cons (step19317 p h) (sat_cons (step19266 p h) (sat_cons (step19264 p h) (sat_cons (step16681 p h) (sat_cons (step17637 p h) (sat_cons (step1858 p h) (sat_cons (step16029 p h) (sat_cons (step6486 p h) (sat_cons (step16221 p h) (sat_cons (step6293 p h) (sat_cons (step1649 p h) (sat_cons (step18790 p h) (sat_cons (step698 p h) (sat_nil p)))))))))))))))))))))))))
def c19323 : List Lit := [(1616, true), (51, false)]
theorem step19323 (p : Nat → Bool) (h : Constraints p) : clause p c19323 = true :=
  Snake9.LocalRup.prove_clause [c19317, c19270, c19313, c19052, c17822, c5803, c17752] c19323 (by decide) p (sat_cons (step19317 p h) (sat_cons (step19270 p h) (sat_cons (step19313 p h) (sat_cons (step19052 p h) (sat_cons (step17822 p h) (sat_cons (step5803 p h) (sat_cons (step17752 p h) (sat_nil p))))))))
def c19324 : List Lit := [(1616, true)]
theorem step19324 (p : Nat → Bool) (h : Constraints p) : clause p c19324 = true :=
  Snake9.LocalRup.prove_clause [c19313, c19270, c19317, c17767, c19323] c19324 (by decide) p (sat_cons (step19313 p h) (sat_cons (step19270 p h) (sat_cons (step19317 p h) (sat_cons (step17767 p h) (sat_cons (step19323 p h) (sat_nil p))))))
def c19325 : List Lit := [(91, true)]
theorem step19325 (p : Nat → Bool) (h : Constraints p) : clause p c19325 = true :=
  Snake9.LocalRup.prove_clause [c19324, c19301, c18870, c19291, c19288, c17637] c19325 (by decide) p (sat_cons (step19324 p h) (sat_cons (step19301 p h) (sat_cons (step18870 p h) (sat_cons (step19291 p h) (sat_cons (step19288 p h) (sat_cons (step17637 p h) (sat_nil p)))))))
def c19326 : List Lit := [(1638, true)]
theorem step19326 (p : Nat → Bool) (h : Constraints p) : clause p c19326 = true :=
  Snake9.LocalRup.prove_clause [c19324, c19318, c1586] c19326 (by decide) p (sat_cons (step19324 p h) (sat_cons (step19318 p h) (sat_cons (step1586 p h) (sat_nil p))))
def c19327 : List Lit := [(1750, false)]
theorem step19327 (p : Nat → Bool) (h : Constraints p) : clause p c19327 = true :=
  Snake9.LocalRup.prove_clause [c19324, c19322] c19327 (by decide) p (sat_cons (step19324 p h) (sat_cons (step19322 p h) (sat_nil p)))
def c19328 : List Lit := [(1726, true)]
theorem step19328 (p : Nat → Bool) (h : Constraints p) : clause p c19328 = true :=
  Snake9.LocalRup.prove_clause [c19325, c19319, c16029] c19328 (by decide) p (sat_cons (step19325 p h) (sat_cons (step19319 p h) (sat_cons (step16029 p h) (sat_nil p))))
def c19329 : List Lit := [(1783, false)]
theorem step19329 (p : Nat → Bool) (h : Constraints p) : clause p c19329 = true :=
  Snake9.LocalRup.prove_clause [c19326, c2384] c19329 (by decide) p (sat_cons (step19326 p h) (sat_cons (step2384 p h) (sat_nil p)))
def c19330 : List Lit := [(120, true)]
theorem step19330 (p : Nat → Bool) (h : Constraints p) : clause p c19330 = true :=
  Snake9.LocalRup.prove_clause [c19327, c3025] c19330 (by decide) p (sat_cons (step19327 p h) (sat_cons (step3025 p h) (sat_nil p)))
def c19331 : List Lit := [(122, true)]
theorem step19331 (p : Nat → Bool) (h : Constraints p) : clause p c19331 = true :=
  Snake9.LocalRup.prove_clause [c19327, c19270, c4141] c19331 (by decide) p (sat_cons (step19327 p h) (sat_cons (step19270 p h) (sat_cons (step4141 p h) (sat_nil p))))
def c19332 : List Lit := [(1759, true)]
theorem step19332 (p : Nat → Bool) (h : Constraints p) : clause p c19332 = true :=
  Snake9.LocalRup.prove_clause [c19328, c2555] c19332 (by decide) p (sat_cons (step19328 p h) (sat_cons (step2555 p h) (sat_nil p)))
def c19333 : List Lit := [(1671, false)]
theorem step19333 (p : Nat → Bool) (h : Constraints p) : clause p c19333 = true :=
  Snake9.LocalRup.prove_clause [c19329, c19327, c19293, c19294, c19332, c18870, c19331, c19266, c16227] c19333 (by decide) p (sat_cons (step19329 p h) (sat_cons (step19327 p h) (sat_cons (step19293 p h) (sat_cons (step19294 p h) (sat_cons (step19332 p h) (sat_cons (step18870 p h) (sat_cons (step19331 p h) (sat_cons (step19266 p h) (sat_cons (step16227 p h) (sat_nil p))))))))))
def c19334 : List Lit := [(76, false)]
theorem step19334 (p : Nat → Bool) (h : Constraints p) : clause p c19334 = true :=
  Snake9.LocalRup.prove_clause [c19330, c19264, c19266, c711] c19334 (by decide) p (sat_cons (step19330 p h) (sat_cons (step19264 p h) (sat_cons (step19266 p h) (sat_cons (step711 p h) (sat_nil p)))))
def c19335 : List Lit := []
theorem step19335 (p : Nat → Bool) (h : Constraints p) : clause p c19335 = true :=
  Snake9.LocalRup.prove_clause [c19334, c19333, c19270, c1649] c19335 (by decide) p (sat_cons (step19334 p h) (sat_cons (step19333 p h) (sat_cons (step19270 p h) (sat_cons (step1649 p h) (sat_nil p)))))
end B112E089
