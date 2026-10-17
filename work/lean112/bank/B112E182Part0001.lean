import B112E182Part0000
namespace B112E182
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c302 : List Lit := [(36, false), (1288, true)]
theorem step302 (p : Nat → Bool) (h : Constraints p) : clause p c302 = true :=
  Snake9.LocalRup.prove_clause [c284, c285, c293, c59, c301, c132, c152, c138, c135, c149, c146, c256, c25, c124, c24, c127, c10] c302 (by decide) p (sat_cons (step284 p h) (sat_cons (step285 p h) (sat_cons (step293 p h) (sat_cons (step59 p h) (sat_cons (step301 p h) (sat_cons (step132 p h) (sat_cons (step152 p h) (sat_cons (step138 p h) (sat_cons (step135 p h) (sat_cons (step149 p h) (sat_cons (step146 p h) (sat_cons (step256 p h) (sat_cons (step25 p h) (sat_cons (step124 p h) (sat_cons (step24 p h) (sat_cons (step127 p h) (sat_cons (step10 p h) (sat_nil p))))))))))))))))))
def c303 : List Lit := [(1268, false), (1288, true)]
theorem step303 (p : Nat → Bool) (h : Constraints p) : clause p c303 = true :=
  Snake9.LocalRup.prove_clause [c293, c286, c271, c55, c302, c116, c301, c134, c131, c120, c122, c164, c118, c263, c8, c104, c9, c102] c303 (by decide) p (sat_cons (step293 p h) (sat_cons (step286 p h) (sat_cons (step271 p h) (sat_cons (step55 p h) (sat_cons (step302 p h) (sat_cons (step116 p h) (sat_cons (step301 p h) (sat_cons (step134 p h) (sat_cons (step131 p h) (sat_cons (step120 p h) (sat_cons (step122 p h) (sat_cons (step164 p h) (sat_cons (step118 p h) (sat_cons (step263 p h) (sat_cons (step8 p h) (sat_cons (step104 p h) (sat_cons (step9 p h) (sat_cons (step102 p h) (sat_nil p)))))))))))))))))))
def c304 : List Lit := [(1295, false)]
theorem step304 (p : Nat → Bool) (h : Constraints p) : clause p c304 = true :=
  Snake9.LocalRup.prove_clause [c299, c237, c273, c295, c169, c173, c234, c267, c230, c244, c199, c190] c304 (by decide) p (sat_cons (step299 p h) (sat_cons (step237 p h) (sat_cons (step273 p h) (sat_cons (step295 p h) (sat_cons (step169 p h) (sat_cons (step173 p h) (sat_cons (step234 p h) (sat_cons (step267 p h) (sat_cons (step230 p h) (sat_cons (step244 p h) (sat_cons (step199 p h) (sat_cons (step190 p h) (sat_nil p)))))))))))))
def c305 : List Lit := [(1272, false)]
theorem step305 (p : Nat → Bool) (h : Constraints p) : clause p c305 = true :=
  Snake9.LocalRup.prove_clause [c304, c286, c164] c305 (by decide) p (sat_cons (step304 p h) (sat_cons (step286 p h) (sat_cons (step164 p h) (sat_nil p))))
def c306 : List Lit := [(1264, false)]
theorem step306 (p : Nat → Bool) (h : Constraints p) : clause p c306 = true :=
  Snake9.LocalRup.prove_clause [c305, c133] c306 (by decide) p (sat_cons (step305 p h) (sat_cons (step133 p h) (sat_nil p)))
def c307 : List Lit := [(1262, false)]
theorem step307 (p : Nat → Bool) (h : Constraints p) : clause p c307 = true :=
  Snake9.LocalRup.prove_clause [c306, c120] c307 (by decide) p (sat_cons (step306 p h) (sat_cons (step120 p h) (sat_nil p)))
def c308 : List Lit := [(1288, true)]
theorem step308 (p : Nat → Bool) (h : Constraints p) : clause p c308 = true :=
  Snake9.LocalRup.prove_clause [c285, c286, c299, c59, c306, c307, c55, c237, c297, c272, c261, c152, c138, c135, c300, c160, c176, c113, c302, c116, c303, c125, c126, c124, c13, c23, c122, c118, c8, c9, c102, c104, c107, c110, c112, c99, c172, c98, c234, c37, c228, c212, c221, c218] c308 (by decide) p (sat_cons (step285 p h) (sat_cons (step286 p h) (sat_cons (step299 p h) (sat_cons (step59 p h) (sat_cons (step306 p h) (sat_cons (step307 p h) (sat_cons (step55 p h) (sat_cons (step237 p h) (sat_cons (step297 p h) (sat_cons (step272 p h) (sat_cons (step261 p h) (sat_cons (step152 p h) (sat_cons (step138 p h) (sat_cons (step135 p h) (sat_cons (step300 p h) (sat_cons (step160 p h) (sat_cons (step176 p h) (sat_cons (step113 p h) (sat_cons (step302 p h) (sat_cons (step116 p h) (sat_cons (step303 p h) (sat_cons (step125 p h) (sat_cons (step126 p h) (sat_cons (step124 p h) (sat_cons (step13 p h) (sat_cons (step23 p h) (sat_cons (step122 p h) (sat_cons (step118 p h) (sat_cons (step8 p h) (sat_cons (step9 p h) (sat_cons (step102 p h) (sat_cons (step104 p h) (sat_cons (step107 p h) (sat_cons (step110 p h) (sat_cons (step112 p h) (sat_cons (step99 p h) (sat_cons (step172 p h) (sat_cons (step98 p h) (sat_cons (step234 p h) (sat_cons (step37 p h) (sat_cons (step228 p h) (sat_cons (step212 p h) (sat_cons (step221 p h) (sat_cons (step218 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c309 : List Lit := [(1271, false)]
theorem step309 (p : Nat → Bool) (h : Constraints p) : clause p c309 = true :=
  Snake9.LocalRup.prove_clause [c304, c308, c161] c309 (by decide) p (sat_cons (step304 p h) (sat_cons (step308 p h) (sat_cons (step161 p h) (sat_nil p))))
def c310 : List Lit := [(1294, true)]
theorem step310 (p : Nat → Bool) (h : Constraints p) : clause p c310 = true :=
  Snake9.LocalRup.prove_clause [c308, c157] c310 (by decide) p (sat_cons (step308 p h) (sat_cons (step157 p h) (sat_nil p)))
def c311 : List Lit := [(1303, true)]
theorem step311 (p : Nat → Bool) (h : Constraints p) : clause p c311 = true :=
  Snake9.LocalRup.prove_clause [c308, c287] c311 (by decide) p (sat_cons (step308 p h) (sat_cons (step287 p h) (sat_nil p)))
def c312 : List Lit := [(1263, false)]
theorem step312 (p : Nat → Bool) (h : Constraints p) : clause p c312 = true :=
  Snake9.LocalRup.prove_clause [c309, c130] c312 (by decide) p (sat_cons (step309 p h) (sat_cons (step130 p h) (sat_nil p)))
def c313 : List Lit := [(1254, false)]
theorem step313 (p : Nat → Bool) (h : Constraints p) : clause p c313 = true :=
  Snake9.LocalRup.prove_clause [c310, c299, c176] c313 (by decide) p (sat_cons (step310 p h) (sat_cons (step299 p h) (sat_cons (step176 p h) (sat_nil p))))
def c314 : List Lit := [(1393, false)]
theorem step314 (p : Nat → Bool) (h : Constraints p) : clause p c314 = true :=
  Snake9.LocalRup.prove_clause [c311, c237, c234] c314 (by decide) p (sat_cons (step311 p h) (sat_cons (step237 p h) (sat_cons (step234 p h) (sat_nil p))))
def c315 : List Lit := [(1261, false)]
theorem step315 (p : Nat → Bool) (h : Constraints p) : clause p c315 = true :=
  Snake9.LocalRup.prove_clause [c312, c119] c315 (by decide) p (sat_cons (step312 p h) (sat_cons (step119 p h) (sat_nil p)))
def c316 : List Lit := [(28, true)]
theorem step316 (p : Nat → Bool) (h : Constraints p) : clause p c316 = true :=
  Snake9.LocalRup.prove_clause [c312, c121] c316 (by decide) p (sat_cons (step312 p h) (sat_cons (step121 p h) (sat_nil p)))
def c317 : List Lit := [(1248, false)]
theorem step317 (p : Nat → Bool) (h : Constraints p) : clause p c317 = true :=
  Snake9.LocalRup.prove_clause [c313, c113] c317 (by decide) p (sat_cons (step313 p h) (sat_cons (step113 p h) (sat_nil p)))
def c318 : List Lit := [(1343, false)]
theorem step318 (p : Nat → Bool) (h : Constraints p) : clause p c318 = true :=
  Snake9.LocalRup.prove_clause [c314, c273, c230] c318 (by decide) p (sat_cons (step314 p h) (sat_cons (step273 p h) (sat_cons (step230 p h) (sat_nil p))))
def c319 : List Lit := [(29, true)]
theorem step319 (p : Nat → Bool) (h : Constraints p) : clause p c319 = true :=
  Snake9.LocalRup.prove_clause [c315, c117] c319 (by decide) p (sat_cons (step315 p h) (sat_cons (step117 p h) (sat_nil p)))
def c320 : List Lit := [(1245, false)]
theorem step320 (p : Nat → Bool) (h : Constraints p) : clause p c320 = true :=
  Snake9.LocalRup.prove_clause [c317, c108] c320 (by decide) p (sat_cons (step317 p h) (sat_cons (step108 p h) (sat_nil p)))
def c321 : List Lit := [(1321, false)]
theorem step321 (p : Nat → Bool) (h : Constraints p) : clause p c321 = true :=
  Snake9.LocalRup.prove_clause [c318, c199] c321 (by decide) p (sat_cons (step318 p h) (sat_cons (step199 p h) (sat_nil p)))
def c322 : List Lit := [(31, true)]
theorem step322 (p : Nat → Bool) (h : Constraints p) : clause p c322 = true :=
  Snake9.LocalRup.prove_clause [c319, c55, c8] c322 (by decide) p (sat_cons (step319 p h) (sat_cons (step55 p h) (sat_cons (step8 p h) (sat_nil p))))
def c323 : List Lit := [(1317, false)]
theorem step323 (p : Nat → Bool) (h : Constraints p) : clause p c323 = true :=
  Snake9.LocalRup.prove_clause [c321, c295, c190] c323 (by decide) p (sat_cons (step321 p h) (sat_cons (step295 p h) (sat_cons (step190 p h) (sat_nil p))))
def c324 : List Lit := [(27, false)]
theorem step324 (p : Nat → Bool) (h : Constraints p) : clause p c324 = true :=
  Snake9.LocalRup.prove_clause [c322, c316, c319, c9] c324 (by decide) p (sat_cons (step322 p h) (sat_cons (step316 p h) (sat_cons (step319 p h) (sat_cons (step9 p h) (sat_nil p)))))
def c325 : List Lit := [(1314, false)]
theorem step325 (p : Nat → Bool) (h : Constraints p) : clause p c325 = true :=
  Snake9.LocalRup.prove_clause [c323, c244] c325 (by decide) p (sat_cons (step323 p h) (sat_cons (step244 p h) (sat_nil p)))
def c326 : List Lit := [(1242, true)]
theorem step326 (p : Nat → Bool) (h : Constraints p) : clause p c326 = true :=
  Snake9.LocalRup.prove_clause [c324, c102] c326 (by decide) p (sat_cons (step324 p h) (sat_cons (step102 p h) (sat_nil p)))
def c327 : List Lit := [(66, true)]
theorem step327 (p : Nat → Bool) (h : Constraints p) : clause p c327 = true :=
  Snake9.LocalRup.prove_clause [c325, c183] c327 (by decide) p (sat_cons (step325 p h) (sat_cons (step183 p h) (sat_nil p)))
def c328 : List Lit := [(64, true)]
theorem step328 (p : Nat → Bool) (h : Constraints p) : clause p c328 = true :=
  Snake9.LocalRup.prove_clause [c325, c184] c328 (by decide) p (sat_cons (step325 p h) (sat_cons (step184 p h) (sat_nil p)))
def c329 : List Lit := [(1244, true)]
theorem step329 (p : Nat → Bool) (h : Constraints p) : clause p c329 = true :=
  Snake9.LocalRup.prove_clause [c326, c104] c329 (by decide) p (sat_cons (step326 p h) (sat_cons (step104 p h) (sat_nil p)))
def c330 : List Lit := [(22, true)]
theorem step330 (p : Nat → Bool) (h : Constraints p) : clause p c330 = true :=
  Snake9.LocalRup.prove_clause [c326, c320, c106] c330 (by decide) p (sat_cons (step326 p h) (sat_cons (step320 p h) (sat_cons (step106 p h) (sat_nil p))))
def c331 : List Lit := [(1247, true)]
theorem step331 (p : Nat → Bool) (h : Constraints p) : clause p c331 = true :=
  Snake9.LocalRup.prove_clause [c329, c107] c331 (by decide) p (sat_cons (step329 p h) (sat_cons (step107 p h) (sat_nil p)))
def c332 : List Lit := [(1239, false)]
theorem step332 (p : Nat → Bool) (h : Constraints p) : clause p c332 = true :=
  Snake9.LocalRup.prove_clause [c329, c317, c110] c332 (by decide) p (sat_cons (step329 p h) (sat_cons (step317 p h) (sat_cons (step110 p h) (sat_nil p))))
def c333 : List Lit := [(1231, false)]
theorem step333 (p : Nat → Bool) (h : Constraints p) : clause p c333 = true :=
  Snake9.LocalRup.prove_clause [c331, c313, c115] c333 (by decide) p (sat_cons (step331 p h) (sat_cons (step313 p h) (sat_cons (step115 p h) (sat_nil p))))
def c334 : List Lit := [(1237, false)]
theorem step334 (p : Nat → Bool) (h : Constraints p) : clause p c334 = true :=
  Snake9.LocalRup.prove_clause [c332, c99] c334 (by decide) p (sat_cons (step332 p h) (sat_cons (step99 p h) (sat_nil p)))
def c335 : List Lit := [(17, true)]
theorem step335 (p : Nat → Bool) (h : Constraints p) : clause p c335 = true :=
  Snake9.LocalRup.prove_clause [c332, c100] c335 (by decide) p (sat_cons (step332 p h) (sat_cons (step100 p h) (sat_nil p)))
def c336 : List Lit := [(1223, false)]
theorem step336 (p : Nat → Bool) (h : Constraints p) : clause p c336 = true :=
  Snake9.LocalRup.prove_clause [c333, c97] c336 (by decide) p (sat_cons (step333 p h) (sat_cons (step97 p h) (sat_nil p)))
def c337 : List Lit := [(20, true)]
theorem step337 (p : Nat → Bool) (h : Constraints p) : clause p c337 = true :=
  Snake9.LocalRup.prove_clause [c334, c98] c337 (by decide) p (sat_cons (step334 p h) (sat_cons (step98 p h) (sat_nil p)))
def c338 : List Lit := [(21, false)]
theorem step338 (p : Nat → Bool) (h : Constraints p) : clause p c338 = true :=
  Snake9.LocalRup.prove_clause [c335, c337, c330, c5] c338 (by decide) p (sat_cons (step335 p h) (sat_cons (step337 p h) (sat_cons (step330 p h) (sat_cons (step5 p h) (sat_nil p)))))
def c339 : List Lit := [(1221, false)]
theorem step339 (p : Nat → Bool) (h : Constraints p) : clause p c339 = true :=
  Snake9.LocalRup.prove_clause [c336, c95] c339 (by decide) p (sat_cons (step336 p h) (sat_cons (step95 p h) (sat_nil p)))
def c340 : List Lit := [(5, true)]
theorem step340 (p : Nat → Bool) (h : Constraints p) : clause p c340 = true :=
  Snake9.LocalRup.prove_clause [c336, c96] c340 (by decide) p (sat_cons (step336 p h) (sat_cons (step96 p h) (sat_nil p)))
def c341 : List Lit := [(7, true)]
theorem step341 (p : Nat → Bool) (h : Constraints p) : clause p c341 = true :=
  Snake9.LocalRup.prove_clause [c339, c93] c341 (by decide) p (sat_cons (step339 p h) (sat_cons (step93 p h) (sat_nil p)))
def c342 : List Lit := [(6, true)]
theorem step342 (p : Nat → Bool) (h : Constraints p) : clause p c342 = true :=
  Snake9.LocalRup.prove_clause [c339, c94] c342 (by decide) p (sat_cons (step339 p h) (sat_cons (step94 p h) (sat_nil p)))
def c343 : List Lit := [(4, false)]
theorem step343 (p : Nat → Bool) (h : Constraints p) : clause p c343 = true :=
  Snake9.LocalRup.prove_clause [c340, c342, c341, c1] c343 (by decide) p (sat_cons (step340 p h) (sat_cons (step342 p h) (sat_cons (step341 p h) (sat_cons (step1 p h) (sat_nil p)))))
def c344 : List Lit := [(65, true)]
theorem step344 (p : Nat → Bool) (h : Constraints p) : clause p c344 = true :=
  Snake9.LocalRup.prove_clause [c340, c52, c343, c338, c2] c344 (by decide) p (sat_cons (step340 p h) (sat_cons (step52 p h) (sat_cons (step343 p h) (sat_cons (step338 p h) (sat_cons (step2 p h) (sat_nil p))))))
def c345 : List Lit := []
theorem step345 (p : Nat → Bool) (h : Constraints p) : clause p c345 = true :=
  Snake9.LocalRup.prove_clause [c344, c340, c327, c328, c43] c345 (by decide) p (sat_cons (step344 p h) (sat_cons (step340 p h) (sat_cons (step327 p h) (sat_cons (step328 p h) (sat_cons (step43 p h) (sat_nil p))))))
end B112E182
