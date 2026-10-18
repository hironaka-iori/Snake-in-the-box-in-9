import B112E249Inputs
namespace B112E249
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c413 : List Lit := [(34, true)]
theorem step413 (p : Nat → Bool) (h : Constraints p) : clause p c413 = true :=
  Snake9.LocalRup.prove_clause [c34, c33] c413 (by decide) p (sat_cons (step34 p h) (sat_cons (step33 p h) (sat_nil p)))
def c414 : List Lit := [(1, false)]
theorem step414 (p : Nat → Bool) (h : Constraints p) : clause p c414 = true :=
  Snake9.LocalRup.prove_clause [c93, c1] c414 (by decide) p (sat_cons (step93 p h) (sat_cons (step1 p h) (sat_nil p)))
def c415 : List Lit := [(33, false)]
theorem step415 (p : Nat → Bool) (h : Constraints p) : clause p c415 = true :=
  Snake9.LocalRup.prove_clause [c94, c18] c415 (by decide) p (sat_cons (step94 p h) (sat_cons (step18 p h) (sat_nil p)))
def c416 : List Lit := [(35, false)]
theorem step416 (p : Nat → Bool) (h : Constraints p) : clause p c416 = true :=
  Snake9.LocalRup.prove_clause [c95, c21] c416 (by decide) p (sat_cons (step95 p h) (sat_cons (step21 p h) (sat_nil p)))
def c417 : List Lit := [(39, false)]
theorem step417 (p : Nat → Bool) (h : Constraints p) : clause p c417 = true :=
  Snake9.LocalRup.prove_clause [c97, c25] c417 (by decide) p (sat_cons (step97 p h) (sat_cons (step25 p h) (sat_nil p)))
def c418 : List Lit := [(418, false)]
theorem step418 (p : Nat → Bool) (h : Constraints p) : clause p c418 = true :=
  Snake9.LocalRup.prove_clause [c242, c239] c418 (by decide) p (sat_cons (step242 p h) (sat_cons (step239 p h) (sat_nil p)))
def c419 : List Lit := [(314, false)]
theorem step419 (p : Nat → Bool) (h : Constraints p) : clause p c419 = true :=
  Snake9.LocalRup.prove_clause [c242, c241] c419 (by decide) p (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_nil p)))
def c420 : List Lit := [(416, false)]
theorem step420 (p : Nat → Bool) (h : Constraints p) : clause p c420 = true :=
  Snake9.LocalRup.prove_clause [c418, c235] c420 (by decide) p (sat_cons (step418 p h) (sat_cons (step235 p h) (sat_nil p)))
def c421 : List Lit := [(364, false)]
theorem step421 (p : Nat → Bool) (h : Constraints p) : clause p c421 = true :=
  Snake9.LocalRup.prove_clause [c418, c238] c421 (by decide) p (sat_cons (step418 p h) (sat_cons (step238 p h) (sat_nil p)))
def c422 : List Lit := [(312, false)]
theorem step422 (p : Nat → Bool) (h : Constraints p) : clause p c422 = true :=
  Snake9.LocalRup.prove_clause [c419, c166] c422 (by decide) p (sat_cons (step419 p h) (sat_cons (step166 p h) (sat_nil p)))
def c423 : List Lit := [(262, false)]
theorem step423 (p : Nat → Bool) (h : Constraints p) : clause p c423 = true :=
  Snake9.LocalRup.prove_clause [c419, c169] c423 (by decide) p (sat_cons (step419 p h) (sat_cons (step169 p h) (sat_nil p)))
def c424 : List Lit := [(414, false)]
theorem step424 (p : Nat → Bool) (h : Constraints p) : clause p c424 = true :=
  Snake9.LocalRup.prove_clause [c420, c231] c424 (by decide) p (sat_cons (step420 p h) (sat_cons (step231 p h) (sat_nil p)))
def c425 : List Lit := [(388, false)]
theorem step425 (p : Nat → Bool) (h : Constraints p) : clause p c425 = true :=
  Snake9.LocalRup.prove_clause [c420, c233] c425 (by decide) p (sat_cons (step420 p h) (sat_cons (step233 p h) (sat_nil p)))
def c426 : List Lit := [(362, false)]
theorem step426 (p : Nat → Bool) (h : Constraints p) : clause p c426 = true :=
  Snake9.LocalRup.prove_clause [c421, c196] c426 (by decide) p (sat_cons (step421 p h) (sat_cons (step196 p h) (sat_nil p)))
def c427 : List Lit := [(338, false)]
theorem step427 (p : Nat → Bool) (h : Constraints p) : clause p c427 = true :=
  Snake9.LocalRup.prove_clause [c421, c199] c427 (by decide) p (sat_cons (step421 p h) (sat_cons (step199 p h) (sat_nil p)))
def c428 : List Lit := [(310, false)]
theorem step428 (p : Nat → Bool) (h : Constraints p) : clause p c428 = true :=
  Snake9.LocalRup.prove_clause [c422, c161] c428 (by decide) p (sat_cons (step422 p h) (sat_cons (step161 p h) (sat_nil p)))
def c429 : List Lit := [(286, false)]
theorem step429 (p : Nat → Bool) (h : Constraints p) : clause p c429 = true :=
  Snake9.LocalRup.prove_clause [c422, c164] c429 (by decide) p (sat_cons (step422 p h) (sat_cons (step164 p h) (sat_nil p)))
def c430 : List Lit := [(236, false)]
theorem step430 (p : Nat → Bool) (h : Constraints p) : clause p c430 = true :=
  Snake9.LocalRup.prove_clause [c423, c129] c430 (by decide) p (sat_cons (step423 p h) (sat_cons (step129 p h) (sat_nil p)))
def c431 : List Lit := [(412, false)]
theorem step431 (p : Nat → Bool) (h : Constraints p) : clause p c431 = true :=
  Snake9.LocalRup.prove_clause [c424, c228] c431 (by decide) p (sat_cons (step424 p h) (sat_cons (step228 p h) (sat_nil p)))
def c432 : List Lit := [(386, false)]
theorem step432 (p : Nat → Bool) (h : Constraints p) : clause p c432 = true :=
  Snake9.LocalRup.prove_clause [c425, c214] c432 (by decide) p (sat_cons (step425 p h) (sat_cons (step214 p h) (sat_nil p)))
def c433 : List Lit := [(348, false)]
theorem step433 (p : Nat → Bool) (h : Constraints p) : clause p c433 = true :=
  Snake9.LocalRup.prove_clause [c426, c194] c433 (by decide) p (sat_cons (step426 p h) (sat_cons (step194 p h) (sat_nil p)))
def c434 : List Lit := [(336, false)]
theorem step434 (p : Nat → Bool) (h : Constraints p) : clause p c434 = true :=
  Snake9.LocalRup.prove_clause [c427, c182] c434 (by decide) p (sat_cons (step427 p h) (sat_cons (step182 p h) (sat_nil p)))
def c435 : List Lit := [(308, false)]
theorem step435 (p : Nat → Bool) (h : Constraints p) : clause p c435 = true :=
  Snake9.LocalRup.prove_clause [c428, c156] c435 (by decide) p (sat_cons (step428 p h) (sat_cons (step156 p h) (sat_nil p)))
def c436 : List Lit := [(296, false)]
theorem step436 (p : Nat → Bool) (h : Constraints p) : clause p c436 = true :=
  Snake9.LocalRup.prove_clause [c428, c159] c436 (by decide) p (sat_cons (step428 p h) (sat_cons (step159 p h) (sat_nil p)))
def c437 : List Lit := [(272, false)]
theorem step437 (p : Nat → Bool) (h : Constraints p) : clause p c437 = true :=
  Snake9.LocalRup.prove_clause [c429, c141] c437 (by decide) p (sat_cons (step429 p h) (sat_cons (step141 p h) (sat_nil p)))
def c438 : List Lit := [(234, false)]
theorem step438 (p : Nat → Bool) (h : Constraints p) : clause p c438 = true :=
  Snake9.LocalRup.prove_clause [c430, c118] c438 (by decide) p (sat_cons (step430 p h) (sat_cons (step118 p h) (sat_nil p)))
def c439 : List Lit := [(410, false)]
theorem step439 (p : Nat → Bool) (h : Constraints p) : clause p c439 = true :=
  Snake9.LocalRup.prove_clause [c431, c226] c439 (by decide) p (sat_cons (step431 p h) (sat_cons (step226 p h) (sat_nil p)))
def c440 : List Lit := [(342, false)]
theorem step440 (p : Nat → Bool) (h : Constraints p) : clause p c440 = true :=
  Snake9.LocalRup.prove_clause [c433, c188] c440 (by decide) p (sat_cons (step433 p h) (sat_cons (step188 p h) (sat_nil p)))
def c441 : List Lit := [(306, false)]
theorem step441 (p : Nat → Bool) (h : Constraints p) : clause p c441 = true :=
  Snake9.LocalRup.prove_clause [c435, c154] c441 (by decide) p (sat_cons (step435 p h) (sat_cons (step154 p h) (sat_nil p)))
def c442 : List Lit := [(290, false)]
theorem step442 (p : Nat → Bool) (h : Constraints p) : clause p c442 = true :=
  Snake9.LocalRup.prove_clause [c436, c148] c442 (by decide) p (sat_cons (step436 p h) (sat_cons (step148 p h) (sat_nil p)))
def c443 : List Lit := [(232, false)]
theorem step443 (p : Nat → Bool) (h : Constraints p) : clause p c443 = true :=
  Snake9.LocalRup.prove_clause [c438, c116] c443 (by decide) p (sat_cons (step438 p h) (sat_cons (step116 p h) (sat_nil p)))
def c444 : List Lit := [(406, false)]
theorem step444 (p : Nat → Bool) (h : Constraints p) : clause p c444 = true :=
  Snake9.LocalRup.prove_clause [c439, c224] c444 (by decide) p (sat_cons (step439 p h) (sat_cons (step224 p h) (sat_nil p)))
def c445 : List Lit := [(66, false), (68, false), (67, false)]
theorem step445 (p : Nat → Bool) (h : Constraints p) : clause p c445 = true :=
  Snake9.LocalRup.prove_clause [c440, c56, c53, c55, c186, c184] c445 (by decide) p (sat_cons (step440 p h) (sat_cons (step56 p h) (sat_cons (step53 p h) (sat_cons (step55 p h) (sat_cons (step186 p h) (sat_cons (step184 p h) (sat_nil p)))))))
def c446 : List Lit := [(1408, true)]
theorem step446 (p : Nat → Bool) (h : Constraints p) : clause p c446 = true :=
  Snake9.LocalRup.prove_clause [c349, c352, c346, c328, c335, c336, c324, c334, c321, c445] c446 (by decide) p (sat_cons (step349 p h) (sat_cons (step352 p h) (sat_cons (step346 p h) (sat_cons (step328 p h) (sat_cons (step335 p h) (sat_cons (step336 p h) (sat_cons (step324 p h) (sat_cons (step334 p h) (sat_cons (step321 p h) (sat_cons (step445 p h) (sat_nil p)))))))))))
def c447 : List Lit := [(1292, true), (117, true)]
theorem step447 (p : Nat → Bool) (h : Constraints p) : clause p c447 = true :=
  Snake9.LocalRup.prove_clause [c249, c250, c247, c248, c9, c10] c447 (by decide) p (sat_cons (step249 p h) (sat_cons (step250 p h) (sat_cons (step247 p h) (sat_cons (step248 p h) (sat_cons (step9 p h) (sat_cons (step10 p h) (sat_nil p)))))))
def c448 : List Lit := [(1295, true)]
theorem step448 (p : Nat → Bool) (h : Constraints p) : clause p c448 = true :=
  Snake9.LocalRup.prove_clause [c413, c443, c251, c252, c249, c250, c447, c245, c247, c248, c9, c111, c244, c4, c114, c11, c112] c448 (by decide) p (sat_cons (step413 p h) (sat_cons (step443 p h) (sat_cons (step251 p h) (sat_cons (step252 p h) (sat_cons (step249 p h) (sat_cons (step250 p h) (sat_cons (step447 p h) (sat_cons (step245 p h) (sat_cons (step247 p h) (sat_cons (step248 p h) (sat_cons (step9 p h) (sat_cons (step111 p h) (sat_cons (step244 p h) (sat_cons (step4 p h) (sat_cons (step114 p h) (sat_cons (step11 p h) (sat_cons (step112 p h) (sat_nil p))))))))))))))))))
def c449 : List Lit := [(1317, true)]
theorem step449 (p : Nat → Bool) (h : Constraints p) : clause p c449 = true :=
  Snake9.LocalRup.prove_clause [c448, c262] c449 (by decide) p (sat_cons (step448 p h) (sat_cons (step262 p h) (sat_nil p)))
def c450 : List Lit := [(40, false), (42, false), (41, false)]
theorem step450 (p : Nat → Bool) (h : Constraints p) : clause p c450 = true :=
  Snake9.LocalRup.prove_clause [c442, c31, c26, c29, c146, c142] c450 (by decide) p (sat_cons (step442 p h) (sat_cons (step31 p h) (sat_cons (step26 p h) (sat_cons (step29 p h) (sat_cons (step146 p h) (sat_cons (step142 p h) (sat_nil p)))))))
def c451 : List Lit := [(1318, true), (4, true), (261, true)]
theorem step451 (p : Nat → Bool) (h : Constraints p) : clause p c451 = true :=
  Snake9.LocalRup.prove_clause [c448, c414, c128, c117, c115, c113, c111, c447, c119, c110, c106, c105, c109, c108, c107, c127, c126, c121, c120, c264, c263, c253, c261, c245, c246, c256, c243, c244, c12, c3, c7, c2, c8] c451 (by decide) p (sat_cons (step448 p h) (sat_cons (step414 p h) (sat_cons (step128 p h) (sat_cons (step117 p h) (sat_cons (step115 p h) (sat_cons (step113 p h) (sat_cons (step111 p h) (sat_cons (step447 p h) (sat_cons (step119 p h) (sat_cons (step110 p h) (sat_cons (step106 p h) (sat_cons (step105 p h) (sat_cons (step109 p h) (sat_cons (step108 p h) (sat_cons (step107 p h) (sat_cons (step127 p h) (sat_cons (step126 p h) (sat_cons (step121 p h) (sat_cons (step120 p h) (sat_cons (step264 p h) (sat_cons (step263 p h) (sat_cons (step253 p h) (sat_cons (step261 p h) (sat_cons (step245 p h) (sat_cons (step246 p h) (sat_cons (step256 p h) (sat_cons (step243 p h) (sat_cons (step244 p h) (sat_cons (step12 p h) (sat_cons (step3 p h) (sat_cons (step7 p h) (sat_cons (step2 p h) (sat_cons (step8 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c452 : List Lit := [(1328, true), (136, true)]
theorem step452 (p : Nat → Bool) (h : Constraints p) : clause p c452 = true :=
  Snake9.LocalRup.prove_clause [c268, c269, c266, c267, c16, c17] c452 (by decide) p (sat_cons (step268 p h) (sat_cons (step269 p h) (sat_cons (step266 p h) (sat_cons (step267 p h) (sat_cons (step16 p h) (sat_cons (step17 p h) (sat_nil p)))))))
def c453 : List Lit := [(1442, true), (210, true)]
theorem step453 (p : Nat → Bool) (h : Constraints p) : clause p c453 = true :=
  Snake9.LocalRup.prove_clause [c384, c385, c382, c383, c380, c91, c92] c453 (by decide) p (sat_cons (step384 p h) (sat_cons (step385 p h) (sat_cons (step382 p h) (sat_cons (step383 p h) (sat_cons (step380 p h) (sat_cons (step91 p h) (sat_cons (step92 p h) (sat_nil p))))))))
def c454 : List Lit := [(1409, true), (1399, false)]
theorem step454 (p : Nat → Bool) (h : Constraints p) : clause p c454 = true :=
  Snake9.LocalRup.prove_clause [c344, c350, c353, c347, c328, c335, c336, c324, c334, c321, c445] c454 (by decide) p (sat_cons (step344 p h) (sat_cons (step350 p h) (sat_cons (step353 p h) (sat_cons (step347 p h) (sat_cons (step328 p h) (sat_cons (step335 p h) (sat_cons (step336 p h) (sat_cons (step324 p h) (sat_cons (step334 p h) (sat_cons (step321 p h) (sat_cons (step445 p h) (sat_nil p))))))))))))
def c455 : List Lit := [(1383, true), (1354, true), (72, false), (41, true), (335, true)]
theorem step455 (p : Nat → Bool) (h : Constraints p) : clause p c455 = true :=
  Snake9.LocalRup.prove_clause [c179, c175, c174, c178, c177, c176, c324, c326, c321, c322, c50, c52, c51, c47, c291, c278, c298, c284] c455 (by decide) p (sat_cons (step179 p h) (sat_cons (step175 p h) (sat_cons (step174 p h) (sat_cons (step178 p h) (sat_cons (step177 p h) (sat_cons (step176 p h) (sat_cons (step324 p h) (sat_cons (step326 p h) (sat_cons (step321 p h) (sat_cons (step322 p h) (sat_cons (step50 p h) (sat_cons (step52 p h) (sat_cons (step51 p h) (sat_cons (step47 p h) (sat_cons (step291 p h) (sat_cons (step278 p h) (sat_cons (step298 p h) (sat_cons (step284 p h) (sat_nil p)))))))))))))))))))
def c456 : List Lit := [(1347, true), (158, true), (48, false)]
theorem step456 (p : Nat → Bool) (h : Constraints p) : clause p c456 = true :=
  Snake9.LocalRup.prove_clause [c286, c287, c41, c42] c456 (by decide) p (sat_cons (step286 p h) (sat_cons (step287 p h) (sat_cons (step41 p h) (sat_cons (step42 p h) (sat_nil p)))))
def c457 : List Lit := [(1328, true)]
theorem step457 (p : Nat → Bool) (h : Constraints p) : clause p c457 = true :=
  Snake9.LocalRup.prove_clause [c437, c268, c269, c452, c266, c267, c132, c17, c133, c15, c131, c130] c457 (by decide) p (sat_cons (step437 p h) (sat_cons (step268 p h) (sat_cons (step269 p h) (sat_cons (step452 p h) (sat_cons (step266 p h) (sat_cons (step267 p h) (sat_cons (step132 p h) (sat_cons (step17 p h) (sat_cons (step133 p h) (sat_cons (step15 p h) (sat_cons (step131 p h) (sat_cons (step130 p h) (sat_nil p)))))))))))))
def c458 : List Lit := [(1336, true)]
theorem step458 (p : Nat → Bool) (h : Constraints p) : clause p c458 = true :=
  Snake9.LocalRup.prove_clause [c457, c275] c458 (by decide) p (sat_cons (step457 p h) (sat_cons (step275 p h) (sat_nil p)))
def c459 : List Lit := [(41, true), (1388, false), (1453, false), (36, false), (148, true), (1318, false)]
theorem step459 (p : Nat → Bool) (h : Constraints p) : clause p c459 = true :=
  Snake9.LocalRup.prove_clause [c458, c99, c412, c413, c359, c405, c410, c313, c301, c297, c283, c284, c294, c279, c300, c29, c312, c32, c409, c22, c407, c338, c360, c340, c344] c459 (by decide) p (sat_cons (step458 p h) (sat_cons (step99 p h) (sat_cons (step412 p h) (sat_cons (step413 p h) (sat_cons (step359 p h) (sat_cons (step405 p h) (sat_cons (step410 p h) (sat_cons (step313 p h) (sat_cons (step301 p h) (sat_cons (step297 p h) (sat_cons (step283 p h) (sat_cons (step284 p h) (sat_cons (step294 p h) (sat_cons (step279 p h) (sat_cons (step300 p h) (sat_cons (step29 p h) (sat_cons (step312 p h) (sat_cons (step32 p h) (sat_cons (step409 p h) (sat_cons (step22 p h) (sat_cons (step407 p h) (sat_cons (step338 p h) (sat_cons (step360 p h) (sat_cons (step340 p h) (sat_cons (step344 p h) (sat_nil p))))))))))))))))))))))))))
def c460 : List Lit := [(1331, true), (41, false), (144, true)]
theorem step460 (p : Nat → Bool) (h : Constraints p) : clause p c460 = true :=
  Snake9.LocalRup.prove_clause [c417, c98, c270, c271, c450, c24, c30] c460 (by decide) p (sat_cons (step417 p h) (sat_cons (step98 p h) (sat_cons (step270 p h) (sat_cons (step271 p h) (sat_cons (step450 p h) (sat_cons (step24 p h) (sat_cons (step30 p h) (sat_nil p))))))))
def c461 : List Lit := [(1349, true), (48, false)]
theorem step461 (p : Nat → Bool) (h : Constraints p) : clause p c461 = true :=
  Snake9.TreeRup.prove_clause [c441, c100, c428, c422, c419, c242, c416, c415, c413, c457, c412, c289, c291, c286, c287, c456, c42, c150, c40, c151, c152, c35, c153, c149, c44, c155, c158, c39, c160, c163, c147, c37, c38, c36, c165, c168, c140, c144, c240, c451, c138, c139, c142, c234, c236, c137, c135, c230, c197, c136, c134, c227, c181, c183, c20, c225, c178, c179, c173, c223, c177, c175, c171, c221, c176, c174, c170, c453, c52, c45, c386, c321, c317, c389, c324, c320, c331, c459, c460, c273, c276, c303, c312, c409, c407, c361, c332, c325, c327, c323, c50, c51] c461 (by decide) p (sat_cons (step441 p h) (sat_cons (step100 p h) (sat_cons (step428 p h) (sat_cons (step422 p h) (sat_cons (step419 p h) (sat_cons (step242 p h) (sat_cons (step416 p h) (sat_cons (step415 p h) (sat_cons (step413 p h) (sat_cons (step457 p h) (sat_cons (step412 p h) (sat_cons (step289 p h) (sat_cons (step291 p h) (sat_cons (step286 p h) (sat_cons (step287 p h) (sat_cons (step456 p h) (sat_cons (step42 p h) (sat_cons (step150 p h) (sat_cons (step40 p h) (sat_cons (step151 p h) (sat_cons (step152 p h) (sat_cons (step35 p h) (sat_cons (step153 p h) (sat_cons (step149 p h) (sat_cons (step44 p h) (sat_cons (step155 p h) (sat_cons (step158 p h) (sat_cons (step39 p h) (sat_cons (step160 p h) (sat_cons (step163 p h) (sat_cons (step147 p h) (sat_cons (step37 p h) (sat_cons (step38 p h) (sat_cons (step36 p h) (sat_cons (step165 p h) (sat_cons (step168 p h) (sat_cons (step140 p h) (sat_cons (step144 p h) (sat_cons (step240 p h) (sat_cons (step451 p h) (sat_cons (step138 p h) (sat_cons (step139 p h) (sat_cons (step142 p h) (sat_cons (step234 p h) (sat_cons (step236 p h) (sat_cons (step137 p h) (sat_cons (step135 p h) (sat_cons (step230 p h) (sat_cons (step197 p h) (sat_cons (step136 p h) (sat_cons (step134 p h) (sat_cons (step227 p h) (sat_cons (step181 p h) (sat_cons (step183 p h) (sat_cons (step20 p h) (sat_cons (step225 p h) (sat_cons (step178 p h) (sat_cons (step179 p h) (sat_cons (step173 p h) (sat_cons (step223 p h) (sat_cons (step177 p h) (sat_cons (step175 p h) (sat_cons (step171 p h) (sat_cons (step221 p h) (sat_cons (step176 p h) (sat_cons (step174 p h) (sat_cons (step170 p h) (sat_cons (step453 p h) (sat_cons (step52 p h) (sat_cons (step45 p h) (sat_cons (step386 p h) (sat_cons (step321 p h) (sat_cons (step317 p h) (sat_cons (step389 p h) (sat_cons (step324 p h) (sat_cons (step320 p h) (sat_cons (step331 p h) (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step273 p h) (sat_cons (step276 p h) (sat_cons (step303 p h) (sat_cons (step312 p h) (sat_cons (step409 p h) (sat_cons (step407 p h) (sat_cons (step361 p h) (sat_cons (step332 p h) (sat_cons (step325 p h) (sat_cons (step327 p h) (sat_cons (step323 p h) (sat_cons (step50 p h) (sat_cons (step51 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c462 : List Lit := [(1331, true), (1318, false), (36, false), (41, false), (1349, false)]
theorem step462 (p : Nat → Bool) (h : Constraints p) : clause p c462 = true :=
  Snake9.LocalRup.prove_clause [c413, c458, c422, c412, c242, c270, c460, c22, c450, c136, c338, c279, c137, c340, c281, c138, c454, c295, c140, c301, c162, c163, c313, c165, c157, c410, c240, c147, c402, c234, c144, c230, c143, c227, c28, c225, c223, c221, c453, c386, c392, c370, c371, c368, c365, c367, c77] c462 (by decide) p (sat_cons (step413 p h) (sat_cons (step458 p h) (sat_cons (step422 p h) (sat_cons (step412 p h) (sat_cons (step242 p h) (sat_cons (step270 p h) (sat_cons (step460 p h) (sat_cons (step22 p h) (sat_cons (step450 p h) (sat_cons (step136 p h) (sat_cons (step338 p h) (sat_cons (step279 p h) (sat_cons (step137 p h) (sat_cons (step340 p h) (sat_cons (step281 p h) (sat_cons (step138 p h) (sat_cons (step454 p h) (sat_cons (step295 p h) (sat_cons (step140 p h) (sat_cons (step301 p h) (sat_cons (step162 p h) (sat_cons (step163 p h) (sat_cons (step313 p h) (sat_cons (step165 p h) (sat_cons (step157 p h) (sat_cons (step410 p h) (sat_cons (step240 p h) (sat_cons (step147 p h) (sat_cons (step402 p h) (sat_cons (step234 p h) (sat_cons (step144 p h) (sat_cons (step230 p h) (sat_cons (step143 p h) (sat_cons (step227 p h) (sat_cons (step28 p h) (sat_cons (step225 p h) (sat_cons (step223 p h) (sat_cons (step221 p h) (sat_cons (step453 p h) (sat_cons (step386 p h) (sat_cons (step392 p h) (sat_cons (step370 p h) (sat_cons (step371 p h) (sat_cons (step368 p h) (sat_cons (step365 p h) (sat_cons (step367 p h) (sat_cons (step77 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c463 : List Lit := [(40, false), (1453, false), (1318, false), (36, false), (41, false), (1349, false)]
theorem step463 (p : Nat → Bool) (h : Constraints p) : clause p c463 = true :=
  Snake9.LocalRup.prove_clause [c457, c413, c412, c462, c273, c276, c22, c450, c338, c279, c340, c281, c454, c295, c401, c305, c411, c314] c463 (by decide) p (sat_cons (step457 p h) (sat_cons (step413 p h) (sat_cons (step412 p h) (sat_cons (step462 p h) (sat_cons (step273 p h) (sat_cons (step276 p h) (sat_cons (step22 p h) (sat_cons (step450 p h) (sat_cons (step338 p h) (sat_cons (step279 p h) (sat_cons (step340 p h) (sat_cons (step281 p h) (sat_cons (step454 p h) (sat_cons (step295 p h) (sat_cons (step401 p h) (sat_cons (step305 p h) (sat_cons (step411 p h) (sat_cons (step314 p h) (sat_nil p)))))))))))))))))))
def c464 : List Lit := [(1419, true), (78, false)]
theorem step464 (p : Nat → Bool) (h : Constraints p) : clause p c464 = true :=
  Snake9.LocalRup.prove_clause [c364, c365, c362, c363, c72, c66, c71] c464 (by decide) p (sat_cons (step364 p h) (sat_cons (step365 p h) (sat_cons (step362 p h) (sat_cons (step363 p h) (sat_cons (step72 p h) (sat_cons (step66 p h) (sat_cons (step71 p h) (sat_nil p))))))))
def c465 : List Lit := [(1454, true), (1419, false), (41, false)]
theorem step465 (p : Nat → Bool) (h : Constraints p) : clause p c465 = true :=
  Snake9.LocalRup.prove_clause [c371, c395, c372, c392, c368, c386, c367, c384, c385, c382, c383, c380, c381, c78, c92, c88, c89] c465 (by decide) p (sat_cons (step371 p h) (sat_cons (step395 p h) (sat_cons (step372 p h) (sat_cons (step392 p h) (sat_cons (step368 p h) (sat_cons (step386 p h) (sat_cons (step367 p h) (sat_cons (step384 p h) (sat_cons (step385 p h) (sat_cons (step382 p h) (sat_cons (step383 p h) (sat_cons (step380 p h) (sat_cons (step381 p h) (sat_cons (step78 p h) (sat_cons (step92 p h) (sat_cons (step88 p h) (sat_cons (step89 p h) (sat_nil p))))))))))))))))))
def c466 : List Lit := [(1442, true)]
theorem step466 (p : Nat → Bool) (h : Constraints p) : clause p c466 = true :=
  Snake9.LocalRup.prove_clause [c444, c384, c385, c453, c382, c383, c380, c381, c222, c92, c88, c90] c466 (by decide) p (sat_cons (step444 p h) (sat_cons (step384 p h) (sat_cons (step385 p h) (sat_cons (step453 p h) (sat_cons (step382 p h) (sat_cons (step383 p h) (sat_cons (step380 p h) (sat_cons (step381 p h) (sat_cons (step222 p h) (sat_cons (step92 p h) (sat_cons (step88 p h) (sat_cons (step90 p h) (sat_nil p)))))))))))))
def c467 : List Lit := [(1446, true)]
theorem step467 (p : Nat → Bool) (h : Constraints p) : clause p c467 = true :=
  Snake9.LocalRup.prove_clause [c466, c386] c467 (by decide) p (sat_cons (step466 p h) (sat_cons (step386 p h) (sat_nil p)))
def c468 : List Lit := [(415, true), (86, false), (94, false), (78, false), (36, false)]
theorem step468 (p : Nat → Bool) (h : Constraints p) : clause p c468 = true :=
  Snake9.LocalRup.prove_clause [c103, c68, c230, c232, c229, c213, c215, c220, c211, c205, c219, c207, c204, c218, c76, c203, c83, c74, c73, c67] c468 (by decide) p (sat_cons (step103 p h) (sat_cons (step68 p h) (sat_cons (step230 p h) (sat_cons (step232 p h) (sat_cons (step229 p h) (sat_cons (step213 p h) (sat_cons (step215 p h) (sat_cons (step220 p h) (sat_cons (step211 p h) (sat_cons (step205 p h) (sat_cons (step219 p h) (sat_cons (step207 p h) (sat_cons (step204 p h) (sat_cons (step218 p h) (sat_cons (step76 p h) (sat_cons (step203 p h) (sat_cons (step83 p h) (sat_cons (step74 p h) (sat_cons (step73 p h) (sat_cons (step67 p h) (sat_nil p)))))))))))))))))))))
def c469 : List Lit := [(78, false), (1465, true), (36, false), (41, false), (48, false)]
theorem step469 (p : Nat → Bool) (h : Constraints p) : clause p c469 = true :=
  Snake9.LocalRup.prove_clause [c467, c446, c466, c418, c101, c399, c396, c464, c371, c465, c393, c402, c356, c454, c329, c342, c387, c376, c378, c372, c374, c369, c468, c237, c195, c197, c192, c181, c191, c178, c190, c177, c189, c176, c62, c63, c64, c60, c327, c321, c52, c47] c469 (by decide) p (sat_cons (step467 p h) (sat_cons (step446 p h) (sat_cons (step466 p h) (sat_cons (step418 p h) (sat_cons (step101 p h) (sat_cons (step399 p h) (sat_cons (step396 p h) (sat_cons (step464 p h) (sat_cons (step371 p h) (sat_cons (step465 p h) (sat_cons (step393 p h) (sat_cons (step402 p h) (sat_cons (step356 p h) (sat_cons (step454 p h) (sat_cons (step329 p h) (sat_cons (step342 p h) (sat_cons (step387 p h) (sat_cons (step376 p h) (sat_cons (step378 p h) (sat_cons (step372 p h) (sat_cons (step374 p h) (sat_cons (step369 p h) (sat_cons (step468 p h) (sat_cons (step237 p h) (sat_cons (step195 p h) (sat_cons (step197 p h) (sat_cons (step192 p h) (sat_cons (step181 p h) (sat_cons (step191 p h) (sat_cons (step178 p h) (sat_cons (step190 p h) (sat_cons (step177 p h) (sat_cons (step189 p h) (sat_cons (step176 p h) (sat_cons (step62 p h) (sat_cons (step63 p h) (sat_cons (step64 p h) (sat_cons (step60 p h) (sat_cons (step327 p h) (sat_cons (step321 p h) (sat_cons (step52 p h) (sat_cons (step47 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c470 : List Lit := [(1453, true)]
theorem step470 (p : Nat → Bool) (h : Constraints p) : clause p c470 = true :=
  Snake9.LocalRup.prove_clause [c467, c389] c470 (by decide) p (sat_cons (step467 p h) (sat_cons (step389 p h) (sat_nil p)))
def c471 : List Lit := [(1318, false), (36, false), (41, false), (48, false)]
theorem step471 (p : Nat → Bool) (h : Constraints p) : clause p c471 = true :=
  Snake9.LocalRup.prove_clause [c457, c412, c96, c470, c461, c293, c462, c273, c276, c304, c313, c410, c469, c23, c463] c471 (by decide) p (sat_cons (step457 p h) (sat_cons (step412 p h) (sat_cons (step96 p h) (sat_cons (step470 p h) (sat_cons (step461 p h) (sat_cons (step293 p h) (sat_cons (step462 p h) (sat_cons (step273 p h) (sat_cons (step276 p h) (sat_cons (step304 p h) (sat_cons (step313 p h) (sat_cons (step410 p h) (sat_cons (step469 p h) (sat_cons (step23 p h) (sat_cons (step463 p h) (sat_nil p))))))))))))))))
def c472 : List Lit := [(1454, true), (88, false), (41, false)]
theorem step472 (p : Nat → Bool) (h : Constraints p) : clause p c472 = true :=
  Snake9.LocalRup.prove_clause [c467, c465, c392, c365, c370, c77, c368, c367] c472 (by decide) p (sat_cons (step467 p h) (sat_cons (step465 p h) (sat_cons (step392 p h) (sat_cons (step365 p h) (sat_cons (step370 p h) (sat_cons (step77 p h) (sat_cons (step368 p h) (sat_cons (step367 p h) (sat_nil p)))))))))
def c473 : List Lit := [(1465, true), (36, false), (41, false), (48, false)]
theorem step473 (p : Nat → Bool) (h : Constraints p) : clause p c473 = true :=
  Snake9.LocalRup.prove_clause [c413, c34, c419, c19, c471, c451, c168, c160, c157, c147, c144, c143, c28, c472, c469, c402, c338, c454, c340] c473 (by decide) p (sat_cons (step413 p h) (sat_cons (step34 p h) (sat_cons (step419 p h) (sat_cons (step19 p h) (sat_cons (step471 p h) (sat_cons (step451 p h) (sat_cons (step168 p h) (sat_cons (step160 p h) (sat_cons (step157 p h) (sat_cons (step147 p h) (sat_cons (step144 p h) (sat_cons (step143 p h) (sat_cons (step28 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step402 p h) (sat_cons (step338 p h) (sat_cons (step454 p h) (sat_cons (step340 p h) (sat_nil p))))))))))))))))))))
def c474 : List Lit := [(1409, true), (172, true), (180, true), (21, false), (48, false)]
theorem step474 (p : Nat → Bool) (h : Constraints p) : clause p c474 = true :=
  Snake9.LocalRup.prove_clause [c101, c356, c454, c329, c342, c62, c63, c64, c57, c327, c321, c52, c47] c474 (by decide) p (sat_cons (step101 p h) (sat_cons (step356 p h) (sat_cons (step454 p h) (sat_cons (step329 p h) (sat_cons (step342 p h) (sat_cons (step62 p h) (sat_cons (step63 p h) (sat_cons (step64 p h) (sat_cons (step57 p h) (sat_cons (step327 p h) (sat_cons (step321 p h) (sat_cons (step52 p h) (sat_cons (step47 p h) (sat_nil p))))))))))))))
def c475 : List Lit := [(36, false), (41, false), (48, false)]
theorem step475 (p : Nat → Bool) (h : Constraints p) : clause p c475 = true :=
  Snake9.TreeRup.prove_clause [c34, c413, c448, c419, c242, c457, c412, c449, c96, c467, c466, c461, c293, c19, c471, c263, c451, c260, c167, c168, c259, c240, c162, c234, c236, c140, c195, c197, c138, c192, c181, c137, c191, c178, c136, c190, c177, c460, c189, c176, c273, c276, c304, c309, c409, c473, c410, c310, c305, c295, c281, c279, c450, c23, c464, c371, c474, c403, c396, c393, c372, c387, c369, c378, c468] c475 (by decide) p (sat_cons (step34 p h) (sat_cons (step413 p h) (sat_cons (step448 p h) (sat_cons (step419 p h) (sat_cons (step242 p h) (sat_cons (step457 p h) (sat_cons (step412 p h) (sat_cons (step449 p h) (sat_cons (step96 p h) (sat_cons (step467 p h) (sat_cons (step466 p h) (sat_cons (step461 p h) (sat_cons (step293 p h) (sat_cons (step19 p h) (sat_cons (step471 p h) (sat_cons (step263 p h) (sat_cons (step451 p h) (sat_cons (step260 p h) (sat_cons (step167 p h) (sat_cons (step168 p h) (sat_cons (step259 p h) (sat_cons (step240 p h) (sat_cons (step162 p h) (sat_cons (step234 p h) (sat_cons (step236 p h) (sat_cons (step140 p h) (sat_cons (step195 p h) (sat_cons (step197 p h) (sat_cons (step138 p h) (sat_cons (step192 p h) (sat_cons (step181 p h) (sat_cons (step137 p h) (sat_cons (step191 p h) (sat_cons (step178 p h) (sat_cons (step136 p h) (sat_cons (step190 p h) (sat_cons (step177 p h) (sat_cons (step460 p h) (sat_cons (step189 p h) (sat_cons (step176 p h) (sat_cons (step273 p h) (sat_cons (step276 p h) (sat_cons (step304 p h) (sat_cons (step309 p h) (sat_cons (step409 p h) (sat_cons (step473 p h) (sat_cons (step410 p h) (sat_cons (step310 p h) (sat_cons (step305 p h) (sat_cons (step295 p h) (sat_cons (step281 p h) (sat_cons (step279 p h) (sat_cons (step450 p h) (sat_cons (step23 p h) (sat_cons (step464 p h) (sat_cons (step371 p h) (sat_cons (step474 p h) (sat_cons (step403 p h) (sat_cons (step396 p h) (sat_cons (step393 p h) (sat_cons (step372 p h) (sat_cons (step387 p h) (sat_cons (step369 p h) (sat_cons (step378 p h) (sat_cons (step468 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c476 : List Lit := [(389, true), (96, true), (79, true), (95, false), (94, false), (1410, true), (78, false), (21, false)]
theorem step476 (p : Nat → Bool) (h : Constraints p) : clause p c476 = true :=
  Snake9.LocalRup.prove_clause [c217, c218, c84, c83, c59, c58, c82, c342, c326, c333, c328, c335, c354, c347] c476 (by decide) p (sat_cons (step217 p h) (sat_cons (step218 p h) (sat_cons (step84 p h) (sat_cons (step83 p h) (sat_cons (step59 p h) (sat_cons (step58 p h) (sat_cons (step82 p h) (sat_cons (step342 p h) (sat_cons (step326 p h) (sat_cons (step333 p h) (sat_cons (step328 p h) (sat_cons (step335 p h) (sat_cons (step354 p h) (sat_cons (step347 p h) (sat_nil p)))))))))))))))
end B112E249
