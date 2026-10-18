import B112E234Part0000
namespace B112E234
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c363 : List Lit := [(10, true), (9, false), (1338, false)]
theorem step363 (p : Nat → Bool) (h : Constraints p) : clause p c363 = true :=
  Snake9.LocalRup.prove_clause [c331, c293, c315, c323, c103, c352, c339, c361, c256, c139, c141, c362, c228, c291, c286, c282, c272, c270, c259, c263, c19, c260, c47, c46, c346, c296, c171, c153, c158] c363 (by decide) p (sat_cons (step331 p h) (sat_cons (step293 p h) (sat_cons (step315 p h) (sat_cons (step323 p h) (sat_cons (step103 p h) (sat_cons (step352 p h) (sat_cons (step339 p h) (sat_cons (step361 p h) (sat_cons (step256 p h) (sat_cons (step139 p h) (sat_cons (step141 p h) (sat_cons (step362 p h) (sat_cons (step228 p h) (sat_cons (step291 p h) (sat_cons (step286 p h) (sat_cons (step282 p h) (sat_cons (step272 p h) (sat_cons (step270 p h) (sat_cons (step259 p h) (sat_cons (step263 p h) (sat_cons (step19 p h) (sat_cons (step260 p h) (sat_cons (step47 p h) (sat_cons (step46 p h) (sat_cons (step346 p h) (sat_cons (step296 p h) (sat_cons (step171 p h) (sat_cons (step153 p h) (sat_cons (step158 p h) (sat_nil p))))))))))))))))))))))))))))))
def c364 : List Lit := [(1349, true), (1218, false), (1338, false)]
theorem step364 (p : Nat → Bool) (h : Constraints p) : clause p c364 = true :=
  Snake9.LocalRup.prove_clause [c256, c272, c350, c270, c259, c141, c263, c346, c260] c364 (by decide) p (sat_cons (step256 p h) (sat_cons (step272 p h) (sat_cons (step350 p h) (sat_cons (step270 p h) (sat_cons (step259 p h) (sat_cons (step141 p h) (sat_cons (step263 p h) (sat_cons (step346 p h) (sat_cons (step260 p h) (sat_nil p))))))))))
def c365 : List Lit := [(77, false), (73, false), (42, false), (13, false), (1344, true), (11, true)]
theorem step365 (p : Nat → Bool) (h : Constraints p) : clause p c365 = true :=
  Snake9.LocalRup.prove_clause [c117, c85, c354] c365 (by decide) p (sat_cons (step117 p h) (sat_cons (step85 p h) (sat_cons (step354 p h) (sat_nil p))))
def c366 : List Lit := [(9, false), (1338, false)]
theorem step366 (p : Nat → Bool) (h : Constraints p) : clause p c366 = true :=
  Snake9.TreeRup.prove_clause [c103, c352, c339, c323, c315, c293, c331, c330, c312, c98, c2, c112, c120, c256, c361, c363, c15, c47, c46, c296, c42, c153, c158, c171, c175, c225, c290, c287, c284, c271, c264, c364, c282, c286, c291, c228, c226, c176, c179, c219, c172, c146, c149, c215, c166, c141, c137, c206, c160, c138, c136, c204, c3, c1, c74, c365, c259, c273, c263, c265, c261, c93, c95] c366 (by decide) p (sat_cons (step103 p h) (sat_cons (step352 p h) (sat_cons (step339 p h) (sat_cons (step323 p h) (sat_cons (step315 p h) (sat_cons (step293 p h) (sat_cons (step331 p h) (sat_cons (step330 p h) (sat_cons (step312 p h) (sat_cons (step98 p h) (sat_cons (step2 p h) (sat_cons (step112 p h) (sat_cons (step120 p h) (sat_cons (step256 p h) (sat_cons (step361 p h) (sat_cons (step363 p h) (sat_cons (step15 p h) (sat_cons (step47 p h) (sat_cons (step46 p h) (sat_cons (step296 p h) (sat_cons (step42 p h) (sat_cons (step153 p h) (sat_cons (step158 p h) (sat_cons (step171 p h) (sat_cons (step175 p h) (sat_cons (step225 p h) (sat_cons (step290 p h) (sat_cons (step287 p h) (sat_cons (step284 p h) (sat_cons (step271 p h) (sat_cons (step264 p h) (sat_cons (step364 p h) (sat_cons (step282 p h) (sat_cons (step286 p h) (sat_cons (step291 p h) (sat_cons (step228 p h) (sat_cons (step226 p h) (sat_cons (step176 p h) (sat_cons (step179 p h) (sat_cons (step219 p h) (sat_cons (step172 p h) (sat_cons (step146 p h) (sat_cons (step149 p h) (sat_cons (step215 p h) (sat_cons (step166 p h) (sat_cons (step141 p h) (sat_cons (step137 p h) (sat_cons (step206 p h) (sat_cons (step160 p h) (sat_cons (step138 p h) (sat_cons (step136 p h) (sat_cons (step204 p h) (sat_cons (step3 p h) (sat_cons (step1 p h) (sat_cons (step74 p h) (sat_cons (step365 p h) (sat_cons (step259 p h) (sat_cons (step273 p h) (sat_cons (step263 p h) (sat_cons (step265 p h) (sat_cons (step261 p h) (sat_cons (step93 p h) (sat_cons (step95 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c367 : List Lit := [(1195, true), (1200, false)]
theorem step367 (p : Nat → Bool) (h : Constraints p) : clause p c367 = true :=
  Snake9.LocalRup.prove_clause [c323, c103, c315, c352, c293, c331, c339, c102, c138, c139, c350, c20, c282, c47, c46, c286, c296, c42, c291, c153, c228, c155, c179, c171, c170, c158, c166, c160, c161, c32, c56, c29] c367 (by decide) p (sat_cons (step323 p h) (sat_cons (step103 p h) (sat_cons (step315 p h) (sat_cons (step352 p h) (sat_cons (step293 p h) (sat_cons (step331 p h) (sat_cons (step339 p h) (sat_cons (step102 p h) (sat_cons (step138 p h) (sat_cons (step139 p h) (sat_cons (step350 p h) (sat_cons (step20 p h) (sat_cons (step282 p h) (sat_cons (step47 p h) (sat_cons (step46 p h) (sat_cons (step286 p h) (sat_cons (step296 p h) (sat_cons (step42 p h) (sat_cons (step291 p h) (sat_cons (step153 p h) (sat_cons (step228 p h) (sat_cons (step155 p h) (sat_cons (step179 p h) (sat_cons (step171 p h) (sat_cons (step170 p h) (sat_cons (step158 p h) (sat_cons (step166 p h) (sat_cons (step160 p h) (sat_cons (step161 p h) (sat_cons (step32 p h) (sat_cons (step56 p h) (sat_cons (step29 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c368 : List Lit := [(1338, false)]
theorem step368 (p : Nat → Bool) (h : Constraints p) : clause p c368 = true :=
  Snake9.LocalRup.prove_clause [c335, c322, c326, c331, c330, c293, c98, c312, c315, c2, c323, c112, c256, c366, c143, c146, c367, c144, c147, c151, c182, c137, c229, c228, c136, c219, c291, c3, c215, c286, c1, c206, c282, c204, c272, c270, c74, c259, c263, c81, c260] c368 (by decide) p (sat_cons (step335 p h) (sat_cons (step322 p h) (sat_cons (step326 p h) (sat_cons (step331 p h) (sat_cons (step330 p h) (sat_cons (step293 p h) (sat_cons (step98 p h) (sat_cons (step312 p h) (sat_cons (step315 p h) (sat_cons (step2 p h) (sat_cons (step323 p h) (sat_cons (step112 p h) (sat_cons (step256 p h) (sat_cons (step366 p h) (sat_cons (step143 p h) (sat_cons (step146 p h) (sat_cons (step367 p h) (sat_cons (step144 p h) (sat_cons (step147 p h) (sat_cons (step151 p h) (sat_cons (step182 p h) (sat_cons (step137 p h) (sat_cons (step229 p h) (sat_cons (step228 p h) (sat_cons (step136 p h) (sat_cons (step219 p h) (sat_cons (step291 p h) (sat_cons (step3 p h) (sat_cons (step215 p h) (sat_cons (step286 p h) (sat_cons (step1 p h) (sat_cons (step206 p h) (sat_cons (step282 p h) (sat_cons (step204 p h) (sat_cons (step272 p h) (sat_cons (step270 p h) (sat_cons (step74 p h) (sat_cons (step259 p h) (sat_cons (step263 p h) (sat_cons (step81 p h) (sat_cons (step260 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c369 : List Lit := [(81, true)]
theorem step369 (p : Nat → Bool) (h : Constraints p) : clause p c369 = true :=
  Snake9.LocalRup.prove_clause [c368, c253] c369 (by decide) p (sat_cons (step368 p h) (sat_cons (step253 p h) (sat_nil p)))
def c370 : List Lit := [(78, true)]
theorem step370 (p : Nat → Bool) (h : Constraints p) : clause p c370 = true :=
  Snake9.LocalRup.prove_clause [c368, c254] c370 (by decide) p (sat_cons (step368 p h) (sat_cons (step254 p h) (sat_nil p)))
def c371 : List Lit := [(83, false)]
theorem step371 (p : Nat → Bool) (h : Constraints p) : clause p c371 = true :=
  Snake9.LocalRup.prove_clause [c368, c328] c371 (by decide) p (sat_cons (step368 p h) (sat_cons (step328 p h) (sat_nil p)))
def c372 : List Lit := [(80, true)]
theorem step372 (p : Nat → Bool) (h : Constraints p) : clause p c372 = true :=
  Snake9.LocalRup.prove_clause [c369, c119, c91] c372 (by decide) p (sat_cons (step369 p h) (sat_cons (step119 p h) (sat_cons (step91 p h) (sat_nil p))))
def c373 : List Lit := [(12, true)]
theorem step373 (p : Nat → Bool) (h : Constraints p) : clause p c373 = true :=
  Snake9.LocalRup.prove_clause [c370, c118, c87] c373 (by decide) p (sat_cons (step370 p h) (sat_cons (step118 p h) (sat_cons (step87 p h) (sat_nil p))))
def c374 : List Lit := [(1345, true)]
theorem step374 (p : Nat → Bool) (h : Constraints p) : clause p c374 = true :=
  Snake9.LocalRup.prove_clause [c371, c265] c374 (by decide) p (sat_cons (step371 p h) (sat_cons (step265 p h) (sat_nil p)))
def c375 : List Lit := [(1218, true), (13, false), (1206, false), (20, true)]
theorem step375 (p : Nat → Bool) (h : Constraints p) : clause p c375 = true :=
  Snake9.LocalRup.prove_clause [c339, c102, c155, c171, c170, c158, c166, c160, c161, c32, c56, c29] c375 (by decide) p (sat_cons (step339 p h) (sat_cons (step102 p h) (sat_cons (step155 p h) (sat_cons (step171 p h) (sat_cons (step170 p h) (sat_cons (step158 p h) (sat_cons (step166 p h) (sat_cons (step160 p h) (sat_cons (step161 p h) (sat_cons (step32 p h) (sat_cons (step56 p h) (sat_cons (step29 p h) (sat_nil p)))))))))))))
def c376 : List Lit := [(1218, false), (10, false), (1195, false)]
theorem step376 (p : Nat → Bool) (h : Constraints p) : clause p c376 = true :=
  Snake9.LocalRup.prove_clause [c334, c326, c313, c373, c370, c141, c146, c183, c179, c147, c229, c144, c221, c26, c202, c358, c356] c376 (by decide) p (sat_cons (step334 p h) (sat_cons (step326 p h) (sat_cons (step313 p h) (sat_cons (step373 p h) (sat_cons (step370 p h) (sat_cons (step141 p h) (sat_cons (step146 p h) (sat_cons (step183 p h) (sat_cons (step179 p h) (sat_cons (step147 p h) (sat_cons (step229 p h) (sat_cons (step144 p h) (sat_cons (step221 p h) (sat_cons (step26 p h) (sat_cons (step202 p h) (sat_cons (step358 p h) (sat_cons (step356 p h) (sat_nil p))))))))))))))))))
def c377 : List Lit := [(14, false), (10, false), (1195, false)]
theorem step377 (p : Nat → Bool) (h : Constraints p) : clause p c377 = true :=
  Snake9.LocalRup.prove_clause [c370, c373, c322, c326, c313, c25, c27, c144, c147, c182, c229, c221, c358, c202, c356] c377 (by decide) p (sat_cons (step370 p h) (sat_cons (step373 p h) (sat_cons (step322 p h) (sat_cons (step326 p h) (sat_cons (step313 p h) (sat_cons (step25 p h) (sat_cons (step27 p h) (sat_cons (step144 p h) (sat_cons (step147 p h) (sat_cons (step182 p h) (sat_cons (step229 p h) (sat_cons (step221 p h) (sat_cons (step358 p h) (sat_cons (step202 p h) (sat_cons (step356 p h) (sat_nil p))))))))))))))))
def c378 : List Lit := [(10, false), (1195, false)]
theorem step378 (p : Nat → Bool) (h : Constraints p) : clause p c378 = true :=
  Snake9.LocalRup.prove_clause [c105, c372, c103, c352, c104, c339, c376, c171, c377, c157, c158, c170, c153, c40, c49, c45, c166, c36, c160, c161, c55, c54, c297] c378 (by decide) p (sat_cons (step105 p h) (sat_cons (step372 p h) (sat_cons (step103 p h) (sat_cons (step352 p h) (sat_cons (step104 p h) (sat_cons (step339 p h) (sat_cons (step376 p h) (sat_cons (step171 p h) (sat_cons (step377 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step170 p h) (sat_cons (step153 p h) (sat_cons (step40 p h) (sat_cons (step49 p h) (sat_cons (step45 p h) (sat_cons (step166 p h) (sat_cons (step36 p h) (sat_cons (step160 p h) (sat_cons (step161 p h) (sat_cons (step55 p h) (sat_cons (step54 p h) (sat_cons (step297 p h) (sat_nil p))))))))))))))))))))))))
def c379 : List Lit := [(1225, true), (14, true), (1195, false)]
theorem step379 (p : Nat → Bool) (h : Constraints p) : clause p c379 = true :=
  Snake9.LocalRup.prove_clause [c322, c378, c182, c362, c147, c144] c379 (by decide) p (sat_cons (step322 p h) (sat_cons (step378 p h) (sat_cons (step182 p h) (sat_cons (step362 p h) (sat_cons (step147 p h) (sat_cons (step144 p h) (sat_nil p)))))))
def c380 : List Lit := [(1225, true), (1195, false)]
theorem step380 (p : Nat → Bool) (h : Constraints p) : clause p c380 = true :=
  Snake9.LocalRup.prove_clause [c322, c370, c373, c182, c379, c147, c25, c144] c380 (by decide) p (sat_cons (step322 p h) (sat_cons (step370 p h) (sat_cons (step373 p h) (sat_cons (step182 p h) (sat_cons (step379 p h) (sat_cons (step147 p h) (sat_cons (step25 p h) (sat_cons (step144 p h) (sat_nil p)))))))))
def c381 : List Lit := [(1195, false)]
theorem step381 (p : Nat → Bool) (h : Constraints p) : clause p c381 = true :=
  Snake9.LocalRup.prove_clause [c326, c331, c330, c293, c312, c315, c323, c374, c371, c117, c352, c336, c378, c380, c229, c228, c219, c291, c215, c286, c206, c282, c204, c268, c270, c266, c258, c260, c261, c81, c84, c86, c88, c19, c140, c145] c381 (by decide) p (sat_cons (step326 p h) (sat_cons (step331 p h) (sat_cons (step330 p h) (sat_cons (step293 p h) (sat_cons (step312 p h) (sat_cons (step315 p h) (sat_cons (step323 p h) (sat_cons (step374 p h) (sat_cons (step371 p h) (sat_cons (step117 p h) (sat_cons (step352 p h) (sat_cons (step336 p h) (sat_cons (step378 p h) (sat_cons (step380 p h) (sat_cons (step229 p h) (sat_cons (step228 p h) (sat_cons (step219 p h) (sat_cons (step291 p h) (sat_cons (step215 p h) (sat_cons (step286 p h) (sat_cons (step206 p h) (sat_cons (step282 p h) (sat_cons (step204 p h) (sat_cons (step268 p h) (sat_cons (step270 p h) (sat_cons (step266 p h) (sat_cons (step258 p h) (sat_cons (step260 p h) (sat_cons (step261 p h) (sat_cons (step81 p h) (sat_cons (step84 p h) (sat_cons (step86 p h) (sat_cons (step88 p h) (sat_cons (step19 p h) (sat_cons (step140 p h) (sat_cons (step145 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c382 : List Lit := [(13, true)]
theorem step382 (p : Nat → Bool) (h : Constraints p) : clause p c382 = true :=
  Snake9.LocalRup.prove_clause [c381, c138] c382 (by decide) p (sat_cons (step381 p h) (sat_cons (step138 p h) (sat_nil p)))
def c383 : List Lit := [(10, true)]
theorem step383 (p : Nat → Bool) (h : Constraints p) : clause p c383 = true :=
  Snake9.LocalRup.prove_clause [c381, c139] c383 (by decide) p (sat_cons (step381 p h) (sat_cons (step139 p h) (sat_nil p)))
def c384 : List Lit := [(1349, true)]
theorem step384 (p : Nat → Bool) (h : Constraints p) : clause p c384 = true :=
  Snake9.LocalRup.prove_clause [c381, c350] c384 (by decide) p (sat_cons (step381 p h) (sat_cons (step350 p h) (sat_nil p)))
def c385 : List Lit := [(1200, false)]
theorem step385 (p : Nat → Bool) (h : Constraints p) : clause p c385 = true :=
  Snake9.LocalRup.prove_clause [c381, c367] c385 (by decide) p (sat_cons (step381 p h) (sat_cons (step367 p h) (sat_nil p)))
def c386 : List Lit := [(11, false)]
theorem step386 (p : Nat → Bool) (h : Constraints p) : clause p c386 = true :=
  Snake9.LocalRup.prove_clause [c382, c383, c352, c20] c386 (by decide) p (sat_cons (step382 p h) (sat_cons (step383 p h) (sat_cons (step352 p h) (sat_cons (step20 p h) (sat_nil p)))))
def c387 : List Lit := [(1376, true)]
theorem step387 (p : Nat → Bool) (h : Constraints p) : clause p c387 = true :=
  Snake9.LocalRup.prove_clause [c384, c323, c282] c387 (by decide) p (sat_cons (step384 p h) (sat_cons (step323 p h) (sat_cons (step282 p h) (sat_nil p))))
def c388 : List Lit := [(1197, false)]
theorem step388 (p : Nat → Bool) (h : Constraints p) : clause p c388 = true :=
  Snake9.LocalRup.prove_clause [c385, c146] c388 (by decide) p (sat_cons (step385 p h) (sat_cons (step146 p h) (sat_nil p)))
def c389 : List Lit := [(17, true)]
theorem step389 (p : Nat → Bool) (h : Constraints p) : clause p c389 = true :=
  Snake9.LocalRup.prove_clause [c386, c103, c352, c47] c389 (by decide) p (sat_cons (step386 p h) (sat_cons (step103 p h) (sat_cons (step352 p h) (sat_cons (step47 p h) (sat_nil p)))))
def c390 : List Lit := [(18, true)]
theorem step390 (p : Nat → Bool) (h : Constraints p) : clause p c390 = true :=
  Snake9.LocalRup.prove_clause [c386, c103, c352, c46] c390 (by decide) p (sat_cons (step386 p h) (sat_cons (step103 p h) (sat_cons (step352 p h) (sat_cons (step46 p h) (sat_nil p)))))
def c391 : List Lit := [(1389, true)]
theorem step391 (p : Nat → Bool) (h : Constraints p) : clause p c391 = true :=
  Snake9.LocalRup.prove_clause [c387, c315, c286] c391 (by decide) p (sat_cons (step387 p h) (sat_cons (step315 p h) (sat_cons (step286 p h) (sat_nil p))))
def c392 : List Lit := [(9, true)]
theorem step392 (p : Nat → Bool) (h : Constraints p) : clause p c392 = true :=
  Snake9.LocalRup.prove_clause [c388, c143] c392 (by decide) p (sat_cons (step388 p h) (sat_cons (step143 p h) (sat_nil p)))
def c393 : List Lit := [(16, false)]
theorem step393 (p : Nat → Bool) (h : Constraints p) : clause p c393 = true :=
  Snake9.LocalRup.prove_clause [c390, c383, c352, c40] c393 (by decide) p (sat_cons (step390 p h) (sat_cons (step383 p h) (sat_cons (step352 p h) (sat_cons (step40 p h) (sat_nil p)))))
def c394 : List Lit := [(20, false)]
theorem step394 (p : Nat → Bool) (h : Constraints p) : clause p c394 = true :=
  Snake9.LocalRup.prove_clause [c390, c352, c383, c42] c394 (by decide) p (sat_cons (step390 p h) (sat_cons (step352 p h) (sat_cons (step383 p h) (sat_cons (step42 p h) (sat_nil p)))))
def c395 : List Lit := [(1285, false)]
theorem step395 (p : Nat → Bool) (h : Constraints p) : clause p c395 = true :=
  Snake9.LocalRup.prove_clause [c391, c293, c291] c395 (by decide) p (sat_cons (step391 p h) (sat_cons (step293 p h) (sat_cons (step291 p h) (sat_nil p))))
def c396 : List Lit := [(29, false)]
theorem step396 (p : Nat → Bool) (h : Constraints p) : clause p c396 = true :=
  Snake9.LocalRup.prove_clause [c392, c370, c373, c26] c396 (by decide) p (sat_cons (step392 p h) (sat_cons (step370 p h) (sat_cons (step373 p h) (sat_cons (step26 p h) (sat_nil p)))))
def c397 : List Lit := [(8, false)]
theorem step397 (p : Nat → Bool) (h : Constraints p) : clause p c397 = true :=
  Snake9.LocalRup.prove_clause [c392, c389, c373, c5] c397 (by decide) p (sat_cons (step392 p h) (sat_cons (step389 p h) (sat_cons (step373 p h) (sat_cons (step5 p h) (sat_nil p)))))
def c398 : List Lit := [(1206, true)]
theorem step398 (p : Nat → Bool) (h : Constraints p) : clause p c398 = true :=
  Snake9.LocalRup.prove_clause [c393, c153] c398 (by decide) p (sat_cons (step393 p h) (sat_cons (step153 p h) (sat_nil p)))
def c399 : List Lit := [(1218, true)]
theorem step399 (p : Nat → Bool) (h : Constraints p) : clause p c399 = true :=
  Snake9.LocalRup.prove_clause [c394, c398, c382, c375] c399 (by decide) p (sat_cons (step394 p h) (sat_cons (step398 p h) (sat_cons (step382 p h) (sat_cons (step375 p h) (sat_nil p)))))
def c400 : List Lit := [(26, true)]
theorem step400 (p : Nat → Bool) (h : Constraints p) : clause p c400 = true :=
  Snake9.LocalRup.prove_clause [c397, c100, c383, c386, c12] c400 (by decide) p (sat_cons (step397 p h) (sat_cons (step100 p h) (sat_cons (step383 p h) (sat_cons (step386 p h) (sat_cons (step12 p h) (sat_nil p))))))
def c401 : List Lit := [(1224, true)]
theorem step401 (p : Nat → Bool) (h : Constraints p) : clause p c401 = true :=
  Snake9.LocalRup.prove_clause [c399, c175] c401 (by decide) p (sat_cons (step399 p h) (sat_cons (step175 p h) (sat_nil p)))
def c402 : List Lit := [(1236, true)]
theorem step402 (p : Nat → Bool) (h : Constraints p) : clause p c402 = true :=
  Snake9.LocalRup.prove_clause [c400, c383, c396, c356] c402 (by decide) p (sat_cons (step400 p h) (sat_cons (step383 p h) (sat_cons (step396 p h) (sat_cons (step356 p h) (sat_nil p)))))
def c403 : List Lit := [(1271, false)]
theorem step403 (p : Nat → Bool) (h : Constraints p) : clause p c403 = true :=
  Snake9.LocalRup.prove_clause [c401, c395, c226] c403 (by decide) p (sat_cons (step401 p h) (sat_cons (step395 p h) (sat_cons (step226 p h) (sat_nil p))))
def c404 : List Lit := [(1244, true)]
theorem step404 (p : Nat → Bool) (h : Constraints p) : clause p c404 = true :=
  Snake9.LocalRup.prove_clause [c402, c202] c404 (by decide) p (sat_cons (step402 p h) (sat_cons (step202 p h) (sat_nil p)))
def c405 : List Lit := []
theorem step405 (p : Nat → Bool) (h : Constraints p) : clause p c405 = true :=
  Snake9.LocalRup.prove_clause [c404, c403, c313, c221] c405 (by decide) p (sat_cons (step404 p h) (sat_cons (step403 p h) (sat_cons (step313 p h) (sat_cons (step221 p h) (sat_nil p)))))
end B112E234
