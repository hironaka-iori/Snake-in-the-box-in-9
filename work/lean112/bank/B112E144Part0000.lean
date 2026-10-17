import B112E144Inputs
namespace B112E144
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c363 : List Lit := [(81, true)]
theorem step363 (p : Nat → Bool) (h : Constraints p) : clause p c363 = true :=
  Snake9.LocalRup.prove_clause [c84, c83] c363 (by decide) p (sat_cons (step84 p h) (sat_cons (step83 p h) (sat_nil p)))
def c364 : List Lit := [(56, false)]
theorem step364 (p : Nat → Bool) (h : Constraints p) : clause p c364 = true :=
  Snake9.LocalRup.prove_clause [c104, c62] c364 (by decide) p (sat_cons (step104 p h) (sat_cons (step62 p h) (sat_nil p)))
def c365 : List Lit := [(67, false)]
theorem step365 (p : Nat → Bool) (h : Constraints p) : clause p c365 = true :=
  Snake9.LocalRup.prove_clause [c108, c74] c365 (by decide) p (sat_cons (step108 p h) (sat_cons (step74 p h) (sat_nil p)))
def c366 : List Lit := [(418, false)]
theorem step366 (p : Nat → Bool) (h : Constraints p) : clause p c366 = true :=
  Snake9.LocalRup.prove_clause [c168, c165] c366 (by decide) p (sat_cons (step168 p h) (sat_cons (step165 p h) (sat_nil p)))
def c367 : List Lit := [(314, false)]
theorem step367 (p : Nat → Bool) (h : Constraints p) : clause p c367 = true :=
  Snake9.LocalRup.prove_clause [c168, c167] c367 (by decide) p (sat_cons (step168 p h) (sat_cons (step167 p h) (sat_nil p)))
def c368 : List Lit := [(364, false)]
theorem step368 (p : Nat → Bool) (h : Constraints p) : clause p c368 = true :=
  Snake9.LocalRup.prove_clause [c366, c164] c368 (by decide) p (sat_cons (step366 p h) (sat_cons (step164 p h) (sat_nil p)))
def c369 : List Lit := [(262, false)]
theorem step369 (p : Nat → Bool) (h : Constraints p) : clause p c369 = true :=
  Snake9.LocalRup.prove_clause [c367, c147] c369 (by decide) p (sat_cons (step367 p h) (sat_cons (step147 p h) (sat_nil p)))
def c370 : List Lit := [(338, false)]
theorem step370 (p : Nat → Bool) (h : Constraints p) : clause p c370 = true :=
  Snake9.LocalRup.prove_clause [c368, c157] c370 (by decide) p (sat_cons (step368 p h) (sat_cons (step157 p h) (sat_nil p)))
def c371 : List Lit := [(260, false)]
theorem step371 (p : Nat → Bool) (h : Constraints p) : clause p c371 = true :=
  Snake9.LocalRup.prove_clause [c369, c143] c371 (by decide) p (sat_cons (step369 p h) (sat_cons (step143 p h) (sat_nil p)))
def c372 : List Lit := [(336, false)]
theorem step372 (p : Nat → Bool) (h : Constraints p) : clause p c372 = true :=
  Snake9.LocalRup.prove_clause [c370, c155] c372 (by decide) p (sat_cons (step370 p h) (sat_cons (step155 p h) (sat_nil p)))
def c373 : List Lit := [(246, false)]
theorem step373 (p : Nat → Bool) (h : Constraints p) : clause p c373 = true :=
  Snake9.LocalRup.prove_clause [c371, c141] c373 (by decide) p (sat_cons (step371 p h) (sat_cons (step141 p h) (sat_nil p)))
def c374 : List Lit := [(1363, true)]
theorem step374 (p : Nat → Bool) (h : Constraints p) : clause p c374 = true :=
  Snake9.LocalRup.prove_clause [c364, c284] c374 (by decide) p (sat_cons (step364 p h) (sat_cons (step284 p h) (sat_nil p)))
def c375 : List Lit := [(58, true), (1364, true)]
theorem step375 (p : Nat → Bool) (h : Constraints p) : clause p c375 = true :=
  Snake9.LocalRup.prove_clause [c364, c285] c375 (by decide) p (sat_cons (step364 p h) (sat_cons (step285 p h) (sat_nil p)))
def c376 : List Lit := [(1365, true)]
theorem step376 (p : Nat → Bool) (h : Constraints p) : clause p c376 = true :=
  Snake9.LocalRup.prove_clause [c374, c286] c376 (by decide) p (sat_cons (step374 p h) (sat_cons (step286 p h) (sat_nil p)))
def c377 : List Lit := [(54, true), (1366, true)]
theorem step377 (p : Nat → Bool) (h : Constraints p) : clause p c377 = true :=
  Snake9.LocalRup.prove_clause [c374, c288] c377 (by decide) p (sat_cons (step374 p h) (sat_cons (step288 p h) (sat_nil p)))
def c378 : List Lit := [(1373, true)]
theorem step378 (p : Nat → Bool) (h : Constraints p) : clause p c378 = true :=
  Snake9.LocalRup.prove_clause [c376, c294] c378 (by decide) p (sat_cons (step376 p h) (sat_cons (step294 p h) (sat_nil p)))
def c379 : List Lit := [(1370, false), (1374, true)]
theorem step379 (p : Nat → Bool) (h : Constraints p) : clause p c379 = true :=
  Snake9.LocalRup.prove_clause [c376, c295] c379 (by decide) p (sat_cons (step376 p h) (sat_cons (step295 p h) (sat_nil p)))
def c380 : List Lit := [(1371, false), (1375, true)]
theorem step380 (p : Nat → Bool) (h : Constraints p) : clause p c380 = true :=
  Snake9.LocalRup.prove_clause [c376, c296] c380 (by decide) p (sat_cons (step376 p h) (sat_cons (step296 p h) (sat_nil p)))
def c381 : List Lit := [(1381, true)]
theorem step381 (p : Nat → Bool) (h : Constraints p) : clause p c381 = true :=
  Snake9.LocalRup.prove_clause [c365, c302] c381 (by decide) p (sat_cons (step365 p h) (sat_cons (step302 p h) (sat_nil p)))
def c382 : List Lit := [(1379, false), (1382, true)]
theorem step382 (p : Nat → Bool) (h : Constraints p) : clause p c382 = true :=
  Snake9.LocalRup.prove_clause [c365, c303] c382 (by decide) p (sat_cons (step365 p h) (sat_cons (step303 p h) (sat_nil p)))
def c383 : List Lit := [(1388, false), (1393, true)]
theorem step383 (p : Nat → Bool) (h : Constraints p) : clause p c383 = true :=
  Snake9.LocalRup.prove_clause [c381, c310] c383 (by decide) p (sat_cons (step381 p h) (sat_cons (step310 p h) (sat_nil p)))
def c384 : List Lit := [(1393, false), (1401, true)]
theorem step384 (p : Nat → Bool) (h : Constraints p) : clause p c384 = true :=
  Snake9.LocalRup.prove_clause [c378, c313] c384 (by decide) p (sat_cons (step378 p h) (sat_cons (step313 p h) (sat_nil p)))
def c385 : List Lit := [(1394, false), (1402, true)]
theorem step385 (p : Nat → Bool) (h : Constraints p) : clause p c385 = true :=
  Snake9.LocalRup.prove_clause [c378, c314] c385 (by decide) p (sat_cons (step378 p h) (sat_cons (step314 p h) (sat_nil p)))
def c386 : List Lit := [(1337, true)]
theorem step386 (p : Nat → Bool) (h : Constraints p) : clause p c386 = true :=
  Snake9.LocalRup.prove_clause [c102, c263, c265, c255, c257, c240, c251, c243, c234, c250, c242, c233, c59, c58] c386 (by decide) p (sat_cons (step102 p h) (sat_cons (step263 p h) (sat_cons (step265 p h) (sat_cons (step255 p h) (sat_cons (step257 p h) (sat_cons (step240 p h) (sat_cons (step251 p h) (sat_cons (step243 p h) (sat_cons (step234 p h) (sat_cons (step250 p h) (sat_cons (step242 p h) (sat_cons (step233 p h) (sat_cons (step59 p h) (sat_cons (step58 p h) (sat_nil p)))))))))))))))
def c387 : List Lit := [(7, false), (23, false), (19, false)]
theorem step387 (p : Nat → Bool) (h : Constraints p) : clause p c387 = true :=
  Snake9.LocalRup.prove_clause [c95, c44, c39] c387 (by decide) p (sat_cons (step95 p h) (sat_cons (step44 p h) (sat_cons (step39 p h) (sat_nil p))))
def c388 : List Lit := [(1289, true), (1277, false)]
theorem step388 (p : Nat → Bool) (h : Constraints p) : clause p c388 = true :=
  Snake9.LocalRup.prove_clause [c94, c209, c217, c218, c212, c185, c199, c180, c197, c198, c177, c34, c18] c388 (by decide) p (sat_cons (step94 p h) (sat_cons (step209 p h) (sat_cons (step217 p h) (sat_cons (step218 p h) (sat_cons (step212 p h) (sat_cons (step185 p h) (sat_cons (step199 p h) (sat_cons (step180 p h) (sat_cons (step197 p h) (sat_cons (step198 p h) (sat_cons (step177 p h) (sat_cons (step34 p h) (sat_cons (step18 p h) (sat_nil p))))))))))))))
def c389 : List Lit := [(1252, true), (7, false)]
theorem step389 (p : Nat → Bool) (h : Constraints p) : clause p c389 = true :=
  Snake9.LocalRup.prove_clause [c91, c169, c170, c7, c9] c389 (by decide) p (sat_cons (step91 p h) (sat_cons (step169 p h) (sat_cons (step170 p h) (sat_cons (step7 p h) (sat_cons (step9 p h) (sat_nil p))))))
def c390 : List Lit := [(1370, true), (7, false)]
theorem step390 (p : Nat → Bool) (h : Constraints p) : clause p c390 = true :=
  Snake9.LocalRup.prove_clause [c106, c291, c292, c290, c68, c70] c390 (by decide) p (sat_cons (step106 p h) (sat_cons (step291 p h) (sat_cons (step292 p h) (sat_cons (step290 p h) (sat_cons (step68 p h) (sat_cons (step70 p h) (sat_nil p)))))))
def c391 : List Lit := [(1403, true), (1382, false), (1370, false)]
theorem step391 (p : Nat → Bool) (h : Constraints p) : clause p c391 = true :=
  Snake9.LocalRup.prove_clause [c105, c311, c379, c317, c316, c298, c312, c287, c308, c309, c375, c306, c304, c64, c80] c391 (by decide) p (sat_cons (step105 p h) (sat_cons (step311 p h) (sat_cons (step379 p h) (sat_cons (step317 p h) (sat_cons (step316 p h) (sat_cons (step298 p h) (sat_cons (step312 p h) (sat_cons (step287 p h) (sat_cons (step308 p h) (sat_cons (step309 p h) (sat_cons (step375 p h) (sat_cons (step306 p h) (sat_cons (step304 p h) (sat_cons (step64 p h) (sat_cons (step80 p h) (sat_nil p))))))))))))))))
def c392 : List Lit := [(74, false), (77, false), (76, false)]
theorem step392 (p : Nat → Bool) (h : Constraints p) : clause p c392 = true :=
  Snake9.LocalRup.prove_clause [c110, c77, c78] c392 (by decide) p (sat_cons (step110 p h) (sat_cons (step77 p h) (sat_cons (step78 p h) (sat_nil p))))
def c393 : List Lit := [(1388, true)]
theorem step393 (p : Nat → Bool) (h : Constraints p) : clause p c393 = true :=
  Snake9.LocalRup.prove_clause [c308, c309, c307, c304, c305, c392] c393 (by decide) p (sat_cons (step308 p h) (sat_cons (step309 p h) (sat_cons (step307 p h) (sat_cons (step304 p h) (sat_cons (step305 p h) (sat_cons (step392 p h) (sat_nil p)))))))
def c394 : List Lit := [(94, false), (100, false), (97, false)]
theorem step394 (p : Nat → Bool) (h : Constraints p) : clause p c394 = true :=
  Snake9.LocalRup.prove_clause [c112, c87, c88] c394 (by decide) p (sat_cons (step112 p h) (sat_cons (step87 p h) (sat_cons (step88 p h) (sat_nil p))))
def c395 : List Lit := [(1445, true)]
theorem step395 (p : Nat → Bool) (h : Constraints p) : clause p c395 = true :=
  Snake9.LocalRup.prove_clause [c339, c340, c338, c335, c336, c337, c334, c394] c395 (by decide) p (sat_cons (step339 p h) (sat_cons (step340 p h) (sat_cons (step338 p h) (sat_cons (step335 p h) (sat_cons (step336 p h) (sat_cons (step337 p h) (sat_cons (step334 p h) (sat_cons (step394 p h) (sat_nil p)))))))))
def c396 : List Lit := [(1414, true)]
theorem step396 (p : Nat → Bool) (h : Constraints p) : clause p c396 = true :=
  Snake9.LocalRup.prove_clause [c363, c84, c321, c322, c320, c82] c396 (by decide) p (sat_cons (step363 p h) (sat_cons (step84 p h) (sat_cons (step321 p h) (sat_cons (step322 p h) (sat_cons (step320 p h) (sat_cons (step82 p h) (sat_nil p)))))))
def c397 : List Lit := [(1393, true)]
theorem step397 (p : Nat → Bool) (h : Constraints p) : clause p c397 = true :=
  Snake9.LocalRup.prove_clause [c393, c383] c397 (by decide) p (sat_cons (step393 p h) (sat_cons (step383 p h) (sat_nil p)))
def c398 : List Lit := [(1425, true)]
theorem step398 (p : Nat → Bool) (h : Constraints p) : clause p c398 = true :=
  Snake9.LocalRup.prove_clause [c396, c331] c398 (by decide) p (sat_cons (step396 p h) (sat_cons (step331 p h) (sat_nil p)))
def c399 : List Lit := [(1453, true)]
theorem step399 (p : Nat → Bool) (h : Constraints p) : clause p c399 = true :=
  Snake9.LocalRup.prove_clause [c398, c395, c341] c399 (by decide) p (sat_cons (step398 p h) (sat_cons (step395 p h) (sat_cons (step341 p h) (sat_nil p))))
def c400 : List Lit := [(1401, true)]
theorem step400 (p : Nat → Bool) (h : Constraints p) : clause p c400 = true :=
  Snake9.LocalRup.prove_clause [c397, c384] c400 (by decide) p (sat_cons (step397 p h) (sat_cons (step384 p h) (sat_nil p)))
def c401 : List Lit := [(1469, true)]
theorem step401 (p : Nat → Bool) (h : Constraints p) : clause p c401 = true :=
  Snake9.LocalRup.prove_clause [c399, c400, c344] c401 (by decide) p (sat_cons (step399 p h) (sat_cons (step400 p h) (sat_cons (step344 p h) (sat_nil p))))
def c402 : List Lit := [(1357, false)]
theorem step402 (p : Nat → Bool) (h : Constraints p) : clause p c402 = true :=
  Snake9.LocalRup.prove_clause [c401, c358, c357] c402 (by decide) p (sat_cons (step401 p h) (sat_cons (step358 p h) (sat_cons (step357 p h) (sat_nil p))))
def c403 : List Lit := [(11, true), (1271, false), (22, false), (23, false), (24, true), (7, false)]
theorem step403 (p : Nat → Bool) (h : Constraints p) : clause p c403 = true :=
  Snake9.LocalRup.prove_clause [c95, c397, c399, c358, c386, c96, c389, c172, c390, c379, c315, c346, c356, c282, c39, c202, c206, c215, c229, c190, c181, c177, c179, c180, c189, c193, c225, c175, c216, c24, c208, c43, c203, c362] c403 (by decide) p (sat_cons (step95 p h) (sat_cons (step397 p h) (sat_cons (step399 p h) (sat_cons (step358 p h) (sat_cons (step386 p h) (sat_cons (step96 p h) (sat_cons (step389 p h) (sat_cons (step172 p h) (sat_cons (step390 p h) (sat_cons (step379 p h) (sat_cons (step315 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step282 p h) (sat_cons (step39 p h) (sat_cons (step202 p h) (sat_cons (step206 p h) (sat_cons (step215 p h) (sat_cons (step229 p h) (sat_cons (step190 p h) (sat_cons (step181 p h) (sat_cons (step177 p h) (sat_cons (step179 p h) (sat_cons (step180 p h) (sat_cons (step189 p h) (sat_cons (step193 p h) (sat_cons (step225 p h) (sat_cons (step175 p h) (sat_cons (step216 p h) (sat_cons (step24 p h) (sat_cons (step208 p h) (sat_cons (step43 p h) (sat_cons (step203 p h) (sat_cons (step362 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c404 : List Lit := [(12, false), (13, false), (23, false), (1277, false), (7, false)]
theorem step404 (p : Nat → Bool) (h : Constraints p) : clause p c404 = true :=
  Snake9.LocalRup.prove_clause [c399, c358, c386, c93, c209, c390, c389, c26, c29, c32, c175, c178, c301, c180, c382, c193, c391, c349, c355, c280, c231, c228, c194, c212, c181, c199, c179, c197, c20, c21, c361] c404 (by decide) p (sat_cons (step399 p h) (sat_cons (step358 p h) (sat_cons (step386 p h) (sat_cons (step93 p h) (sat_cons (step209 p h) (sat_cons (step390 p h) (sat_cons (step389 p h) (sat_cons (step26 p h) (sat_cons (step29 p h) (sat_cons (step32 p h) (sat_cons (step175 p h) (sat_cons (step178 p h) (sat_cons (step301 p h) (sat_cons (step180 p h) (sat_cons (step382 p h) (sat_cons (step193 p h) (sat_cons (step391 p h) (sat_cons (step349 p h) (sat_cons (step355 p h) (sat_cons (step280 p h) (sat_cons (step231 p h) (sat_cons (step228 p h) (sat_cons (step194 p h) (sat_cons (step212 p h) (sat_cons (step181 p h) (sat_cons (step199 p h) (sat_cons (step179 p h) (sat_cons (step197 p h) (sat_cons (step20 p h) (sat_cons (step21 p h) (sat_cons (step361 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c405 : List Lit := [(11, false), (12, true), (19, true)]
theorem step405 (p : Nat → Bool) (h : Constraints p) : clause p c405 = true :=
  Snake9.LocalRup.prove_clause [c93, c373, c369, c94, c20, c21, c361, c38, c127, c128, c129, c131, c139, c126, c145, c125, c123, c35, c122, c33, c121, c19, c120] c405 (by decide) p (sat_cons (step93 p h) (sat_cons (step373 p h) (sat_cons (step369 p h) (sat_cons (step94 p h) (sat_cons (step20 p h) (sat_cons (step21 p h) (sat_cons (step361 p h) (sat_cons (step38 p h) (sat_cons (step127 p h) (sat_cons (step128 p h) (sat_cons (step129 p h) (sat_cons (step131 p h) (sat_cons (step139 p h) (sat_cons (step126 p h) (sat_cons (step145 p h) (sat_cons (step125 p h) (sat_cons (step123 p h) (sat_cons (step35 p h) (sat_cons (step122 p h) (sat_cons (step33 p h) (sat_cons (step121 p h) (sat_cons (step19 p h) (sat_cons (step120 p h) (sat_nil p))))))))))))))))))))))))
def c406 : List Lit := [(1264, true), (11, true), (13, false), (23, false), (1252, false)]
theorem step406 (p : Nat → Bool) (h : Constraints p) : clause p c406 = true :=
  Snake9.LocalRup.prove_clause [c177, c180, c172, c190, c193, c181, c175, c179, c24] c406 (by decide) p (sat_cons (step177 p h) (sat_cons (step180 p h) (sat_cons (step172 p h) (sat_cons (step190 p h) (sat_cons (step193 p h) (sat_cons (step181 p h) (sat_cons (step175 p h) (sat_cons (step179 p h) (sat_cons (step24 p h) (sat_nil p))))))))))
def c407 : List Lit := [(13, false), (23, false), (19, true), (7, false)]
theorem step407 (p : Nat → Bool) (h : Constraints p) : clause p c407 = true :=
  Snake9.LocalRup.prove_clause [c397, c386, c358, c399, c202, c206, c390, c379, c315, c346, c356, c282, c389, c404, c200, c212, c232, c405, c406, c228, c280, c355, c349, c391, c382, c301, c28, c31, c175, c179, c194, c181] c407 (by decide) p (sat_cons (step397 p h) (sat_cons (step386 p h) (sat_cons (step358 p h) (sat_cons (step399 p h) (sat_cons (step202 p h) (sat_cons (step206 p h) (sat_cons (step390 p h) (sat_cons (step379 p h) (sat_cons (step315 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step282 p h) (sat_cons (step389 p h) (sat_cons (step404 p h) (sat_cons (step200 p h) (sat_cons (step212 p h) (sat_cons (step232 p h) (sat_cons (step405 p h) (sat_cons (step406 p h) (sat_cons (step228 p h) (sat_cons (step280 p h) (sat_cons (step355 p h) (sat_cons (step349 p h) (sat_cons (step391 p h) (sat_cons (step382 p h) (sat_cons (step301 p h) (sat_cons (step28 p h) (sat_cons (step31 p h) (sat_cons (step175 p h) (sat_cons (step179 p h) (sat_cons (step194 p h) (sat_cons (step181 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c408 : List Lit := [(12, true), (23, false), (24, true), (7, false)]
theorem step408 (p : Nat → Bool) (h : Constraints p) : clause p c408 = true :=
  Snake9.LocalRup.prove_clause [c95, c96, c371, c94, c39, c407, c43, c42, c362, c41, c132, c133, c137, c140, c130, c126, c125, c405, c35, c403, c33, c201, c198] c408 (by decide) p (sat_cons (step95 p h) (sat_cons (step96 p h) (sat_cons (step371 p h) (sat_cons (step94 p h) (sat_cons (step39 p h) (sat_cons (step407 p h) (sat_cons (step43 p h) (sat_cons (step42 p h) (sat_cons (step362 p h) (sat_cons (step41 p h) (sat_cons (step132 p h) (sat_cons (step133 p h) (sat_cons (step137 p h) (sat_cons (step140 p h) (sat_cons (step130 p h) (sat_cons (step126 p h) (sat_cons (step125 p h) (sat_cons (step405 p h) (sat_cons (step35 p h) (sat_cons (step403 p h) (sat_cons (step33 p h) (sat_cons (step201 p h) (sat_cons (step198 p h) (sat_nil p))))))))))))))))))))))))
def c409 : List Lit := [(1255, true), (5, true), (13, true), (7, false)]
theorem step409 (p : Nat → Bool) (h : Constraints p) : clause p c409 = true :=
  Snake9.LocalRup.prove_clause [c89, c90, c389, c173, c175, c171, c2, c3, c359] c409 (by decide) p (sat_cons (step89 p h) (sat_cons (step90 p h) (sat_cons (step389 p h) (sat_cons (step173 p h) (sat_cons (step175 p h) (sat_cons (step171 p h) (sat_cons (step2 p h) (sat_cons (step3 p h) (sat_cons (step359 p h) (sat_nil p))))))))))
def c410 : List Lit := [(11, true), (1255, false), (12, false), (1278, false), (22, false), (13, true), (1293, true)]
theorem step410 (p : Nat → Bool) (h : Constraints p) : clause p c410 = true :=
  Snake9.LocalRup.prove_clause [c92, c94, c210, c232, c194, c181, c177, c180, c193, c229, c179, c213, c17, c199, c22, c198, c33] c410 (by decide) p (sat_cons (step92 p h) (sat_cons (step94 p h) (sat_cons (step210 p h) (sat_cons (step232 p h) (sat_cons (step194 p h) (sat_cons (step181 p h) (sat_cons (step177 p h) (sat_cons (step180 p h) (sat_cons (step193 p h) (sat_cons (step229 p h) (sat_cons (step179 p h) (sat_cons (step213 p h) (sat_cons (step17 p h) (sat_cons (step199 p h) (sat_cons (step22 p h) (sat_cons (step198 p h) (sat_cons (step33 p h) (sat_nil p))))))))))))))))))
def c411 : List Lit := [(23, false), (24, true), (7, false)]
theorem step411 (p : Nat → Bool) (h : Constraints p) : clause p c411 = true :=
  Snake9.LocalRup.prove_clause [c397, c399, c358, c386, c95, c96, c371, c369, c91, c93, c39, c390, c379, c315, c346, c356, c282, c407, c42, c43, c362, c203, c41, c208, c132, c133, c137, c138, c140, c145, c129, c124, c128, c118, c127, c117, c6, c8, c408, c409, c410, c20, c21, c361, c38] c411 (by decide) p (sat_cons (step397 p h) (sat_cons (step399 p h) (sat_cons (step358 p h) (sat_cons (step386 p h) (sat_cons (step95 p h) (sat_cons (step96 p h) (sat_cons (step371 p h) (sat_cons (step369 p h) (sat_cons (step91 p h) (sat_cons (step93 p h) (sat_cons (step39 p h) (sat_cons (step390 p h) (sat_cons (step379 p h) (sat_cons (step315 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step282 p h) (sat_cons (step407 p h) (sat_cons (step42 p h) (sat_cons (step43 p h) (sat_cons (step362 p h) (sat_cons (step203 p h) (sat_cons (step41 p h) (sat_cons (step208 p h) (sat_cons (step132 p h) (sat_cons (step133 p h) (sat_cons (step137 p h) (sat_cons (step138 p h) (sat_cons (step140 p h) (sat_cons (step145 p h) (sat_cons (step129 p h) (sat_cons (step124 p h) (sat_cons (step128 p h) (sat_cons (step118 p h) (sat_cons (step127 p h) (sat_cons (step117 p h) (sat_cons (step6 p h) (sat_cons (step8 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step410 p h) (sat_cons (step20 p h) (sat_cons (step21 p h) (sat_cons (step361 p h) (sat_cons (step38 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c412 : List Lit := [(11, true), (1255, false), (13, true), (1282, false), (1402, false)]
theorem step412 (p : Nat → Bool) (h : Constraints p) : clause p c412 = true :=
  Snake9.LocalRup.prove_clause [c399, c92, c386, c358, c395, c396, c111, c346, c356, c282, c232, c194, c181, c177, c179, c180, c15, c193, c228, c280, c281, c355, c264, c347, c260, c342, c332, c327, c329, c324, c325, c323, c51, c85, c241, c86, c245] c412 (by decide) p (sat_cons (step399 p h) (sat_cons (step92 p h) (sat_cons (step386 p h) (sat_cons (step358 p h) (sat_cons (step395 p h) (sat_cons (step396 p h) (sat_cons (step111 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step282 p h) (sat_cons (step232 p h) (sat_cons (step194 p h) (sat_cons (step181 p h) (sat_cons (step177 p h) (sat_cons (step179 p h) (sat_cons (step180 p h) (sat_cons (step15 p h) (sat_cons (step193 p h) (sat_cons (step228 p h) (sat_cons (step280 p h) (sat_cons (step281 p h) (sat_cons (step355 p h) (sat_cons (step264 p h) (sat_cons (step347 p h) (sat_cons (step260 p h) (sat_cons (step342 p h) (sat_cons (step332 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step324 p h) (sat_cons (step325 p h) (sat_cons (step323 p h) (sat_cons (step51 p h) (sat_cons (step85 p h) (sat_cons (step241 p h) (sat_cons (step86 p h) (sat_cons (step245 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c413 : List Lit := [(1255, false), (13, true), (1278, false), (1402, false)]
theorem step413 (p : Nat → Bool) (h : Constraints p) : clause p c413 = true :=
  Snake9.LocalRup.prove_clause [c399, c93, c386, c358, c92, c395, c396, c111, c210, c346, c356, c282, c192, c412, c20, c21, c361, c197, c199, c213, c229, c224, c193, c280, c281, c180, c355, c264, c178, c347, c260, c15, c342, c332, c327, c329, c324, c325, c323, c51, c85, c241, c86, c245] c413 (by decide) p (sat_cons (step399 p h) (sat_cons (step93 p h) (sat_cons (step386 p h) (sat_cons (step358 p h) (sat_cons (step92 p h) (sat_cons (step395 p h) (sat_cons (step396 p h) (sat_cons (step111 p h) (sat_cons (step210 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step282 p h) (sat_cons (step192 p h) (sat_cons (step412 p h) (sat_cons (step20 p h) (sat_cons (step21 p h) (sat_cons (step361 p h) (sat_cons (step197 p h) (sat_cons (step199 p h) (sat_cons (step213 p h) (sat_cons (step229 p h) (sat_cons (step224 p h) (sat_cons (step193 p h) (sat_cons (step280 p h) (sat_cons (step281 p h) (sat_cons (step180 p h) (sat_cons (step355 p h) (sat_cons (step264 p h) (sat_cons (step178 p h) (sat_cons (step347 p h) (sat_cons (step260 p h) (sat_cons (step15 p h) (sat_cons (step342 p h) (sat_cons (step332 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step324 p h) (sat_cons (step325 p h) (sat_cons (step323 p h) (sat_cons (step51 p h) (sat_cons (step85 p h) (sat_cons (step241 p h) (sat_cons (step86 p h) (sat_cons (step245 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c414 : List Lit := [(11, false), (13, true), (24, true), (7, false)]
theorem step414 (p : Nat → Bool) (h : Constraints p) : clause p c414 = true :=
  Snake9.TreeRup.prove_clause [c89, c95, c91, c106, c93, c386, c358, c399, c397, c168, c364, c105, c393, c390, c379, c315, c39, c202, c411, c204, c207, c413, c409, c7, c389, c175, c2, c12, c68, c1, c172, c188, c20, c21, c361, c197, c38, c199, c127, c213, c128, c220, c129, c277, c139, c354, c142, c351, c146, c319, c166, c162, c156, c154, c152, c148, c66, c65, c375, c287, c298, c299, c318, c293, c312, c290, c382, c63, c301] c414 (by decide) p (sat_cons (step89 p h) (sat_cons (step95 p h) (sat_cons (step91 p h) (sat_cons (step106 p h) (sat_cons (step93 p h) (sat_cons (step386 p h) (sat_cons (step358 p h) (sat_cons (step399 p h) (sat_cons (step397 p h) (sat_cons (step168 p h) (sat_cons (step364 p h) (sat_cons (step105 p h) (sat_cons (step393 p h) (sat_cons (step390 p h) (sat_cons (step379 p h) (sat_cons (step315 p h) (sat_cons (step39 p h) (sat_cons (step202 p h) (sat_cons (step411 p h) (sat_cons (step204 p h) (sat_cons (step207 p h) (sat_cons (step413 p h) (sat_cons (step409 p h) (sat_cons (step7 p h) (sat_cons (step389 p h) (sat_cons (step175 p h) (sat_cons (step2 p h) (sat_cons (step12 p h) (sat_cons (step68 p h) (sat_cons (step1 p h) (sat_cons (step172 p h) (sat_cons (step188 p h) (sat_cons (step20 p h) (sat_cons (step21 p h) (sat_cons (step361 p h) (sat_cons (step197 p h) (sat_cons (step38 p h) (sat_cons (step199 p h) (sat_cons (step127 p h) (sat_cons (step213 p h) (sat_cons (step128 p h) (sat_cons (step220 p h) (sat_cons (step129 p h) (sat_cons (step277 p h) (sat_cons (step139 p h) (sat_cons (step354 p h) (sat_cons (step142 p h) (sat_cons (step351 p h) (sat_cons (step146 p h) (sat_cons (step319 p h) (sat_cons (step166 p h) (sat_cons (step162 p h) (sat_cons (step156 p h) (sat_cons (step154 p h) (sat_cons (step152 p h) (sat_cons (step148 p h) (sat_cons (step66 p h) (sat_cons (step65 p h) (sat_cons (step375 p h) (sat_cons (step287 p h) (sat_cons (step298 p h) (sat_cons (step299 p h) (sat_cons (step318 p h) (sat_cons (step293 p h) (sat_cons (step312 p h) (sat_cons (step290 p h) (sat_cons (step382 p h) (sat_cons (step63 p h) (sat_cons (step301 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c415 : List Lit := [(1403, true), (60, true), (57, false), (1, false), (1370, false)]
theorem step415 (p : Nat → Bool) (h : Constraints p) : clause p c415 = true :=
  Snake9.LocalRup.prove_clause [c397, c317, c391, c380, c382, c293, c301, c290, c63] c415 (by decide) p (sat_cons (step397 p h) (sat_cons (step317 p h) (sat_cons (step391 p h) (sat_cons (step380 p h) (sat_cons (step382 p h) (sat_cons (step293 p h) (sat_cons (step301 p h) (sat_cons (step290 p h) (sat_cons (step63 p h) (sat_nil p))))))))))
def c416 : List Lit := [(13, true), (24, true), (7, false)]
theorem step416 (p : Nat → Bool) (h : Constraints p) : clause p c416 = true :=
  Snake9.TreeRup.prove_clause [c397, c95, c89, c91, c106, c399, c358, c395, c386, c396, c111, c92, c39, c202, c411, c204, c207, c210, c390, c379, c315, c389, c172, c413, c175, c409, c1, c2, c7, c12, c68, c414, c177, c180, c189, c223, c277, c354, c415, c349, c350, c355, c342, c280, c278, c332, c228, c264, c327, c329, c190, c260, c324, c325, c323, c181, c85, c179, c86, c15, c245, c51, c241] c416 (by decide) p (sat_cons (step397 p h) (sat_cons (step95 p h) (sat_cons (step89 p h) (sat_cons (step91 p h) (sat_cons (step106 p h) (sat_cons (step399 p h) (sat_cons (step358 p h) (sat_cons (step395 p h) (sat_cons (step386 p h) (sat_cons (step396 p h) (sat_cons (step111 p h) (sat_cons (step92 p h) (sat_cons (step39 p h) (sat_cons (step202 p h) (sat_cons (step411 p h) (sat_cons (step204 p h) (sat_cons (step207 p h) (sat_cons (step210 p h) (sat_cons (step390 p h) (sat_cons (step379 p h) (sat_cons (step315 p h) (sat_cons (step389 p h) (sat_cons (step172 p h) (sat_cons (step413 p h) (sat_cons (step175 p h) (sat_cons (step409 p h) (sat_cons (step1 p h) (sat_cons (step2 p h) (sat_cons (step7 p h) (sat_cons (step12 p h) (sat_cons (step68 p h) (sat_cons (step414 p h) (sat_cons (step177 p h) (sat_cons (step180 p h) (sat_cons (step189 p h) (sat_cons (step223 p h) (sat_cons (step277 p h) (sat_cons (step354 p h) (sat_cons (step415 p h) (sat_cons (step349 p h) (sat_cons (step350 p h) (sat_cons (step355 p h) (sat_cons (step342 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step332 p h) (sat_cons (step228 p h) (sat_cons (step264 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step190 p h) (sat_cons (step260 p h) (sat_cons (step324 p h) (sat_cons (step325 p h) (sat_cons (step323 p h) (sat_cons (step181 p h) (sat_cons (step85 p h) (sat_cons (step179 p h) (sat_cons (step86 p h) (sat_cons (step15 p h) (sat_cons (step245 p h) (sat_cons (step51 p h) (sat_cons (step241 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c417 : List Lit := [(11, true), (1292, true), (1, false), (13, false), (1278, false), (1254, false)]
theorem step417 (p : Nat → Bool) (h : Constraints p) : clause p c417 = true :=
  Snake9.LocalRup.prove_clause [c210, c228, c190, c181, c177, c179, c180, c23, c189, c200, c224, c213] c417 (by decide) p (sat_cons (step210 p h) (sat_cons (step228 p h) (sat_cons (step190 p h) (sat_cons (step181 p h) (sat_cons (step177 p h) (sat_cons (step179 p h) (sat_cons (step180 p h) (sat_cons (step23 p h) (sat_cons (step189 p h) (sat_cons (step200 p h) (sat_cons (step224 p h) (sat_cons (step213 p h) (sat_nil p)))))))))))))
def c418 : List Lit := [(1292, true), (1, false), (13, false), (1278, false), (19, true), (1254, false)]
theorem step418 (p : Nat → Bool) (h : Constraints p) : clause p c418 = true :=
  Snake9.LocalRup.prove_clause [c93, c417, c20, c21, c405, c361, c23, c197, c178, c199, c180, c213, c189, c224] c418 (by decide) p (sat_cons (step93 p h) (sat_cons (step417 p h) (sat_cons (step20 p h) (sat_cons (step21 p h) (sat_cons (step405 p h) (sat_cons (step361 p h) (sat_cons (step23 p h) (sat_cons (step197 p h) (sat_cons (step178 p h) (sat_cons (step199 p h) (sat_cons (step180 p h) (sat_cons (step213 p h) (sat_cons (step189 p h) (sat_cons (step224 p h) (sat_nil p)))))))))))))))
def c419 : List Lit := [(1, false), (24, true), (7, false)]
theorem step419 (p : Nat → Bool) (h : Constraints p) : clause p c419 = true :=
  Snake9.LocalRup.prove_clause [c397, c95, c386, c358, c399, c416, c39, c202, c411, c204, c207, c390, c379, c315, c346, c356, c282, c389, c172, c418, c280, c355, c349, c391, c382, c301, c27, c25, c200, c405, c213, c179, c229, c181, c190] c419 (by decide) p (sat_cons (step397 p h) (sat_cons (step95 p h) (sat_cons (step386 p h) (sat_cons (step358 p h) (sat_cons (step399 p h) (sat_cons (step416 p h) (sat_cons (step39 p h) (sat_cons (step202 p h) (sat_cons (step411 p h) (sat_cons (step204 p h) (sat_cons (step207 p h) (sat_cons (step390 p h) (sat_cons (step379 p h) (sat_cons (step315 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step282 p h) (sat_cons (step389 p h) (sat_cons (step172 p h) (sat_cons (step418 p h) (sat_cons (step280 p h) (sat_cons (step355 p h) (sat_cons (step349 p h) (sat_cons (step391 p h) (sat_cons (step382 p h) (sat_cons (step301 p h) (sat_cons (step27 p h) (sat_cons (step25 p h) (sat_cons (step200 p h) (sat_cons (step405 p h) (sat_cons (step213 p h) (sat_cons (step179 p h) (sat_cons (step229 p h) (sat_cons (step181 p h) (sat_cons (step190 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c420 : List Lit := [(11, true), (1255, false), (13, false), (1278, false), (1370, false)]
theorem step420 (p : Nat → Bool) (h : Constraints p) : clause p c420 = true :=
  Snake9.LocalRup.prove_clause [c397, c386, c358, c399, c379, c315, c346, c356, c282, c210, c232, c194, c181, c177, c179, c180, c193, c229, c228, c213, c280, c200, c355, c30, c349, c301, c391, c382] c420 (by decide) p (sat_cons (step397 p h) (sat_cons (step386 p h) (sat_cons (step358 p h) (sat_cons (step399 p h) (sat_cons (step379 p h) (sat_cons (step315 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step282 p h) (sat_cons (step210 p h) (sat_cons (step232 p h) (sat_cons (step194 p h) (sat_cons (step181 p h) (sat_cons (step177 p h) (sat_cons (step179 p h) (sat_cons (step180 p h) (sat_cons (step193 p h) (sat_cons (step229 p h) (sat_cons (step228 p h) (sat_cons (step213 p h) (sat_cons (step280 p h) (sat_cons (step200 p h) (sat_cons (step355 p h) (sat_cons (step30 p h) (sat_cons (step349 p h) (sat_cons (step301 p h) (sat_cons (step391 p h) (sat_cons (step382 p h) (sat_nil p)))))))))))))))))))))))))))))
def c421 : List Lit := [(24, true), (7, false)]
theorem step421 (p : Nat → Bool) (h : Constraints p) : clause p c421 = true :=
  Snake9.LocalRup.prove_clause [c397, c95, c93, c386, c358, c399, c390, c379, c315, c346, c356, c282, c389, c39, c202, c411, c204, c207, c416, c419, c175, c192, c420, c20, c21, c405, c361, c197, c199, c213, c229, c224, c193, c280, c180, c355, c178, c349, c30, c391, c301, c382] c421 (by decide) p (sat_cons (step397 p h) (sat_cons (step95 p h) (sat_cons (step93 p h) (sat_cons (step386 p h) (sat_cons (step358 p h) (sat_cons (step399 p h) (sat_cons (step390 p h) (sat_cons (step379 p h) (sat_cons (step315 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step282 p h) (sat_cons (step389 p h) (sat_cons (step39 p h) (sat_cons (step202 p h) (sat_cons (step411 p h) (sat_cons (step204 p h) (sat_cons (step207 p h) (sat_cons (step416 p h) (sat_cons (step419 p h) (sat_cons (step175 p h) (sat_cons (step192 p h) (sat_cons (step420 p h) (sat_cons (step20 p h) (sat_cons (step21 p h) (sat_cons (step405 p h) (sat_cons (step361 p h) (sat_cons (step197 p h) (sat_cons (step199 p h) (sat_cons (step213 p h) (sat_cons (step229 p h) (sat_cons (step224 p h) (sat_cons (step193 p h) (sat_cons (step280 p h) (sat_cons (step180 p h) (sat_cons (step355 p h) (sat_cons (step178 p h) (sat_cons (step349 p h) (sat_cons (step30 p h) (sat_cons (step391 p h) (sat_cons (step301 p h) (sat_cons (step382 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c422 : List Lit := [(1471, true), (9, false), (1268, false), (1263, false), (13, false), (1370, false)]
theorem step422 (p : Nat → Bool) (h : Constraints p) : clause p c422 = true :=
  Snake9.LocalRup.prove_clause [c358, c399, c395, c397, c396, c111, c97, c379, c315, c346, c356, c347, c349, c342, c317, c391, c332, c298, c382, c327, c329, c377, c301, c325, c323, c31, c30, c85, c204, c201, c86, c205, c215, c244, c224, c257, c281, c266, c264, c240, c258, c235, c252, c47, c57, c247] c422 (by decide) p (sat_cons (step358 p h) (sat_cons (step399 p h) (sat_cons (step395 p h) (sat_cons (step397 p h) (sat_cons (step396 p h) (sat_cons (step111 p h) (sat_cons (step97 p h) (sat_cons (step379 p h) (sat_cons (step315 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step347 p h) (sat_cons (step349 p h) (sat_cons (step342 p h) (sat_cons (step317 p h) (sat_cons (step391 p h) (sat_cons (step332 p h) (sat_cons (step298 p h) (sat_cons (step382 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step377 p h) (sat_cons (step301 p h) (sat_cons (step325 p h) (sat_cons (step323 p h) (sat_cons (step31 p h) (sat_cons (step30 p h) (sat_cons (step85 p h) (sat_cons (step204 p h) (sat_cons (step201 p h) (sat_cons (step86 p h) (sat_cons (step205 p h) (sat_cons (step215 p h) (sat_cons (step244 p h) (sat_cons (step224 p h) (sat_cons (step257 p h) (sat_cons (step281 p h) (sat_cons (step266 p h) (sat_cons (step264 p h) (sat_cons (step240 p h) (sat_cons (step258 p h) (sat_cons (step235 p h) (sat_cons (step252 p h) (sat_cons (step47 p h) (sat_cons (step57 p h) (sat_cons (step247 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c423 : List Lit := [(12, true), (1283, true), (11, false), (7, false)]
theorem step423 (p : Nat → Bool) (h : Constraints p) : clause p c423 = true :=
  Snake9.LocalRup.prove_clause [c93, c21, c20, c361, c197, c405, c201, c387, c215, c204, c205] c423 (by decide) p (sat_cons (step93 p h) (sat_cons (step21 p h) (sat_cons (step20 p h) (sat_cons (step361 p h) (sat_cons (step197 p h) (sat_cons (step405 p h) (sat_cons (step201 p h) (sat_cons (step387 p h) (sat_cons (step215 p h) (sat_cons (step204 p h) (sat_cons (step205 p h) (sat_nil p))))))))))))
def c424 : List Lit := [(9, false), (11, false), (1263, false), (13, false), (7, false)]
theorem step424 (p : Nat → Bool) (h : Constraints p) : clause p c424 = true :=
  Snake9.LocalRup.prove_clause [c93, c92, c386, c358, c395, c396, c111, c21, c20, c361, c197, c199, c390, c422, c355, c280, c224, c423, c29, c30, c360, c204, c301, c16, c205, c382, c212, c391, c223, c277, c278, c354, c264, c350, c260, c342, c332, c327, c329, c324, c325, c323, c51, c85, c241, c86, c245] c424 (by decide) p (sat_cons (step93 p h) (sat_cons (step92 p h) (sat_cons (step386 p h) (sat_cons (step358 p h) (sat_cons (step395 p h) (sat_cons (step396 p h) (sat_cons (step111 p h) (sat_cons (step21 p h) (sat_cons (step20 p h) (sat_cons (step361 p h) (sat_cons (step197 p h) (sat_cons (step199 p h) (sat_cons (step390 p h) (sat_cons (step422 p h) (sat_cons (step355 p h) (sat_cons (step280 p h) (sat_cons (step224 p h) (sat_cons (step423 p h) (sat_cons (step29 p h) (sat_cons (step30 p h) (sat_cons (step360 p h) (sat_cons (step204 p h) (sat_cons (step301 p h) (sat_cons (step16 p h) (sat_cons (step205 p h) (sat_cons (step382 p h) (sat_cons (step212 p h) (sat_cons (step391 p h) (sat_cons (step223 p h) (sat_cons (step277 p h) (sat_cons (step278 p h) (sat_cons (step354 p h) (sat_cons (step264 p h) (sat_cons (step350 p h) (sat_cons (step260 p h) (sat_cons (step342 p h) (sat_cons (step332 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step324 p h) (sat_cons (step325 p h) (sat_cons (step323 p h) (sat_cons (step51 p h) (sat_cons (step85 p h) (sat_cons (step241 p h) (sat_cons (step86 p h) (sat_cons (step245 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c425 : List Lit := [(1277, true), (7, false)]
theorem step425 (p : Nat → Bool) (h : Constraints p) : clause p c425 = true :=
  Snake9.LocalRup.prove_clause [c205, c206, c204, c202, c387] c425 (by decide) p (sat_cons (step205 p h) (sat_cons (step206 p h) (sat_cons (step204 p h) (sat_cons (step202 p h) (sat_cons (step387 p h) (sat_nil p))))))
def c426 : List Lit := [(1292, false), (1402, false)]
theorem step426 (p : Nat → Bool) (h : Constraints p) : clause p c426 = true :=
  Snake9.LocalRup.prove_clause [c399, c386, c358, c395, c396, c111, c99, c346, c356, c280, c281, c355, c264, c347, c260, c342, c332, c327, c329, c324, c325, c323, c85, c86, c244, c245, c258, c241, c252, c54, c247, c53] c426 (by decide) p (sat_cons (step399 p h) (sat_cons (step386 p h) (sat_cons (step358 p h) (sat_cons (step395 p h) (sat_cons (step396 p h) (sat_cons (step111 p h) (sat_cons (step99 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step280 p h) (sat_cons (step281 p h) (sat_cons (step355 p h) (sat_cons (step264 p h) (sat_cons (step347 p h) (sat_cons (step260 p h) (sat_cons (step342 p h) (sat_cons (step332 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step324 p h) (sat_cons (step325 p h) (sat_cons (step323 p h) (sat_cons (step85 p h) (sat_cons (step86 p h) (sat_cons (step244 p h) (sat_cons (step245 p h) (sat_cons (step258 p h) (sat_cons (step241 p h) (sat_cons (step252 p h) (sat_cons (step54 p h) (sat_cons (step247 p h) (sat_cons (step53 p h) (sat_nil p)))))))))))))))))))))))))))))))))
end B112E144
