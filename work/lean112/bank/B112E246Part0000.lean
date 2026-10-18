import B112E246Inputs
namespace B112E246
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c371 : List Lit := [(33, false)]
theorem step371 (p : Nat → Bool) (h : Constraints p) : clause p c371 = true :=
  Snake9.LocalRup.prove_clause [c120, c13] c371 (by decide) p (sat_cons (step120 p h) (sat_cons (step13 p h) (sat_nil p)))
def c372 : List Lit := [(418, false)]
theorem step372 (p : Nat → Bool) (h : Constraints p) : clause p c372 = true :=
  Snake9.LocalRup.prove_clause [c175, c174] c372 (by decide) p (sat_cons (step175 p h) (sat_cons (step174 p h) (sat_nil p)))
def c373 : List Lit := [(416, false)]
theorem step373 (p : Nat → Bool) (h : Constraints p) : clause p c373 = true :=
  Snake9.LocalRup.prove_clause [c372, c173] c373 (by decide) p (sat_cons (step372 p h) (sat_cons (step173 p h) (sat_nil p)))
def c374 : List Lit := [(414, false)]
theorem step374 (p : Nat → Bool) (h : Constraints p) : clause p c374 = true :=
  Snake9.LocalRup.prove_clause [c373, c170] c374 (by decide) p (sat_cons (step373 p h) (sat_cons (step170 p h) (sat_nil p)))
def c375 : List Lit := [(388, false)]
theorem step375 (p : Nat → Bool) (h : Constraints p) : clause p c375 = true :=
  Snake9.LocalRup.prove_clause [c373, c172] c375 (by decide) p (sat_cons (step373 p h) (sat_cons (step172 p h) (sat_nil p)))
def c376 : List Lit := [(1308, true)]
theorem step376 (p : Nat → Bool) (h : Constraints p) : clause p c376 = true :=
  Snake9.LocalRup.prove_clause [c371, c212] c376 (by decide) p (sat_cons (step371 p h) (sat_cons (step212 p h) (sat_nil p)))
def c377 : List Lit := [(1306, false), (1309, true)]
theorem step377 (p : Nat → Bool) (h : Constraints p) : clause p c377 = true :=
  Snake9.LocalRup.prove_clause [c371, c213] c377 (by decide) p (sat_cons (step371 p h) (sat_cons (step213 p h) (sat_nil p)))
def c378 : List Lit := [(1311, true)]
theorem step378 (p : Nat → Bool) (h : Constraints p) : clause p c378 = true :=
  Snake9.LocalRup.prove_clause [c376, c214] c378 (by decide) p (sat_cons (step376 p h) (sat_cons (step214 p h) (sat_nil p)))
def c379 : List Lit := [(1303, false), (1312, true)]
theorem step379 (p : Nat → Bool) (h : Constraints p) : clause p c379 = true :=
  Snake9.LocalRup.prove_clause [c376, c215] c379 (by decide) p (sat_cons (step376 p h) (sat_cons (step215 p h) (sat_nil p)))
def c380 : List Lit := [(1330, false), (1338, true)]
theorem step380 (p : Nat → Bool) (h : Constraints p) : clause p c380 = true :=
  Snake9.LocalRup.prove_clause [c378, c228] c380 (by decide) p (sat_cons (step378 p h) (sat_cons (step228 p h) (sat_nil p)))
def c381 : List Lit := [(1331, false), (1339, true)]
theorem step381 (p : Nat → Bool) (h : Constraints p) : clause p c381 = true :=
  Snake9.LocalRup.prove_clause [c378, c229] c381 (by decide) p (sat_cons (step378 p h) (sat_cons (step229 p h) (sat_nil p)))
def c382 : List Lit := [(1326, true)]
theorem step382 (p : Nat → Bool) (h : Constraints p) : clause p c382 = true :=
  Snake9.LocalRup.prove_clause [c123, c224, c225, c222, c223, c221, c20, c19] c382 (by decide) p (sat_cons (step123 p h) (sat_cons (step224 p h) (sat_cons (step225 p h) (sat_cons (step222 p h) (sat_cons (step223 p h) (sat_cons (step221 p h) (sat_cons (step20 p h) (sat_cons (step19 p h) (sat_nil p)))))))))
def c383 : List Lit := [(1330, true)]
theorem step383 (p : Nat → Bool) (h : Constraints p) : clause p c383 = true :=
  Snake9.LocalRup.prove_clause [c382, c226] c383 (by decide) p (sat_cons (step382 p h) (sat_cons (step226 p h) (sat_nil p)))
def c384 : List Lit := [(1338, true)]
theorem step384 (p : Nat → Bool) (h : Constraints p) : clause p c384 = true :=
  Snake9.LocalRup.prove_clause [c383, c380] c384 (by decide) p (sat_cons (step383 p h) (sat_cons (step380 p h) (sat_nil p)))
def c385 : List Lit := [(1388, true)]
theorem step385 (p : Nat → Bool) (h : Constraints p) : clause p c385 = true :=
  Snake9.LocalRup.prove_clause [c130, c268, c270, c266, c262, c263, c56, c63] c385 (by decide) p (sat_cons (step130 p h) (sat_cons (step268 p h) (sat_cons (step270 p h) (sat_cons (step266 p h) (sat_cons (step262 p h) (sat_cons (step263 p h) (sat_cons (step56 p h) (sat_cons (step63 p h) (sat_nil p)))))))))
def c386 : List Lit := [(1392, true)]
theorem step386 (p : Nat → Bool) (h : Constraints p) : clause p c386 = true :=
  Snake9.LocalRup.prove_clause [c385, c275] c386 (by decide) p (sat_cons (step385 p h) (sat_cons (step275 p h) (sat_nil p)))
def c387 : List Lit := [(1400, true)]
theorem step387 (p : Nat → Bool) (h : Constraints p) : clause p c387 = true :=
  Snake9.LocalRup.prove_clause [c386, c385, c129, c283, c286, c277, c249, c257, c244, c246, c254, c255, c241, c242, c27, c48, c55] c387 (by decide) p (sat_cons (step386 p h) (sat_cons (step385 p h) (sat_cons (step129 p h) (sat_cons (step283 p h) (sat_cons (step286 p h) (sat_cons (step277 p h) (sat_cons (step249 p h) (sat_cons (step257 p h) (sat_cons (step244 p h) (sat_cons (step246 p h) (sat_cons (step254 p h) (sat_cons (step255 p h) (sat_cons (step241 p h) (sat_cons (step242 p h) (sat_cons (step27 p h) (sat_cons (step48 p h) (sat_cons (step55 p h) (sat_nil p))))))))))))))))))
def c388 : List Lit := [(1421, true), (1415, true)]
theorem step388 (p : Nat → Bool) (h : Constraints p) : clause p c388 = true :=
  Snake9.LocalRup.prove_clause [c137, c136, c298, c308, c309, c305, c302, c303, c91, c86, c84, c294, c296, c300, c70] c388 (by decide) p (sat_cons (step137 p h) (sat_cons (step136 p h) (sat_cons (step298 p h) (sat_cons (step308 p h) (sat_cons (step309 p h) (sat_cons (step305 p h) (sat_cons (step302 p h) (sat_cons (step303 p h) (sat_cons (step91 p h) (sat_cons (step86 p h) (sat_cons (step84 p h) (sat_cons (step294 p h) (sat_cons (step296 p h) (sat_cons (step300 p h) (sat_cons (step70 p h) (sat_nil p))))))))))))))))
def c389 : List Lit := [(1426, true)]
theorem step389 (p : Nat → Bool) (h : Constraints p) : clause p c389 = true :=
  Snake9.LocalRup.prove_clause [c132, c134, c314, c319, c388, c316, c297, c299, c294, c295, c75, c78, c70, c305, c310, c302, c303, c84] c389 (by decide) p (sat_cons (step132 p h) (sat_cons (step134 p h) (sat_cons (step314 p h) (sat_cons (step319 p h) (sat_cons (step388 p h) (sat_cons (step316 p h) (sat_cons (step297 p h) (sat_cons (step299 p h) (sat_cons (step294 p h) (sat_cons (step295 p h) (sat_cons (step75 p h) (sat_cons (step78 p h) (sat_cons (step70 p h) (sat_cons (step305 p h) (sat_cons (step310 p h) (sat_cons (step302 p h) (sat_cons (step303 p h) (sat_cons (step84 p h) (sat_nil p)))))))))))))))))))
def c390 : List Lit := [(1277, true)]
theorem step390 (p : Nat → Bool) (h : Constraints p) : clause p c390 = true :=
  Snake9.LocalRup.prove_clause [c118, c200, c201, c198, c199, c197, c11, c10] c390 (by decide) p (sat_cons (step118 p h) (sat_cons (step200 p h) (sat_cons (step201 p h) (sat_cons (step198 p h) (sat_cons (step199 p h) (sat_cons (step197 p h) (sat_cons (step11 p h) (sat_cons (step10 p h) (sat_nil p)))))))))
def c391 : List Lit := [(1281, true)]
theorem step391 (p : Nat → Bool) (h : Constraints p) : clause p c391 = true :=
  Snake9.LocalRup.prove_clause [c390, c202] c391 (by decide) p (sat_cons (step390 p h) (sat_cons (step202 p h) (sat_nil p)))
def c392 : List Lit := [(1262, true)]
theorem step392 (p : Nat → Bool) (h : Constraints p) : clause p c392 = true :=
  Snake9.LocalRup.prove_clause [c114, c115, c187, c188, c185, c186, c178, c183, c184, c4, c176, c7, c368] c392 (by decide) p (sat_cons (step114 p h) (sat_cons (step115 p h) (sat_cons (step187 p h) (sat_cons (step188 p h) (sat_cons (step185 p h) (sat_cons (step186 p h) (sat_cons (step178 p h) (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step4 p h) (sat_cons (step176 p h) (sat_cons (step7 p h) (sat_cons (step368 p h) (sat_nil p))))))))))))))
def c393 : List Lit := [(1289, true)]
theorem step393 (p : Nat → Bool) (h : Constraints p) : clause p c393 = true :=
  Snake9.LocalRup.prove_clause [c392, c391, c204] c393 (by decide) p (sat_cons (step392 p h) (sat_cons (step391 p h) (sat_cons (step204 p h) (sat_nil p))))
def c394 : List Lit := [(1353, true)]
theorem step394 (p : Nat → Bool) (h : Constraints p) : clause p c394 = true :=
  Snake9.LocalRup.prove_clause [c393, c384, c232] c394 (by decide) p (sat_cons (step393 p h) (sat_cons (step384 p h) (sat_cons (step232 p h) (sat_nil p))))
def c395 : List Lit := [(1473, false)]
theorem step395 (p : Nat → Bool) (h : Constraints p) : clause p c395 = true :=
  Snake9.LocalRup.prove_clause [c394, c367, c363] c395 (by decide) p (sat_cons (step394 p h) (sat_cons (step367 p h) (sat_cons (step363 p h) (sat_nil p))))
def c396 : List Lit := [(1355, true), (1282, false)]
theorem step396 (p : Nat → Bool) (h : Constraints p) : clause p c396 = true :=
  Snake9.LocalRup.prove_clause [c392, c384, c382, c122, c114, c115, c205, c237, c236, c207, c381, c190, c227, c219, c217, c218, c18, c15, c180, c181, c189, c176, c185, c186, c183, c184, c4, c7, c368] c396 (by decide) p (sat_cons (step392 p h) (sat_cons (step384 p h) (sat_cons (step382 p h) (sat_cons (step122 p h) (sat_cons (step114 p h) (sat_cons (step115 p h) (sat_cons (step205 p h) (sat_cons (step237 p h) (sat_cons (step236 p h) (sat_cons (step207 p h) (sat_cons (step381 p h) (sat_cons (step190 p h) (sat_cons (step227 p h) (sat_cons (step219 p h) (sat_cons (step217 p h) (sat_cons (step218 p h) (sat_cons (step18 p h) (sat_cons (step15 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step189 p h) (sat_cons (step176 p h) (sat_cons (step185 p h) (sat_cons (step186 p h) (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step4 p h) (sat_cons (step7 p h) (sat_cons (step368 p h) (sat_nil p))))))))))))))))))))))))))))))
def c397 : List Lit := [(373, false), (1436, true), (93, true)]
theorem step397 (p : Nat → Bool) (h : Constraints p) : clause p c397 = true :=
  Snake9.LocalRup.prove_clause [c375, c373, c139, c140, c138, c153, c154, c171, c151, c168, c150, c160, c161, c149, c159, c156, c89, c158, c155, c97, c101, c98, c326, c330, c94, c95, c370, c93] c397 (by decide) p (sat_cons (step375 p h) (sat_cons (step373 p h) (sat_cons (step139 p h) (sat_cons (step140 p h) (sat_cons (step138 p h) (sat_cons (step153 p h) (sat_cons (step154 p h) (sat_cons (step171 p h) (sat_cons (step151 p h) (sat_cons (step168 p h) (sat_cons (step150 p h) (sat_cons (step160 p h) (sat_cons (step161 p h) (sat_cons (step149 p h) (sat_cons (step159 p h) (sat_cons (step156 p h) (sat_cons (step89 p h) (sat_cons (step158 p h) (sat_cons (step155 p h) (sat_cons (step97 p h) (sat_cons (step101 p h) (sat_cons (step98 p h) (sat_cons (step326 p h) (sat_cons (step330 p h) (sat_cons (step94 p h) (sat_cons (step95 p h) (sat_cons (step370 p h) (sat_cons (step93 p h) (sat_nil p)))))))))))))))))))))))))))))
def c398 : List Lit := [(409, true), (103, true), (1443, true)]
theorem step398 (p : Nat → Bool) (h : Constraints p) : clause p c398 = true :=
  Snake9.LocalRup.prove_clause [c143, c141, c164, c165, c163, c162, c109, c111, c335, c112, c339, c104, c331] c398 (by decide) p (sat_cons (step143 p h) (sat_cons (step141 p h) (sat_cons (step164 p h) (sat_cons (step165 p h) (sat_cons (step163 p h) (sat_cons (step162 p h) (sat_cons (step109 p h) (sat_cons (step111 p h) (sat_cons (step335 p h) (sat_cons (step112 p h) (sat_cons (step339 p h) (sat_cons (step104 p h) (sat_cons (step331 p h) (sat_nil p))))))))))))))
def c399 : List Lit := [(1415, true), (1417, true)]
theorem step399 (p : Nat → Bool) (h : Constraints p) : clause p c399 = true :=
  Snake9.TreeRup.prove_clause [c135, c136, c132, c390, c367, c387, c389, c142, c374, c373, c139, c140, c302, c86, c303, c84, c294, c83, c298, c300, c296, c74, c75, c67, c70, c193, c195, c203, c396, c365, c354, c349, c342, c346, c397, c148, c144, c73, c72, c107, c334, c336, c345, c328, c398, c166, c167, c169, c171, c160, c152, c159, c151, c158, c150, c149, c89, c97, c326, c101, c98] c399 (by decide) p (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step132 p h) (sat_cons (step390 p h) (sat_cons (step367 p h) (sat_cons (step387 p h) (sat_cons (step389 p h) (sat_cons (step142 p h) (sat_cons (step374 p h) (sat_cons (step373 p h) (sat_cons (step139 p h) (sat_cons (step140 p h) (sat_cons (step302 p h) (sat_cons (step86 p h) (sat_cons (step303 p h) (sat_cons (step84 p h) (sat_cons (step294 p h) (sat_cons (step83 p h) (sat_cons (step298 p h) (sat_cons (step300 p h) (sat_cons (step296 p h) (sat_cons (step74 p h) (sat_cons (step75 p h) (sat_cons (step67 p h) (sat_cons (step70 p h) (sat_cons (step193 p h) (sat_cons (step195 p h) (sat_cons (step203 p h) (sat_cons (step396 p h) (sat_cons (step365 p h) (sat_cons (step354 p h) (sat_cons (step349 p h) (sat_cons (step342 p h) (sat_cons (step346 p h) (sat_cons (step397 p h) (sat_cons (step148 p h) (sat_cons (step144 p h) (sat_cons (step73 p h) (sat_cons (step72 p h) (sat_cons (step107 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step345 p h) (sat_cons (step328 p h) (sat_cons (step398 p h) (sat_cons (step166 p h) (sat_cons (step167 p h) (sat_cons (step169 p h) (sat_cons (step171 p h) (sat_cons (step160 p h) (sat_cons (step152 p h) (sat_cons (step159 p h) (sat_cons (step151 p h) (sat_cons (step158 p h) (sat_cons (step150 p h) (sat_cons (step149 p h) (sat_cons (step89 p h) (sat_cons (step97 p h) (sat_cons (step326 p h) (sat_cons (step101 p h) (sat_cons (step98 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c400 : List Lit := [(1446, true), (97, false), (1439, false)]
theorem step400 (p : Nat → Bool) (h : Constraints p) : clause p c400 = true :=
  Snake9.LocalRup.prove_clause [c140, c99, c336, c341, c344, c338, c329, c332, c92] c400 (by decide) p (sat_cons (step140 p h) (sat_cons (step99 p h) (sat_cons (step336 p h) (sat_cons (step341 p h) (sat_cons (step344 p h) (sat_cons (step338 p h) (sat_cons (step329 p h) (sat_cons (step332 p h) (sat_cons (step92 p h) (sat_nil p))))))))))
def c401 : List Lit := [(1381, true), (1371, true), (83, false)]
theorem step401 (p : Nat → Bool) (h : Constraints p) : clause p c401 = true :=
  Snake9.LocalRup.prove_clause [c134, c129, c79, c257, c259, c254, c255, c37, c247, c241, c242, c33, c49, c54] c401 (by decide) p (sat_cons (step134 p h) (sat_cons (step129 p h) (sat_cons (step79 p h) (sat_cons (step257 p h) (sat_cons (step259 p h) (sat_cons (step254 p h) (sat_cons (step255 p h) (sat_cons (step37 p h) (sat_cons (step247 p h) (sat_cons (step241 p h) (sat_cons (step242 p h) (sat_cons (step33 p h) (sat_cons (step49 p h) (sat_cons (step54 p h) (sat_nil p)))))))))))))))
def c402 : List Lit := [(1401, true), (83, false)]
theorem step402 (p : Nat → Bool) (h : Constraints p) : clause p c402 = true :=
  Snake9.LocalRup.prove_clause [c134, c386, c385, c129, c79, c284, c290, c280, c250, c401, c277, c287, c249, c244, c246, c241, c242, c27, c37, c260, c254, c255, c55, c48] c402 (by decide) p (sat_cons (step134 p h) (sat_cons (step386 p h) (sat_cons (step385 p h) (sat_cons (step129 p h) (sat_cons (step79 p h) (sat_cons (step284 p h) (sat_cons (step290 p h) (sat_cons (step280 p h) (sat_cons (step250 p h) (sat_cons (step401 p h) (sat_cons (step277 p h) (sat_cons (step287 p h) (sat_cons (step249 p h) (sat_cons (step244 p h) (sat_cons (step246 p h) (sat_cons (step241 p h) (sat_cons (step242 p h) (sat_cons (step27 p h) (sat_cons (step37 p h) (sat_cons (step260 p h) (sat_cons (step254 p h) (sat_cons (step255 p h) (sat_cons (step55 p h) (sat_cons (step48 p h) (sat_nil p)))))))))))))))))))))))))
def c403 : List Lit := [(1379, true), (62, true), (60, false)]
theorem step403 (p : Nat → Bool) (h : Constraints p) : clause p c403 = true :=
  Snake9.LocalRup.prove_clause [c129, c254, c255, c55, c48] c403 (by decide) p (sat_cons (step129 p h) (sat_cons (step254 p h) (sat_cons (step255 p h) (sat_cons (step55 p h) (sat_cons (step48 p h) (sat_nil p))))))
def c404 : List Lit := [(1445, true)]
theorem step404 (p : Nat → Bool) (h : Constraints p) : clause p c404 = true :=
  Snake9.LocalRup.prove_clause [c138, c340, c343, c337, c327, c329, c332, c325, c95, c92] c404 (by decide) p (sat_cons (step138 p h) (sat_cons (step340 p h) (sat_cons (step343 p h) (sat_cons (step337 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step332 p h) (sat_cons (step325 p h) (sat_cons (step95 p h) (sat_cons (step92 p h) (sat_nil p)))))))))))
def c405 : List Lit := [(1454, true)]
theorem step405 (p : Nat → Bool) (h : Constraints p) : clause p c405 = true :=
  Snake9.LocalRup.prove_clause [c404, c389, c347] c405 (by decide) p (sat_cons (step404 p h) (sat_cons (step389 p h) (sat_cons (step347 p h) (sat_nil p))))
def c406 : List Lit := [(69, false), (13, false), (59, false), (67, false)]
theorem step406 (p : Nat → Bool) (h : Constraints p) : clause p c406 = true :=
  Snake9.LocalRup.prove_clause [c116, c44, c41, c8] c406 (by decide) p (sat_cons (step116 p h) (sat_cons (step44 p h) (sat_cons (step41 p h) (sat_cons (step8 p h) (sat_nil p)))))
def c407 : List Lit := [(83, false), (64, false), (1395, true), (1255, true), (72, true), (15, false), (71, true), (63, false), (62, true), (60, false)]
theorem step407 (p : Nat → Bool) (h : Constraints p) : clause p c407 = true :=
  Snake9.LocalRup.prove_clause [c117, c127, c179, c263, c403, c37, c36, c260, c176, c177, c281, c181, c1, c273, c271, c9, c38, c264, c266, c64, c65, c59] c407 (by decide) p (sat_cons (step117 p h) (sat_cons (step127 p h) (sat_cons (step179 p h) (sat_cons (step263 p h) (sat_cons (step403 p h) (sat_cons (step37 p h) (sat_cons (step36 p h) (sat_cons (step260 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_cons (step281 p h) (sat_cons (step181 p h) (sat_cons (step1 p h) (sat_cons (step273 p h) (sat_cons (step271 p h) (sat_cons (step9 p h) (sat_cons (step38 p h) (sat_cons (step264 p h) (sat_cons (step266 p h) (sat_cons (step64 p h) (sat_cons (step65 p h) (sat_cons (step59 p h) (sat_nil p)))))))))))))))))))))))
def c408 : List Lit := [(1413, false), (1428, true), (1417, false), (18, false)]
theorem step408 (p : Nat → Bool) (h : Constraints p) : clause p c408 = true :=
  Snake9.LocalRup.prove_clause [c132, c309, c324, c298, c301, c321, c75, c68, c310, c305] c408 (by decide) p (sat_cons (step132 p h) (sat_cons (step309 p h) (sat_cons (step324 p h) (sat_cons (step298 p h) (sat_cons (step301 p h) (sat_cons (step321 p h) (sat_cons (step75 p h) (sat_cons (step68 p h) (sat_cons (step310 p h) (sat_cons (step305 p h) (sat_nil p)))))))))))
def c409 : List Lit := [(64, false), (1428, true), (1395, true), (1255, true), (1417, false), (72, true), (1268, true), (71, true), (63, false), (62, true), (60, false)]
theorem step409 (p : Nat → Bool) (h : Constraints p) : clause p c409 = true :=
  Snake9.LocalRup.prove_clause [c133, c193, c408, c194, c407, c294, c296, c297, c77, c69, c76, c318, c80, c311, c307] c409 (by decide) p (sat_cons (step133 p h) (sat_cons (step193 p h) (sat_cons (step408 p h) (sat_cons (step194 p h) (sat_cons (step407 p h) (sat_cons (step294 p h) (sat_cons (step296 p h) (sat_cons (step297 p h) (sat_cons (step77 p h) (sat_cons (step69 p h) (sat_cons (step76 p h) (sat_cons (step318 p h) (sat_cons (step80 p h) (sat_cons (step311 p h) (sat_cons (step307 p h) (sat_nil p))))))))))))))))
def c410 : List Lit := [(72, true), (1270, true), (71, true), (68, true), (62, true), (67, false), (60, false)]
theorem step410 (p : Nat → Bool) (h : Constraints p) : clause p c410 = true :=
  Snake9.LocalRup.prove_clause [c125, c116, c135, c382, c393, c367, c391, c405, c404, c385, c131, c196, c195, c263, c403, c257, c277, c25, c22, c242, c244, c249, c287, c356, c366, c24, c8, c5, c6, c42, c184, c220, c83, c185, c227, c303, c381, c233, c238, c364, c208, c361, c358, c191, c289, c352, c409, c243, c245, c250, c292, c280, c278, c260, c273, c271, c264, c266, c62, c61] c410 (by decide) p (sat_cons (step125 p h) (sat_cons (step116 p h) (sat_cons (step135 p h) (sat_cons (step382 p h) (sat_cons (step393 p h) (sat_cons (step367 p h) (sat_cons (step391 p h) (sat_cons (step405 p h) (sat_cons (step404 p h) (sat_cons (step385 p h) (sat_cons (step131 p h) (sat_cons (step196 p h) (sat_cons (step195 p h) (sat_cons (step263 p h) (sat_cons (step403 p h) (sat_cons (step257 p h) (sat_cons (step277 p h) (sat_cons (step25 p h) (sat_cons (step22 p h) (sat_cons (step242 p h) (sat_cons (step244 p h) (sat_cons (step249 p h) (sat_cons (step287 p h) (sat_cons (step356 p h) (sat_cons (step366 p h) (sat_cons (step24 p h) (sat_cons (step8 p h) (sat_cons (step5 p h) (sat_cons (step6 p h) (sat_cons (step42 p h) (sat_cons (step184 p h) (sat_cons (step220 p h) (sat_cons (step83 p h) (sat_cons (step185 p h) (sat_cons (step227 p h) (sat_cons (step303 p h) (sat_cons (step381 p h) (sat_cons (step233 p h) (sat_cons (step238 p h) (sat_cons (step364 p h) (sat_cons (step208 p h) (sat_cons (step361 p h) (sat_cons (step358 p h) (sat_cons (step191 p h) (sat_cons (step289 p h) (sat_cons (step352 p h) (sat_cons (step409 p h) (sat_cons (step243 p h) (sat_cons (step245 p h) (sat_cons (step250 p h) (sat_cons (step292 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step260 p h) (sat_cons (step273 p h) (sat_cons (step271 p h) (sat_cons (step264 p h) (sat_cons (step266 p h) (sat_cons (step62 p h) (sat_cons (step61 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c411 : List Lit := [(83, true), (62, true), (1428, true), (1417, false), (18, false)]
theorem step411 (p : Nat → Bool) (h : Constraints p) : clause p c411 = true :=
  Snake9.LocalRup.prove_clause [c133, c408, c294, c296, c77, c69, c67, c305, c300, c310, c321] c411 (by decide) p (sat_cons (step133 p h) (sat_cons (step408 p h) (sat_cons (step294 p h) (sat_cons (step296 p h) (sat_cons (step77 p h) (sat_cons (step69 p h) (sat_cons (step67 p h) (sat_cons (step305 p h) (sat_cons (step300 p h) (sat_cons (step310 p h) (sat_cons (step321 p h) (sat_nil p))))))))))))
def c412 : List Lit := [(82, false), (68, true), (62, true), (1428, true), (1417, false), (18, false), (60, false)]
theorem step412 (p : Nat → Bool) (h : Constraints p) : clause p c412 = true :=
  Snake9.LocalRup.prove_clause [c129, c125, c133, c404, c395, c385, c403, c24, c411, c37, c260, c280, c25, c55, c77, c69, c76, c67, c305, c299, c310, c318, c317, c311, c350, c307, c362, c80, c292, c241, c250, c244, c245, c249, c243, c289, c22, c282, c256, c261] c412 (by decide) p (sat_cons (step129 p h) (sat_cons (step125 p h) (sat_cons (step133 p h) (sat_cons (step404 p h) (sat_cons (step395 p h) (sat_cons (step385 p h) (sat_cons (step403 p h) (sat_cons (step24 p h) (sat_cons (step411 p h) (sat_cons (step37 p h) (sat_cons (step260 p h) (sat_cons (step280 p h) (sat_cons (step25 p h) (sat_cons (step55 p h) (sat_cons (step77 p h) (sat_cons (step69 p h) (sat_cons (step76 p h) (sat_cons (step67 p h) (sat_cons (step305 p h) (sat_cons (step299 p h) (sat_cons (step310 p h) (sat_cons (step318 p h) (sat_cons (step317 p h) (sat_cons (step311 p h) (sat_cons (step350 p h) (sat_cons (step307 p h) (sat_cons (step362 p h) (sat_cons (step80 p h) (sat_cons (step292 p h) (sat_cons (step241 p h) (sat_cons (step250 p h) (sat_cons (step244 p h) (sat_cons (step245 p h) (sat_cons (step249 p h) (sat_cons (step243 p h) (sat_cons (step289 p h) (sat_cons (step22 p h) (sat_cons (step282 p h) (sat_cons (step256 p h) (sat_cons (step261 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c413 : List Lit := [(1395, true), (1270, true), (68, true), (65, true), (62, true), (60, false)]
theorem step413 (p : Nat → Bool) (h : Constraints p) : clause p c413 = true :=
  Snake9.LocalRup.prove_clause [c129, c125, c385, c130, c196, c25, c55, c403, c260, c282, c281, c261, c273, c256, c406, c57, c264, c410, c58] c413 (by decide) p (sat_cons (step129 p h) (sat_cons (step125 p h) (sat_cons (step385 p h) (sat_cons (step130 p h) (sat_cons (step196 p h) (sat_cons (step25 p h) (sat_cons (step55 p h) (sat_cons (step403 p h) (sat_cons (step260 p h) (sat_cons (step282 p h) (sat_cons (step281 p h) (sat_cons (step261 p h) (sat_cons (step273 p h) (sat_cons (step256 p h) (sat_cons (step406 p h) (sat_cons (step57 p h) (sat_cons (step264 p h) (sat_cons (step410 p h) (sat_cons (step58 p h) (sat_nil p))))))))))))))))))))
def c414 : List Lit := [(1354, true)]
theorem step414 (p : Nat → Bool) (h : Constraints p) : clause p c414 = true :=
  Snake9.LocalRup.prove_clause [c393, c384, c391, c382, c122, c114, c115, c233, c235, c381, c206, c227, c190, c219, c217, c218, c18, c15, c180, c181, c189, c176, c185, c186, c183, c184, c4, c7, c368] c414 (by decide) p (sat_cons (step393 p h) (sat_cons (step384 p h) (sat_cons (step391 p h) (sat_cons (step382 p h) (sat_cons (step122 p h) (sat_cons (step114 p h) (sat_cons (step115 p h) (sat_cons (step233 p h) (sat_cons (step235 p h) (sat_cons (step381 p h) (sat_cons (step206 p h) (sat_cons (step227 p h) (sat_cons (step190 p h) (sat_cons (step219 p h) (sat_cons (step217 p h) (sat_cons (step218 p h) (sat_cons (step18 p h) (sat_cons (step15 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step189 p h) (sat_cons (step176 p h) (sat_cons (step185 p h) (sat_cons (step186 p h) (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step4 p h) (sat_cons (step7 p h) (sat_cons (step368 p h) (sat_nil p))))))))))))))))))))))))))))))
def c415 : List Lit := [(1472, false)]
theorem step415 (p : Nat → Bool) (h : Constraints p) : clause p c415 = true :=
  Snake9.LocalRup.prove_clause [c414, c367, c364] c415 (by decide) p (sat_cons (step414 p h) (sat_cons (step367 p h) (sat_cons (step364 p h) (sat_nil p))))
def c416 : List Lit := [(1457, false)]
theorem step416 (p : Nat → Bool) (h : Constraints p) : clause p c416 = true :=
  Snake9.LocalRup.prove_clause [c415, c387, c355] c416 (by decide) p (sat_cons (step415 p h) (sat_cons (step387 p h) (sat_cons (step355 p h) (sat_nil p))))
def c417 : List Lit := [(1403, false)]
theorem step417 (p : Nat → Bool) (h : Constraints p) : clause p c417 = true :=
  Snake9.LocalRup.prove_clause [c415, c405, c361] c417 (by decide) p (sat_cons (step415 p h) (sat_cons (step405 p h) (sat_cons (step361 p h) (sat_nil p))))
def c418 : List Lit := [(1429, false)]
theorem step418 (p : Nat → Bool) (h : Constraints p) : clause p c418 = true :=
  Snake9.LocalRup.prove_clause [c416, c404, c353] c418 (by decide) p (sat_cons (step416 p h) (sat_cons (step404 p h) (sat_cons (step353 p h) (sat_nil p))))
def c419 : List Lit := [(1373, false), (68, true), (65, true), (62, true), (60, false)]
theorem step419 (p : Nat → Bool) (h : Constraints p) : clause p c419 = true :=
  Snake9.LocalRup.prove_clause [c385, c417, c405, c367, c390, c403, c260, c280, c288, c289, c359, c413, c365, c203, c396] c419 (by decide) p (sat_cons (step385 p h) (sat_cons (step417 p h) (sat_cons (step405 p h) (sat_cons (step367 p h) (sat_cons (step390 p h) (sat_cons (step403 p h) (sat_cons (step260 p h) (sat_cons (step280 p h) (sat_cons (step288 p h) (sat_cons (step289 p h) (sat_cons (step359 p h) (sat_cons (step413 p h) (sat_cons (step365 p h) (sat_cons (step203 p h) (sat_cons (step396 p h) (sat_nil p))))))))))))))))
def c420 : List Lit := [(1417, false), (18, false), (1427, true), (68, true), (1428, true), (62, true), (60, false)]
theorem step420 (p : Nat → Bool) (h : Constraints p) : clause p c420 = true :=
  Snake9.LocalRup.prove_clause [c132, c309, c412, c320, c295, c300, c297, c75, c68, c317, c305, c310] c420 (by decide) p (sat_cons (step132 p h) (sat_cons (step309 p h) (sat_cons (step412 p h) (sat_cons (step320 p h) (sat_cons (step295 p h) (sat_cons (step300 p h) (sat_cons (step297 p h) (sat_cons (step75 p h) (sat_cons (step68 p h) (sat_cons (step317 p h) (sat_cons (step305 p h) (sat_cons (step310 p h) (sat_nil p)))))))))))))
def c421 : List Lit := [(68, true), (65, true), (62, true), (60, false)]
theorem step421 (p : Nat → Bool) (h : Constraints p) : clause p c421 = true :=
  Snake9.LocalRup.prove_clause [c129, c125, c385, c405, c415, c367, c404, c390, c136, c137, c403, c260, c280, c284, c358, c352, c55, c25, c419, c249, c244, c242, c22, c256, c261, c282, c285, c359, c360, c365, c350, c396, c323, c203, c195, c193, c420, c302, c303, c399, c86, c84, c320, c308, c305, c91, c68, c69, c301, c296] c421 (by decide) p (sat_cons (step129 p h) (sat_cons (step125 p h) (sat_cons (step385 p h) (sat_cons (step405 p h) (sat_cons (step415 p h) (sat_cons (step367 p h) (sat_cons (step404 p h) (sat_cons (step390 p h) (sat_cons (step136 p h) (sat_cons (step137 p h) (sat_cons (step403 p h) (sat_cons (step260 p h) (sat_cons (step280 p h) (sat_cons (step284 p h) (sat_cons (step358 p h) (sat_cons (step352 p h) (sat_cons (step55 p h) (sat_cons (step25 p h) (sat_cons (step419 p h) (sat_cons (step249 p h) (sat_cons (step244 p h) (sat_cons (step242 p h) (sat_cons (step22 p h) (sat_cons (step256 p h) (sat_cons (step261 p h) (sat_cons (step282 p h) (sat_cons (step285 p h) (sat_cons (step359 p h) (sat_cons (step360 p h) (sat_cons (step365 p h) (sat_cons (step350 p h) (sat_cons (step396 p h) (sat_cons (step323 p h) (sat_cons (step203 p h) (sat_cons (step195 p h) (sat_cons (step193 p h) (sat_cons (step420 p h) (sat_cons (step302 p h) (sat_cons (step303 p h) (sat_cons (step399 p h) (sat_cons (step86 p h) (sat_cons (step84 p h) (sat_cons (step320 p h) (sat_cons (step308 p h) (sat_cons (step305 p h) (sat_cons (step91 p h) (sat_cons (step68 p h) (sat_cons (step69 p h) (sat_cons (step301 p h) (sat_cons (step296 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c422 : List Lit := [(18, false), (93, false), (83, true), (1416, true)]
theorem step422 (p : Nat → Bool) (h : Constraints p) : clause p c422 = true :=
  Snake9.LocalRup.prove_clause [c137, c91, c68, c69, c301, c296] c422 (by decide) p (sat_cons (step137 p h) (sat_cons (step91 p h) (sat_cons (step68 p h) (sat_cons (step69 p h) (sat_cons (step301 p h) (sat_cons (step296 p h) (sat_nil p)))))))
def c423 : List Lit := [(1439, false), (1446, true)]
theorem step423 (p : Nat → Bool) (h : Constraints p) : clause p c423 = true :=
  Snake9.LocalRup.prove_clause [c336, c400, c344, c325, c327] c423 (by decide) p (sat_cons (step336 p h) (sat_cons (step400 p h) (sat_cons (step344 p h) (sat_cons (step325 p h) (sat_cons (step327 p h) (sat_nil p))))))
def c424 : List Lit := [(80, false), (92, false), (85, false), (1439, true)]
theorem step424 (p : Nat → Bool) (h : Constraints p) : clause p c424 = true :=
  Snake9.LocalRup.prove_clause [c143, c142, c375, c373, c139, c141, c140, c334, c107, c333, c110, c72, c73, c144, c148, c153, c154, c171, c151, c167, c168, c150, c166, c160, c149, c164, c159, c88, c163, c157, c158, c96, c113, c102, c100, c105, c103, c99] c424 (by decide) p (sat_cons (step143 p h) (sat_cons (step142 p h) (sat_cons (step375 p h) (sat_cons (step373 p h) (sat_cons (step139 p h) (sat_cons (step141 p h) (sat_cons (step140 p h) (sat_cons (step334 p h) (sat_cons (step107 p h) (sat_cons (step333 p h) (sat_cons (step110 p h) (sat_cons (step72 p h) (sat_cons (step73 p h) (sat_cons (step144 p h) (sat_cons (step148 p h) (sat_cons (step153 p h) (sat_cons (step154 p h) (sat_cons (step171 p h) (sat_cons (step151 p h) (sat_cons (step167 p h) (sat_cons (step168 p h) (sat_cons (step150 p h) (sat_cons (step166 p h) (sat_cons (step160 p h) (sat_cons (step149 p h) (sat_cons (step164 p h) (sat_cons (step159 p h) (sat_cons (step88 p h) (sat_cons (step163 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step96 p h) (sat_cons (step113 p h) (sat_cons (step102 p h) (sat_cons (step100 p h) (sat_cons (step105 p h) (sat_cons (step103 p h) (sat_cons (step99 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c425 : List Lit := [(69, true), (1395, true), (13, false), (62, true), (67, false), (79, true)]
theorem step425 (p : Nat → Bool) (h : Constraints p) : clause p c425 = true :=
  Snake9.LocalRup.prove_clause [c130, c129, c131, c265, c57, c54, c263, c254, c271, c257, c281, c279, c260, c274, c272, c264, c267, c58, c62, c61] c425 (by decide) p (sat_cons (step130 p h) (sat_cons (step129 p h) (sat_cons (step131 p h) (sat_cons (step265 p h) (sat_cons (step57 p h) (sat_cons (step54 p h) (sat_cons (step263 p h) (sat_cons (step254 p h) (sat_cons (step271 p h) (sat_cons (step257 p h) (sat_cons (step281 p h) (sat_cons (step279 p h) (sat_cons (step260 p h) (sat_cons (step274 p h) (sat_cons (step272 p h) (sat_cons (step264 p h) (sat_cons (step267 p h) (sat_cons (step58 p h) (sat_cons (step62 p h) (sat_cons (step61 p h) (sat_nil p)))))))))))))))))))))
def c426 : List Lit := [(69, false), (13, false), (67, false), (85, false)]
theorem step426 (p : Nat → Bool) (h : Constraints p) : clause p c426 = true :=
  Snake9.LocalRup.prove_clause [c116, c47, c43, c8] c426 (by decide) p (sat_cons (step116 p h) (sat_cons (step47 p h) (sat_cons (step43 p h) (sat_cons (step8 p h) (sat_nil p)))))
def c427 : List Lit := [(69, true), (13, false), (79, true), (62, true), (67, false)]
theorem step427 (p : Nat → Bool) (h : Constraints p) : clause p c427 = true :=
  Snake9.LocalRup.prove_clause [c126, c417, c425, c289, c249, c244, c246, c242, c22, c26] c427 (by decide) p (sat_cons (step126 p h) (sat_cons (step417 p h) (sat_cons (step425 p h) (sat_cons (step289 p h) (sat_cons (step249 p h) (sat_cons (step244 p h) (sat_cons (step246 p h) (sat_cons (step242 p h) (sat_cons (step22 p h) (sat_cons (step26 p h) (sat_nil p)))))))))))
def c428 : List Lit := [(13, false), (62, true), (67, false), (79, true), (85, false)]
theorem step428 (p : Nat → Bool) (h : Constraints p) : clause p c428 = true :=
  Snake9.LocalRup.prove_clause [c426, c427] c428 (by decide) p (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_nil p)))
def c429 : List Lit := [(62, true), (1394, false), (67, false), (79, true), (85, false)]
theorem step429 (p : Nat → Bool) (h : Constraints p) : clause p c429 = true :=
  Snake9.LocalRup.prove_clause [c390, c367, c405, c125, c126, c428, c196, c203, c396, c365, c359, c288, c249, c244, c246, c242, c22, c25, c26, c45] c429 (by decide) p (sat_cons (step390 p h) (sat_cons (step367 p h) (sat_cons (step405 p h) (sat_cons (step125 p h) (sat_cons (step126 p h) (sat_cons (step428 p h) (sat_cons (step196 p h) (sat_cons (step203 p h) (sat_cons (step396 p h) (sat_cons (step365 p h) (sat_cons (step359 p h) (sat_cons (step288 p h) (sat_cons (step249 p h) (sat_cons (step244 p h) (sat_cons (step246 p h) (sat_cons (step242 p h) (sat_cons (step22 p h) (sat_cons (step25 p h) (sat_cons (step26 p h) (sat_cons (step45 p h) (sat_nil p)))))))))))))))))))))
def c430 : List Lit := [(1370, true), (62, false)]
theorem step430 (p : Nat → Bool) (h : Constraints p) : clause p c430 = true :=
  Snake9.LocalRup.prove_clause [c244, c246, c241, c242, c27] c430 (by decide) p (sat_cons (step244 p h) (sat_cons (step246 p h) (sat_cons (step241 p h) (sat_cons (step242 p h) (sat_cons (step27 p h) (sat_nil p))))))
def c431 : List Lit := [(71, false), (73, false), (76, false)]
theorem step431 (p : Nat → Bool) (h : Constraints p) : clause p c431 = true :=
  Snake9.LocalRup.prove_clause [c130, c56, c63] c431 (by decide) p (sat_cons (step130 p h) (sat_cons (step56 p h) (sat_cons (step63 p h) (sat_nil p))))
def c432 : List Lit := [(1371, true), (61, true), (70, false), (62, false)]
theorem step432 (p : Nat → Bool) (h : Constraints p) : clause p c432 = true :=
  Snake9.LocalRup.prove_clause [c242, c245, c247, c243, c30] c432 (by decide) p (sat_cons (step242 p h) (sat_cons (step245 p h) (sat_cons (step247 p h) (sat_cons (step243 p h) (sat_cons (step30 p h) (sat_nil p))))))
def c433 : List Lit := [(1417, false), (1412, false), (1402, false)]
theorem step433 (p : Nat → Bool) (h : Constraints p) : clause p c433 = true :=
  Snake9.LocalRup.prove_clause [c405, c367, c390, c415, c404, c137, c360, c350, c297, c317, c359, c365, c396, c203, c195, c193, c309, c310, c320, c305, c300, c91, c68] c433 (by decide) p (sat_cons (step405 p h) (sat_cons (step367 p h) (sat_cons (step390 p h) (sat_cons (step415 p h) (sat_cons (step404 p h) (sat_cons (step137 p h) (sat_cons (step360 p h) (sat_cons (step350 p h) (sat_cons (step297 p h) (sat_cons (step317 p h) (sat_cons (step359 p h) (sat_cons (step365 p h) (sat_cons (step396 p h) (sat_cons (step203 p h) (sat_cons (step195 p h) (sat_cons (step193 p h) (sat_cons (step309 p h) (sat_cons (step310 p h) (sat_cons (step320 p h) (sat_cons (step305 p h) (sat_cons (step300 p h) (sat_cons (step91 p h) (sat_cons (step68 p h) (sat_nil p))))))))))))))))))))))))
def c434 : List Lit := [(1417, true), (1402, false)]
theorem step434 (p : Nat → Bool) (h : Constraints p) : clause p c434 = true :=
  Snake9.LocalRup.prove_clause [c415, c404, c405, c367, c390, c136, c359, c365, c396, c203, c195, c193, c360, c350, c323, c302, c303, c399, c86, c84, c320, c422, c308, c305] c434 (by decide) p (sat_cons (step415 p h) (sat_cons (step404 p h) (sat_cons (step405 p h) (sat_cons (step367 p h) (sat_cons (step390 p h) (sat_cons (step136 p h) (sat_cons (step359 p h) (sat_cons (step365 p h) (sat_cons (step396 p h) (sat_cons (step203 p h) (sat_cons (step195 p h) (sat_cons (step193 p h) (sat_cons (step360 p h) (sat_cons (step350 p h) (sat_cons (step323 p h) (sat_cons (step302 p h) (sat_cons (step303 p h) (sat_cons (step399 p h) (sat_cons (step86 p h) (sat_cons (step84 p h) (sat_cons (step320 p h) (sat_cons (step422 p h) (sat_cons (step308 p h) (sat_cons (step305 p h) (sat_nil p)))))))))))))))))))))))))
end B112E246
