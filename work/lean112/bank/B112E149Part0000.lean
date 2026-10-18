import B112E149Inputs
namespace B112E149
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c318 : List Lit := [(68, true)]
theorem step318 (p : Nat → Bool) (h : Constraints p) : clause p c318 = true :=
  Snake9.LocalRup.prove_clause [c82, c81] c318 (by decide) p (sat_cons (step82 p h) (sat_cons (step81 p h) (sat_nil p)))
def c319 : List Lit := [(390, false)]
theorem step319 (p : Nat → Bool) (h : Constraints p) : clause p c319 = true :=
  Snake9.LocalRup.prove_clause [c213, c210] c319 (by decide) p (sat_cons (step213 p h) (sat_cons (step210 p h) (sat_nil p)))
def c320 : List Lit := [(294, false)]
theorem step320 (p : Nat → Bool) (h : Constraints p) : clause p c320 = true :=
  Snake9.LocalRup.prove_clause [c213, c212] c320 (by decide) p (sat_cons (step213 p h) (sat_cons (step212 p h) (sat_nil p)))
def c321 : List Lit := [(388, false)]
theorem step321 (p : Nat → Bool) (h : Constraints p) : clause p c321 = true :=
  Snake9.LocalRup.prove_clause [c319, c206] c321 (by decide) p (sat_cons (step319 p h) (sat_cons (step206 p h) (sat_nil p)))
def c322 : List Lit := [(340, false)]
theorem step322 (p : Nat → Bool) (h : Constraints p) : clause p c322 = true :=
  Snake9.LocalRup.prove_clause [c319, c209] c322 (by decide) p (sat_cons (step319 p h) (sat_cons (step209 p h) (sat_nil p)))
def c323 : List Lit := [(292, false)]
theorem step323 (p : Nat → Bool) (h : Constraints p) : clause p c323 = true :=
  Snake9.LocalRup.prove_clause [c320, c168] c323 (by decide) p (sat_cons (step320 p h) (sat_cons (step168 p h) (sat_nil p)))
def c324 : List Lit := [(244, false)]
theorem step324 (p : Nat → Bool) (h : Constraints p) : clause p c324 = true :=
  Snake9.LocalRup.prove_clause [c320, c171] c324 (by decide) p (sat_cons (step320 p h) (sat_cons (step171 p h) (sat_nil p)))
def c325 : List Lit := [(362, false)]
theorem step325 (p : Nat → Bool) (h : Constraints p) : clause p c325 = true :=
  Snake9.LocalRup.prove_clause [c321, c205] c325 (by decide) p (sat_cons (step321 p h) (sat_cons (step205 p h) (sat_nil p)))
def c326 : List Lit := [(290, false)]
theorem step326 (p : Nat → Bool) (h : Constraints p) : clause p c326 = true :=
  Snake9.LocalRup.prove_clause [c323, c163] c326 (by decide) p (sat_cons (step323 p h) (sat_cons (step163 p h) (sat_nil p)))
def c327 : List Lit := [(266, false)]
theorem step327 (p : Nat → Bool) (h : Constraints p) : clause p c327 = true :=
  Snake9.LocalRup.prove_clause [c323, c166] c327 (by decide) p (sat_cons (step323 p h) (sat_cons (step166 p h) (sat_nil p)))
def c328 : List Lit := [(242, false)]
theorem step328 (p : Nat → Bool) (h : Constraints p) : clause p c328 = true :=
  Snake9.LocalRup.prove_clause [c324, c135] c328 (by decide) p (sat_cons (step324 p h) (sat_cons (step135 p h) (sat_nil p)))
def c329 : List Lit := [(220, false)]
theorem step329 (p : Nat → Bool) (h : Constraints p) : clause p c329 = true :=
  Snake9.LocalRup.prove_clause [c324, c136] c329 (by decide) p (sat_cons (step324 p h) (sat_cons (step136 p h) (sat_nil p)))
def c330 : List Lit := [(360, false)]
theorem step330 (p : Nat → Bool) (h : Constraints p) : clause p c330 = true :=
  Snake9.LocalRup.prove_clause [c325, c199] c330 (by decide) p (sat_cons (step325 p h) (sat_cons (step199 p h) (sat_nil p)))
def c331 : List Lit := [(276, false)]
theorem step331 (p : Nat → Bool) (h : Constraints p) : clause p c331 = true :=
  Snake9.LocalRup.prove_clause [c326, c161] c331 (by decide) p (sat_cons (step326 p h) (sat_cons (step161 p h) (sat_nil p)))
def c332 : List Lit := [(264, false)]
theorem step332 (p : Nat → Bool) (h : Constraints p) : clause p c332 = true :=
  Snake9.LocalRup.prove_clause [c327, c148] c332 (by decide) p (sat_cons (step327 p h) (sat_cons (step148 p h) (sat_nil p)))
def c333 : List Lit := [(240, false)]
theorem step333 (p : Nat → Bool) (h : Constraints p) : clause p c333 = true :=
  Snake9.LocalRup.prove_clause [c328, c131] c333 (by decide) p (sat_cons (step328 p h) (sat_cons (step131 p h) (sat_nil p)))
def c334 : List Lit := [(218, false)]
theorem step334 (p : Nat → Bool) (h : Constraints p) : clause p c334 = true :=
  Snake9.LocalRup.prove_clause [c329, c111] c334 (by decide) p (sat_cons (step329 p h) (sat_cons (step111 p h) (sat_nil p)))
def c335 : List Lit := [(208, false)]
theorem step335 (p : Nat → Bool) (h : Constraints p) : clause p c335 = true :=
  Snake9.LocalRup.prove_clause [c329, c112] c335 (by decide) p (sat_cons (step329 p h) (sat_cons (step112 p h) (sat_nil p)))
def c336 : List Lit := [(354, false)]
theorem step336 (p : Nat → Bool) (h : Constraints p) : clause p c336 = true :=
  Snake9.LocalRup.prove_clause [c330, c198] c336 (by decide) p (sat_cons (step330 p h) (sat_cons (step198 p h) (sat_nil p)))
def c337 : List Lit := [(258, false)]
theorem step337 (p : Nat → Bool) (h : Constraints p) : clause p c337 = true :=
  Snake9.LocalRup.prove_clause [c332, c146] c337 (by decide) p (sat_cons (step332 p h) (sat_cons (step146 p h) (sat_nil p)))
def c338 : List Lit := [(238, false)]
theorem step338 (p : Nat → Bool) (h : Constraints p) : clause p c338 = true :=
  Snake9.LocalRup.prove_clause [c333, c127] c338 (by decide) p (sat_cons (step333 p h) (sat_cons (step127 p h) (sat_nil p)))
def c339 : List Lit := [(256, false)]
theorem step339 (p : Nat → Bool) (h : Constraints p) : clause p c339 = true :=
  Snake9.LocalRup.prove_clause [c337, c141] c339 (by decide) p (sat_cons (step337 p h) (sat_cons (step141 p h) (sat_nil p)))
def c340 : List Lit := [(80, false), (83, false), (81, false)]
theorem step340 (p : Nat → Bool) (h : Constraints p) : clause p c340 = true :=
  Snake9.LocalRup.prove_clause [c336, c89, c88, c90, c197, c196] c340 (by decide) p (sat_cons (step336 p h) (sat_cons (step89 p h) (sat_cons (step88 p h) (sat_cons (step90 p h) (sat_cons (step197 p h) (sat_cons (step196 p h) (sat_nil p)))))))
def c341 : List Lit := [(1288, true)]
theorem step341 (p : Nat → Bool) (h : Constraints p) : clause p c341 = true :=
  Snake9.LocalRup.prove_clause [c296, c297, c294, c295, c340] c341 (by decide) p (sat_cons (step296 p h) (sat_cons (step297 p h) (sat_cons (step294 p h) (sat_cons (step295 p h) (sat_cons (step340 p h) (sat_nil p))))))
def c342 : List Lit := [(1291, true)]
theorem step342 (p : Nat → Bool) (h : Constraints p) : clause p c342 = true :=
  Snake9.LocalRup.prove_clause [c341, c298] c342 (by decide) p (sat_cons (step341 p h) (sat_cons (step298 p h) (sat_nil p)))
def c343 : List Lit := [(8, false), (10, false), (2, false)]
theorem step343 (p : Nat → Bool) (h : Constraints p) : clause p c343 = true :=
  Snake9.LocalRup.prove_clause [c334, c4, c11, c10, c109, c107, c110, c108] c343 (by decide) p (sat_cons (step334 p h) (sat_cons (step4 p h) (sat_cons (step11 p h) (sat_cons (step10 p h) (sat_cons (step109 p h) (sat_cons (step107 p h) (sat_cons (step110 p h) (sat_cons (step108 p h) (sat_nil p)))))))))
def c344 : List Lit := [(1149, false), (1160, true)]
theorem step344 (p : Nat → Bool) (h : Constraints p) : clause p c344 = true :=
  Snake9.LocalRup.prove_clause [c225, c216, c218, c224, c220, c221, c219, c343] c344 (by decide) p (sat_cons (step225 p h) (sat_cons (step216 p h) (sat_cons (step218 p h) (sat_cons (step224 p h) (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step219 p h) (sat_cons (step343 p h) (sat_nil p)))))))))
def c345 : List Lit := [(2, false), (1160, true)]
theorem step345 (p : Nat → Bool) (h : Constraints p) : clause p c345 = true :=
  Snake9.LocalRup.prove_clause [c335, c344, c215, c214, c223, c1, c7, c6, c104, c8, c105, c222, c106, c219, c103, c3, c102, c2] c345 (by decide) p (sat_cons (step335 p h) (sat_cons (step344 p h) (sat_cons (step215 p h) (sat_cons (step214 p h) (sat_cons (step223 p h) (sat_cons (step1 p h) (sat_cons (step7 p h) (sat_cons (step6 p h) (sat_cons (step104 p h) (sat_cons (step8 p h) (sat_cons (step105 p h) (sat_cons (step222 p h) (sat_cons (step106 p h) (sat_cons (step219 p h) (sat_cons (step103 p h) (sat_cons (step3 p h) (sat_cons (step102 p h) (sat_cons (step2 p h) (sat_nil p)))))))))))))))))))
def c346 : List Lit := [(1160, true)]
theorem step346 (p : Nat → Bool) (h : Constraints p) : clause p c346 = true :=
  Snake9.LocalRup.prove_clause [c344, c214, c215, c345, c217, c224, c220, c221, c219, c5, c9, c8] c346 (by decide) p (sat_cons (step344 p h) (sat_cons (step214 p h) (sat_cons (step215 p h) (sat_cons (step345 p h) (sat_cons (step217 p h) (sat_cons (step224 p h) (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step219 p h) (sat_cons (step5 p h) (sat_cons (step9 p h) (sat_cons (step8 p h) (sat_nil p)))))))))))))
def c347 : List Lit := [(1182, true)]
theorem step347 (p : Nat → Bool) (h : Constraints p) : clause p c347 = true :=
  Snake9.LocalRup.prove_clause [c346, c243] c347 (by decide) p (sat_cons (step346 p h) (sat_cons (step243 p h) (sat_nil p)))
def c348 : List Lit := [(1216, true), (143, true)]
theorem step348 (p : Nat → Bool) (h : Constraints p) : clause p c348 = true :=
  Snake9.LocalRup.prove_clause [c271, c273, c268, c269, c263, c267, c260, c69, c65] c348 (by decide) p (sat_cons (step271 p h) (sat_cons (step273 p h) (sat_cons (step268 p h) (sat_cons (step269 p h) (sat_cons (step263 p h) (sat_cons (step267 p h) (sat_cons (step260 p h) (sat_cons (step69 p h) (sat_cons (step65 p h) (sat_nil p))))))))))
def c349 : List Lit := [(1283, true), (72, false), (50, false)]
theorem step349 (p : Nat → Bool) (h : Constraints p) : clause p c349 = true :=
  Snake9.LocalRup.prove_clause [c291, c292, c290, c83] c349 (by decide) p (sat_cons (step291 p h) (sat_cons (step292 p h) (sat_cons (step290 p h) (sat_cons (step83 p h) (sat_nil p)))))
def c350 : List Lit := [(1319, true), (72, false), (50, false)]
theorem step350 (p : Nat → Bool) (h : Constraints p) : clause p c350 = true :=
  Snake9.LocalRup.prove_clause [c341, c349, c299, c311, c300, c310, c307, c302, c301, c84, c85, c293, c290] c350 (by decide) p (sat_cons (step341 p h) (sat_cons (step349 p h) (sat_cons (step299 p h) (sat_cons (step311 p h) (sat_cons (step300 p h) (sat_cons (step310 p h) (sat_cons (step307 p h) (sat_cons (step302 p h) (sat_cons (step301 p h) (sat_cons (step84 p h) (sat_cons (step85 p h) (sat_cons (step293 p h) (sat_cons (step290 p h) (sat_nil p))))))))))))))
def c351 : List Lit := [(1197, false), (1190, false), (1216, false), (1236, true)]
theorem step351 (p : Nat → Bool) (h : Constraints p) : clause p c351 = true :=
  Snake9.LocalRup.prove_clause [c347, c346, c248, c283, c282, c257, c279, c284, c244, c259, c238, c240, c250, c235, c236, c229, c231, c234, c226, c227, c29, c22, c36, c37] c351 (by decide) p (sat_cons (step347 p h) (sat_cons (step346 p h) (sat_cons (step248 p h) (sat_cons (step283 p h) (sat_cons (step282 p h) (sat_cons (step257 p h) (sat_cons (step279 p h) (sat_cons (step284 p h) (sat_cons (step244 p h) (sat_cons (step259 p h) (sat_cons (step238 p h) (sat_cons (step240 p h) (sat_cons (step250 p h) (sat_cons (step235 p h) (sat_cons (step236 p h) (sat_cons (step229 p h) (sat_cons (step231 p h) (sat_cons (step234 p h) (sat_cons (step226 p h) (sat_cons (step227 p h) (sat_cons (step29 p h) (sat_cons (step22 p h) (sat_cons (step36 p h) (sat_cons (step37 p h) (sat_nil p)))))))))))))))))))))))))
def c352 : List Lit := [(243, false), (33, false), (1176, true), (32, false), (37, false)]
theorem step352 (p : Nat → Bool) (h : Constraints p) : clause p c352 = true :=
  Snake9.LocalRup.prove_clause [c320, c213, c318, c101, c99, c100, c98, c93, c242, c169, c170, c211, c164, c207, c147, c193, c194, c144, c191, c192, c177, c140, c190, c184, c185, c176, c137, c138, c186, c183, c180, c181, c175, c80, c182, c179, c174, c79, c78, c75, c76, c77, c73, c72, c74, c12, c56, c48, c51, c46, c231, c232, c241, c227, c235, c19, c233] c352 (by decide) p (sat_cons (step320 p h) (sat_cons (step213 p h) (sat_cons (step318 p h) (sat_cons (step101 p h) (sat_cons (step99 p h) (sat_cons (step100 p h) (sat_cons (step98 p h) (sat_cons (step93 p h) (sat_cons (step242 p h) (sat_cons (step169 p h) (sat_cons (step170 p h) (sat_cons (step211 p h) (sat_cons (step164 p h) (sat_cons (step207 p h) (sat_cons (step147 p h) (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step144 p h) (sat_cons (step191 p h) (sat_cons (step192 p h) (sat_cons (step177 p h) (sat_cons (step140 p h) (sat_cons (step190 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step176 p h) (sat_cons (step137 p h) (sat_cons (step138 p h) (sat_cons (step186 p h) (sat_cons (step183 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step175 p h) (sat_cons (step80 p h) (sat_cons (step182 p h) (sat_cons (step179 p h) (sat_cons (step174 p h) (sat_cons (step79 p h) (sat_cons (step78 p h) (sat_cons (step75 p h) (sat_cons (step76 p h) (sat_cons (step77 p h) (sat_cons (step73 p h) (sat_cons (step72 p h) (sat_cons (step74 p h) (sat_cons (step12 p h) (sat_cons (step56 p h) (sat_cons (step48 p h) (sat_cons (step51 p h) (sat_cons (step46 p h) (sat_cons (step231 p h) (sat_cons (step232 p h) (sat_cons (step241 p h) (sat_cons (step227 p h) (sat_cons (step235 p h) (sat_cons (step19 p h) (sat_cons (step233 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c353 : List Lit := [(1167, false), (121, true), (1190, false), (1216, false), (1236, true)]
theorem step353 (p : Nat → Bool) (h : Constraints p) : clause p c353 = true :=
  Snake9.LocalRup.prove_clause [c346, c351, c253, c251, c248, c256, c277, c285, c245, c242, c240, c241, c244, c235, c236, c284, c234, c279, c34, c38, c39, c258, c316, c250, c227, c22, c232] c353 (by decide) p (sat_cons (step346 p h) (sat_cons (step351 p h) (sat_cons (step253 p h) (sat_cons (step251 p h) (sat_cons (step248 p h) (sat_cons (step256 p h) (sat_cons (step277 p h) (sat_cons (step285 p h) (sat_cons (step245 p h) (sat_cons (step242 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step244 p h) (sat_cons (step235 p h) (sat_cons (step236 p h) (sat_cons (step284 p h) (sat_cons (step234 p h) (sat_cons (step279 p h) (sat_cons (step34 p h) (sat_cons (step38 p h) (sat_cons (step39 p h) (sat_cons (step258 p h) (sat_cons (step316 p h) (sat_cons (step250 p h) (sat_cons (step227 p h) (sat_cons (step22 p h) (sat_cons (step232 p h) (sat_nil p))))))))))))))))))))))))))))
def c354 : List Lit := [(1190, false), (1216, false), (37, false), (1236, true)]
theorem step354 (p : Nat → Bool) (h : Constraints p) : clause p c354 = true :=
  Snake9.LocalRup.prove_clause [c346, c248, c256, c277, c351, c285, c253, c254, c245, c252, c352, c251, c134, c130, c132, c126, c118, c124, c114, c113, c353, c229, c231, c226, c227, c13, c46, c28, c16] c354 (by decide) p (sat_cons (step346 p h) (sat_cons (step248 p h) (sat_cons (step256 p h) (sat_cons (step277 p h) (sat_cons (step351 p h) (sat_cons (step285 p h) (sat_cons (step253 p h) (sat_cons (step254 p h) (sat_cons (step245 p h) (sat_cons (step252 p h) (sat_cons (step352 p h) (sat_cons (step251 p h) (sat_cons (step134 p h) (sat_cons (step130 p h) (sat_cons (step132 p h) (sat_cons (step126 p h) (sat_cons (step118 p h) (sat_cons (step124 p h) (sat_cons (step114 p h) (sat_cons (step113 p h) (sat_cons (step353 p h) (sat_cons (step229 p h) (sat_cons (step231 p h) (sat_cons (step226 p h) (sat_cons (step227 p h) (sat_cons (step13 p h) (sat_cons (step46 p h) (sat_cons (step28 p h) (sat_cons (step16 p h) (sat_nil p))))))))))))))))))))))))))))))
def c355 : List Lit := [(1216, true), (45, true)]
theorem step355 (p : Nat → Bool) (h : Constraints p) : clause p c355 = true :=
  Snake9.LocalRup.prove_clause [c271, c273, c348, c269, c263, c66, c260, c67, c65] c355 (by decide) p (sat_cons (step271 p h) (sat_cons (step273 p h) (sat_cons (step348 p h) (sat_cons (step269 p h) (sat_cons (step263 p h) (sat_cons (step66 p h) (sat_cons (step260 p h) (sat_cons (step67 p h) (sat_cons (step65 p h) (sat_nil p))))))))))
def c356 : List Lit := [(1213, true), (45, true), (37, false), (1236, true)]
theorem step356 (p : Nat → Bool) (h : Constraints p) : clause p c356 = true :=
  Snake9.TreeRup.prove_clause [c326, c213, c318, c101, c99, c100, c98, c93, c97, c346, c268, c269, c267, c68, c67, c156, c65, c157, c158, c159, c160, c162, c154, c167, c150, c151, c211, c149, c58, c207, c193, c194, c191, c192, c177, c190, c184, c185, c176, c186, c183, c180, c181, c175, c80, c182, c179, c174, c79, c78, c75, c76, c77, c73, c72, c74, c12, c55, c56, c236, c62, c254, c238, c60, c255, c244, c262, c284, c264, c278, c275] c356 (by decide) p (sat_cons (step326 p h) (sat_cons (step213 p h) (sat_cons (step318 p h) (sat_cons (step101 p h) (sat_cons (step99 p h) (sat_cons (step100 p h) (sat_cons (step98 p h) (sat_cons (step93 p h) (sat_cons (step97 p h) (sat_cons (step346 p h) (sat_cons (step268 p h) (sat_cons (step269 p h) (sat_cons (step267 p h) (sat_cons (step68 p h) (sat_cons (step67 p h) (sat_cons (step156 p h) (sat_cons (step65 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step159 p h) (sat_cons (step160 p h) (sat_cons (step162 p h) (sat_cons (step154 p h) (sat_cons (step167 p h) (sat_cons (step150 p h) (sat_cons (step151 p h) (sat_cons (step211 p h) (sat_cons (step149 p h) (sat_cons (step58 p h) (sat_cons (step207 p h) (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step191 p h) (sat_cons (step192 p h) (sat_cons (step177 p h) (sat_cons (step190 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step176 p h) (sat_cons (step186 p h) (sat_cons (step183 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step175 p h) (sat_cons (step80 p h) (sat_cons (step182 p h) (sat_cons (step179 p h) (sat_cons (step174 p h) (sat_cons (step79 p h) (sat_cons (step78 p h) (sat_cons (step75 p h) (sat_cons (step76 p h) (sat_cons (step77 p h) (sat_cons (step73 p h) (sat_cons (step72 p h) (sat_cons (step74 p h) (sat_cons (step12 p h) (sat_cons (step55 p h) (sat_cons (step56 p h) (sat_cons (step236 p h) (sat_cons (step62 p h) (sat_cons (step254 p h) (sat_cons (step238 p h) (sat_cons (step60 p h) (sat_cons (step255 p h) (sat_cons (step244 p h) (sat_cons (step262 p h) (sat_cons (step284 p h) (sat_cons (step264 p h) (sat_cons (step278 p h) (sat_cons (step275 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c357 : List Lit := [(287, false), (45, true), (37, false), (1236, true)]
theorem step357 (p : Nat → Bool) (h : Constraints p) : clause p c357 = true :=
  Snake9.TreeRup.prove_clause [c326, c213, c318, c101, c99, c100, c98, c93, c97, c346, c356, c159, c160, c162, c154, c167, c150, c151, c211, c149, c58, c207, c193, c194, c191, c192, c177, c190, c184, c185, c176, c186, c183, c180, c181, c175, c80, c182, c179, c174, c79, c78, c75, c76, c77, c73, c72, c74, c12, c55, c56, c236, c62, c254, c238, c60, c255, c244, c261, c284, c263, c278, c274] c357 (by decide) p (sat_cons (step326 p h) (sat_cons (step213 p h) (sat_cons (step318 p h) (sat_cons (step101 p h) (sat_cons (step99 p h) (sat_cons (step100 p h) (sat_cons (step98 p h) (sat_cons (step93 p h) (sat_cons (step97 p h) (sat_cons (step346 p h) (sat_cons (step356 p h) (sat_cons (step159 p h) (sat_cons (step160 p h) (sat_cons (step162 p h) (sat_cons (step154 p h) (sat_cons (step167 p h) (sat_cons (step150 p h) (sat_cons (step151 p h) (sat_cons (step211 p h) (sat_cons (step149 p h) (sat_cons (step58 p h) (sat_cons (step207 p h) (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step191 p h) (sat_cons (step192 p h) (sat_cons (step177 p h) (sat_cons (step190 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step176 p h) (sat_cons (step186 p h) (sat_cons (step183 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step175 p h) (sat_cons (step80 p h) (sat_cons (step182 p h) (sat_cons (step179 p h) (sat_cons (step174 p h) (sat_cons (step79 p h) (sat_cons (step78 p h) (sat_cons (step75 p h) (sat_cons (step76 p h) (sat_cons (step77 p h) (sat_cons (step73 p h) (sat_cons (step72 p h) (sat_cons (step74 p h) (sat_cons (step12 p h) (sat_cons (step55 p h) (sat_cons (step56 p h) (sat_cons (step236 p h) (sat_cons (step62 p h) (sat_cons (step254 p h) (sat_cons (step238 p h) (sat_cons (step60 p h) (sat_cons (step255 p h) (sat_cons (step244 p h) (sat_cons (step261 p h) (sat_cons (step284 p h) (sat_cons (step263 p h) (sat_cons (step278 p h) (sat_cons (step274 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c358 : List Lit := [(1217, false), (1197, false), (1236, true)]
theorem step358 (p : Nat → Bool) (h : Constraints p) : clause p c358 = true :=
  Snake9.LocalRup.prove_clause [c347, c346, c255, c283, c280, c278, c257, c284, c249, c244, c238, c240, c235, c236, c229, c231, c234, c29, c226, c227, c22, c36, c37] c358 (by decide) p (sat_cons (step347 p h) (sat_cons (step346 p h) (sat_cons (step255 p h) (sat_cons (step283 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step257 p h) (sat_cons (step284 p h) (sat_cons (step249 p h) (sat_cons (step244 p h) (sat_cons (step238 p h) (sat_cons (step240 p h) (sat_cons (step235 p h) (sat_cons (step236 p h) (sat_cons (step229 p h) (sat_cons (step231 p h) (sat_cons (step234 p h) (sat_cons (step29 p h) (sat_cons (step226 p h) (sat_cons (step227 p h) (sat_cons (step22 p h) (sat_cons (step36 p h) (sat_cons (step37 p h) (sat_nil p))))))))))))))))))))))))
def c359 : List Lit := [(1217, true), (39, false), (37, true)]
theorem step359 (p : Nat → Bool) (h : Constraints p) : clause p c359 = true :=
  Snake9.LocalRup.prove_clause [c265, c275, c274, c266, c268, c269, c260, c267, c59, c65, c63] c359 (by decide) p (sat_cons (step265 p h) (sat_cons (step275 p h) (sat_cons (step274 p h) (sat_cons (step266 p h) (sat_cons (step268 p h) (sat_cons (step269 p h) (sat_cons (step260 p h) (sat_cons (step267 p h) (sat_cons (step59 p h) (sat_cons (step65 p h) (sat_cons (step63 p h) (sat_nil p))))))))))))
def c360 : List Lit := [(1319, true), (50, false)]
theorem step360 (p : Nat → Bool) (h : Constraints p) : clause p c360 = true :=
  Snake9.LocalRup.prove_clause [c341, c319, c322, c350, c71, c172, c173, c178, c194, c195, c208, c191, c204, c189, c203, c188, c202, c187, c201, c87, c200, c292, c299, c310, c306, c307, c305, c302, c303, c304, c301, c92, c91] c360 (by decide) p (sat_cons (step341 p h) (sat_cons (step319 p h) (sat_cons (step322 p h) (sat_cons (step350 p h) (sat_cons (step71 p h) (sat_cons (step172 p h) (sat_cons (step173 p h) (sat_cons (step178 p h) (sat_cons (step194 p h) (sat_cons (step195 p h) (sat_cons (step208 p h) (sat_cons (step191 p h) (sat_cons (step204 p h) (sat_cons (step189 p h) (sat_cons (step203 p h) (sat_cons (step188 p h) (sat_cons (step202 p h) (sat_cons (step187 p h) (sat_cons (step201 p h) (sat_cons (step87 p h) (sat_cons (step200 p h) (sat_cons (step292 p h) (sat_cons (step299 p h) (sat_cons (step310 p h) (sat_cons (step306 p h) (sat_cons (step307 p h) (sat_cons (step305 p h) (sat_cons (step302 p h) (sat_cons (step303 p h) (sat_cons (step304 p h) (sat_cons (step301 p h) (sat_cons (step92 p h) (sat_cons (step91 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c361 : List Lit := [(1190, false), (291, true), (1236, true)]
theorem step361 (p : Nat → Bool) (h : Constraints p) : clause p c361 = true :=
  Snake9.LocalRup.prove_clause [c96, c162, c159, c158, c157, c156, c348, c164, c147, c144, c140, c137, c351, c354, c253, c57, c252, c50] c361 (by decide) p (sat_cons (step96 p h) (sat_cons (step162 p h) (sat_cons (step159 p h) (sat_cons (step158 p h) (sat_cons (step157 p h) (sat_cons (step156 p h) (sat_cons (step348 p h) (sat_cons (step164 p h) (sat_cons (step147 p h) (sat_cons (step144 p h) (sat_cons (step140 p h) (sat_cons (step137 p h) (sat_cons (step351 p h) (sat_cons (step354 p h) (sat_cons (step253 p h) (sat_cons (step57 p h) (sat_cons (step252 p h) (sat_cons (step50 p h) (sat_nil p)))))))))))))))))))
def c362 : List Lit := [(1217, true), (37, true)]
theorem step362 (p : Nat → Bool) (h : Constraints p) : clause p c362 = true :=
  Snake9.LocalRup.prove_clause [c275, c359, c266, c261] c362 (by decide) p (sat_cons (step275 p h) (sat_cons (step359 p h) (sat_cons (step266 p h) (sat_cons (step261 p h) (sat_nil p)))))
def c363 : List Lit := [(37, true), (20, true), (1236, true)]
theorem step363 (p : Nat → Bool) (h : Constraints p) : clause p c363 = true :=
  Snake9.LocalRup.prove_clause [c96, c346, c236, c57, c362, c276, c358, c285, c253, c245, c252, c239, c241, c49, c237, c229, c233, c227, c19] c363 (by decide) p (sat_cons (step96 p h) (sat_cons (step346 p h) (sat_cons (step236 p h) (sat_cons (step57 p h) (sat_cons (step362 p h) (sat_cons (step276 p h) (sat_cons (step358 p h) (sat_cons (step285 p h) (sat_cons (step253 p h) (sat_cons (step245 p h) (sat_cons (step252 p h) (sat_cons (step239 p h) (sat_cons (step241 p h) (sat_cons (step49 p h) (sat_cons (step237 p h) (sat_cons (step229 p h) (sat_cons (step233 p h) (sat_cons (step227 p h) (sat_cons (step19 p h) (sat_nil p))))))))))))))))))))
def c364 : List Lit := [(1318, true)]
theorem step364 (p : Nat → Bool) (h : Constraints p) : clause p c364 = true :=
  Snake9.LocalRup.prove_clause [c342, c341, c319, c309, c308, c299, c306, c307, c291, c292, c305, c302, c303, c290, c304, c301, c92, c86, c91, c87, c200, c187, c201, c188, c202, c189, c203, c191, c204, c193, c208] c364 (by decide) p (sat_cons (step342 p h) (sat_cons (step341 p h) (sat_cons (step319 p h) (sat_cons (step309 p h) (sat_cons (step308 p h) (sat_cons (step299 p h) (sat_cons (step306 p h) (sat_cons (step307 p h) (sat_cons (step291 p h) (sat_cons (step292 p h) (sat_cons (step305 p h) (sat_cons (step302 p h) (sat_cons (step303 p h) (sat_cons (step290 p h) (sat_cons (step304 p h) (sat_cons (step301 p h) (sat_cons (step92 p h) (sat_cons (step86 p h) (sat_cons (step91 p h) (sat_cons (step87 p h) (sat_cons (step200 p h) (sat_cons (step187 p h) (sat_cons (step201 p h) (sat_cons (step188 p h) (sat_cons (step202 p h) (sat_cons (step189 p h) (sat_cons (step203 p h) (sat_cons (step191 p h) (sat_cons (step204 p h) (sat_cons (step193 p h) (sat_cons (step208 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c365 : List Lit := [(1328, true)]
theorem step365 (p : Nat → Bool) (h : Constraints p) : clause p c365 = true :=
  Snake9.LocalRup.prove_clause [c364, c312, c313, c360, c289, c286, c288, c287] c365 (by decide) p (sat_cons (step364 p h) (sat_cons (step312 p h) (sat_cons (step313 p h) (sat_cons (step360 p h) (sat_cons (step289 p h) (sat_cons (step286 p h) (sat_cons (step288 p h) (sat_cons (step287 p h) (sat_nil p)))))))))
def c366 : List Lit := [(1236, false)]
theorem step366 (p : Nat → Bool) (h : Constraints p) : clause p c366 = true :=
  Snake9.LocalRup.prove_clause [c365, c315, c314] c366 (by decide) p (sat_cons (step365 p h) (sat_cons (step315 p h) (sat_cons (step314 p h) (sat_nil p))))
def c367 : List Lit := [(37, true)]
theorem step367 (p : Nat → Bool) (h : Constraints p) : clause p c367 = true :=
  Snake9.LocalRup.prove_clause [c96, c366, c346, c339, c57, c362, c276, c363, c358, c285, c253, c254, c245, c251, c252, c53, c242, c50, c49, c139, c48, c46, c231, c232, c241, c227, c235, c19, c233] c367 (by decide) p (sat_cons (step96 p h) (sat_cons (step366 p h) (sat_cons (step346 p h) (sat_cons (step339 p h) (sat_cons (step57 p h) (sat_cons (step362 p h) (sat_cons (step276 p h) (sat_cons (step363 p h) (sat_cons (step358 p h) (sat_cons (step285 p h) (sat_cons (step253 p h) (sat_cons (step254 p h) (sat_cons (step245 p h) (sat_cons (step251 p h) (sat_cons (step252 p h) (sat_cons (step53 p h) (sat_cons (step242 p h) (sat_cons (step50 p h) (sat_cons (step49 p h) (sat_cons (step139 p h) (sat_cons (step48 p h) (sat_cons (step46 p h) (sat_cons (step231 p h) (sat_cons (step232 p h) (sat_cons (step241 p h) (sat_cons (step227 p h) (sat_cons (step235 p h) (sat_cons (step19 p h) (sat_cons (step233 p h) (sat_nil p))))))))))))))))))))))))))))))
def c368 : List Lit := [(20, true), (34, false), (1176, true)]
theorem step368 (p : Nat → Bool) (h : Constraints p) : clause p c368 = true :=
  Snake9.LocalRup.prove_clause [c239, c236, c237, c241, c234, c229, c231, c31, c226, c227, c20, c36, c37] c368 (by decide) p (sat_cons (step239 p h) (sat_cons (step236 p h) (sat_cons (step237 p h) (sat_cons (step241 p h) (sat_cons (step234 p h) (sat_cons (step229 p h) (sat_cons (step231 p h) (sat_cons (step31 p h) (sat_cons (step226 p h) (sat_cons (step227 p h) (sat_cons (step20 p h) (sat_cons (step36 p h) (sat_cons (step37 p h) (sat_nil p))))))))))))))
def c369 : List Lit := [(22, false), (14, false), (19, true), (15, false), (18, false)]
theorem step369 (p : Nat → Bool) (h : Constraints p) : clause p c369 = true :=
  Snake9.LocalRup.prove_clause [c36, c20, c37] c369 (by decide) p (sat_cons (step36 p h) (sat_cons (step20 p h) (sat_cons (step37 p h) (sat_nil p))))
def c370 : List Lit := [(229, false), (19, true), (35, true), (20, false)]
theorem step370 (p : Nat → Bool) (h : Constraints p) : clause p c370 = true :=
  Snake9.LocalRup.prove_clause [c328, c320, c366, c132, c133, c134, c128, c170, c120, c361, c119, c246, c247, c35, c45] c370 (by decide) p (sat_cons (step328 p h) (sat_cons (step320 p h) (sat_cons (step366 p h) (sat_cons (step132 p h) (sat_cons (step133 p h) (sat_cons (step134 p h) (sat_cons (step128 p h) (sat_cons (step170 p h) (sat_cons (step120 p h) (sat_cons (step361 p h) (sat_cons (step119 p h) (sat_cons (step246 p h) (sat_cons (step247 p h) (sat_cons (step35 p h) (sat_cons (step45 p h) (sat_nil p))))))))))))))))
def c371 : List Lit := [(14, false), (113, true), (117, true), (19, true), (15, false), (18, false), (34, false)]
theorem step371 (p : Nat → Bool) (h : Constraints p) : clause p c371 = true :=
  Snake9.LocalRup.prove_clause [c346, c366, c13, c369, c234, c235, c238, c244, c284, c281, c24, c16, c17, c46, c21, c254, c249, c259, c257, c250, c279, c247, c271, c44, c269] c371 (by decide) p (sat_cons (step346 p h) (sat_cons (step366 p h) (sat_cons (step13 p h) (sat_cons (step369 p h) (sat_cons (step234 p h) (sat_cons (step235 p h) (sat_cons (step238 p h) (sat_cons (step244 p h) (sat_cons (step284 p h) (sat_cons (step281 p h) (sat_cons (step24 p h) (sat_cons (step16 p h) (sat_cons (step17 p h) (sat_cons (step46 p h) (sat_cons (step21 p h) (sat_cons (step254 p h) (sat_cons (step249 p h) (sat_cons (step259 p h) (sat_cons (step257 p h) (sat_cons (step250 p h) (sat_cons (step279 p h) (sat_cons (step247 p h) (sat_cons (step271 p h) (sat_cons (step44 p h) (sat_cons (step269 p h) (sat_nil p))))))))))))))))))))))))))
def c372 : List Lit := [(1165, true), (34, false), (1176, true)]
theorem step372 (p : Nat → Bool) (h : Constraints p) : clause p c372 = true :=
  Snake9.LocalRup.prove_clause [c367, c338, c94, c368, c55, c226, c227, c33, c370, c117, c118, c116, c114, c115, c113, c371, c231, c241, c235, c233, c234, c36, c37, c25, c38, c23, c18, c125, c122, c40, c41, c43, c317] c372 (by decide) p (sat_cons (step367 p h) (sat_cons (step338 p h) (sat_cons (step94 p h) (sat_cons (step368 p h) (sat_cons (step55 p h) (sat_cons (step226 p h) (sat_cons (step227 p h) (sat_cons (step33 p h) (sat_cons (step370 p h) (sat_cons (step117 p h) (sat_cons (step118 p h) (sat_cons (step116 p h) (sat_cons (step114 p h) (sat_cons (step115 p h) (sat_cons (step113 p h) (sat_cons (step371 p h) (sat_cons (step231 p h) (sat_cons (step241 p h) (sat_cons (step235 p h) (sat_cons (step233 p h) (sat_cons (step234 p h) (sat_cons (step36 p h) (sat_cons (step37 p h) (sat_cons (step25 p h) (sat_cons (step38 p h) (sat_cons (step23 p h) (sat_cons (step18 p h) (sat_cons (step125 p h) (sat_cons (step122 p h) (sat_cons (step40 p h) (sat_cons (step41 p h) (sat_cons (step43 p h) (sat_cons (step317 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c373 : List Lit := [(31, true), (1192, false), (1224, true), (19, true), (35, true), (34, false)]
theorem step373 (p : Nat → Bool) (h : Constraints p) : clause p c373 = true :=
  Snake9.LocalRup.prove_clause [c332, c323, c52, c142, c143, c145, c147, c140, c165, c138, c159, c48, c158, c254, c157, c257, c156, c279, c348] c373 (by decide) p (sat_cons (step332 p h) (sat_cons (step323 p h) (sat_cons (step52 p h) (sat_cons (step142 p h) (sat_cons (step143 p h) (sat_cons (step145 p h) (sat_cons (step147 p h) (sat_cons (step140 p h) (sat_cons (step165 p h) (sat_cons (step138 p h) (sat_cons (step159 p h) (sat_cons (step48 p h) (sat_cons (step158 p h) (sat_cons (step254 p h) (sat_cons (step157 p h) (sat_cons (step257 p h) (sat_cons (step156 p h) (sat_cons (step279 p h) (sat_cons (step348 p h) (sat_nil p))))))))))))))))))))
def c374 : List Lit := [(17, false), (18, false), (117, true), (22, false), (1224, true), (19, true), (14, false), (35, true), (34, false)]
theorem step374 (p : Nat → Bool) (h : Constraints p) : clause p c374 = true :=
  Snake9.LocalRup.prove_clause [c281, c22, c249, c373, c46, c14, c254, c24, c259, c257, c250, c279, c247, c271, c44, c269] c374 (by decide) p (sat_cons (step281 p h) (sat_cons (step22 p h) (sat_cons (step249 p h) (sat_cons (step373 p h) (sat_cons (step46 p h) (sat_cons (step14 p h) (sat_cons (step254 p h) (sat_cons (step24 p h) (sat_cons (step259 p h) (sat_cons (step257 p h) (sat_cons (step250 p h) (sat_cons (step279 p h) (sat_cons (step247 p h) (sat_cons (step271 p h) (sat_cons (step44 p h) (sat_cons (step269 p h) (sat_nil p)))))))))))))))))
def c375 : List Lit := [(17, true), (1202, true), (22, false), (14, false), (20, false), (34, false)]
theorem step375 (p : Nat → Bool) (h : Constraints p) : clause p c375 = true :=
  Snake9.LocalRup.prove_clause [c367, c338, c333, c55, c30, c370, c118, c114, c113, c39, c15, c124, c125, c46, c129, c121, c254, c120, c42, c259, c119, c250, c35, c246, c247, c45] c375 (by decide) p (sat_cons (step367 p h) (sat_cons (step338 p h) (sat_cons (step333 p h) (sat_cons (step55 p h) (sat_cons (step30 p h) (sat_cons (step370 p h) (sat_cons (step118 p h) (sat_cons (step114 p h) (sat_cons (step113 p h) (sat_cons (step39 p h) (sat_cons (step15 p h) (sat_cons (step124 p h) (sat_cons (step125 p h) (sat_cons (step46 p h) (sat_cons (step129 p h) (sat_cons (step121 p h) (sat_cons (step254 p h) (sat_cons (step120 p h) (sat_cons (step42 p h) (sat_cons (step259 p h) (sat_cons (step119 p h) (sat_cons (step250 p h) (sat_cons (step35 p h) (sat_cons (step246 p h) (sat_cons (step247 p h) (sat_cons (step45 p h) (sat_nil p)))))))))))))))))))))))))))
def c376 : List Lit := [(34, false), (1176, true)]
theorem step376 (p : Nat → Bool) (h : Constraints p) : clause p c376 = true :=
  Snake9.LocalRup.prove_clause [c367, c346, c366, c242, c230, c368, c55, c372, c229, c232, c240, c241, c30, c244, c235, c370, c284, c234, c117, c281, c116, c115, c375, c20, c374, c228] c376 (by decide) p (sat_cons (step367 p h) (sat_cons (step346 p h) (sat_cons (step366 p h) (sat_cons (step242 p h) (sat_cons (step230 p h) (sat_cons (step368 p h) (sat_cons (step55 p h) (sat_cons (step372 p h) (sat_cons (step229 p h) (sat_cons (step232 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step30 p h) (sat_cons (step244 p h) (sat_cons (step235 p h) (sat_cons (step370 p h) (sat_cons (step284 p h) (sat_cons (step234 p h) (sat_cons (step117 p h) (sat_cons (step281 p h) (sat_cons (step116 p h) (sat_cons (step115 p h) (sat_cons (step375 p h) (sat_cons (step20 p h) (sat_cons (step374 p h) (sat_cons (step228 p h) (sat_nil p)))))))))))))))))))))))))))
def c377 : List Lit := [(24, true), (1224, true), (1197, false)]
theorem step377 (p : Nat → Bool) (h : Constraints p) : clause p c377 = true :=
  Snake9.LocalRup.prove_clause [c367, c281, c259, c249, c250, c257, c246, c279, c348, c355, c66, c70] c377 (by decide) p (sat_cons (step367 p h) (sat_cons (step281 p h) (sat_cons (step259 p h) (sat_cons (step249 p h) (sat_cons (step250 p h) (sat_cons (step257 p h) (sat_cons (step246 p h) (sat_cons (step279 p h) (sat_cons (step348 p h) (sat_cons (step355 p h) (sat_cons (step66 p h) (sat_cons (step70 p h) (sat_nil p)))))))))))))
def c378 : List Lit := [(24, false), (17, false), (14, false), (1176, true)]
theorem step378 (p : Nat → Bool) (h : Constraints p) : clause p c378 = true :=
  Snake9.LocalRup.prove_clause [c22, c21, c234, c227, c235, c229, c241] c378 (by decide) p (sat_cons (step22 p h) (sat_cons (step21 p h) (sat_cons (step234 p h) (sat_cons (step227 p h) (sat_cons (step235 p h) (sat_cons (step229 p h) (sat_cons (step241 p h) (sat_nil p))))))))
def c379 : List Lit := [(17, false), (14, false), (1176, true)]
theorem step379 (p : Nat → Bool) (h : Constraints p) : clause p c379 = true :=
  Snake9.LocalRup.prove_clause [c366, c346, c376, c251, c253, c378, c377, c284, c244, c238, c240, c235, c229, c234, c227, c20] c379 (by decide) p (sat_cons (step366 p h) (sat_cons (step346 p h) (sat_cons (step376 p h) (sat_cons (step251 p h) (sat_cons (step253 p h) (sat_cons (step378 p h) (sat_cons (step377 p h) (sat_cons (step284 p h) (sat_cons (step244 p h) (sat_cons (step238 p h) (sat_cons (step240 p h) (sat_cons (step235 p h) (sat_cons (step229 p h) (sat_cons (step234 p h) (sat_cons (step227 p h) (sat_cons (step20 p h) (sat_nil p)))))))))))))))))
def c380 : List Lit := [(237, false), (17, true), (14, false), (19, true), (20, false), (34, true)]
theorem step380 (p : Nat → Bool) (h : Constraints p) : clause p c380 = true :=
  Snake9.LocalRup.prove_clause [c333, c328, c320, c366, c95, c367, c126, c129, c130, c133, c120, c134, c118, c119, c170, c114, c361, c113, c246, c247, c15, c45, c47, c35, c54] c380 (by decide) p (sat_cons (step333 p h) (sat_cons (step328 p h) (sat_cons (step320 p h) (sat_cons (step366 p h) (sat_cons (step95 p h) (sat_cons (step367 p h) (sat_cons (step126 p h) (sat_cons (step129 p h) (sat_cons (step130 p h) (sat_cons (step133 p h) (sat_cons (step120 p h) (sat_cons (step134 p h) (sat_cons (step118 p h) (sat_cons (step119 p h) (sat_cons (step170 p h) (sat_cons (step114 p h) (sat_cons (step361 p h) (sat_cons (step113 p h) (sat_cons (step246 p h) (sat_cons (step247 p h) (sat_cons (step15 p h) (sat_cons (step45 p h) (sat_cons (step47 p h) (sat_cons (step35 p h) (sat_cons (step54 p h) (sat_nil p))))))))))))))))))))))))))
def c381 : List Lit := [(14, false), (19, true), (20, false), (1176, true)]
theorem step381 (p : Nat → Bool) (h : Constraints p) : clause p c381 = true :=
  Snake9.LocalRup.prove_clause [c366, c346, c376, c251, c253, c379, c380, c123, c124, c121, c39, c42, c234, c377, c235, c284, c238, c244] c381 (by decide) p (sat_cons (step366 p h) (sat_cons (step346 p h) (sat_cons (step376 p h) (sat_cons (step251 p h) (sat_cons (step253 p h) (sat_cons (step379 p h) (sat_cons (step380 p h) (sat_cons (step123 p h) (sat_cons (step124 p h) (sat_cons (step121 p h) (sat_cons (step39 p h) (sat_cons (step42 p h) (sat_cons (step234 p h) (sat_cons (step377 p h) (sat_cons (step235 p h) (sat_cons (step284 p h) (sat_cons (step238 p h) (sat_cons (step244 p h) (sat_nil p)))))))))))))))))))
end B112E149
