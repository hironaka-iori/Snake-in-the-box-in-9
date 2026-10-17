import B112E242Inputs
namespace B112E242
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c192 : List Lit := [(40, false)]
theorem step192 (p : Nat → Bool) (h : Constraints p) : clause p c192 = true :=
  Snake9.LocalRup.prove_clause [c49, c9] c192 (by decide) p (sat_cons (step49 p h) (sat_cons (step9 p h) (sat_nil p)))
def c193 : List Lit := [(45, false)]
theorem step193 (p : Nat → Bool) (h : Constraints p) : clause p c193 = true :=
  Snake9.LocalRup.prove_clause [c52, c14] c193 (by decide) p (sat_cons (step52 p h) (sat_cons (step14 p h) (sat_nil p)))
def c194 : List Lit := [(73, false)]
theorem step194 (p : Nat → Bool) (h : Constraints p) : clause p c194 = true :=
  Snake9.LocalRup.prove_clause [c57, c30] c194 (by decide) p (sat_cons (step57 p h) (sat_cons (step30 p h) (sat_nil p)))
def c195 : List Lit := [(77, false)]
theorem step195 (p : Nat → Bool) (h : Constraints p) : clause p c195 = true :=
  Snake9.LocalRup.prove_clause [c58, c31] c195 (by decide) p (sat_cons (step58 p h) (sat_cons (step31 p h) (sat_nil p)))
def c196 : List Lit := [(78, false)]
theorem step196 (p : Nat → Bool) (h : Constraints p) : clause p c196 = true :=
  Snake9.LocalRup.prove_clause [c59, c32] c196 (by decide) p (sat_cons (step59 p h) (sat_cons (step32 p h) (sat_nil p)))
def c197 : List Lit := [(87, false)]
theorem step197 (p : Nat → Bool) (h : Constraints p) : clause p c197 = true :=
  Snake9.LocalRup.prove_clause [c60, c33] c197 (by decide) p (sat_cons (step60 p h) (sat_cons (step33 p h) (sat_nil p)))
def c198 : List Lit := [(410, false)]
theorem step198 (p : Nat → Bool) (h : Constraints p) : clause p c198 = true :=
  Snake9.LocalRup.prove_clause [c73, c72] c198 (by decide) p (sat_cons (step73 p h) (sat_cons (step72 p h) (sat_nil p)))
def c199 : List Lit := [(408, false)]
theorem step199 (p : Nat → Bool) (h : Constraints p) : clause p c199 = true :=
  Snake9.LocalRup.prove_clause [c198, c71] c199 (by decide) p (sat_cons (step198 p h) (sat_cons (step71 p h) (sat_nil p)))
def c200 : List Lit := [(406, false)]
theorem step200 (p : Nat → Bool) (h : Constraints p) : clause p c200 = true :=
  Snake9.LocalRup.prove_clause [c199, c70] c200 (by decide) p (sat_cons (step199 p h) (sat_cons (step70 p h) (sat_nil p)))
def c201 : List Lit := [(404, false)]
theorem step201 (p : Nat → Bool) (h : Constraints p) : clause p c201 = true :=
  Snake9.LocalRup.prove_clause [c200, c69] c201 (by decide) p (sat_cons (step200 p h) (sat_cons (step69 p h) (sat_nil p)))
def c202 : List Lit := [(402, false)]
theorem step202 (p : Nat → Bool) (h : Constraints p) : clause p c202 = true :=
  Snake9.LocalRup.prove_clause [c201, c68] c202 (by decide) p (sat_cons (step201 p h) (sat_cons (step68 p h) (sat_nil p)))
def c203 : List Lit := [(1244, true)]
theorem step203 (p : Nat → Bool) (h : Constraints p) : clause p c203 = true :=
  Snake9.LocalRup.prove_clause [c192, c99] c203 (by decide) p (sat_cons (step192 p h) (sat_cons (step99 p h) (sat_nil p)))
def c204 : List Lit := [(1246, true)]
theorem step204 (p : Nat → Bool) (h : Constraints p) : clause p c204 = true :=
  Snake9.LocalRup.prove_clause [c203, c100] c204 (by decide) p (sat_cons (step203 p h) (sat_cons (step100 p h) (sat_nil p)))
def c205 : List Lit := [(1239, false), (1251, true)]
theorem step205 (p : Nat → Bool) (h : Constraints p) : clause p c205 = true :=
  Snake9.LocalRup.prove_clause [c204, c101] c205 (by decide) p (sat_cons (step204 p h) (sat_cons (step101 p h) (sat_nil p)))
def c206 : List Lit := [(1262, true)]
theorem step206 (p : Nat → Bool) (h : Constraints p) : clause p c206 = true :=
  Snake9.LocalRup.prove_clause [c193, c107] c206 (by decide) p (sat_cons (step193 p h) (sat_cons (step107 p h) (sat_nil p)))
def c207 : List Lit := [(47, true), (1263, true)]
theorem step207 (p : Nat → Bool) (h : Constraints p) : clause p c207 = true :=
  Snake9.LocalRup.prove_clause [c193, c108] c207 (by decide) p (sat_cons (step193 p h) (sat_cons (step108 p h) (sat_nil p)))
def c208 : List Lit := [(1264, false), (1267, true)]
theorem step208 (p : Nat → Bool) (h : Constraints p) : clause p c208 = true :=
  Snake9.LocalRup.prove_clause [c206, c111] c208 (by decide) p (sat_cons (step206 p h) (sat_cons (step111 p h) (sat_nil p)))
def c209 : List Lit := [(1331, true)]
theorem step209 (p : Nat → Bool) (h : Constraints p) : clause p c209 = true :=
  Snake9.LocalRup.prove_clause [c194, c139] c209 (by decide) p (sat_cons (step194 p h) (sat_cons (step139 p h) (sat_nil p)))
def c210 : List Lit := [(72, true), (1332, true)]
theorem step210 (p : Nat → Bool) (h : Constraints p) : clause p c210 = true :=
  Snake9.LocalRup.prove_clause [c194, c140] c210 (by decide) p (sat_cons (step194 p h) (sat_cons (step140 p h) (sat_nil p)))
def c211 : List Lit := [(1333, true)]
theorem step211 (p : Nat → Bool) (h : Constraints p) : clause p c211 = true :=
  Snake9.LocalRup.prove_clause [c195, c141] c211 (by decide) p (sat_cons (step195 p h) (sat_cons (step141 p h) (sat_nil p)))
def c212 : List Lit := [(1336, true)]
theorem step212 (p : Nat → Bool) (h : Constraints p) : clause p c212 = true :=
  Snake9.LocalRup.prove_clause [c209, c211, c142] c212 (by decide) p (sat_cons (step209 p h) (sat_cons (step211 p h) (sat_cons (step142 p h) (sat_nil p))))
def c213 : List Lit := [(1332, false), (1337, true)]
theorem step213 (p : Nat → Bool) (h : Constraints p) : clause p c213 = true :=
  Snake9.LocalRup.prove_clause [c211, c143] c213 (by decide) p (sat_cons (step211 p h) (sat_cons (step143 p h) (sat_nil p)))
def c214 : List Lit := [(1340, true)]
theorem step214 (p : Nat → Bool) (h : Constraints p) : clause p c214 = true :=
  Snake9.LocalRup.prove_clause [c212, c144] c214 (by decide) p (sat_cons (step212 p h) (sat_cons (step144 p h) (sat_nil p)))
def c215 : List Lit := [(1328, false), (1341, true)]
theorem step215 (p : Nat → Bool) (h : Constraints p) : clause p c215 = true :=
  Snake9.LocalRup.prove_clause [c212, c146] c215 (by decide) p (sat_cons (step212 p h) (sat_cons (step146 p h) (sat_nil p)))
def c216 : List Lit := [(1320, false), (1349, true)]
theorem step216 (p : Nat → Bool) (h : Constraints p) : clause p c216 = true :=
  Snake9.LocalRup.prove_clause [c214, c148] c216 (by decide) p (sat_cons (step214 p h) (sat_cons (step148 p h) (sat_nil p)))
def c217 : List Lit := [(1321, false), (1350, true)]
theorem step217 (p : Nat → Bool) (h : Constraints p) : clause p c217 = true :=
  Snake9.LocalRup.prove_clause [c214, c150] c217 (by decide) p (sat_cons (step214 p h) (sat_cons (step150 p h) (sat_nil p)))
def c218 : List Lit := [(1362, true)]
theorem step218 (p : Nat → Bool) (h : Constraints p) : clause p c218 = true :=
  Snake9.LocalRup.prove_clause [c196, c151] c218 (by decide) p (sat_cons (step196 p h) (sat_cons (step151 p h) (sat_nil p)))
def c219 : List Lit := [(1365, true)]
theorem step219 (p : Nat → Bool) (h : Constraints p) : clause p c219 = true :=
  Snake9.LocalRup.prove_clause [c197, c152] c219 (by decide) p (sat_cons (step197 p h) (sat_cons (step152 p h) (sat_nil p)))
def c220 : List Lit := [(1369, true)]
theorem step220 (p : Nat → Bool) (h : Constraints p) : clause p c220 = true :=
  Snake9.LocalRup.prove_clause [c219, c154] c220 (by decide) p (sat_cons (step219 p h) (sat_cons (step154 p h) (sat_nil p)))
def c221 : List Lit := [(1367, false), (1370, true)]
theorem step221 (p : Nat → Bool) (h : Constraints p) : clause p c221 = true :=
  Snake9.LocalRup.prove_clause [c219, c155] c221 (by decide) p (sat_cons (step219 p h) (sat_cons (step155 p h) (sat_nil p)))
def c222 : List Lit := [(1374, true)]
theorem step222 (p : Nat → Bool) (h : Constraints p) : clause p c222 = true :=
  Snake9.LocalRup.prove_clause [c218, c220, c156] c222 (by decide) p (sat_cons (step218 p h) (sat_cons (step220 p h) (sat_cons (step156 p h) (sat_nil p))))
def c223 : List Lit := [(1370, false), (1375, true)]
theorem step223 (p : Nat → Bool) (h : Constraints p) : clause p c223 = true :=
  Snake9.LocalRup.prove_clause [c218, c157] c223 (by decide) p (sat_cons (step218 p h) (sat_cons (step157 p h) (sat_nil p)))
def c224 : List Lit := [(1393, false), (1402, true)]
theorem step224 (p : Nat → Bool) (h : Constraints p) : clause p c224 = true :=
  Snake9.LocalRup.prove_clause [c222, c179] c224 (by decide) p (sat_cons (step222 p h) (sat_cons (step179 p h) (sat_nil p)))
def c225 : List Lit := [(1394, false), (1403, true)]
theorem step225 (p : Nat → Bool) (h : Constraints p) : clause p c225 = true :=
  Snake9.LocalRup.prove_clause [c222, c180] c225 (by decide) p (sat_cons (step222 p h) (sat_cons (step180 p h) (sat_nil p)))
def c226 : List Lit := [(1395, false), (1404, true)]
theorem step226 (p : Nat → Bool) (h : Constraints p) : clause p c226 = true :=
  Snake9.LocalRup.prove_clause [c222, c181] c226 (by decide) p (sat_cons (step222 p h) (sat_cons (step181 p h) (sat_nil p)))
def c227 : List Lit := [(1239, true)]
theorem step227 (p : Nat → Bool) (h : Constraints p) : clause p c227 = true :=
  Snake9.LocalRup.prove_clause [c48, c97, c98, c95, c96, c7, c8] c227 (by decide) p (sat_cons (step48 p h) (sat_cons (step97 p h) (sat_cons (step98 p h) (sat_cons (step95 p h) (sat_cons (step96 p h) (sat_cons (step7 p h) (sat_cons (step8 p h) (sat_nil p))))))))
def c228 : List Lit := [(1251, true)]
theorem step228 (p : Nat → Bool) (h : Constraints p) : clause p c228 = true :=
  Snake9.LocalRup.prove_clause [c227, c205] c228 (by decide) p (sat_cons (step227 p h) (sat_cons (step205 p h) (sat_nil p)))
def c229 : List Lit := [(1313, false), (1320, true)]
theorem step229 (p : Nat → Bool) (h : Constraints p) : clause p c229 = true :=
  Snake9.LocalRup.prove_clause [c55, c26, c132, c130, c131, c134, c128, c126, c124, c22, c24] c229 (by decide) p (sat_cons (step55 p h) (sat_cons (step26 p h) (sat_cons (step132 p h) (sat_cons (step130 p h) (sat_cons (step131 p h) (sat_cons (step134 p h) (sat_cons (step128 p h) (sat_cons (step126 p h) (sat_cons (step124 p h) (sat_cons (step22 p h) (sat_cons (step24 p h) (sat_nil p))))))))))))
def c230 : List Lit := [(1306, true)]
theorem step230 (p : Nat → Bool) (h : Constraints p) : clause p c230 = true :=
  Snake9.LocalRup.prove_clause [c55, c26, c124, c125, c22, c23] c230 (by decide) p (sat_cons (step55 p h) (sat_cons (step26 p h) (sat_cons (step124 p h) (sat_cons (step125 p h) (sat_cons (step22 p h) (sat_cons (step23 p h) (sat_nil p)))))))
def c231 : List Lit := [(1308, true)]
theorem step231 (p : Nat → Bool) (h : Constraints p) : clause p c231 = true :=
  Snake9.LocalRup.prove_clause [c230, c126] c231 (by decide) p (sat_cons (step230 p h) (sat_cons (step126 p h) (sat_nil p)))
def c232 : List Lit := [(1319, true)]
theorem step232 (p : Nat → Bool) (h : Constraints p) : clause p c232 = true :=
  Snake9.LocalRup.prove_clause [c231, c133] c232 (by decide) p (sat_cons (step231 p h) (sat_cons (step133 p h) (sat_nil p)))
def c233 : List Lit := [(1349, true)]
theorem step233 (p : Nat → Bool) (h : Constraints p) : clause p c233 = true :=
  Snake9.LocalRup.prove_clause [c56, c232, c216, c229, c129, c28, c147, c145, c215, c213, c138, c210, c137, c29] c233 (by decide) p (sat_cons (step56 p h) (sat_cons (step232 p h) (sat_cons (step216 p h) (sat_cons (step229 p h) (sat_cons (step129 p h) (sat_cons (step28 p h) (sat_cons (step147 p h) (sat_cons (step145 p h) (sat_cons (step215 p h) (sat_cons (step213 p h) (sat_cons (step138 p h) (sat_cons (step210 p h) (sat_cons (step137 p h) (sat_cons (step29 p h) (sat_nil p)))))))))))))))
def c234 : List Lit := [(1217, true)]
theorem step234 (p : Nat → Bool) (h : Constraints p) : clause p c234 = true :=
  Snake9.LocalRup.prove_clause [c47, c89, c90, c88, c83, c86, c87, c80, c6, c5] c234 (by decide) p (sat_cons (step47 p h) (sat_cons (step89 p h) (sat_cons (step90 p h) (sat_cons (step88 p h) (sat_cons (step83 p h) (sat_cons (step86 p h) (sat_cons (step87 p h) (sat_cons (step80 p h) (sat_cons (step6 p h) (sat_cons (step5 p h) (sat_nil p)))))))))))
def c235 : List Lit := [(1198, true)]
theorem step235 (p : Nat → Bool) (h : Constraints p) : clause p c235 = true :=
  Snake9.LocalRup.prove_clause [c44, c78, c79, c77, c74, c75, c76, c1, c2] c235 (by decide) p (sat_cons (step44 p h) (sat_cons (step78 p h) (sat_cons (step79 p h) (sat_cons (step77 p h) (sat_cons (step74 p h) (sat_cons (step75 p h) (sat_cons (step76 p h) (sat_cons (step1 p h) (sat_cons (step2 p h) (sat_nil p))))))))))
def c236 : List Lit := [(1225, true)]
theorem step236 (p : Nat → Bool) (h : Constraints p) : clause p c236 = true :=
  Snake9.LocalRup.prove_clause [c235, c234, c93] c236 (by decide) p (sat_cons (step235 p h) (sat_cons (step234 p h) (sat_cons (step93 p h) (sat_nil p))))
def c237 : List Lit := [(1267, true)]
theorem step237 (p : Nat → Bool) (h : Constraints p) : clause p c237 = true :=
  Snake9.LocalRup.prove_clause [c53, c208, c112, c109, c110, c207, c20, c19] c237 (by decide) p (sat_cons (step53 p h) (sat_cons (step208 p h) (sat_cons (step112 p h) (sat_cons (step109 p h) (sat_cons (step110 p h) (sat_cons (step207 p h) (sat_cons (step20 p h) (sat_cons (step19 p h) (sat_nil p)))))))))
def c238 : List Lit := [(1271, true)]
theorem step238 (p : Nat → Bool) (h : Constraints p) : clause p c238 = true :=
  Snake9.LocalRup.prove_clause [c237, c113] c238 (by decide) p (sat_cons (step237 p h) (sat_cons (step113 p h) (sat_nil p)))
def c239 : List Lit := [(1280, true)]
theorem step239 (p : Nat → Bool) (h : Constraints p) : clause p c239 = true :=
  Snake9.LocalRup.prove_clause [c238, c228, c116] c239 (by decide) p (sat_cons (step238 p h) (sat_cons (step228 p h) (sat_cons (step116 p h) (sat_nil p))))
def c240 : List Lit := [(1296, true)]
theorem step240 (p : Nat → Bool) (h : Constraints p) : clause p c240 = true :=
  Snake9.LocalRup.prove_clause [c239, c236, c119] c240 (by decide) p (sat_cons (step239 p h) (sat_cons (step236 p h) (sat_cons (step119 p h) (sat_nil p))))
def c241 : List Lit := [(1422, false)]
theorem step241 (p : Nat → Bool) (h : Constraints p) : clause p c241 = true :=
  Snake9.LocalRup.prove_clause [c240, c190, c187] c241 (by decide) p (sat_cons (step240 p h) (sat_cons (step190 p h) (sat_cons (step187 p h) (sat_nil p))))
def c242 : List Lit := [(1404, false)]
theorem step242 (p : Nat → Bool) (h : Constraints p) : clause p c242 = true :=
  Snake9.LocalRup.prove_clause [c241, c233, c185] c242 (by decide) p (sat_cons (step241 p h) (sat_cons (step233 p h) (sat_cons (step185 p h) (sat_nil p))))
def c243 : List Lit := [(1395, false)]
theorem step243 (p : Nat → Bool) (h : Constraints p) : clause p c243 = true :=
  Snake9.LocalRup.prove_clause [c242, c226] c243 (by decide) p (sat_cons (step242 p h) (sat_cons (step226 p h) (sat_nil p)))
def c244 : List Lit := [(1391, false)]
theorem step244 (p : Nat → Bool) (h : Constraints p) : clause p c244 = true :=
  Snake9.LocalRup.prove_clause [c243, c176] c244 (by decide) p (sat_cons (step243 p h) (sat_cons (step176 p h) (sat_nil p)))
def c245 : List Lit := [(100, true), (103, true)]
theorem step245 (p : Nat → Bool) (h : Constraints p) : clause p c245 = true :=
  Snake9.LocalRup.prove_clause [c244, c63, c165, c173, c162, c164, c172, c167, c39, c40, c191] c245 (by decide) p (sat_cons (step244 p h) (sat_cons (step63 p h) (sat_cons (step165 p h) (sat_cons (step173 p h) (sat_cons (step162 p h) (sat_cons (step164 p h) (sat_cons (step172 p h) (sat_cons (step167 p h) (sat_cons (step39 p h) (sat_cons (step40 p h) (sat_cons (step191 p h) (sat_nil p))))))))))))
def c246 : List Lit := [(1390, true), (103, true)]
theorem step246 (p : Nat → Bool) (h : Constraints p) : clause p c246 = true :=
  Snake9.LocalRup.prove_clause [c63, c165, c169, c171, c167, c163, c39, c40, c191] c246 (by decide) p (sat_cons (step63 p h) (sat_cons (step165 p h) (sat_cons (step169 p h) (sat_cons (step171 p h) (sat_cons (step167 p h) (sat_cons (step163 p h) (sat_cons (step39 p h) (sat_cons (step40 p h) (sat_cons (step191 p h) (sat_nil p))))))))))
def c247 : List Lit := [(1350, true), (1309, false)]
theorem step247 (p : Nat → Bool) (h : Constraints p) : clause p c247 = true :=
  Snake9.LocalRup.prove_clause [c56, c135, c217, c149, c136, c145, c215, c130, c213, c138, c129, c210, c137, c28, c29] c247 (by decide) p (sat_cons (step56 p h) (sat_cons (step135 p h) (sat_cons (step217 p h) (sat_cons (step149 p h) (sat_cons (step136 p h) (sat_cons (step145 p h) (sat_cons (step215 p h) (sat_cons (step130 p h) (sat_cons (step213 p h) (sat_cons (step138 p h) (sat_cons (step129 p h) (sat_cons (step210 p h) (sat_cons (step137 p h) (sat_cons (step28 p h) (sat_cons (step29 p h) (sat_nil p))))))))))))))))
def c248 : List Lit := [(46, true), (60, true)]
theorem step248 (p : Nat → Bool) (h : Constraints p) : clause p c248 = true :=
  Snake9.LocalRup.prove_clause [c64, c233, c190, c236, c228, c237, c51, c50, c10, c12, c105, c102, c114, c106, c117, c115, c120, c118, c188, c121, c184, c189, c225, c183, c175, c224, c246, c177, c42, c160, c161, c35, c158] c248 (by decide) p (sat_cons (step64 p h) (sat_cons (step233 p h) (sat_cons (step190 p h) (sat_cons (step236 p h) (sat_cons (step228 p h) (sat_cons (step237 p h) (sat_cons (step51 p h) (sat_cons (step50 p h) (sat_cons (step10 p h) (sat_cons (step12 p h) (sat_cons (step105 p h) (sat_cons (step102 p h) (sat_cons (step114 p h) (sat_cons (step106 p h) (sat_cons (step117 p h) (sat_cons (step115 p h) (sat_cons (step120 p h) (sat_cons (step118 p h) (sat_cons (step188 p h) (sat_cons (step121 p h) (sat_cons (step184 p h) (sat_cons (step189 p h) (sat_cons (step225 p h) (sat_cons (step183 p h) (sat_cons (step175 p h) (sat_cons (step224 p h) (sat_cons (step246 p h) (sat_cons (step177 p h) (sat_cons (step42 p h) (sat_cons (step160 p h) (sat_cons (step161 p h) (sat_cons (step35 p h) (sat_cons (step158 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c249 : List Lit := [(1389, true)]
theorem step249 (p : Nat → Bool) (h : Constraints p) : clause p c249 = true :=
  Snake9.LocalRup.prove_clause [c63, c168, c170, c166, c163, c39, c40, c191] c249 (by decide) p (sat_cons (step63 p h) (sat_cons (step168 p h) (sat_cons (step170 p h) (sat_cons (step166 p h) (sat_cons (step163 p h) (sat_cons (step39 p h) (sat_cons (step40 p h) (sat_cons (step191 p h) (sat_nil p)))))))))
def c250 : List Lit := [(1393, true)]
theorem step250 (p : Nat → Bool) (h : Constraints p) : clause p c250 = true :=
  Snake9.LocalRup.prove_clause [c249, c174] c250 (by decide) p (sat_cons (step249 p h) (sat_cons (step174 p h) (sat_nil p)))
def c251 : List Lit := [(1402, true)]
theorem step251 (p : Nat → Bool) (h : Constraints p) : clause p c251 = true :=
  Snake9.LocalRup.prove_clause [c250, c224] c251 (by decide) p (sat_cons (step250 p h) (sat_cons (step224 p h) (sat_nil p)))
def c252 : List Lit := [(1420, true)]
theorem step252 (p : Nat → Bool) (h : Constraints p) : clause p c252 = true :=
  Snake9.LocalRup.prove_clause [c251, c233, c183] c252 (by decide) p (sat_cons (step251 p h) (sat_cons (step233 p h) (sat_cons (step183 p h) (sat_nil p))))
def c253 : List Lit := [(1298, false)]
theorem step253 (p : Nat → Bool) (h : Constraints p) : clause p c253 = true :=
  Snake9.LocalRup.prove_clause [c252, c190, c189] c253 (by decide) p (sat_cons (step252 p h) (sat_cons (step190 p h) (sat_cons (step189 p h) (sat_nil p))))
def c254 : List Lit := [(1282, false)]
theorem step254 (p : Nat → Bool) (h : Constraints p) : clause p c254 = true :=
  Snake9.LocalRup.prove_clause [c253, c236, c121] c254 (by decide) p (sat_cons (step253 p h) (sat_cons (step236 p h) (sat_cons (step121 p h) (sat_nil p))))
def c255 : List Lit := [(1273, false)]
theorem step255 (p : Nat → Bool) (h : Constraints p) : clause p c255 = true :=
  Snake9.LocalRup.prove_clause [c254, c228, c118] c255 (by decide) p (sat_cons (step254 p h) (sat_cons (step228 p h) (sat_cons (step118 p h) (sat_nil p))))
end B112E242
