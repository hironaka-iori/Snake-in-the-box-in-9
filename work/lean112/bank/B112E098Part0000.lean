import B112E098Inputs
namespace B112E098
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c223 : List Lit := [(49, true)]
theorem step223 (p : Nat → Bool) (h : Constraints p) : clause p c223 = true :=
  Snake9.LocalRup.prove_clause [c25, c24] c223 (by decide) p (sat_cons (step25 p h) (sat_cons (step24 p h) (sat_nil p)))
def c224 : List Lit := [(50, false), (54, false)]
theorem step224 (p : Nat → Bool) (h : Constraints p) : clause p c224 = true :=
  Snake9.LocalRup.prove_clause [c223, c25, c26] c224 (by decide) p (sat_cons (step223 p h) (sat_cons (step25 p h) (sat_cons (step26 p h) (sat_nil p))))
def c225 : List Lit := [(6, false)]
theorem step225 (p : Nat → Bool) (h : Constraints p) : clause p c225 = true :=
  Snake9.LocalRup.prove_clause [c58, c3] c225 (by decide) p (sat_cons (step58 p h) (sat_cons (step3 p h) (sat_nil p)))
def c226 : List Lit := [(1169, true)]
theorem step226 (p : Nat → Bool) (h : Constraints p) : clause p c226 = true :=
  Snake9.LocalRup.prove_clause [c225, c77] c226 (by decide) p (sat_cons (step225 p h) (sat_cons (step77 p h) (sat_nil p)))
def c227 : List Lit := [(1171, true)]
theorem step227 (p : Nat → Bool) (h : Constraints p) : clause p c227 = true :=
  Snake9.LocalRup.prove_clause [c226, c78] c227 (by decide) p (sat_cons (step226 p h) (sat_cons (step78 p h) (sat_nil p)))
def c228 : List Lit := [(3, true), (1172, true)]
theorem step228 (p : Nat → Bool) (h : Constraints p) : clause p c228 = true :=
  Snake9.LocalRup.prove_clause [c226, c79] c228 (by decide) p (sat_cons (step226 p h) (sat_cons (step79 p h) (sat_nil p)))
def c229 : List Lit := [(1176, false), (1180, true)]
theorem step229 (p : Nat → Bool) (h : Constraints p) : clause p c229 = true :=
  Snake9.LocalRup.prove_clause [c227, c82] c229 (by decide) p (sat_cons (step227 p h) (sat_cons (step82 p h) (sat_nil p)))
def c230 : List Lit := [(1180, true)]
theorem step230 (p : Nat → Bool) (h : Constraints p) : clause p c230 = true :=
  Snake9.LocalRup.prove_clause [c57, c229, c83, c81, c228, c80, c1, c2, c221] c230 (by decide) p (sat_cons (step57 p h) (sat_cons (step229 p h) (sat_cons (step83 p h) (sat_cons (step81 p h) (sat_cons (step228 p h) (sat_cons (step80 p h) (sat_cons (step1 p h) (sat_cons (step2 p h) (sat_cons (step221 p h) (sat_nil p))))))))))
def c231 : List Lit := [(1202, true)]
theorem step231 (p : Nat → Bool) (h : Constraints p) : clause p c231 = true :=
  Snake9.LocalRup.prove_clause [c230, c93] c231 (by decide) p (sat_cons (step230 p h) (sat_cons (step93 p h) (sat_nil p)))
def c232 : List Lit := [(1272, true)]
theorem step232 (p : Nat → Bool) (h : Constraints p) : clause p c232 = true :=
  Snake9.LocalRup.prove_clause [c142, c143, c141, c224] c232 (by decide) p (sat_cons (step142 p h) (sat_cons (step143 p h) (sat_cons (step141 p h) (sat_cons (step224 p h) (sat_nil p)))))
def c233 : List Lit := [(1280, true)]
theorem step233 (p : Nat → Bool) (h : Constraints p) : clause p c233 = true :=
  Snake9.LocalRup.prove_clause [c232, c144] c233 (by decide) p (sat_cons (step232 p h) (sat_cons (step144 p h) (sat_nil p)))
def c234 : List Lit := [(1295, true)]
theorem step234 (p : Nat → Bool) (h : Constraints p) : clause p c234 = true :=
  Snake9.LocalRup.prove_clause [c70, c151, c153, c148, c149, c147, c33, c29] c234 (by decide) p (sat_cons (step70 p h) (sat_cons (step151 p h) (sat_cons (step153 p h) (sat_cons (step148 p h) (sat_cons (step149 p h) (sat_cons (step147 p h) (sat_cons (step33 p h) (sat_cons (step29 p h) (sat_nil p)))))))))
def c235 : List Lit := [(1299, true)]
theorem step235 (p : Nat → Bool) (h : Constraints p) : clause p c235 = true :=
  Snake9.LocalRup.prove_clause [c234, c155] c235 (by decide) p (sat_cons (step234 p h) (sat_cons (step155 p h) (sat_nil p)))
def c236 : List Lit := [(1307, true)]
theorem step236 (p : Nat → Bool) (h : Constraints p) : clause p c236 = true :=
  Snake9.LocalRup.prove_clause [c235, c233, c159] c236 (by decide) p (sat_cons (step235 p h) (sat_cons (step233 p h) (sat_cons (step159 p h) (sat_nil p))))
def c237 : List Lit := [(1327, true)]
theorem step237 (p : Nat → Bool) (h : Constraints p) : clause p c237 = true :=
  Snake9.LocalRup.prove_clause [c73, c174, c176, c171, c165, c167, c169, c170, c163, c35, c46, c45] c237 (by decide) p (sat_cons (step73 p h) (sat_cons (step174 p h) (sat_cons (step176 p h) (sat_cons (step171 p h) (sat_cons (step165 p h) (sat_cons (step167 p h) (sat_cons (step169 p h) (sat_cons (step170 p h) (sat_cons (step163 p h) (sat_cons (step35 p h) (sat_cons (step46 p h) (sat_cons (step45 p h) (sat_nil p)))))))))))))
def c238 : List Lit := [(1293, true), (82, false)]
theorem step238 (p : Nat → Bool) (h : Constraints p) : clause p c238 = true :=
  Snake9.LocalRup.prove_clause [c70, c148, c149, c33, c32] c238 (by decide) p (sat_cons (step70 p h) (sat_cons (step148 p h) (sat_cons (step149 p h) (sat_cons (step33 p h) (sat_cons (step32 p h) (sat_nil p))))))
def c239 : List Lit := [(72, false), (70, false), (82, false), (1294, true)]
theorem step239 (p : Nat → Bool) (h : Constraints p) : clause p c239 = true :=
  Snake9.LocalRup.prove_clause [c30, c31, c150] c239 (by decide) p (sat_cons (step30 p h) (sat_cons (step31 p h) (sat_cons (step150 p h) (sat_nil p))))
def c240 : List Lit := [(1324, true), (1296, true)]
theorem step240 (p : Nat → Bool) (h : Constraints p) : clause p c240 = true :=
  Snake9.LocalRup.prove_clause [c70, c69, c152, c171, c172, c170, c238, c154, c147, c239, c33, c150, c28, c39] c240 (by decide) p (sat_cons (step70 p h) (sat_cons (step69 p h) (sat_cons (step152 p h) (sat_cons (step171 p h) (sat_cons (step172 p h) (sat_cons (step170 p h) (sat_cons (step238 p h) (sat_cons (step154 p h) (sat_cons (step147 p h) (sat_cons (step239 p h) (sat_cons (step33 p h) (sat_cons (step150 p h) (sat_cons (step28 p h) (sat_cons (step39 p h) (sat_nil p)))))))))))))))
def c241 : List Lit := [(82, false), (79, false), (1296, true)]
theorem step241 (p : Nat → Bool) (h : Constraints p) : clause p c241 = true :=
  Snake9.LocalRup.prove_clause [c70, c71, c152, c238, c154, c147, c239, c36, c33, c41, c150, c38] c241 (by decide) p (sat_cons (step70 p h) (sat_cons (step71 p h) (sat_cons (step152 p h) (sat_cons (step238 p h) (sat_cons (step154 p h) (sat_cons (step147 p h) (sat_cons (step239 p h) (sat_cons (step36 p h) (sat_cons (step33 p h) (sat_cons (step41 p h) (sat_cons (step150 p h) (sat_cons (step38 p h) (sat_nil p)))))))))))))
def c242 : List Lit := [(1328, true), (1296, true)]
theorem step242 (p : Nat → Bool) (h : Constraints p) : clause p c242 = true :=
  Snake9.LocalRup.prove_clause [c73, c240, c175, c177, c165, c167, c162, c163, c241, c173, c169, c170, c35, c46, c45] c242 (by decide) p (sat_cons (step73 p h) (sat_cons (step240 p h) (sat_cons (step175 p h) (sat_cons (step177 p h) (sat_cons (step165 p h) (sat_cons (step167 p h) (sat_cons (step162 p h) (sat_cons (step163 p h) (sat_cons (step241 p h) (sat_cons (step173 p h) (sat_cons (step169 p h) (sat_cons (step170 p h) (sat_cons (step35 p h) (sat_cons (step46 p h) (sat_cons (step45 p h) (sat_nil p))))))))))))))))
def c243 : List Lit := [(1214, false), (1249, true)]
theorem step243 (p : Nat → Bool) (h : Constraints p) : clause p c243 = true :=
  Snake9.LocalRup.prove_clause [c63, c132, c110, c111, c130, c105, c123, c103, c104, c121, c18, c16, c118] c243 (by decide) p (sat_cons (step63 p h) (sat_cons (step132 p h) (sat_cons (step110 p h) (sat_cons (step111 p h) (sat_cons (step130 p h) (sat_cons (step105 p h) (sat_cons (step123 p h) (sat_cons (step103 p h) (sat_cons (step104 p h) (sat_cons (step121 p h) (sat_cons (step18 p h) (sat_cons (step16 p h) (sat_cons (step118 p h) (sat_nil p))))))))))))))
def c244 : List Lit := [(1195, true), (26, false)]
theorem step244 (p : Nat → Bool) (h : Constraints p) : clause p c244 = true :=
  Snake9.LocalRup.prove_clause [c59, c90, c91, c89, c85, c6, c4, c84] c244 (by decide) p (sat_cons (step59 p h) (sat_cons (step90 p h) (sat_cons (step91 p h) (sat_cons (step89 p h) (sat_cons (step85 p h) (sat_cons (step6 p h) (sat_cons (step4 p h) (sat_cons (step84 p h) (sat_nil p)))))))))
def c245 : List Lit := [(1248, true)]
theorem step245 (p : Nat → Bool) (h : Constraints p) : clause p c245 = true :=
  Snake9.LocalRup.prove_clause [c67, c66, c127, c129, c123, c108, c120, c121, c105, c119, c118, c104, c23, c21, c222] c245 (by decide) p (sat_cons (step67 p h) (sat_cons (step66 p h) (sat_cons (step127 p h) (sat_cons (step129 p h) (sat_cons (step123 p h) (sat_cons (step108 p h) (sat_cons (step120 p h) (sat_cons (step121 p h) (sat_cons (step105 p h) (sat_cons (step119 p h) (sat_cons (step118 p h) (sat_cons (step104 p h) (sat_cons (step23 p h) (sat_cons (step21 p h) (sat_cons (step222 p h) (sat_nil p))))))))))))))))
def c246 : List Lit := [(1242, true), (1217, true)]
theorem step246 (p : Nat → Bool) (h : Constraints p) : clause p c246 = true :=
  Snake9.LocalRup.prove_clause [c63, c64, c67, c104, c103, c18, c16, c118, c121, c124, c126, c122, c116, c119, c19, c23, c17] c246 (by decide) p (sat_cons (step63 p h) (sat_cons (step64 p h) (sat_cons (step67 p h) (sat_cons (step104 p h) (sat_cons (step103 p h) (sat_cons (step18 p h) (sat_cons (step16 p h) (sat_cons (step118 p h) (sat_cons (step121 p h) (sat_cons (step124 p h) (sat_cons (step126 p h) (sat_cons (step122 p h) (sat_cons (step116 p h) (sat_cons (step119 p h) (sat_cons (step19 p h) (sat_cons (step23 p h) (sat_cons (step17 p h) (sat_nil p))))))))))))))))))
def c247 : List Lit := [(1219, true), (1328, false), (17, false), (26, false)]
theorem step247 (p : Nat → Bool) (h : Constraints p) : clause p c247 = true :=
  Snake9.LocalRup.prove_clause [c230, c62, c75, c220, c236, c233, c234, c76, c244, c94, c105, c106, c15, c12, c50, c186, c191, c195, c204, c246, c128, c138, c218, c211, c214, c205, c160, c196, c157, c193, c192, c146, c188, c189, c145, c52, c56] c247 (by decide) p (sat_cons (step230 p h) (sat_cons (step62 p h) (sat_cons (step75 p h) (sat_cons (step220 p h) (sat_cons (step236 p h) (sat_cons (step233 p h) (sat_cons (step234 p h) (sat_cons (step76 p h) (sat_cons (step244 p h) (sat_cons (step94 p h) (sat_cons (step105 p h) (sat_cons (step106 p h) (sat_cons (step15 p h) (sat_cons (step12 p h) (sat_cons (step50 p h) (sat_cons (step186 p h) (sat_cons (step191 p h) (sat_cons (step195 p h) (sat_cons (step204 p h) (sat_cons (step246 p h) (sat_cons (step128 p h) (sat_cons (step138 p h) (sat_cons (step218 p h) (sat_cons (step211 p h) (sat_cons (step214 p h) (sat_cons (step205 p h) (sat_cons (step160 p h) (sat_cons (step196 p h) (sat_cons (step157 p h) (sat_cons (step193 p h) (sat_cons (step192 p h) (sat_cons (step146 p h) (sat_cons (step188 p h) (sat_cons (step189 p h) (sat_cons (step145 p h) (sat_cons (step52 p h) (sat_cons (step56 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c248 : List Lit := [(1368, true), (1328, false)]
theorem step248 (p : Nat → Bool) (h : Constraints p) : clause p c248 = true :=
  Snake9.LocalRup.prove_clause [c236, c233, c234, c76, c203, c210, c213, c204, c160, c195, c157, c190, c191, c146, c189, c187, c145, c52, c56] c248 (by decide) p (sat_cons (step236 p h) (sat_cons (step233 p h) (sat_cons (step234 p h) (sat_cons (step76 p h) (sat_cons (step203 p h) (sat_cons (step210 p h) (sat_cons (step213 p h) (sat_cons (step204 p h) (sat_cons (step160 p h) (sat_cons (step195 p h) (sat_cons (step157 p h) (sat_cons (step190 p h) (sat_cons (step191 p h) (sat_cons (step146 p h) (sat_cons (step189 p h) (sat_cons (step187 p h) (sat_cons (step145 p h) (sat_cons (step52 p h) (sat_cons (step56 p h) (sat_nil p))))))))))))))))))))
def c249 : List Lit := [(1342, true), (63, false)]
theorem step249 (p : Nat → Bool) (h : Constraints p) : clause p c249 = true :=
  Snake9.LocalRup.prove_clause [c68, c27, c190, c191, c189, c187, c56] c249 (by decide) p (sat_cons (step68 p h) (sat_cons (step27 p h) (sat_cons (step190 p h) (sat_cons (step191 p h) (sat_cons (step189 p h) (sat_cons (step187 p h) (sat_cons (step56 p h) (sat_nil p))))))))
def c250 : List Lit := [(1342, false), (1356, true), (82, true), (24, false), (1192, true)]
theorem step250 (p : Nat → Bool) (h : Constraints p) : clause p c250 = true :=
  Snake9.LocalRup.prove_clause [c60, c59, c74, c72, c88, c86, c89, c5, c10, c163, c165, c172, c177, c205, c196, c193, c87, c8, c9, c195, c199, c208, c184, c185, c179, c178, c182, c183, c48, c166, c173, c47, c164, c170, c188, c37, c51, c44] c250 (by decide) p (sat_cons (step60 p h) (sat_cons (step59 p h) (sat_cons (step74 p h) (sat_cons (step72 p h) (sat_cons (step88 p h) (sat_cons (step86 p h) (sat_cons (step89 p h) (sat_cons (step5 p h) (sat_cons (step10 p h) (sat_cons (step163 p h) (sat_cons (step165 p h) (sat_cons (step172 p h) (sat_cons (step177 p h) (sat_cons (step205 p h) (sat_cons (step196 p h) (sat_cons (step193 p h) (sat_cons (step87 p h) (sat_cons (step8 p h) (sat_cons (step9 p h) (sat_cons (step195 p h) (sat_cons (step199 p h) (sat_cons (step208 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step179 p h) (sat_cons (step178 p h) (sat_cons (step182 p h) (sat_cons (step183 p h) (sat_cons (step48 p h) (sat_cons (step166 p h) (sat_cons (step173 p h) (sat_cons (step47 p h) (sat_cons (step164 p h) (sat_cons (step170 p h) (sat_cons (step188 p h) (sat_cons (step37 p h) (sat_cons (step51 p h) (sat_cons (step44 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c251 : List Lit := [(1356, true), (82, true), (24, false), (1192, true), (26, false)]
theorem step251 (p : Nat → Bool) (h : Constraints p) : clause p c251 = true :=
  Snake9.LocalRup.prove_clause [c59, c75, c88, c86, c89, c5, c10, c209, c250, c191, c186, c50, c42, c43, c164, c169, c166, c173, c180] c251 (by decide) p (sat_cons (step59 p h) (sat_cons (step75 p h) (sat_cons (step88 p h) (sat_cons (step86 p h) (sat_cons (step89 p h) (sat_cons (step5 p h) (sat_cons (step10 p h) (sat_cons (step209 p h) (sat_cons (step250 p h) (sat_cons (step191 p h) (sat_cons (step186 p h) (sat_cons (step50 p h) (sat_cons (step42 p h) (sat_cons (step43 p h) (sat_cons (step164 p h) (sat_cons (step169 p h) (sat_cons (step166 p h) (sat_cons (step173 p h) (sat_cons (step180 p h) (sat_nil p))))))))))))))))))))
def c252 : List Lit := [(24, false), (1192, true), (1212, true)]
theorem step252 (p : Nat → Bool) (h : Constraints p) : clause p c252 = true :=
  Snake9.TreeRup.prove_clause [c230, c245, c60, c61, c59, c236, c220, c233, c234, c68, c62, c75, c88, c86, c89, c5, c10, c163, c165, c96, c87, c8, c9, c14, c6, c97, c244, c94, c137, c217, c212, c11, c172, c177, c206, c197, c247, c108, c248, c219, c139, c131, c246, c251, c211, c215, c218, c160, c138, c157, c132, c130, c146, c109, c125, c145, c107, c115, c27, c15, c113, c12, c53, c54, c50, c189, c188, c194] c252 (by decide) p (sat_cons (step230 p h) (sat_cons (step245 p h) (sat_cons (step60 p h) (sat_cons (step61 p h) (sat_cons (step59 p h) (sat_cons (step236 p h) (sat_cons (step220 p h) (sat_cons (step233 p h) (sat_cons (step234 p h) (sat_cons (step68 p h) (sat_cons (step62 p h) (sat_cons (step75 p h) (sat_cons (step88 p h) (sat_cons (step86 p h) (sat_cons (step89 p h) (sat_cons (step5 p h) (sat_cons (step10 p h) (sat_cons (step163 p h) (sat_cons (step165 p h) (sat_cons (step96 p h) (sat_cons (step87 p h) (sat_cons (step8 p h) (sat_cons (step9 p h) (sat_cons (step14 p h) (sat_cons (step6 p h) (sat_cons (step97 p h) (sat_cons (step244 p h) (sat_cons (step94 p h) (sat_cons (step137 p h) (sat_cons (step217 p h) (sat_cons (step212 p h) (sat_cons (step11 p h) (sat_cons (step172 p h) (sat_cons (step177 p h) (sat_cons (step206 p h) (sat_cons (step197 p h) (sat_cons (step247 p h) (sat_cons (step108 p h) (sat_cons (step248 p h) (sat_cons (step219 p h) (sat_cons (step139 p h) (sat_cons (step131 p h) (sat_cons (step246 p h) (sat_cons (step251 p h) (sat_cons (step211 p h) (sat_cons (step215 p h) (sat_cons (step218 p h) (sat_cons (step160 p h) (sat_cons (step138 p h) (sat_cons (step157 p h) (sat_cons (step132 p h) (sat_cons (step130 p h) (sat_cons (step146 p h) (sat_cons (step109 p h) (sat_cons (step125 p h) (sat_cons (step145 p h) (sat_cons (step107 p h) (sat_cons (step115 p h) (sat_cons (step27 p h) (sat_cons (step15 p h) (sat_cons (step113 p h) (sat_cons (step12 p h) (sat_cons (step53 p h) (sat_cons (step54 p h) (sat_cons (step50 p h) (sat_cons (step189 p h) (sat_cons (step188 p h) (sat_cons (step194 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c253 : List Lit := [(82, true), (95, true), (1356, true), (28, true), (77, true)]
theorem step253 (p : Nat → Bool) (h : Constraints p) : clause p c253 = true :=
  Snake9.LocalRup.prove_clause [c72, c163, c165, c186, c191, c195, c208, c178, c172, c173, c177, c179, c170, c205, c166, c196, c199, c164, c193, c184, c188, c182, c40, c51, c44] c253 (by decide) p (sat_cons (step72 p h) (sat_cons (step163 p h) (sat_cons (step165 p h) (sat_cons (step186 p h) (sat_cons (step191 p h) (sat_cons (step195 p h) (sat_cons (step208 p h) (sat_cons (step178 p h) (sat_cons (step172 p h) (sat_cons (step173 p h) (sat_cons (step177 p h) (sat_cons (step179 p h) (sat_cons (step170 p h) (sat_cons (step205 p h) (sat_cons (step166 p h) (sat_cons (step196 p h) (sat_cons (step199 p h) (sat_cons (step164 p h) (sat_cons (step193 p h) (sat_cons (step184 p h) (sat_cons (step188 p h) (sat_cons (step182 p h) (sat_cons (step40 p h) (sat_cons (step51 p h) (sat_cons (step44 p h) (sat_nil p))))))))))))))))))))))))))
def c254 : List Lit := [(1324, false), (82, false), (1346, false), (1369, true), (77, true)]
theorem step254 (p : Nat → Bool) (h : Constraints p) : clause p c254 = true :=
  Snake9.LocalRup.prove_clause [c236, c233, c211, c208, c163, c165, c177, c179, c204, c166, c214, c164, c160, c241, c156] c254 (by decide) p (sat_cons (step236 p h) (sat_cons (step233 p h) (sat_cons (step211 p h) (sat_cons (step208 p h) (sat_cons (step163 p h) (sat_cons (step165 p h) (sat_cons (step177 p h) (sat_cons (step179 p h) (sat_cons (step204 p h) (sat_cons (step166 p h) (sat_cons (step214 p h) (sat_cons (step164 p h) (sat_cons (step160 p h) (sat_cons (step241 p h) (sat_cons (step156 p h) (sat_nil p))))))))))))))))
def c255 : List Lit := [(95, true), (1369, true), (28, true), (77, true)]
theorem step255 (p : Nat → Bool) (h : Constraints p) : clause p c255 = true :=
  Snake9.LocalRup.prove_clause [c236, c233, c237, c68, c211, c186, c191, c195, c201, c216, c161, c253, c254, c240, c156, c158, c160, c146, c214, c145, c202, c196, c27, c193, c192, c188, c189, c56] c255 (by decide) p (sat_cons (step236 p h) (sat_cons (step233 p h) (sat_cons (step237 p h) (sat_cons (step68 p h) (sat_cons (step211 p h) (sat_cons (step186 p h) (sat_cons (step191 p h) (sat_cons (step195 p h) (sat_cons (step201 p h) (sat_cons (step216 p h) (sat_cons (step161 p h) (sat_cons (step253 p h) (sat_cons (step254 p h) (sat_cons (step240 p h) (sat_cons (step156 p h) (sat_cons (step158 p h) (sat_cons (step160 p h) (sat_cons (step146 p h) (sat_cons (step214 p h) (sat_cons (step145 p h) (sat_cons (step202 p h) (sat_cons (step196 p h) (sat_cons (step27 p h) (sat_cons (step193 p h) (sat_cons (step192 p h) (sat_cons (step188 p h) (sat_cons (step189 p h) (sat_cons (step56 p h) (sat_nil p)))))))))))))))))))))))))))))
def c256 : List Lit := [(1192, true), (1212, true)]
theorem step256 (p : Nat → Bool) (h : Constraints p) : clause p c256 = true :=
  Snake9.LocalRup.prove_clause [c230, c59, c60, c220, c236, c75, c233, c97, c244, c94, c88, c89, c86, c87, c5, c7, c8, c10, c9, c252, c101, c243, c138, c218, c211, c209, c255, c50, c42, c43, c164, c169, c166, c171, c180, c181, c179, c173, c168, c207, c238, c34, c214, c147, c160, c154, c156] c256 (by decide) p (sat_cons (step230 p h) (sat_cons (step59 p h) (sat_cons (step60 p h) (sat_cons (step220 p h) (sat_cons (step236 p h) (sat_cons (step75 p h) (sat_cons (step233 p h) (sat_cons (step97 p h) (sat_cons (step244 p h) (sat_cons (step94 p h) (sat_cons (step88 p h) (sat_cons (step89 p h) (sat_cons (step86 p h) (sat_cons (step87 p h) (sat_cons (step5 p h) (sat_cons (step7 p h) (sat_cons (step8 p h) (sat_cons (step10 p h) (sat_cons (step9 p h) (sat_cons (step252 p h) (sat_cons (step101 p h) (sat_cons (step243 p h) (sat_cons (step138 p h) (sat_cons (step218 p h) (sat_cons (step211 p h) (sat_cons (step209 p h) (sat_cons (step255 p h) (sat_cons (step50 p h) (sat_cons (step42 p h) (sat_cons (step43 p h) (sat_cons (step164 p h) (sat_cons (step169 p h) (sat_cons (step166 p h) (sat_cons (step171 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step179 p h) (sat_cons (step173 p h) (sat_cons (step168 p h) (sat_cons (step207 p h) (sat_cons (step238 p h) (sat_cons (step34 p h) (sat_cons (step214 p h) (sat_cons (step147 p h) (sat_cons (step160 p h) (sat_cons (step154 p h) (sat_cons (step156 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c257 : List Lit := [(1335, true), (95, false)]
theorem step257 (p : Nat → Bool) (h : Constraints p) : clause p c257 = true :=
  Snake9.LocalRup.prove_clause [c75, c49, c184, c185, c183, c47] c257 (by decide) p (sat_cons (step75 p h) (sat_cons (step49 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step183 p h) (sat_cons (step47 p h) (sat_nil p)))))))
def c258 : List Lit := [(95, false), (1369, true), (26, false)]
theorem step258 (p : Nat → Bool) (h : Constraints p) : clause p c258 = true :=
  Snake9.LocalRup.prove_clause [c236, c75, c233, c234, c211, c50, c42, c43, c162, c169, c165, c171, c177, c205, c257, c198, c199, c204, c249, c214, c145, c160, c146, c157] c258 (by decide) p (sat_cons (step236 p h) (sat_cons (step75 p h) (sat_cons (step233 p h) (sat_cons (step234 p h) (sat_cons (step211 p h) (sat_cons (step50 p h) (sat_cons (step42 p h) (sat_cons (step43 p h) (sat_cons (step162 p h) (sat_cons (step169 p h) (sat_cons (step165 p h) (sat_cons (step171 p h) (sat_cons (step177 p h) (sat_cons (step205 p h) (sat_cons (step257 p h) (sat_cons (step198 p h) (sat_cons (step199 p h) (sat_cons (step204 p h) (sat_cons (step249 p h) (sat_cons (step214 p h) (sat_cons (step145 p h) (sat_cons (step160 p h) (sat_cons (step146 p h) (sat_cons (step157 p h) (sat_nil p)))))))))))))))))))))))))
def c259 : List Lit := [(1347, false), (1369, true)]
theorem step259 (p : Nat → Bool) (h : Constraints p) : clause p c259 = true :=
  Snake9.LocalRup.prove_clause [c236, c237, c233, c211, c202, c205, c214, c242, c160, c156] c259 (by decide) p (sat_cons (step236 p h) (sat_cons (step237 p h) (sat_cons (step233 p h) (sat_cons (step211 p h) (sat_cons (step202 p h) (sat_cons (step205 p h) (sat_cons (step214 p h) (sat_cons (step242 p h) (sat_cons (step160 p h) (sat_cons (step156 p h) (sat_nil p)))))))))))
def c260 : List Lit := [(1369, true), (26, false)]
theorem step260 (p : Nat → Bool) (h : Constraints p) : clause p c260 = true :=
  Snake9.LocalRup.prove_clause [c233, c234, c76, c237, c258, c186, c191, c195, c201, c216, c161, c259, c196, c193, c192, c188, c189, c52, c56, c145, c146, c157, c158, c160, c242, c214, c204] c260 (by decide) p (sat_cons (step233 p h) (sat_cons (step234 p h) (sat_cons (step76 p h) (sat_cons (step237 p h) (sat_cons (step258 p h) (sat_cons (step186 p h) (sat_cons (step191 p h) (sat_cons (step195 p h) (sat_cons (step201 p h) (sat_cons (step216 p h) (sat_cons (step161 p h) (sat_cons (step259 p h) (sat_cons (step196 p h) (sat_cons (step193 p h) (sat_cons (step192 p h) (sat_cons (step188 p h) (sat_cons (step189 p h) (sat_cons (step52 p h) (sat_cons (step56 p h) (sat_cons (step145 p h) (sat_cons (step146 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step160 p h) (sat_cons (step242 p h) (sat_cons (step214 p h) (sat_cons (step204 p h) (sat_nil p))))))))))))))))))))))))))))
def c261 : List Lit := [(1212, true)]
theorem step261 (p : Nat → Bool) (h : Constraints p) : clause p c261 = true :=
  Snake9.LocalRup.prove_clause [c220, c245, c230, c62, c97, c244, c94, c256, c260, c218, c138, c140, c128, c132, c95, c246, c109, c92, c107, c85, c15, c84, c13] c261 (by decide) p (sat_cons (step220 p h) (sat_cons (step245 p h) (sat_cons (step230 p h) (sat_cons (step62 p h) (sat_cons (step97 p h) (sat_cons (step244 p h) (sat_cons (step94 p h) (sat_cons (step256 p h) (sat_cons (step260 p h) (sat_cons (step218 p h) (sat_cons (step138 p h) (sat_cons (step140 p h) (sat_cons (step128 p h) (sat_cons (step132 p h) (sat_cons (step95 p h) (sat_cons (step246 p h) (sat_cons (step109 p h) (sat_cons (step92 p h) (sat_cons (step107 p h) (sat_cons (step85 p h) (sat_cons (step15 p h) (sat_cons (step84 p h) (sat_cons (step13 p h) (sat_nil p))))))))))))))))))))))))
def c262 : List Lit := [(1214, true)]
theorem step262 (p : Nat → Bool) (h : Constraints p) : clause p c262 = true :=
  Snake9.LocalRup.prove_clause [c261, c99] c262 (by decide) p (sat_cons (step261 p h) (sat_cons (step99 p h) (sat_nil p)))
def c263 : List Lit := [(1222, true)]
theorem step263 (p : Nat → Bool) (h : Constraints p) : clause p c263 = true :=
  Snake9.LocalRup.prove_clause [c262, c110] c263 (by decide) p (sat_cons (step262 p h) (sat_cons (step110 p h) (sat_nil p)))
def c264 : List Lit := [(1249, true)]
theorem step264 (p : Nat → Bool) (h : Constraints p) : clause p c264 = true :=
  Snake9.LocalRup.prove_clause [c262, c243] c264 (by decide) p (sat_cons (step262 p h) (sat_cons (step243 p h) (sat_nil p)))
def c265 : List Lit := [(1262, true)]
theorem step265 (p : Nat → Bool) (h : Constraints p) : clause p c265 = true :=
  Snake9.LocalRup.prove_clause [c264, c231, c135] c265 (by decide) p (sat_cons (step264 p h) (sat_cons (step231 p h) (sat_cons (step135 p h) (sat_nil p))))
def c266 : List Lit := [(1370, false)]
theorem step266 (p : Nat → Bool) (h : Constraints p) : clause p c266 = true :=
  Snake9.LocalRup.prove_clause [c265, c220, c217] c266 (by decide) p (sat_cons (step265 p h) (sat_cons (step220 p h) (sat_cons (step217 p h) (sat_nil p))))
def c267 : List Lit := [(1357, false)]
theorem step267 (p : Nat → Bool) (h : Constraints p) : clause p c267 = true :=
  Snake9.LocalRup.prove_clause [c266, c236, c212] c267 (by decide) p (sat_cons (step266 p h) (sat_cons (step236 p h) (sat_cons (step212 p h) (sat_nil p))))
def c268 : List Lit := [(1342, true), (1241, true)]
theorem step268 (p : Nat → Bool) (h : Constraints p) : clause p c268 = true :=
  Snake9.LocalRup.prove_clause [c65, c125, c115, c113, c123, c121, c117, c114, c22, c20, c190, c191, c189, c187, c55] c268 (by decide) p (sat_cons (step65 p h) (sat_cons (step125 p h) (sat_cons (step115 p h) (sat_cons (step113 p h) (sat_cons (step123 p h) (sat_cons (step121 p h) (sat_cons (step117 p h) (sat_cons (step114 p h) (sat_cons (step22 p h) (sat_cons (step20 p h) (sat_cons (step190 p h) (sat_cons (step191 p h) (sat_cons (step189 p h) (sat_cons (step187 p h) (sat_cons (step55 p h) (sat_nil p))))))))))))))))
def c269 : List Lit := [(1263, true)]
theorem step269 (p : Nat → Bool) (h : Constraints p) : clause p c269 = true :=
  Snake9.TreeRup.prove_clause [c231, c264, c263, c230, c262, c59, c261, c60, c61, c65, c267, c266, c233, c234, c136, c138, c134, c131, c94, c246, c90, c244, c105, c88, c89, c111, c112, c86, c87, c5, c133, c100, c102, c8, c10, c123, c125, c98, c9, c163, c121, c115, c14, c165, c117, c113, c114, c11, c22, c172, c20, c177, c206, c197, c268, c250, c215, c160, c157, c146, c145, c53, c54, c187, c189, c194, c192, c188, c200, c257] c269 (by decide) p (sat_cons (step231 p h) (sat_cons (step264 p h) (sat_cons (step263 p h) (sat_cons (step230 p h) (sat_cons (step262 p h) (sat_cons (step59 p h) (sat_cons (step261 p h) (sat_cons (step60 p h) (sat_cons (step61 p h) (sat_cons (step65 p h) (sat_cons (step267 p h) (sat_cons (step266 p h) (sat_cons (step233 p h) (sat_cons (step234 p h) (sat_cons (step136 p h) (sat_cons (step138 p h) (sat_cons (step134 p h) (sat_cons (step131 p h) (sat_cons (step94 p h) (sat_cons (step246 p h) (sat_cons (step90 p h) (sat_cons (step244 p h) (sat_cons (step105 p h) (sat_cons (step88 p h) (sat_cons (step89 p h) (sat_cons (step111 p h) (sat_cons (step112 p h) (sat_cons (step86 p h) (sat_cons (step87 p h) (sat_cons (step5 p h) (sat_cons (step133 p h) (sat_cons (step100 p h) (sat_cons (step102 p h) (sat_cons (step8 p h) (sat_cons (step10 p h) (sat_cons (step123 p h) (sat_cons (step125 p h) (sat_cons (step98 p h) (sat_cons (step9 p h) (sat_cons (step163 p h) (sat_cons (step121 p h) (sat_cons (step115 p h) (sat_cons (step14 p h) (sat_cons (step165 p h) (sat_cons (step117 p h) (sat_cons (step113 p h) (sat_cons (step114 p h) (sat_cons (step11 p h) (sat_cons (step22 p h) (sat_cons (step172 p h) (sat_cons (step20 p h) (sat_cons (step177 p h) (sat_cons (step206 p h) (sat_cons (step197 p h) (sat_cons (step268 p h) (sat_cons (step250 p h) (sat_cons (step215 p h) (sat_cons (step160 p h) (sat_cons (step157 p h) (sat_cons (step146 p h) (sat_cons (step145 p h) (sat_cons (step53 p h) (sat_cons (step54 p h) (sat_cons (step187 p h) (sat_cons (step189 p h) (sat_cons (step194 p h) (sat_cons (step192 p h) (sat_cons (step188 p h) (sat_cons (step200 p h) (sat_cons (step257 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c270 : List Lit := [(1369, false)]
theorem step270 (p : Nat → Bool) (h : Constraints p) : clause p c270 = true :=
  Snake9.LocalRup.prove_clause [c269, c220, c218] c270 (by decide) p (sat_cons (step269 p h) (sat_cons (step220 p h) (sat_cons (step218 p h) (sat_nil p))))
def c271 : List Lit := [(1347, false)]
theorem step271 (p : Nat → Bool) (h : Constraints p) : clause p c271 = true :=
  Snake9.LocalRup.prove_clause [c270, c259] c271 (by decide) p (sat_cons (step270 p h) (sat_cons (step259 p h) (sat_nil p)))
def c272 : List Lit := [(1343, false)]
theorem step272 (p : Nat → Bool) (h : Constraints p) : clause p c272 = true :=
  Snake9.LocalRup.prove_clause [c271, c196] c272 (by decide) p (sat_cons (step271 p h) (sat_cons (step196 p h) (sat_nil p)))
def c273 : List Lit := [(1339, false)]
theorem step273 (p : Nat → Bool) (h : Constraints p) : clause p c273 = true :=
  Snake9.LocalRup.prove_clause [c272, c193] c273 (by decide) p (sat_cons (step272 p h) (sat_cons (step193 p h) (sat_nil p)))
def c274 : List Lit := [(1342, false)]
theorem step274 (p : Nat → Bool) (h : Constraints p) : clause p c274 = true :=
  Snake9.LocalRup.prove_clause [c271, c237, c273, c272, c76, c234, c233, c270, c195, c199, c201, c257, c216, c186, c188, c161, c192, c189, c52, c56, c145, c146, c157, c158, c160, c242, c214, c204] c274 (by decide) p (sat_cons (step271 p h) (sat_cons (step237 p h) (sat_cons (step273 p h) (sat_cons (step272 p h) (sat_cons (step76 p h) (sat_cons (step234 p h) (sat_cons (step233 p h) (sat_cons (step270 p h) (sat_cons (step195 p h) (sat_cons (step199 p h) (sat_cons (step201 p h) (sat_cons (step257 p h) (sat_cons (step216 p h) (sat_cons (step186 p h) (sat_cons (step188 p h) (sat_cons (step161 p h) (sat_cons (step192 p h) (sat_cons (step189 p h) (sat_cons (step52 p h) (sat_cons (step56 p h) (sat_cons (step145 p h) (sat_cons (step146 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step160 p h) (sat_cons (step242 p h) (sat_cons (step214 p h) (sat_cons (step204 p h) (sat_nil p)))))))))))))))))))))))))))))
def c275 : List Lit := [(1338, false)]
theorem step275 (p : Nat → Bool) (h : Constraints p) : clause p c275 = true :=
  Snake9.LocalRup.prove_clause [c274, c191] c275 (by decide) p (sat_cons (step274 p h) (sat_cons (step191 p h) (sat_nil p)))
def c276 : List Lit := [(63, false)]
theorem step276 (p : Nat → Bool) (h : Constraints p) : clause p c276 = true :=
  Snake9.LocalRup.prove_clause [c274, c249] c276 (by decide) p (sat_cons (step274 p h) (sat_cons (step249 p h) (sat_nil p)))
def c277 : List Lit := [(95, true)]
theorem step277 (p : Nat → Bool) (h : Constraints p) : clause p c277 = true :=
  Snake9.LocalRup.prove_clause [c275, c186] c277 (by decide) p (sat_cons (step275 p h) (sat_cons (step186 p h) (sat_nil p)))
def c278 : List Lit := [(1286, true)]
theorem step278 (p : Nat → Bool) (h : Constraints p) : clause p c278 = true :=
  Snake9.LocalRup.prove_clause [c276, c145] c278 (by decide) p (sat_cons (step276 p h) (sat_cons (step145 p h) (sat_nil p)))
def c279 : List Lit := [(1335, true)]
theorem step279 (p : Nat → Bool) (h : Constraints p) : clause p c279 = true :=
  Snake9.LocalRup.prove_clause [c277, c257] c279 (by decide) p (sat_cons (step277 p h) (sat_cons (step257 p h) (sat_nil p)))
def c280 : List Lit := [(1288, true)]
theorem step280 (p : Nat → Bool) (h : Constraints p) : clause p c280 = true :=
  Snake9.LocalRup.prove_clause [c278, c146] c280 (by decide) p (sat_cons (step278 p h) (sat_cons (step146 p h) (sat_nil p)))
def c281 : List Lit := [(1346, true)]
theorem step281 (p : Nat → Bool) (h : Constraints p) : clause p c281 = true :=
  Snake9.LocalRup.prove_clause [c279, c198] c281 (by decide) p (sat_cons (step279 p h) (sat_cons (step198 p h) (sat_nil p)))
def c282 : List Lit := [(1300, true)]
theorem step282 (p : Nat → Bool) (h : Constraints p) : clause p c282 = true :=
  Snake9.LocalRup.prove_clause [c280, c234, c157] c282 (by decide) p (sat_cons (step280 p h) (sat_cons (step234 p h) (sat_cons (step157 p h) (sat_nil p))))
def c283 : List Lit := [(1354, true)]
theorem step283 (p : Nat → Bool) (h : Constraints p) : clause p c283 = true :=
  Snake9.LocalRup.prove_clause [c281, c237, c201] c283 (by decide) p (sat_cons (step281 p h) (sat_cons (step237 p h) (sat_cons (step201 p h) (sat_nil p))))
def c284 : List Lit := [(1308, true)]
theorem step284 (p : Nat → Bool) (h : Constraints p) : clause p c284 = true :=
  Snake9.LocalRup.prove_clause [c282, c233, c160] c284 (by decide) p (sat_cons (step282 p h) (sat_cons (step233 p h) (sat_cons (step160 p h) (sat_nil p))))
def c285 : List Lit := [(1309, false)]
theorem step285 (p : Nat → Bool) (h : Constraints p) : clause p c285 = true :=
  Snake9.LocalRup.prove_clause [c283, c270, c216] c285 (by decide) p (sat_cons (step283 p h) (sat_cons (step270 p h) (sat_cons (step216 p h) (sat_nil p))))
def c286 : List Lit := [(1355, false)]
theorem step286 (p : Nat → Bool) (h : Constraints p) : clause p c286 = true :=
  Snake9.LocalRup.prove_clause [c284, c270, c214] c286 (by decide) p (sat_cons (step284 p h) (sat_cons (step270 p h) (sat_cons (step214 p h) (sat_nil p))))
end B112E098
