import B112E184Inputs
namespace B112E184
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c140 : List Lit := [(53, false), (49, false), (52, false)]
theorem step140 (p : Nat → Bool) (h : Constraints p) : clause p c140 = true :=
  Snake9.LocalRup.prove_clause [c2, c15] c140 (by decide) p (sat_cons (step2 p h) (sat_cons (step15 p h) (sat_nil p)))
def c141 : List Lit := [(17, false)]
theorem step141 (p : Nat → Bool) (h : Constraints p) : clause p c141 = true :=
  Snake9.LocalRup.prove_clause [c32, c3] c141 (by decide) p (sat_cons (step32 p h) (sat_cons (step3 p h) (sat_nil p)))
def c142 : List Lit := [(70, false)]
theorem step142 (p : Nat → Bool) (h : Constraints p) : clause p c142 = true :=
  Snake9.LocalRup.prove_clause [c40, c18] c142 (by decide) p (sat_cons (step40 p h) (sat_cons (step18 p h) (sat_nil p)))
def c143 : List Lit := [(1220, true)]
theorem step143 (p : Nat → Bool) (h : Constraints p) : clause p c143 = true :=
  Snake9.LocalRup.prove_clause [c141, c51] c143 (by decide) p (sat_cons (step141 p h) (sat_cons (step51 p h) (sat_nil p)))
def c144 : List Lit := [(1218, false), (1221, true)]
theorem step144 (p : Nat → Bool) (h : Constraints p) : clause p c144 = true :=
  Snake9.LocalRup.prove_clause [c141, c52] c144 (by decide) p (sat_cons (step141 p h) (sat_cons (step52 p h) (sat_nil p)))
def c145 : List Lit := [(1228, true)]
theorem step145 (p : Nat → Bool) (h : Constraints p) : clause p c145 = true :=
  Snake9.LocalRup.prove_clause [c143, c57] c145 (by decide) p (sat_cons (step143 p h) (sat_cons (step57 p h) (sat_nil p)))
def c146 : List Lit := [(1225, false), (1229, true)]
theorem step146 (p : Nat → Bool) (h : Constraints p) : clause p c146 = true :=
  Snake9.LocalRup.prove_clause [c143, c58] c146 (by decide) p (sat_cons (step143 p h) (sat_cons (step58 p h) (sat_nil p)))
def c147 : List Lit := [(1234, true)]
theorem step147 (p : Nat → Bool) (h : Constraints p) : clause p c147 = true :=
  Snake9.LocalRup.prove_clause [c145, c60] c147 (by decide) p (sat_cons (step145 p h) (sat_cons (step60 p h) (sat_nil p)))
def c148 : List Lit := [(1212, false), (1235, true)]
theorem step148 (p : Nat → Bool) (h : Constraints p) : clause p c148 = true :=
  Snake9.LocalRup.prove_clause [c145, c62] c148 (by decide) p (sat_cons (step145 p h) (sat_cons (step62 p h) (sat_nil p)))
def c149 : List Lit := [(1274, false), (1283, true)]
theorem step149 (p : Nat → Bool) (h : Constraints p) : clause p c149 = true :=
  Snake9.LocalRup.prove_clause [c147, c84] c149 (by decide) p (sat_cons (step147 p h) (sat_cons (step84 p h) (sat_nil p)))
def c150 : List Lit := [(1275, false), (1284, true)]
theorem step150 (p : Nat → Bool) (h : Constraints p) : clause p c150 = true :=
  Snake9.LocalRup.prove_clause [c147, c85] c150 (by decide) p (sat_cons (step147 p h) (sat_cons (step85 p h) (sat_nil p)))
def c151 : List Lit := [(1306, true)]
theorem step151 (p : Nat → Bool) (h : Constraints p) : clause p c151 = true :=
  Snake9.LocalRup.prove_clause [c142, c94] c151 (by decide) p (sat_cons (step142 p h) (sat_cons (step94 p h) (sat_nil p)))
def c152 : List Lit := [(1308, true)]
theorem step152 (p : Nat → Bool) (h : Constraints p) : clause p c152 = true :=
  Snake9.LocalRup.prove_clause [c151, c95] c152 (by decide) p (sat_cons (step151 p h) (sat_cons (step95 p h) (sat_nil p)))
def c153 : List Lit := [(1316, true)]
theorem step153 (p : Nat → Bool) (h : Constraints p) : clause p c153 = true :=
  Snake9.LocalRup.prove_clause [c152, c101] c153 (by decide) p (sat_cons (step152 p h) (sat_cons (step101 p h) (sat_nil p)))
def c154 : List Lit := [(1313, false), (1317, true)]
theorem step154 (p : Nat → Bool) (h : Constraints p) : clause p c154 = true :=
  Snake9.LocalRup.prove_clause [c152, c102] c154 (by decide) p (sat_cons (step152 p h) (sat_cons (step102 p h) (sat_nil p)))
def c155 : List Lit := [(1314, false), (1318, true)]
theorem step155 (p : Nat → Bool) (h : Constraints p) : clause p c155 = true :=
  Snake9.LocalRup.prove_clause [c152, c103] c155 (by decide) p (sat_cons (step152 p h) (sat_cons (step103 p h) (sat_nil p)))
def c156 : List Lit := [(1300, false), (1323, true)]
theorem step156 (p : Nat → Bool) (h : Constraints p) : clause p c156 = true :=
  Snake9.LocalRup.prove_clause [c153, c104] c156 (by decide) p (sat_cons (step153 p h) (sat_cons (step104 p h) (sat_nil p)))
def c157 : List Lit := [(1260, true)]
theorem step157 (p : Nat → Bool) (h : Constraints p) : clause p c157 = true :=
  Snake9.LocalRup.prove_clause [c37, c74, c75, c72, c73, c12, c13] c157 (by decide) p (sat_cons (step37 p h) (sat_cons (step74 p h) (sat_cons (step75 p h) (sat_cons (step72 p h) (sat_cons (step73 p h) (sat_cons (step12 p h) (sat_cons (step13 p h) (sat_nil p))))))))
def c158 : List Lit := [(1268, true)]
theorem step158 (p : Nat → Bool) (h : Constraints p) : clause p c158 = true :=
  Snake9.LocalRup.prove_clause [c157, c79] c158 (by decide) p (sat_cons (step157 p h) (sat_cons (step79 p h) (sat_nil p)))
def c159 : List Lit := [(1274, true)]
theorem step159 (p : Nat → Bool) (h : Constraints p) : clause p c159 = true :=
  Snake9.LocalRup.prove_clause [c158, c81] c159 (by decide) p (sat_cons (step158 p h) (sat_cons (step81 p h) (sat_nil p)))
def c160 : List Lit := [(1283, true)]
theorem step160 (p : Nat → Bool) (h : Constraints p) : clause p c160 = true :=
  Snake9.LocalRup.prove_clause [c159, c149] c160 (by decide) p (sat_cons (step159 p h) (sat_cons (step149 p h) (sat_nil p)))
def c161 : List Lit := [(1375, false)]
theorem step161 (p : Nat → Bool) (h : Constraints p) : clause p c161 = true :=
  Snake9.LocalRup.prove_clause [c160, c139, c137] c161 (by decide) p (sat_cons (step160 p h) (sat_cons (step139 p h) (sat_cons (step137 p h) (sat_nil p))))
def c162 : List Lit := [(1313, true), (1284, true)]
theorem step162 (p : Nat → Bool) (h : Constraints p) : clause p c162 = true :=
  Snake9.LocalRup.prove_clause [c33, c159, c158, c150, c83, c70, c68, c67, c69, c71, c65, c64, c11, c86, c61, c59, c144, c50, c146, c56, c49, c4, c5, c98, c99, c97, c19] c162 (by decide) p (sat_cons (step33 p h) (sat_cons (step159 p h) (sat_cons (step158 p h) (sat_cons (step150 p h) (sat_cons (step83 p h) (sat_cons (step70 p h) (sat_cons (step68 p h) (sat_cons (step67 p h) (sat_cons (step69 p h) (sat_cons (step71 p h) (sat_cons (step65 p h) (sat_cons (step64 p h) (sat_cons (step11 p h) (sat_cons (step86 p h) (sat_cons (step61 p h) (sat_cons (step59 p h) (sat_cons (step144 p h) (sat_cons (step50 p h) (sat_cons (step146 p h) (sat_cons (step56 p h) (sat_cons (step49 p h) (sat_cons (step4 p h) (sat_cons (step5 p h) (sat_cons (step98 p h) (sat_cons (step99 p h) (sat_cons (step97 p h) (sat_cons (step19 p h) (sat_nil p))))))))))))))))))))))))))))
def c163 : List Lit := [(1300, true)]
theorem step163 (p : Nat → Bool) (h : Constraints p) : clause p c163 = true :=
  Snake9.LocalRup.prove_clause [c39, c92, c93, c90, c91, c88, c89, c87, c16, c17] c163 (by decide) p (sat_cons (step39 p h) (sat_cons (step92 p h) (sat_cons (step93 p h) (sat_cons (step90 p h) (sat_cons (step91 p h) (sat_cons (step88 p h) (sat_cons (step89 p h) (sat_cons (step87 p h) (sat_cons (step16 p h) (sat_cons (step17 p h) (sat_nil p)))))))))))
def c164 : List Lit := [(1337, true), (82, false), (71, false)]
theorem step164 (p : Nat → Bool) (h : Constraints p) : clause p c164 = true :=
  Snake9.LocalRup.prove_clause [c43, c44, c115, c116, c114, c27, c29, c24] c164 (by decide) p (sat_cons (step43 p h) (sat_cons (step44 p h) (sat_cons (step115 p h) (sat_cons (step116 p h) (sat_cons (step114 p h) (sat_cons (step27 p h) (sat_cons (step29 p h) (sat_cons (step24 p h) (sat_nil p)))))))))
def c165 : List Lit := [(97, false), (99, false), (98, false)]
theorem step165 (p : Nat → Bool) (h : Constraints p) : clause p c165 = true :=
  Snake9.LocalRup.prove_clause [c45, c31, c30] c165 (by decide) p (sat_cons (step45 p h) (sat_cons (step31 p h) (sat_cons (step30 p h) (sat_nil p))))
def c166 : List Lit := [(1353, true)]
theorem step166 (p : Nat → Bool) (h : Constraints p) : clause p c166 = true :=
  Snake9.LocalRup.prove_clause [c124, c125, c122, c123, c165] c166 (by decide) p (sat_cons (step124 p h) (sat_cons (step125 p h) (sat_cons (step122 p h) (sat_cons (step123 p h) (sat_cons (step165 p h) (sat_nil p))))))
def c167 : List Lit := [(1356, true)]
theorem step167 (p : Nat → Bool) (h : Constraints p) : clause p c167 = true :=
  Snake9.LocalRup.prove_clause [c166, c126] c167 (by decide) p (sat_cons (step166 p h) (sat_cons (step126 p h) (sat_nil p)))
def c168 : List Lit := [(1284, true)]
theorem step168 (p : Nat → Bool) (h : Constraints p) : clause p c168 = true :=
  Snake9.LocalRup.prove_clause [c159, c158, c157, c2, c36, c34, c38, c35, c163, c161, c166, c167, c150, c86, c82, c83, c61, c148, c80, c71, c146, c59, c48, c77, c78, c65, c66, c55, c144, c47, c76, c63, c53, c54, c49, c46, c1, c140, c10, c6, c14, c7, c9, c8, c112, c118, c162, c154, c105, c135, c131, c127, c132, c121, c119, c25, c116] c168 (by decide) p (sat_cons (step159 p h) (sat_cons (step158 p h) (sat_cons (step157 p h) (sat_cons (step2 p h) (sat_cons (step36 p h) (sat_cons (step34 p h) (sat_cons (step38 p h) (sat_cons (step35 p h) (sat_cons (step163 p h) (sat_cons (step161 p h) (sat_cons (step166 p h) (sat_cons (step167 p h) (sat_cons (step150 p h) (sat_cons (step86 p h) (sat_cons (step82 p h) (sat_cons (step83 p h) (sat_cons (step61 p h) (sat_cons (step148 p h) (sat_cons (step80 p h) (sat_cons (step71 p h) (sat_cons (step146 p h) (sat_cons (step59 p h) (sat_cons (step48 p h) (sat_cons (step77 p h) (sat_cons (step78 p h) (sat_cons (step65 p h) (sat_cons (step66 p h) (sat_cons (step55 p h) (sat_cons (step144 p h) (sat_cons (step47 p h) (sat_cons (step76 p h) (sat_cons (step63 p h) (sat_cons (step53 p h) (sat_cons (step54 p h) (sat_cons (step49 p h) (sat_cons (step46 p h) (sat_cons (step1 p h) (sat_cons (step140 p h) (sat_cons (step10 p h) (sat_cons (step6 p h) (sat_cons (step14 p h) (sat_cons (step7 p h) (sat_cons (step9 p h) (sat_cons (step8 p h) (sat_cons (step112 p h) (sat_cons (step118 p h) (sat_cons (step162 p h) (sat_cons (step154 p h) (sat_cons (step105 p h) (sat_cons (step135 p h) (sat_cons (step131 p h) (sat_cons (step127 p h) (sat_cons (step132 p h) (sat_cons (step121 p h) (sat_cons (step119 p h) (sat_cons (step25 p h) (sat_cons (step116 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c169 : List Lit := [(1323, true)]
theorem step169 (p : Nat → Bool) (h : Constraints p) : clause p c169 = true :=
  Snake9.LocalRup.prove_clause [c163, c156] c169 (by decide) p (sat_cons (step163 p h) (sat_cons (step156 p h) (sat_nil p)))
def c170 : List Lit := [(1362, true)]
theorem step170 (p : Nat → Bool) (h : Constraints p) : clause p c170 = true :=
  Snake9.LocalRup.prove_clause [c167, c128] c170 (by decide) p (sat_cons (step167 p h) (sat_cons (step128 p h) (sat_nil p)))
def c171 : List Lit := [(1374, false)]
theorem step171 (p : Nat → Bool) (h : Constraints p) : clause p c171 = true :=
  Snake9.LocalRup.prove_clause [c168, c139, c138] c171 (by decide) p (sat_cons (step168 p h) (sat_cons (step139 p h) (sat_cons (step138 p h) (sat_nil p))))
def c172 : List Lit := [(1364, false)]
theorem step172 (p : Nat → Bool) (h : Constraints p) : clause p c172 = true :=
  Snake9.LocalRup.prove_clause [c169, c171, c133] c172 (by decide) p (sat_cons (step169 p h) (sat_cons (step171 p h) (sat_cons (step133 p h) (sat_nil p))))
def c173 : List Lit := [(1325, false)]
theorem step173 (p : Nat → Bool) (h : Constraints p) : clause p c173 = true :=
  Snake9.LocalRup.prove_clause [c170, c171, c136] c173 (by decide) p (sat_cons (step170 p h) (sat_cons (step171 p h) (sat_cons (step136 p h) (sat_nil p))))
def c174 : List Lit := [(1341, false)]
theorem step174 (p : Nat → Bool) (h : Constraints p) : clause p c174 = true :=
  Snake9.LocalRup.prove_clause [c172, c167, c132] c174 (by decide) p (sat_cons (step172 p h) (sat_cons (step167 p h) (sat_cons (step132 p h) (sat_nil p))))
def c175 : List Lit := [(1318, false)]
theorem step175 (p : Nat → Bool) (h : Constraints p) : clause p c175 = true :=
  Snake9.LocalRup.prove_clause [c173, c163, c106] c175 (by decide) p (sat_cons (step173 p h) (sat_cons (step163 p h) (sat_cons (step106 p h) (sat_nil p))))
def c176 : List Lit := [(1333, false)]
theorem step176 (p : Nat → Bool) (h : Constraints p) : clause p c176 = true :=
  Snake9.LocalRup.prove_clause [c174, c120] c176 (by decide) p (sat_cons (step174 p h) (sat_cons (step120 p h) (sat_nil p)))
def c177 : List Lit := [(1314, false)]
theorem step177 (p : Nat → Bool) (h : Constraints p) : clause p c177 = true :=
  Snake9.LocalRup.prove_clause [c175, c155] c177 (by decide) p (sat_cons (step175 p h) (sat_cons (step155 p h) (sat_nil p)))
def c178 : List Lit := [(1331, false)]
theorem step178 (p : Nat → Bool) (h : Constraints p) : clause p c178 = true :=
  Snake9.LocalRup.prove_clause [c176, c111] c178 (by decide) p (sat_cons (step176 p h) (sat_cons (step111 p h) (sat_nil p)))
def c179 : List Lit := [(1311, false), (84, false)]
theorem step179 (p : Nat → Bool) (h : Constraints p) : clause p c179 = true :=
  Snake9.LocalRup.prove_clause [c43, c177, c163, c171, c166, c28, c98, c100, c154, c26, c105, c121, c134, c127, c129] c179 (by decide) p (sat_cons (step43 p h) (sat_cons (step177 p h) (sat_cons (step163 p h) (sat_cons (step171 p h) (sat_cons (step166 p h) (sat_cons (step28 p h) (sat_cons (step98 p h) (sat_cons (step100 p h) (sat_cons (step154 p h) (sat_cons (step26 p h) (sat_cons (step105 p h) (sat_cons (step121 p h) (sat_cons (step134 p h) (sat_cons (step127 p h) (sat_cons (step129 p h) (sat_nil p))))))))))))))))
def c180 : List Lit := [(1337, true)]
theorem step180 (p : Nat → Bool) (h : Constraints p) : clause p c180 = true :=
  Snake9.LocalRup.prove_clause [c41, c178, c176, c116, c179, c96, c20, c21, c164, c107, c109, c113, c23] c180 (by decide) p (sat_cons (step41 p h) (sat_cons (step178 p h) (sat_cons (step176 p h) (sat_cons (step116 p h) (sat_cons (step179 p h) (sat_cons (step96 p h) (sat_cons (step20 p h) (sat_cons (step21 p h) (sat_cons (step164 p h) (sat_cons (step107 p h) (sat_cons (step109 p h) (sat_cons (step113 p h) (sat_cons (step23 p h) (sat_nil p))))))))))))))
def c181 : List Lit := [(1340, true)]
theorem step181 (p : Nat → Bool) (h : Constraints p) : clause p c181 = true :=
  Snake9.LocalRup.prove_clause [c180, c117] c181 (by decide) p (sat_cons (step180 p h) (sat_cons (step117 p h) (sat_nil p)))
def c182 : List Lit := [(1332, false)]
theorem step182 (p : Nat → Bool) (h : Constraints p) : clause p c182 = true :=
  Snake9.LocalRup.prove_clause [c180, c174, c119] c182 (by decide) p (sat_cons (step180 p h) (sat_cons (step174 p h) (sat_cons (step119 p h) (sat_nil p))))
def c183 : List Lit := [(1363, true)]
theorem step183 (p : Nat → Bool) (h : Constraints p) : clause p c183 = true :=
  Snake9.LocalRup.prove_clause [c181, c167, c130] c183 (by decide) p (sat_cons (step181 p h) (sat_cons (step167 p h) (sat_cons (step130 p h) (sat_nil p))))
def c184 : List Lit := [(1330, false)]
theorem step184 (p : Nat → Bool) (h : Constraints p) : clause p c184 = true :=
  Snake9.LocalRup.prove_clause [c182, c110] c184 (by decide) p (sat_cons (step182 p h) (sat_cons (step110 p h) (sat_nil p)))
def c185 : List Lit := [(77, true)]
theorem step185 (p : Nat → Bool) (h : Constraints p) : clause p c185 = true :=
  Snake9.LocalRup.prove_clause [c182, c112] c185 (by decide) p (sat_cons (step182 p h) (sat_cons (step112 p h) (sat_nil p)))
def c186 : List Lit := [(1324, false)]
theorem step186 (p : Nat → Bool) (h : Constraints p) : clause p c186 = true :=
  Snake9.LocalRup.prove_clause [c183, c171, c134] c186 (by decide) p (sat_cons (step183 p h) (sat_cons (step171 p h) (sat_cons (step134 p h) (sat_nil p))))
def c187 : List Lit := [(78, true)]
theorem step187 (p : Nat → Bool) (h : Constraints p) : clause p c187 = true :=
  Snake9.LocalRup.prove_clause [c184, c108] c187 (by decide) p (sat_cons (step184 p h) (sat_cons (step108 p h) (sat_nil p)))
def c188 : List Lit := [(80, true)]
theorem step188 (p : Nat → Bool) (h : Constraints p) : clause p c188 = true :=
  Snake9.LocalRup.prove_clause [c185, c42, c22] c188 (by decide) p (sat_cons (step185 p h) (sat_cons (step42 p h) (sat_cons (step22 p h) (sat_nil p))))
def c189 : List Lit := [(1317, false)]
theorem step189 (p : Nat → Bool) (h : Constraints p) : clause p c189 = true :=
  Snake9.LocalRup.prove_clause [c186, c163, c105] c189 (by decide) p (sat_cons (step186 p h) (sat_cons (step163 p h) (sat_cons (step105 p h) (sat_nil p))))
def c190 : List Lit := [(76, false)]
theorem step190 (p : Nat → Bool) (h : Constraints p) : clause p c190 = true :=
  Snake9.LocalRup.prove_clause [c187, c185, c188, c23] c190 (by decide) p (sat_cons (step187 p h) (sat_cons (step185 p h) (sat_cons (step188 p h) (sat_cons (step23 p h) (sat_nil p)))))
def c191 : List Lit := [(1313, false)]
theorem step191 (p : Nat → Bool) (h : Constraints p) : clause p c191 = true :=
  Snake9.LocalRup.prove_clause [c189, c154] c191 (by decide) p (sat_cons (step189 p h) (sat_cons (step154 p h) (sat_nil p)))
def c192 : List Lit := [(1311, true)]
theorem step192 (p : Nat → Bool) (h : Constraints p) : clause p c192 = true :=
  Snake9.LocalRup.prove_clause [c190, c96] c192 (by decide) p (sat_cons (step190 p h) (sat_cons (step96 p h) (sat_nil p)))
def c193 : List Lit := []
theorem step193 (p : Nat → Bool) (h : Constraints p) : clause p c193 = true :=
  Snake9.LocalRup.prove_clause [c192, c191, c98] c193 (by decide) p (sat_cons (step192 p h) (sat_cons (step191 p h) (sat_cons (step98 p h) (sat_nil p))))
end B112E184
