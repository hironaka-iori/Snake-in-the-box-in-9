import B112E118Inputs
namespace B112E118
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c126 : List Lit := [(54, false)]
theorem step126 (p : Nat → Bool) (h : Constraints p) : clause p c126 = true :=
  Snake9.LocalRup.prove_clause [c34, c12] c126 (by decide) p (sat_cons (step34 p h) (sat_cons (step12 p h) (sat_nil p)))
def c127 : List Lit := [(1231, true)]
theorem step127 (p : Nat → Bool) (h : Constraints p) : clause p c127 = true :=
  Snake9.LocalRup.prove_clause [c126, c75] c127 (by decide) p (sat_cons (step126 p h) (sat_cons (step75 p h) (sat_nil p)))
def c128 : List Lit := [(1233, true)]
theorem step128 (p : Nat → Bool) (h : Constraints p) : clause p c128 = true :=
  Snake9.LocalRup.prove_clause [c127, c76] c128 (by decide) p (sat_cons (step127 p h) (sat_cons (step76 p h) (sat_nil p)))
def c129 : List Lit := [(1241, true)]
theorem step129 (p : Nat → Bool) (h : Constraints p) : clause p c129 = true :=
  Snake9.LocalRup.prove_clause [c128, c77] c129 (by decide) p (sat_cons (step128 p h) (sat_cons (step77 p h) (sat_nil p)))
def c130 : List Lit := [(1257, false), (1264, true)]
theorem step130 (p : Nat → Bool) (h : Constraints p) : clause p c130 = true :=
  Snake9.LocalRup.prove_clause [c129, c90] c130 (by decide) p (sat_cons (step129 p h) (sat_cons (step90 p h) (sat_nil p)))
def c131 : List Lit := [(1258, false), (1265, true)]
theorem step131 (p : Nat → Bool) (h : Constraints p) : clause p c131 = true :=
  Snake9.LocalRup.prove_clause [c129, c91] c131 (by decide) p (sat_cons (step129 p h) (sat_cons (step91 p h) (sat_nil p)))
def c132 : List Lit := [(1259, false), (1266, true)]
theorem step132 (p : Nat → Bool) (h : Constraints p) : clause p c132 = true :=
  Snake9.LocalRup.prove_clause [c129, c92] c132 (by decide) p (sat_cons (step129 p h) (sat_cons (step92 p h) (sat_nil p)))
def c133 : List Lit := [(1192, true)]
theorem step133 (p : Nat → Bool) (h : Constraints p) : clause p c133 = true :=
  Snake9.LocalRup.prove_clause [c32, c62, c63, c60, c61, c9, c10] c133 (by decide) p (sat_cons (step32 p h) (sat_cons (step62 p h) (sat_cons (step63 p h) (sat_cons (step60 p h) (sat_cons (step61 p h) (sat_cons (step9 p h) (sat_cons (step10 p h) (sat_nil p))))))))
def c134 : List Lit := [(1195, true)]
theorem step134 (p : Nat → Bool) (h : Constraints p) : clause p c134 = true :=
  Snake9.LocalRup.prove_clause [c133, c64] c134 (by decide) p (sat_cons (step133 p h) (sat_cons (step64 p h) (sat_nil p)))
def c135 : List Lit := [(1217, true)]
theorem step135 (p : Nat → Bool) (h : Constraints p) : clause p c135 = true :=
  Snake9.LocalRup.prove_clause [c134, c69] c135 (by decide) p (sat_cons (step134 p h) (sat_cons (step69 p h) (sat_nil p)))
def c136 : List Lit := [(1224, true)]
theorem step136 (p : Nat → Bool) (h : Constraints p) : clause p c136 = true :=
  Snake9.LocalRup.prove_clause [c135, c72] c136 (by decide) p (sat_cons (step135 p h) (sat_cons (step72 p h) (sat_nil p)))
def c137 : List Lit := [(1314, false)]
theorem step137 (p : Nat → Bool) (h : Constraints p) : clause p c137 = true :=
  Snake9.LocalRup.prove_clause [c136, c125, c123] c137 (by decide) p (sat_cons (step136 p h) (sat_cons (step125 p h) (sat_cons (step123 p h) (sat_nil p))))
def c138 : List Lit := [(1254, true), (1225, true)]
theorem step138 (p : Nat → Bool) (h : Constraints p) : clause p c138 = true :=
  Snake9.LocalRup.prove_clause [c28, c133, c135, c74, c56, c44, c43, c42, c73, c71, c65, c59, c55, c54, c48, c41, c1, c58, c57, c53, c51, c50, c8, c2, c84, c85, c83, c15] c138 (by decide) p (sat_cons (step28 p h) (sat_cons (step133 p h) (sat_cons (step135 p h) (sat_cons (step74 p h) (sat_cons (step56 p h) (sat_cons (step44 p h) (sat_cons (step43 p h) (sat_cons (step42 p h) (sat_cons (step73 p h) (sat_cons (step71 p h) (sat_cons (step65 p h) (sat_cons (step59 p h) (sat_cons (step55 p h) (sat_cons (step54 p h) (sat_cons (step48 p h) (sat_cons (step41 p h) (sat_cons (step1 p h) (sat_cons (step58 p h) (sat_cons (step57 p h) (sat_cons (step53 p h) (sat_cons (step51 p h) (sat_cons (step50 p h) (sat_cons (step8 p h) (sat_cons (step2 p h) (sat_cons (step84 p h) (sat_cons (step85 p h) (sat_cons (step83 p h) (sat_cons (step15 p h) (sat_nil p)))))))))))))))))))))))))))))
def c139 : List Lit := [(63, false), (65, false), (64, false)]
theorem step139 (p : Nat → Bool) (h : Constraints p) : clause p c139 = true :=
  Snake9.LocalRup.prove_clause [c35, c14, c13] c139 (by decide) p (sat_cons (step35 p h) (sat_cons (step14 p h) (sat_cons (step13 p h) (sat_nil p))))
def c140 : List Lit := [(1249, true)]
theorem step140 (p : Nat → Bool) (h : Constraints p) : clause p c140 = true :=
  Snake9.LocalRup.prove_clause [c80, c81, c78, c79, c139] c140 (by decide) p (sat_cons (step80 p h) (sat_cons (step81 p h) (sat_cons (step78 p h) (sat_cons (step79 p h) (sat_cons (step139 p h) (sat_nil p))))))
def c141 : List Lit := [(1277, true), (79, false), (68, false)]
theorem step141 (p : Nat → Bool) (h : Constraints p) : clause p c141 = true :=
  Snake9.LocalRup.prove_clause [c38, c39, c101, c102, c100, c23, c25, c20] c141 (by decide) p (sat_cons (step38 p h) (sat_cons (step39 p h) (sat_cons (step101 p h) (sat_cons (step102 p h) (sat_cons (step100 p h) (sat_cons (step23 p h) (sat_cons (step25 p h) (sat_cons (step20 p h) (sat_nil p)))))))))
def c142 : List Lit := [(94, false), (96, false), (95, false)]
theorem step142 (p : Nat → Bool) (h : Constraints p) : clause p c142 = true :=
  Snake9.LocalRup.prove_clause [c40, c27, c26] c142 (by decide) p (sat_cons (step40 p h) (sat_cons (step27 p h) (sat_cons (step26 p h) (sat_nil p))))
def c143 : List Lit := [(1293, true)]
theorem step143 (p : Nat → Bool) (h : Constraints p) : clause p c143 = true :=
  Snake9.LocalRup.prove_clause [c110, c111, c108, c109, c142] c143 (by decide) p (sat_cons (step110 p h) (sat_cons (step111 p h) (sat_cons (step108 p h) (sat_cons (step109 p h) (sat_cons (step142 p h) (sat_nil p))))))
def c144 : List Lit := [(1296, true)]
theorem step144 (p : Nat → Bool) (h : Constraints p) : clause p c144 = true :=
  Snake9.LocalRup.prove_clause [c143, c112] c144 (by decide) p (sat_cons (step143 p h) (sat_cons (step112 p h) (sat_nil p)))
def c145 : List Lit := [(1225, true)]
theorem step145 (p : Nat → Bool) (h : Constraints p) : clause p c145 = true :=
  Snake9.LocalRup.prove_clause [c135, c134, c33, c31, c29, c30, c140, c137, c143, c144, c73, c74, c70, c55, c56, c68, c53, c54, c44, c67, c51, c52, c47, c43, c66, c49, c45, c46, c41, c11, c7, c3, c4, c6, c5, c98, c104, c138, c88, c131, c121, c117, c113, c118, c107, c105, c21, c102] c145 (by decide) p (sat_cons (step135 p h) (sat_cons (step134 p h) (sat_cons (step33 p h) (sat_cons (step31 p h) (sat_cons (step29 p h) (sat_cons (step30 p h) (sat_cons (step140 p h) (sat_cons (step137 p h) (sat_cons (step143 p h) (sat_cons (step144 p h) (sat_cons (step73 p h) (sat_cons (step74 p h) (sat_cons (step70 p h) (sat_cons (step55 p h) (sat_cons (step56 p h) (sat_cons (step68 p h) (sat_cons (step53 p h) (sat_cons (step54 p h) (sat_cons (step44 p h) (sat_cons (step67 p h) (sat_cons (step51 p h) (sat_cons (step52 p h) (sat_cons (step47 p h) (sat_cons (step43 p h) (sat_cons (step66 p h) (sat_cons (step49 p h) (sat_cons (step45 p h) (sat_cons (step46 p h) (sat_cons (step41 p h) (sat_cons (step11 p h) (sat_cons (step7 p h) (sat_cons (step3 p h) (sat_cons (step4 p h) (sat_cons (step6 p h) (sat_cons (step5 p h) (sat_cons (step98 p h) (sat_cons (step104 p h) (sat_cons (step138 p h) (sat_cons (step88 p h) (sat_cons (step131 p h) (sat_cons (step121 p h) (sat_cons (step117 p h) (sat_cons (step113 p h) (sat_cons (step118 p h) (sat_cons (step107 p h) (sat_cons (step105 p h) (sat_cons (step21 p h) (sat_cons (step102 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c146 : List Lit := [(1257, true)]
theorem step146 (p : Nat → Bool) (h : Constraints p) : clause p c146 = true :=
  Snake9.LocalRup.prove_clause [c140, c87] c146 (by decide) p (sat_cons (step140 p h) (sat_cons (step87 p h) (sat_nil p)))
def c147 : List Lit := [(1302, true)]
theorem step147 (p : Nat → Bool) (h : Constraints p) : clause p c147 = true :=
  Snake9.LocalRup.prove_clause [c144, c114] c147 (by decide) p (sat_cons (step144 p h) (sat_cons (step114 p h) (sat_nil p)))
def c148 : List Lit := [(1313, false)]
theorem step148 (p : Nat → Bool) (h : Constraints p) : clause p c148 = true :=
  Snake9.LocalRup.prove_clause [c145, c125, c124] c148 (by decide) p (sat_cons (step145 p h) (sat_cons (step125 p h) (sat_cons (step124 p h) (sat_nil p))))
def c149 : List Lit := [(1264, true)]
theorem step149 (p : Nat → Bool) (h : Constraints p) : clause p c149 = true :=
  Snake9.LocalRup.prove_clause [c146, c130] c149 (by decide) p (sat_cons (step146 p h) (sat_cons (step130 p h) (sat_nil p)))
def c150 : List Lit := [(1266, false)]
theorem step150 (p : Nat → Bool) (h : Constraints p) : clause p c150 = true :=
  Snake9.LocalRup.prove_clause [c147, c148, c122] c150 (by decide) p (sat_cons (step147 p h) (sat_cons (step148 p h) (sat_cons (step122 p h) (sat_nil p))))
def c151 : List Lit := [(1304, false)]
theorem step151 (p : Nat → Bool) (h : Constraints p) : clause p c151 = true :=
  Snake9.LocalRup.prove_clause [c149, c148, c119] c151 (by decide) p (sat_cons (step149 p h) (sat_cons (step148 p h) (sat_cons (step119 p h) (sat_nil p))))
def c152 : List Lit := [(1259, false)]
theorem step152 (p : Nat → Bool) (h : Constraints p) : clause p c152 = true :=
  Snake9.LocalRup.prove_clause [c150, c132] c152 (by decide) p (sat_cons (step150 p h) (sat_cons (step132 p h) (sat_nil p)))
def c153 : List Lit := [(1281, false)]
theorem step153 (p : Nat → Bool) (h : Constraints p) : clause p c153 = true :=
  Snake9.LocalRup.prove_clause [c151, c144, c118] c153 (by decide) p (sat_cons (step151 p h) (sat_cons (step144 p h) (sat_cons (step118 p h) (sat_nil p))))
def c154 : List Lit := [(1255, false)]
theorem step154 (p : Nat → Bool) (h : Constraints p) : clause p c154 = true :=
  Snake9.LocalRup.prove_clause [c152, c140, c89] c154 (by decide) p (sat_cons (step152 p h) (sat_cons (step140 p h) (sat_cons (step89 p h) (sat_nil p))))
def c155 : List Lit := [(1273, false)]
theorem step155 (p : Nat → Bool) (h : Constraints p) : clause p c155 = true :=
  Snake9.LocalRup.prove_clause [c153, c106] c155 (by decide) p (sat_cons (step153 p h) (sat_cons (step106 p h) (sat_nil p)))
def c156 : List Lit := [(1271, false)]
theorem step156 (p : Nat → Bool) (h : Constraints p) : clause p c156 = true :=
  Snake9.LocalRup.prove_clause [c155, c97] c156 (by decide) p (sat_cons (step155 p h) (sat_cons (step97 p h) (sat_nil p)))
def c157 : List Lit := [(1252, false), (81, false)]
theorem step157 (p : Nat → Bool) (h : Constraints p) : clause p c157 = true :=
  Snake9.LocalRup.prove_clause [c38, c154, c140, c148, c143, c24, c84, c86, c88, c22, c131, c107, c120, c113, c115] c157 (by decide) p (sat_cons (step38 p h) (sat_cons (step154 p h) (sat_cons (step140 p h) (sat_cons (step148 p h) (sat_cons (step143 p h) (sat_cons (step24 p h) (sat_cons (step84 p h) (sat_cons (step86 p h) (sat_cons (step88 p h) (sat_cons (step22 p h) (sat_cons (step131 p h) (sat_cons (step107 p h) (sat_cons (step120 p h) (sat_cons (step113 p h) (sat_cons (step115 p h) (sat_nil p))))))))))))))))
def c158 : List Lit := [(1277, true)]
theorem step158 (p : Nat → Bool) (h : Constraints p) : clause p c158 = true :=
  Snake9.LocalRup.prove_clause [c36, c156, c155, c102, c157, c82, c16, c17, c141, c93, c95, c99, c19] c158 (by decide) p (sat_cons (step36 p h) (sat_cons (step156 p h) (sat_cons (step155 p h) (sat_cons (step102 p h) (sat_cons (step157 p h) (sat_cons (step82 p h) (sat_cons (step16 p h) (sat_cons (step17 p h) (sat_cons (step141 p h) (sat_cons (step93 p h) (sat_cons (step95 p h) (sat_cons (step99 p h) (sat_cons (step19 p h) (sat_nil p))))))))))))))
def c159 : List Lit := [(1280, true)]
theorem step159 (p : Nat → Bool) (h : Constraints p) : clause p c159 = true :=
  Snake9.LocalRup.prove_clause [c158, c103] c159 (by decide) p (sat_cons (step158 p h) (sat_cons (step103 p h) (sat_nil p)))
def c160 : List Lit := [(1272, false)]
theorem step160 (p : Nat → Bool) (h : Constraints p) : clause p c160 = true :=
  Snake9.LocalRup.prove_clause [c158, c153, c105] c160 (by decide) p (sat_cons (step158 p h) (sat_cons (step153 p h) (sat_cons (step105 p h) (sat_nil p))))
def c161 : List Lit := [(1303, true)]
theorem step161 (p : Nat → Bool) (h : Constraints p) : clause p c161 = true :=
  Snake9.LocalRup.prove_clause [c159, c144, c116] c161 (by decide) p (sat_cons (step159 p h) (sat_cons (step144 p h) (sat_cons (step116 p h) (sat_nil p))))
def c162 : List Lit := [(1270, false)]
theorem step162 (p : Nat → Bool) (h : Constraints p) : clause p c162 = true :=
  Snake9.LocalRup.prove_clause [c160, c96] c162 (by decide) p (sat_cons (step160 p h) (sat_cons (step96 p h) (sat_nil p)))
def c163 : List Lit := [(74, true)]
theorem step163 (p : Nat → Bool) (h : Constraints p) : clause p c163 = true :=
  Snake9.LocalRup.prove_clause [c160, c98] c163 (by decide) p (sat_cons (step160 p h) (sat_cons (step98 p h) (sat_nil p)))
def c164 : List Lit := [(1265, false)]
theorem step164 (p : Nat → Bool) (h : Constraints p) : clause p c164 = true :=
  Snake9.LocalRup.prove_clause [c161, c148, c120] c164 (by decide) p (sat_cons (step161 p h) (sat_cons (step148 p h) (sat_cons (step120 p h) (sat_nil p))))
def c165 : List Lit := [(75, true)]
theorem step165 (p : Nat → Bool) (h : Constraints p) : clause p c165 = true :=
  Snake9.LocalRup.prove_clause [c162, c94] c165 (by decide) p (sat_cons (step162 p h) (sat_cons (step94 p h) (sat_nil p)))
def c166 : List Lit := [(77, true)]
theorem step166 (p : Nat → Bool) (h : Constraints p) : clause p c166 = true :=
  Snake9.LocalRup.prove_clause [c163, c37, c18] c166 (by decide) p (sat_cons (step163 p h) (sat_cons (step37 p h) (sat_cons (step18 p h) (sat_nil p))))
def c167 : List Lit := [(1258, false)]
theorem step167 (p : Nat → Bool) (h : Constraints p) : clause p c167 = true :=
  Snake9.LocalRup.prove_clause [c164, c131] c167 (by decide) p (sat_cons (step164 p h) (sat_cons (step131 p h) (sat_nil p)))
def c168 : List Lit := [(73, false)]
theorem step168 (p : Nat → Bool) (h : Constraints p) : clause p c168 = true :=
  Snake9.LocalRup.prove_clause [c165, c163, c166, c19] c168 (by decide) p (sat_cons (step165 p h) (sat_cons (step163 p h) (sat_cons (step166 p h) (sat_cons (step19 p h) (sat_nil p)))))
def c169 : List Lit := [(1254, false)]
theorem step169 (p : Nat → Bool) (h : Constraints p) : clause p c169 = true :=
  Snake9.LocalRup.prove_clause [c167, c140, c88] c169 (by decide) p (sat_cons (step167 p h) (sat_cons (step140 p h) (sat_cons (step88 p h) (sat_nil p))))
def c170 : List Lit := [(1252, true)]
theorem step170 (p : Nat → Bool) (h : Constraints p) : clause p c170 = true :=
  Snake9.LocalRup.prove_clause [c168, c82] c170 (by decide) p (sat_cons (step168 p h) (sat_cons (step82 p h) (sat_nil p)))
def c171 : List Lit := []
theorem step171 (p : Nat → Bool) (h : Constraints p) : clause p c171 = true :=
  Snake9.LocalRup.prove_clause [c170, c169, c84] c171 (by decide) p (sat_cons (step170 p h) (sat_cons (step169 p h) (sat_cons (step84 p h) (sat_nil p))))
end B112E118
