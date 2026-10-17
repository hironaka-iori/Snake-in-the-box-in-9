import B112E242Part0000
namespace B112E242
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c256 : List Lit := [(1260, false)]
theorem step256 (p : Nat → Bool) (h : Constraints p) : clause p c256 = true :=
  Snake9.LocalRup.prove_clause [c255, c237, c115] c256 (by decide) p (sat_cons (step255 p h) (sat_cons (step237 p h) (sat_cons (step115 p h) (sat_nil p))))
def c257 : List Lit := [(1257, false), (46, false)]
theorem step257 (p : Nat → Bool) (h : Constraints p) : clause p c257 = true :=
  Snake9.LocalRup.prove_clause [c256, c237, c228, c236, c253, c190, c235, c233, c46, c104, c106, c114, c117, c120, c123, c188, c94, c184, c92, c225, c84, c175, c246, c16, c81, c82, c83, c4, c91, c88, c86, c87, c5] c257 (by decide) p (sat_cons (step256 p h) (sat_cons (step237 p h) (sat_cons (step228 p h) (sat_cons (step236 p h) (sat_cons (step253 p h) (sat_cons (step190 p h) (sat_cons (step235 p h) (sat_cons (step233 p h) (sat_cons (step46 p h) (sat_cons (step104 p h) (sat_cons (step106 p h) (sat_cons (step114 p h) (sat_cons (step117 p h) (sat_cons (step120 p h) (sat_cons (step123 p h) (sat_cons (step188 p h) (sat_cons (step94 p h) (sat_cons (step184 p h) (sat_cons (step92 p h) (sat_cons (step225 p h) (sat_cons (step84 p h) (sat_cons (step175 p h) (sat_cons (step246 p h) (sat_cons (step16 p h) (sat_cons (step81 p h) (sat_cons (step82 p h) (sat_cons (step83 p h) (sat_cons (step4 p h) (sat_cons (step91 p h) (sat_cons (step88 p h) (sat_cons (step86 p h) (sat_cons (step87 p h) (sat_cons (step5 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c258 : List Lit := [(41, false), (46, false)]
theorem step258 (p : Nat → Bool) (h : Constraints p) : clause p c258 = true :=
  Snake9.LocalRup.prove_clause [c51, c62, c243, c242, c233, c202, c190, c61, c239, c235, c63, c45, c257, c102, c13, c103, c18, c15, c245, c246, c81, c37, c38, c175, c178, c43, c225, c182, c160, c66, c184, c223, c159, c67, c188, c221, c34, c65, c122, c153, c94, c36, c92, c41, c85, c40, c3, c11] c258 (by decide) p (sat_cons (step51 p h) (sat_cons (step62 p h) (sat_cons (step243 p h) (sat_cons (step242 p h) (sat_cons (step233 p h) (sat_cons (step202 p h) (sat_cons (step190 p h) (sat_cons (step61 p h) (sat_cons (step239 p h) (sat_cons (step235 p h) (sat_cons (step63 p h) (sat_cons (step45 p h) (sat_cons (step257 p h) (sat_cons (step102 p h) (sat_cons (step13 p h) (sat_cons (step103 p h) (sat_cons (step18 p h) (sat_cons (step15 p h) (sat_cons (step245 p h) (sat_cons (step246 p h) (sat_cons (step81 p h) (sat_cons (step37 p h) (sat_cons (step38 p h) (sat_cons (step175 p h) (sat_cons (step178 p h) (sat_cons (step43 p h) (sat_cons (step225 p h) (sat_cons (step182 p h) (sat_cons (step160 p h) (sat_cons (step66 p h) (sat_cons (step184 p h) (sat_cons (step223 p h) (sat_cons (step159 p h) (sat_cons (step67 p h) (sat_cons (step188 p h) (sat_cons (step221 p h) (sat_cons (step34 p h) (sat_cons (step65 p h) (sat_cons (step122 p h) (sat_cons (step153 p h) (sat_cons (step94 p h) (sat_cons (step36 p h) (sat_cons (step92 p h) (sat_cons (step41 p h) (sat_cons (step85 p h) (sat_cons (step40 p h) (sat_cons (step3 p h) (sat_cons (step11 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c259 : List Lit := [(46, false)]
theorem step259 (p : Nat → Bool) (h : Constraints p) : clause p c259 = true :=
  Snake9.LocalRup.prove_clause [c237, c228, c236, c253, c190, c235, c233, c46, c257, c102, c258, c105, c114, c117, c120, c123, c188, c94, c184, c92, c225, c84, c175, c246, c17, c81, c82, c83, c4, c91, c88, c86, c87, c5] c259 (by decide) p (sat_cons (step237 p h) (sat_cons (step228 p h) (sat_cons (step236 p h) (sat_cons (step253 p h) (sat_cons (step190 p h) (sat_cons (step235 p h) (sat_cons (step233 p h) (sat_cons (step46 p h) (sat_cons (step257 p h) (sat_cons (step102 p h) (sat_cons (step258 p h) (sat_cons (step105 p h) (sat_cons (step114 p h) (sat_cons (step117 p h) (sat_cons (step120 p h) (sat_cons (step123 p h) (sat_cons (step188 p h) (sat_cons (step94 p h) (sat_cons (step184 p h) (sat_cons (step92 p h) (sat_cons (step225 p h) (sat_cons (step84 p h) (sat_cons (step175 p h) (sat_cons (step246 p h) (sat_cons (step17 p h) (sat_cons (step81 p h) (sat_cons (step82 p h) (sat_cons (step83 p h) (sat_cons (step4 p h) (sat_cons (step91 p h) (sat_cons (step88 p h) (sat_cons (step86 p h) (sat_cons (step87 p h) (sat_cons (step5 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c260 : List Lit := [(60, true)]
theorem step260 (p : Nat → Bool) (h : Constraints p) : clause p c260 = true :=
  Snake9.LocalRup.prove_clause [c259, c248] c260 (by decide) p (sat_cons (step259 p h) (sat_cons (step248 p h) (sat_nil p)))
def c261 : List Lit := [(44, false)]
theorem step261 (p : Nat → Bool) (h : Constraints p) : clause p c261 = true :=
  Snake9.LocalRup.prove_clause [c259, c51, c12] c261 (by decide) p (sat_cons (step259 p h) (sat_cons (step51 p h) (sat_cons (step12 p h) (sat_nil p))))
def c262 : List Lit := [(53, false)]
theorem step262 (p : Nat → Bool) (h : Constraints p) : clause p c262 = true :=
  Snake9.LocalRup.prove_clause [c260, c27, c25] c262 (by decide) p (sat_cons (step260 p h) (sat_cons (step27 p h) (sat_cons (step25 p h) (sat_nil p))))
def c263 : List Lit := [(1257, true)]
theorem step263 (p : Nat → Bool) (h : Constraints p) : clause p c263 = true :=
  Snake9.LocalRup.prove_clause [c261, c102] c263 (by decide) p (sat_cons (step261 p h) (sat_cons (step102 p h) (sat_nil p)))
def c264 : List Lit := [(52, false)]
theorem step264 (p : Nat → Bool) (h : Constraints p) : clause p c264 = true :=
  Snake9.LocalRup.prove_clause [c262, c54, c21] c264 (by decide) p (sat_cons (step262 p h) (sat_cons (step54 p h) (sat_cons (step21 p h) (sat_nil p))))
def c265 : List Lit := [(1259, true)]
theorem step265 (p : Nat → Bool) (h : Constraints p) : clause p c265 = true :=
  Snake9.LocalRup.prove_clause [c263, c104] c265 (by decide) p (sat_cons (step263 p h) (sat_cons (step104 p h) (sat_nil p)))
def c266 : List Lit := [(1309, true)]
theorem step266 (p : Nat → Bool) (h : Constraints p) : clause p c266 = true :=
  Snake9.LocalRup.prove_clause [c264, c230, c127] c266 (by decide) p (sat_cons (step264 p h) (sat_cons (step230 p h) (sat_cons (step127 p h) (sat_nil p))))
def c267 : List Lit := [(1272, true)]
theorem step267 (p : Nat → Bool) (h : Constraints p) : clause p c267 = true :=
  Snake9.LocalRup.prove_clause [c265, c237, c114] c267 (by decide) p (sat_cons (step265 p h) (sat_cons (step237 p h) (sat_cons (step114 p h) (sat_nil p))))
def c268 : List Lit := [(1350, true)]
theorem step268 (p : Nat → Bool) (h : Constraints p) : clause p c268 = true :=
  Snake9.LocalRup.prove_clause [c266, c247] c268 (by decide) p (sat_cons (step266 p h) (sat_cons (step247 p h) (sat_nil p)))
def c269 : List Lit := [(1281, true)]
theorem step269 (p : Nat → Bool) (h : Constraints p) : clause p c269 = true :=
  Snake9.LocalRup.prove_clause [c267, c228, c117] c269 (by decide) p (sat_cons (step267 p h) (sat_cons (step228 p h) (sat_cons (step117 p h) (sat_nil p))))
def c270 : List Lit := [(1421, true)]
theorem step270 (p : Nat → Bool) (h : Constraints p) : clause p c270 = true :=
  Snake9.LocalRup.prove_clause [c268, c251, c186] c270 (by decide) p (sat_cons (step268 p h) (sat_cons (step251 p h) (sat_cons (step186 p h) (sat_nil p))))
def c271 : List Lit := [(1297, true)]
theorem step271 (p : Nat → Bool) (h : Constraints p) : clause p c271 = true :=
  Snake9.LocalRup.prove_clause [c269, c236, c120] c271 (by decide) p (sat_cons (step269 p h) (sat_cons (step236 p h) (sat_cons (step120 p h) (sat_nil p))))
def c272 : List Lit := []
theorem step272 (p : Nat → Bool) (h : Constraints p) : clause p c272 = true :=
  Snake9.LocalRup.prove_clause [c271, c270, c190, c188] c272 (by decide) p (sat_cons (step271 p h) (sat_cons (step270 p h) (sat_cons (step190 p h) (sat_cons (step188 p h) (sat_nil p)))))
end B112E242
