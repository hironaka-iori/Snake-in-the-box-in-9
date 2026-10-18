import B112E185Part0006
namespace B112E185
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1245 : List Lit := [(901, true)]
theorem step1245 (p : Nat → Bool) (h : Constraints p) : clause p c1245 = true :=
  Snake9.LocalRup.prove_clause [c1244, c855] c1245 (by decide) p (sat_cons (step1244 p h) (sat_cons (step855 p h) (sat_nil p)))
def c1246 : List Lit := [(802, true), (840, true)]
theorem step1246 (p : Nat → Bool) (h : Constraints p) : clause p c1246 = true :=
  Snake9.LocalRup.prove_clause [c1236, c848, c1121, c1132] c1246 (by decide) p (sat_cons (step1236 p h) (sat_cons (step848 p h) (sat_cons (step1121 p h) (sat_cons (step1132 p h) (sat_nil p)))))
def c1247 : List Lit := [(43, false), (840, true), (802, false)]
theorem step1247 (p : Nat → Bool) (h : Constraints p) : clause p c1247 = true :=
  Snake9.LocalRup.prove_clause [c1224, c536, c843, c579, c573, c1185, c582, c844, c539, c537, c531, c532, c125, c121, c556, c557, c530, c571, c551, c562, c1004, c559] c1247 (by decide) p (sat_cons (step1224 p h) (sat_cons (step536 p h) (sat_cons (step843 p h) (sat_cons (step579 p h) (sat_cons (step573 p h) (sat_cons (step1185 p h) (sat_cons (step582 p h) (sat_cons (step844 p h) (sat_cons (step539 p h) (sat_cons (step537 p h) (sat_cons (step531 p h) (sat_cons (step532 p h) (sat_cons (step125 p h) (sat_cons (step121 p h) (sat_cons (step556 p h) (sat_cons (step557 p h) (sat_cons (step530 p h) (sat_cons (step571 p h) (sat_cons (step551 p h) (sat_cons (step562 p h) (sat_cons (step1004 p h) (sat_cons (step559 p h) (sat_nil p)))))))))))))))))))))))
def c1248 : List Lit := [(840, true), (802, false)]
theorem step1248 (p : Nat → Bool) (h : Constraints p) : clause p c1248 = true :=
  Snake9.LocalRup.prove_clause [c536, c843, c579, c568, c573, c563, c555, c1247, c552, c1133, c553, c554, c557, c570, c582, c844, c539, c537, c531, c532, c979, c1004, c530] c1248 (by decide) p (sat_cons (step536 p h) (sat_cons (step843 p h) (sat_cons (step579 p h) (sat_cons (step568 p h) (sat_cons (step573 p h) (sat_cons (step563 p h) (sat_cons (step555 p h) (sat_cons (step1247 p h) (sat_cons (step552 p h) (sat_cons (step1133 p h) (sat_cons (step553 p h) (sat_cons (step554 p h) (sat_cons (step557 p h) (sat_cons (step570 p h) (sat_cons (step582 p h) (sat_cons (step844 p h) (sat_cons (step539 p h) (sat_cons (step537 p h) (sat_cons (step531 p h) (sat_cons (step532 p h) (sat_cons (step979 p h) (sat_cons (step1004 p h) (sat_cons (step530 p h) (sat_nil p))))))))))))))))))))))))
def c1249 : List Lit := [(910, true)]
theorem step1249 (p : Nat → Bool) (h : Constraints p) : clause p c1249 = true :=
  Snake9.LocalRup.prove_clause [c1127, c1245, c1202, c1242, c1201, c663, c665, c856, c628, c626, c639, c608, c616, c602, c613, c942] c1249 (by decide) p (sat_cons (step1127 p h) (sat_cons (step1245 p h) (sat_cons (step1202 p h) (sat_cons (step1242 p h) (sat_cons (step1201 p h) (sat_cons (step663 p h) (sat_cons (step665 p h) (sat_cons (step856 p h) (sat_cons (step628 p h) (sat_cons (step626 p h) (sat_cons (step639 p h) (sat_cons (step608 p h) (sat_cons (step616 p h) (sat_cons (step602 p h) (sat_cons (step613 p h) (sat_cons (step942 p h) (sat_nil p)))))))))))))))))
def c1250 : List Lit := [(981, true)]
theorem step1250 (p : Nat → Bool) (h : Constraints p) : clause p c1250 = true :=
  Snake9.LocalRup.prove_clause [c1249, c1098] c1250 (by decide) p (sat_cons (step1249 p h) (sat_cons (step1098 p h) (sat_nil p)))
def c1251 : List Lit := [(859, false)]
theorem step1251 (p : Nat → Bool) (h : Constraints p) : clause p c1251 = true :=
  Snake9.LocalRup.prove_clause [c1250, c1103] c1251 (by decide) p (sat_cons (step1250 p h) (sat_cons (step1103 p h) (sat_nil p)))
def c1252 : List Lit := [(840, false)]
theorem step1252 (p : Nat → Bool) (h : Constraints p) : clause p c1252 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1243, c591] c1252 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1243 p h) (sat_cons (step591 p h) (sat_nil p))))
def c1253 : List Lit := [(802, true)]
theorem step1253 (p : Nat → Bool) (h : Constraints p) : clause p c1253 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1246] c1253 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1246 p h) (sat_nil p)))
def c1254 : List Lit := []
theorem step1254 (p : Nat → Bool) (h : Constraints p) : clause p c1254 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1253, c1248] c1254 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1253 p h) (sat_cons (step1248 p h) (sat_nil p))))
end B112E185
