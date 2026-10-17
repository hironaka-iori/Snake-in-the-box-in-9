import B112E158Part0072
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6242 : List Lit := [(58, false)]
theorem step6242 (p : Nat → Bool) (h : Constraints p) : clause p c6242 = true :=
  Snake9.LocalRup.prove_clause [c6236, c6223, c6235, c2055] c6242 (by decide) p (sat_cons (step6236 p h) (sat_cons (step6223 p h) (sat_cons (step6235 p h) (sat_cons (step2055 p h) (sat_nil p)))))
def c6243 : List Lit := [(28, false)]
theorem step6243 (p : Nat → Bool) (h : Constraints p) : clause p c6243 = true :=
  Snake9.LocalRup.prove_clause [c6236, c6235, c6223, c4322] c6243 (by decide) p (sat_cons (step6236 p h) (sat_cons (step6235 p h) (sat_cons (step6223 p h) (sat_cons (step4322 p h) (sat_nil p)))))
def c6244 : List Lit := [(1585, false)]
theorem step6244 (p : Nat → Bool) (h : Constraints p) : clause p c6244 = true :=
  Snake9.LocalRup.prove_clause [c6237, c6233, c1337] c6244 (by decide) p (sat_cons (step6237 p h) (sat_cons (step6233 p h) (sat_cons (step1337 p h) (sat_nil p))))
def c6245 : List Lit := [(80, true)]
theorem step6245 (p : Nat → Bool) (h : Constraints p) : clause p c6245 = true :=
  Snake9.LocalRup.prove_clause [c6238, c1315] c6245 (by decide) p (sat_cons (step6238 p h) (sat_cons (step1315 p h) (sat_nil p)))
def c6246 : List Lit := [(35, true)]
theorem step6246 (p : Nat → Bool) (h : Constraints p) : clause p c6246 = true :=
  Snake9.LocalRup.prove_clause [c6239, c6204, c2460] c6246 (by decide) p (sat_cons (step6239 p h) (sat_cons (step6204 p h) (sat_cons (step2460 p h) (sat_nil p))))
def c6247 : List Lit := [(52, false)]
theorem step6247 (p : Nat → Bool) (h : Constraints p) : clause p c6247 = true :=
  Snake9.LocalRup.prove_clause [c6240, c6225, c6218, c6190] c6247 (by decide) p (sat_cons (step6240 p h) (sat_cons (step6225 p h) (sat_cons (step6218 p h) (sat_cons (step6190 p h) (sat_nil p)))))
def c6248 : List Lit := [(1495, true)]
theorem step6248 (p : Nat → Bool) (h : Constraints p) : clause p c6248 = true :=
  Snake9.LocalRup.prove_clause [c6241, c1139] c6248 (by decide) p (sat_cons (step6241 p h) (sat_cons (step1139 p h) (sat_nil p)))
def c6249 : List Lit := [(1506, true)]
theorem step6249 (p : Nat → Bool) (h : Constraints p) : clause p c6249 = true :=
  Snake9.LocalRup.prove_clause [c6242, c5964, c1158] c6249 (by decide) p (sat_cons (step6242 p h) (sat_cons (step5964 p h) (sat_cons (step1158 p h) (sat_nil p))))
def c6250 : List Lit := [(60, false)]
theorem step6250 (p : Nat → Bool) (h : Constraints p) : clause p c6250 = true :=
  Snake9.LocalRup.prove_clause [c6243, c6242, c6241, c6223, c6225, c6230, c6195] c6250 (by decide) p (sat_cons (step6243 p h) (sat_cons (step6242 p h) (sat_cons (step6241 p h) (sat_cons (step6223 p h) (sat_cons (step6225 p h) (sat_cons (step6230 p h) (sat_cons (step6195 p h) (sat_nil p))))))))
def c6251 : List Lit := [(1581, false)]
theorem step6251 (p : Nat → Bool) (h : Constraints p) : clause p c6251 = true :=
  Snake9.LocalRup.prove_clause [c6244, c1329] c6251 (by decide) p (sat_cons (step6244 p h) (sat_cons (step1329 p h) (sat_nil p)))
def c6252 : List Lit := [(81, true)]
theorem step6252 (p : Nat → Bool) (h : Constraints p) : clause p c6252 = true :=
  Snake9.LocalRup.prove_clause [c6245, c1844] c6252 (by decide) p (sat_cons (step6245 p h) (sat_cons (step1844 p h) (sat_nil p)))
def c6253 : List Lit := [(38, false)]
theorem step6253 (p : Nat → Bool) (h : Constraints p) : clause p c6253 = true :=
  Snake9.LocalRup.prove_clause [c6246, c6230, c6158, c214] c6253 (by decide) p (sat_cons (step6246 p h) (sat_cons (step6230 p h) (sat_cons (step6158 p h) (sat_cons (step214 p h) (sat_nil p)))))
def c6254 : List Lit := [(51, false)]
theorem step6254 (p : Nat → Bool) (h : Constraints p) : clause p c6254 = true :=
  Snake9.LocalRup.prove_clause [c6246, c6247, c6230, c2108] c6254 (by decide) p (sat_cons (step6246 p h) (sat_cons (step6247 p h) (sat_cons (step6230 p h) (sat_cons (step2108 p h) (sat_nil p)))))
def c6255 : List Lit := [(1500, true)]
theorem step6255 (p : Nat → Bool) (h : Constraints p) : clause p c6255 = true :=
  Snake9.LocalRup.prove_clause [c6248, c6171, c1148] c6255 (by decide) p (sat_cons (step6248 p h) (sat_cons (step6171 p h) (sat_cons (step1148 p h) (sat_nil p))))
def c6256 : List Lit := [(1509, true)]
theorem step6256 (p : Nat → Bool) (h : Constraints p) : clause p c6256 = true :=
  Snake9.LocalRup.prove_clause [c6249, c5530] c6256 (by decide) p (sat_cons (step6249 p h) (sat_cons (step5530 p h) (sat_nil p)))
def c6257 : List Lit := [(84, true)]
theorem step6257 (p : Nat → Bool) (h : Constraints p) : clause p c6257 = true :=
  Snake9.LocalRup.prove_clause [c6251, c1321] c6257 (by decide) p (sat_cons (step6251 p h) (sat_cons (step1321 p h) (sat_nil p)))
def c6258 : List Lit := [(1525, true)]
theorem step6258 (p : Nat → Bool) (h : Constraints p) : clause p c6258 = true :=
  Snake9.LocalRup.prove_clause [c6254, c6179, c6248, c6256, c6255, c5444] c6258 (by decide) p (sat_cons (step6254 p h) (sat_cons (step6179 p h) (sat_cons (step6248 p h) (sat_cons (step6256 p h) (sat_cons (step6255 p h) (sat_cons (step5444 p h) (sat_nil p)))))))
def c6259 : List Lit := [(24, false)]
theorem step6259 (p : Nat → Bool) (h : Constraints p) : clause p c6259 = true :=
  Snake9.LocalRup.prove_clause [c6257, c6245, c6252, c566] c6259 (by decide) p (sat_cons (step6257 p h) (sat_cons (step6245 p h) (sat_cons (step6252 p h) (sat_cons (step566 p h) (sat_nil p)))))
def c6260 : List Lit := [(1464, false)]
theorem step6260 (p : Nat → Bool) (h : Constraints p) : clause p c6260 = true :=
  Snake9.LocalRup.prove_clause [c6258, c6225, c1249] c6260 (by decide) p (sat_cons (step6258 p h) (sat_cons (step6225 p h) (sat_cons (step1249 p h) (sat_nil p))))
def c6261 : List Lit := [(4, false)]
theorem step6261 (p : Nat → Bool) (h : Constraints p) : clause p c6261 = true :=
  Snake9.LocalRup.prove_clause [c6260, c6259, c4007] c6261 (by decide) p (sat_cons (step6260 p h) (sat_cons (step6259 p h) (sat_cons (step4007 p h) (sat_nil p))))
def c6262 : List Lit := [(1456, false)]
theorem step6262 (p : Nat → Bool) (h : Constraints p) : clause p c6262 = true :=
  Snake9.LocalRup.prove_clause [c6260, c6160, c1083] c6262 (by decide) p (sat_cons (step6260 p h) (sat_cons (step6160 p h) (sat_cons (step1083 p h) (sat_nil p))))
def c6263 : List Lit := [(36, true)]
theorem step6263 (p : Nat → Bool) (h : Constraints p) : clause p c6263 = true :=
  Snake9.LocalRup.prove_clause [c6261, c6253, c6158, c6240, c6250, c1792] c6263 (by decide) p (sat_cons (step6261 p h) (sat_cons (step6253 p h) (sat_cons (step6158 p h) (sat_cons (step6240 p h) (sat_cons (step6250 p h) (sat_cons (step1792 p h) (sat_nil p)))))))
def c6264 : List Lit := [(1449, false)]
theorem step6264 (p : Nat → Bool) (h : Constraints p) : clause p c6264 = true :=
  Snake9.LocalRup.prove_clause [c6262, c2047] c6264 (by decide) p (sat_cons (step6262 p h) (sat_cons (step2047 p h) (sat_nil p)))
def c6265 : List Lit := [(30, false)]
theorem step6265 (p : Nat → Bool) (h : Constraints p) : clause p c6265 = true :=
  Snake9.LocalRup.prove_clause [c6263, c6158, c6246, c177] c6265 (by decide) p (sat_cons (step6263 p h) (sat_cons (step6158 p h) (sat_cons (step6246 p h) (sat_cons (step177 p h) (sat_nil p)))))
def c6266 : List Lit := []
theorem step6266 (p : Nat → Bool) (h : Constraints p) : clause p c6266 = true :=
  Snake9.LocalRup.prove_clause [c6264, c6265, c6243, c1047] c6266 (by decide) p (sat_cons (step6264 p h) (sat_cons (step6265 p h) (sat_cons (step6243 p h) (sat_cons (step1047 p h) (sat_nil p)))))
end B112E158
