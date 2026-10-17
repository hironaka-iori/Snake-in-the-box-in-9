import B112E090Part0007
namespace B112E090
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1270 : List Lit := [(66, true)]
theorem step1270 (p : Nat → Bool) (h : Constraints p) : clause p c1270 = true :=
  Snake9.LocalRup.prove_clause [c1269, c573] c1270 (by decide) p (sat_cons (step1269 p h) (sat_cons (step573 p h) (sat_nil p)))
def c1271 : List Lit := [(52, false)]
theorem step1271 (p : Nat → Bool) (h : Constraints p) : clause p c1271 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1226, c1255, c108] c1271 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1226 p h) (sat_cons (step1255 p h) (sat_cons (step108 p h) (sat_nil p)))))
def c1272 : List Lit := [(83, false)]
theorem step1272 (p : Nat → Bool) (h : Constraints p) : clause p c1272 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1255, c1226, c110] c1272 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1255 p h) (sat_cons (step1226 p h) (sat_cons (step110 p h) (sat_nil p)))))
def c1273 : List Lit := [(1367, true)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true :=
  Snake9.LocalRup.prove_clause [c1271, c507] c1273 (by decide) p (sat_cons (step1271 p h) (sat_cons (step507 p h) (sat_nil p)))
def c1274 : List Lit := [(1465, true)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true :=
  Snake9.LocalRup.prove_clause [c1272, c647] c1274 (by decide) p (sat_cons (step1272 p h) (sat_cons (step647 p h) (sat_nil p)))
def c1275 : List Lit := [(1376, true)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true :=
  Snake9.LocalRup.prove_clause [c1273, c1226, c1256, c1262, c924] c1275 (by decide) p (sat_cons (step1273 p h) (sat_cons (step1226 p h) (sat_cons (step1256 p h) (sat_cons (step1262 p h) (sat_cons (step924 p h) (sat_nil p))))))
def c1276 : List Lit := [(1384, true)]
theorem step1276 (p : Nat → Bool) (h : Constraints p) : clause p c1276 = true :=
  Snake9.LocalRup.prove_clause [c1275, c798] c1276 (by decide) p (sat_cons (step1275 p h) (sat_cons (step798 p h) (sat_nil p)))
def c1277 : List Lit := [(1506, false)]
theorem step1277 (p : Nat → Bool) (h : Constraints p) : clause p c1277 = true :=
  Snake9.LocalRup.prove_clause [c1275, c1143] c1277 (by decide) p (sat_cons (step1275 p h) (sat_cons (step1143 p h) (sat_nil p)))
def c1278 : List Lit := [(1330, false)]
theorem step1278 (p : Nat → Bool) (h : Constraints p) : clause p c1278 = true :=
  Snake9.LocalRup.prove_clause [c1276, c1268, c1274, c921] c1278 (by decide) p (sat_cons (step1276 p h) (sat_cons (step1268 p h) (sat_cons (step1274 p h) (sat_cons (step921 p h) (sat_nil p)))))
def c1279 : List Lit := []
theorem step1279 (p : Nat → Bool) (h : Constraints p) : clause p c1279 = true :=
  Snake9.LocalRup.prove_clause [c1278, c1277, c1275, c1274, c1267, c1019] c1279 (by decide) p (sat_cons (step1278 p h) (sat_cons (step1277 p h) (sat_cons (step1275 p h) (sat_cons (step1274 p h) (sat_cons (step1267 p h) (sat_cons (step1019 p h) (sat_nil p)))))))
end B112E090
