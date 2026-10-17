import B112E149Part0000
namespace B112E149
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c382 : List Lit := [(19, true), (20, false), (1176, true)]
theorem step382 (p : Nat → Bool) (h : Constraints p) : clause p c382 = true :=
  Snake9.LocalRup.prove_clause [c346, c366, c376, c251, c253, c242, c381, c231, c232, c240, c241, c226, c227, c244, c235, c284, c234, c377, c36, c23, c37] c382 (by decide) p (sat_cons (step346 p h) (sat_cons (step366 p h) (sat_cons (step376 p h) (sat_cons (step251 p h) (sat_cons (step253 p h) (sat_cons (step242 p h) (sat_cons (step381 p h) (sat_cons (step231 p h) (sat_cons (step232 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step226 p h) (sat_cons (step227 p h) (sat_cons (step244 p h) (sat_cons (step235 p h) (sat_cons (step284 p h) (sat_cons (step234 p h) (sat_cons (step377 p h) (sat_cons (step36 p h) (sat_cons (step23 p h) (sat_cons (step37 p h) (sat_nil p))))))))))))))))))))))
def c383 : List Lit := [(14, true), (20, false), (1176, true)]
theorem step383 (p : Nat → Bool) (h : Constraints p) : clause p c383 = true :=
  Snake9.LocalRup.prove_clause [c382, c242, c231, c232, c241, c226, c235, c32, c234] c383 (by decide) p (sat_cons (step382 p h) (sat_cons (step242 p h) (sat_cons (step231 p h) (sat_cons (step232 p h) (sat_cons (step241 p h) (sat_cons (step226 p h) (sat_cons (step235 p h) (sat_cons (step32 p h) (sat_cons (step234 p h) (sat_nil p))))))))))
def c384 : List Lit := [(20, false), (1176, true)]
theorem step384 (p : Nat → Bool) (h : Constraints p) : clause p c384 = true :=
  Snake9.LocalRup.prove_clause [c382, c383, c29, c26, c234, c226, c235, c229, c241] c384 (by decide) p (sat_cons (step382 p h) (sat_cons (step383 p h) (sat_cons (step29 p h) (sat_cons (step26 p h) (sat_cons (step234 p h) (sat_cons (step226 p h) (sat_cons (step235 p h) (sat_cons (step229 p h) (sat_cons (step241 p h) (sat_nil p))))))))))
def c385 : List Lit := [(1176, true)]
theorem step385 (p : Nat → Bool) (h : Constraints p) : clause p c385 = true :=
  Snake9.LocalRup.prove_clause [c239, c384, c236, c237, c241, c234, c229, c231, c226, c227, c27, c369] c385 (by decide) p (sat_cons (step239 p h) (sat_cons (step384 p h) (sat_cons (step236 p h) (sat_cons (step237 p h) (sat_cons (step241 p h) (sat_cons (step234 p h) (sat_cons (step229 p h) (sat_cons (step231 p h) (sat_cons (step226 p h) (sat_cons (step227 p h) (sat_cons (step27 p h) (sat_cons (step369 p h) (sat_nil p)))))))))))))
def c386 : List Lit := [(1184, true)]
theorem step386 (p : Nat → Bool) (h : Constraints p) : clause p c386 = true :=
  Snake9.LocalRup.prove_clause [c385, c346, c245] c386 (by decide) p (sat_cons (step385 p h) (sat_cons (step346 p h) (sat_cons (step245 p h) (sat_nil p))))
def c387 : List Lit := [(1223, false)]
theorem step387 (p : Nat → Bool) (h : Constraints p) : clause p c387 = true :=
  Snake9.LocalRup.prove_clause [c386, c366, c285] c387 (by decide) p (sat_cons (step386 p h) (sat_cons (step366 p h) (sat_cons (step285 p h) (sat_nil p))))
def c388 : List Lit := [(1217, false)]
theorem step388 (p : Nat → Bool) (h : Constraints p) : clause p c388 = true :=
  Snake9.LocalRup.prove_clause [c387, c276] c388 (by decide) p (sat_cons (step387 p h) (sat_cons (step276 p h) (sat_nil p)))
def c389 : List Lit := [(1214, false)]
theorem step389 (p : Nat → Bool) (h : Constraints p) : clause p c389 = true :=
  Snake9.LocalRup.prove_clause [c388, c272] c389 (by decide) p (sat_cons (step388 p h) (sat_cons (step272 p h) (sat_nil p)))
def c390 : List Lit := [(44, false), (45, true)]
theorem step390 (p : Nat → Bool) (h : Constraints p) : clause p c390 = true :=
  Snake9.LocalRup.prove_clause [c367, c366, c68, c357, c156, c158, c157] c390 (by decide) p (sat_cons (step367 p h) (sat_cons (step366 p h) (sat_cons (step68 p h) (sat_cons (step357 p h) (sat_cons (step156 p h) (sat_cons (step158 p h) (sat_cons (step157 p h) (sat_nil p))))))))
def c391 : List Lit := [(44, false), (30, false)]
theorem step391 (p : Nat → Bool) (h : Constraints p) : clause p c391 = true :=
  Snake9.LocalRup.prove_clause [c367, c70, c390] c391 (by decide) p (sat_cons (step367 p h) (sat_cons (step70 p h) (sat_cons (step390 p h) (sat_nil p))))
def c392 : List Lit := [(41, false), (39, false), (42, false)]
theorem step392 (p : Nat → Bool) (h : Constraints p) : clause p c392 = true :=
  Snake9.LocalRup.prove_clause [c331, c59, c64, c61, c152, c149, c153, c150, c155] c392 (by decide) p (sat_cons (step331 p h) (sat_cons (step59 p h) (sat_cons (step64 p h) (sat_cons (step61 p h) (sat_cons (step152 p h) (sat_cons (step149 p h) (sat_cons (step153 p h) (sat_cons (step150 p h) (sat_cons (step155 p h) (sat_nil p))))))))))
def c393 : List Lit := [(1211, false)]
theorem step393 (p : Nat → Bool) (h : Constraints p) : clause p c393 = true :=
  Snake9.LocalRup.prove_clause [c389, c388, c268, c270, c274, c263, c260, c261, c392] c393 (by decide) p (sat_cons (step389 p h) (sat_cons (step388 p h) (sat_cons (step268 p h) (sat_cons (step270 p h) (sat_cons (step274 p h) (sat_cons (step263 p h) (sat_cons (step260 p h) (sat_cons (step261 p h) (sat_cons (step392 p h) (sat_nil p))))))))))
def c394 : List Lit := [(44, true)]
theorem step394 (p : Nat → Bool) (h : Constraints p) : clause p c394 = true :=
  Snake9.LocalRup.prove_clause [c393, c267] c394 (by decide) p (sat_cons (step393 p h) (sat_cons (step267 p h) (sat_nil p)))
def c395 : List Lit := [(30, false)]
theorem step395 (p : Nat → Bool) (h : Constraints p) : clause p c395 = true :=
  Snake9.LocalRup.prove_clause [c394, c391] c395 (by decide) p (sat_cons (step394 p h) (sat_cons (step391 p h) (sat_nil p)))
def c396 : List Lit := [(1190, true)]
theorem step396 (p : Nat → Bool) (h : Constraints p) : clause p c396 = true :=
  Snake9.LocalRup.prove_clause [c395, c246] c396 (by decide) p (sat_cons (step395 p h) (sat_cons (step246 p h) (sat_nil p)))
def c397 : List Lit := [(1216, false)]
theorem step397 (p : Nat → Bool) (h : Constraints p) : clause p c397 = true :=
  Snake9.LocalRup.prove_clause [c396, c367, c366, c354] c397 (by decide) p (sat_cons (step396 p h) (sat_cons (step367 p h) (sat_cons (step366 p h) (sat_cons (step354 p h) (sat_nil p)))))
def c398 : List Lit := [(1213, false)]
theorem step398 (p : Nat → Bool) (h : Constraints p) : clause p c398 = true :=
  Snake9.LocalRup.prove_clause [c397, c271] c398 (by decide) p (sat_cons (step397 p h) (sat_cons (step271 p h) (sat_nil p)))
def c399 : List Lit := [(1208, false)]
theorem step399 (p : Nat → Bool) (h : Constraints p) : clause p c399 = true :=
  Snake9.LocalRup.prove_clause [c397, c273] c399 (by decide) p (sat_cons (step397 p h) (sat_cons (step273 p h) (sat_nil p)))
def c400 : List Lit := [(42, true)]
theorem step400 (p : Nat → Bool) (h : Constraints p) : clause p c400 = true :=
  Snake9.LocalRup.prove_clause [c398, c269] c400 (by decide) p (sat_cons (step398 p h) (sat_cons (step269 p h) (sat_nil p)))
def c401 : List Lit := [(1206, false)]
theorem step401 (p : Nat → Bool) (h : Constraints p) : clause p c401 = true :=
  Snake9.LocalRup.prove_clause [c399, c263] c401 (by decide) p (sat_cons (step399 p h) (sat_cons (step263 p h) (sat_nil p)))
def c402 : List Lit := [(41, true)]
theorem step402 (p : Nat → Bool) (h : Constraints p) : clause p c402 = true :=
  Snake9.LocalRup.prove_clause [c401, c260] c402 (by decide) p (sat_cons (step401 p h) (sat_cons (step260 p h) (sat_nil p)))
def c403 : List Lit := [(39, true)]
theorem step403 (p : Nat → Bool) (h : Constraints p) : clause p c403 = true :=
  Snake9.LocalRup.prove_clause [c401, c261] c403 (by decide) p (sat_cons (step401 p h) (sat_cons (step261 p h) (sat_nil p)))
def c404 : List Lit := []
theorem step404 (p : Nat → Bool) (h : Constraints p) : clause p c404 = true :=
  Snake9.LocalRup.prove_clause [c402, c403, c400, c392] c404 (by decide) p (sat_cons (step402 p h) (sat_cons (step403 p h) (sat_cons (step400 p h) (sat_cons (step392 p h) (sat_nil p)))))
end B112E149
