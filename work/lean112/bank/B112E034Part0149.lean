import B112E034Part0148
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c11315 : List Lit := [(104, true)]
theorem step11315 (p : Nat → Bool) (h : Constraints p) : clause p c11315 = true :=
  Snake9.LocalRup.prove_clause [c11313, c11312, c11278, c11296, c11085, c8386] c11315 (by decide) p (sat_cons (step11313 p h) (sat_cons (step11312 p h) (sat_cons (step11278 p h) (sat_cons (step11296 p h) (sat_cons (step11085 p h) (sat_cons (step8386 p h) (sat_nil p)))))))
def c11316 : List Lit := [(1687, false)]
theorem step11316 (p : Nat → Bool) (h : Constraints p) : clause p c11316 = true :=
  Snake9.LocalRup.prove_clause [c11314, c2177] c11316 (by decide) p (sat_cons (step11314 p h) (sat_cons (step2177 p h) (sat_nil p)))
def c11317 : List Lit := [(101, false)]
theorem step11317 (p : Nat → Bool) (h : Constraints p) : clause p c11317 = true :=
  Snake9.LocalRup.prove_clause [c11315, c11313, c11286, c505] c11317 (by decide) p (sat_cons (step11315 p h) (sat_cons (step11313 p h) (sat_cons (step11286 p h) (sat_cons (step505 p h) (sat_nil p)))))
def c11318 : List Lit := [(1645, false)]
theorem step11318 (p : Nat → Bool) (h : Constraints p) : clause p c11318 = true :=
  Snake9.LocalRup.prove_clause [c11316, c11110, c11186, c10744] c11318 (by decide) p (sat_cons (step11316 p h) (sat_cons (step11110 p h) (sat_cons (step11186 p h) (sat_cons (step10744 p h) (sat_nil p)))))
def c11319 : List Lit := [(57, true)]
theorem step11319 (p : Nat → Bool) (h : Constraints p) : clause p c11319 = true :=
  Snake9.LocalRup.prove_clause [c11317, c11286, c11186, c2066] c11319 (by decide) p (sat_cons (step11317 p h) (sat_cons (step11286 p h) (sat_cons (step11186 p h) (sat_cons (step2066 p h) (sat_nil p)))))
def c11320 : List Lit := []
theorem step11320 (p : Nat → Bool) (h : Constraints p) : clause p c11320 = true :=
  Snake9.LocalRup.prove_clause [c11319, c11318, c11286, c9499] c11320 (by decide) p (sat_cons (step11319 p h) (sat_cons (step11318 p h) (sat_cons (step11286 p h) (sat_cons (step9499 p h) (sat_nil p)))))
end B112E034
