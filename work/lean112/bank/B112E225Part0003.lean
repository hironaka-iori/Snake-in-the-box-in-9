import B112E225Part0002
namespace B112E225
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c709 : List Lit := [(1372, true)]
theorem step709 (p : Nat → Bool) (h : Constraints p) : clause p c709 = true :=
  Snake9.LocalRup.prove_clause [c707, c679, c421] c709 (by decide) p (sat_cons (step707 p h) (sat_cons (step679 p h) (sat_cons (step421 p h) (sat_nil p))))
def c710 : List Lit := [(1419, true)]
theorem step710 (p : Nat → Bool) (h : Constraints p) : clause p c710 = true :=
  Snake9.LocalRup.prove_clause [c708, c601, c484] c710 (by decide) p (sat_cons (step708 p h) (sat_cons (step601 p h) (sat_cons (step484 p h) (sat_nil p))))
def c711 : List Lit := []
theorem step711 (p : Nat → Bool) (h : Constraints p) : clause p c711 = true :=
  Snake9.LocalRup.prove_clause [c710, c709, c696, c501] c711 (by decide) p (sat_cons (step710 p h) (sat_cons (step709 p h) (sat_cons (step696 p h) (sat_cons (step501 p h) (sat_nil p)))))
end B112E225
