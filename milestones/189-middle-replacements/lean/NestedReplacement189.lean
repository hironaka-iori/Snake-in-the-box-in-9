import TwoCrossings188
namespace MiddleReplacement189
open LayerJoining Dimensional188

def middle97 {V : Type} {R : V → V → Prop}
    (p : InducedPath V R 31) (q : InducedPath V R 49)
    (r : InducedPath V R 15)
    (hpq : Compatible p q) (hqr : Compatible q r)
    (hpr : ∀ i j, p.vertex i ≠ r.vertex j ∧ ¬ R (p.vertex i) (r.vertex j)) :
    InducedPath (V × Bool) (LayerAdj R) 97 :=
  twoCrossings p q r hpq hqr hpr

def outer193 {V : Type} {R : V → V → Prop}
    {a c : Nat} (hsum : a+c=94)
    (p : InducedPath (V × Bool) (LayerAdj R) a)
    (q : InducedPath (V × Bool) (LayerAdj R) 97)
    (r : InducedPath (V × Bool) (LayerAdj R) c)
    (hpq : Compatible p q) (hqr : Compatible q r)
    (hpr : ∀ i j, p.vertex i ≠ r.vertex j ∧ ¬ LayerAdj R (p.vertex i) (r.vertex j)) :
    InducedPath ((V × Bool) × Bool) (LayerAdj (LayerAdj R)) 193 := by
  have he : a+97+c+2=193 := by omega
  simpa only [he] using twoCrossings p q r hpq hqr hpr

#print axioms middle97
#print axioms outer193
end MiddleReplacement189
