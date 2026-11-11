import EdgeData190
namespace ExchangeAccounting190
theorem edgeAccounting {V : Type} (es : List (V × V)) (s t : V → Bool) :
    edges es t + incidence es s t + edges es (removed t s) =
    edges es s + incidence es t s + edges es (removed s t) := by
  induction es with
  | nil => simp [edges, incidence]
  | cons e es ih =>
    rcases e with ⟨u,v⟩
    have hp := oneAccounting (s u) (s v) (t u) (t v)
    change (bit (t u && t v) + edges es t) +
      ((if s u && s v then bit (!t u)+bit (!t v) else 0) + incidence es s t) +
      (bit ((t u && !s u) && (t v && !s v)) + edges es (removed t s)) =
      (bit (s u && s v) + edges es s) +
      ((if t u && t v then bit (!s u)+bit (!s v) else 0) + incidence es t s) +
      (bit ((s u && !t u) && (s v && !t v)) + edges es (removed s t))
    omega

#print axioms edgeAccounting
end ExchangeAccounting190
