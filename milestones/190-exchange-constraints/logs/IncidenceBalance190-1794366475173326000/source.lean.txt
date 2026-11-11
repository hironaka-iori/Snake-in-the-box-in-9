import EdgeData190
namespace ExchangeAccounting190
theorem incidenceAccounting {V : Type} (es : List (V × V)) (s t : V → Bool) :
    incidence es s t = 2 * edges es (removed s t) + boundary es s t := by
  induction es with
  | nil => simp [edges, incidence, boundary]
  | cons e es ih =>
    rcases e with ⟨u,v⟩
    have hp := oneIncidence (s u) (s v) (t u) (t v)
    change (if s u && s v then bit (!t u)+bit (!t v) else 0) + incidence es s t =
      2*(bit ((s u && !t u) && (s v && !t v)) + edges es (removed s t)) +
      (bit (s u && s v && (t u != t v)) + boundary es s t)
    omega

#print axioms incidenceAccounting
end ExchangeAccounting190
