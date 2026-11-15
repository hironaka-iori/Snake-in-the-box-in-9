import AggregateDirection6SCConditional
import DirectionWindowBridge6SCToy

/-!
# The toy bound 254 from the automaton with context shares (milestone 35)

`upper_of_refuted6SC_noShare` on `tables6SCToy` (zero potential, lambda = 120/1, one ctx 7 and one
ctx 8 field backed by LRAT-replayed context share certificates):
`(120 + 4200 * 1) * m ≤ 1099800 * 1 + 7 * 120 + (2 ^ 1 - 1)`, so `m ≤ 254`.  No premises.
-/

namespace Snake9
open WindowAutomaton DirectionWindow6SC

theorem upper_254_toy6SC {m : Nat} (p : Snake m) : m ≤ 254 := by
  have := upper_of_refuted6SC_noShare tables6SCToy [] [] ctx7Keys6SCToy ctx8Keys6SCToy trivial trivial
    allCtx7_6SCToy allCtx8_6SCToy (fun _ _ => rfl) rfl cover6_6SCToy rfl coverH8_6SCToy
    ctxCover7_6SCToy ctxCover8_6SCToy stepOK6SCToy p
  change (120 + 4200 * 1) * m ≤ 1099800 * 1 + 7 * 120 + (2 ^ 1 - 1) at this
  omega

end Snake9

#print axioms Snake9.upper_254_toy6SC
