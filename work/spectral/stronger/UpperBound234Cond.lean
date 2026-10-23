import ShareRefs234
import D235Table
import UpperBound235Cond
/-! # The 234 bound from the 235 window premises and the share bridge

`upper_234_of_direction_windows_and_shares_allK6R3W` (AggregateDirectionK6R3WShare234, through
`ShareBonus.upper_of_walk_and_shares` at LB 21: `4935 m ≤ 1159221`, 234.89) needs the K6R3W window
premises `hw2 .. hw6`, given by `S235.T235.prem2 .. prem6` from the 235 shape refutations, and
the share premise `SH234.shares_K6R3W` (unconditional). -/
namespace S235.T235
open S235

/-- 234 from the refutation of the 34 shapes of the 235 bridge. -/
theorem upper_234_of_shapes (hE : ∀ e ∈ E, ShapeRefuted e.c e.L) {m : Nat} (p : Snake9.Snake m) :
    m ≤ 234 :=
  Snake9.upper_234_of_direction_windows_and_shares_allK6R3W p (prem2 hE p) (prem3 hE p) (prem4 hE p)
    (prem5 hE p) (prem6 hE p) (SH234.shares_K6R3W p)

/-- The 234 bound, conditional only on the shapes the 235 bridge has not refuted yet (the
hypotheses of `upper_235_of_remaining`). -/
theorem upper_234_of_remaining (h1 : ShapeRefuted e1.c e1.L) (h3 : ShapeRefuted e3.c e3.L) (h4 : ShapeRefuted e4.c e4.L) (h5 : ShapeRefuted e5.c e5.L) (h6 : ShapeRefuted e6.c e6.L) (h7 : ShapeRefuted e7.c e7.L) (h8 : ShapeRefuted e8.c e8.L) (h9 : ShapeRefuted e9.c e9.L) (h10 : ShapeRefuted e10.c e10.L) (h11 : ShapeRefuted e11.c e11.L) (h12 : ShapeRefuted e12.c e12.L) (h14 : ShapeRefuted e14.c e14.L) (h15 : ShapeRefuted e15.c e15.L) (h19 : ShapeRefuted e19.c e19.L) (h24 : ShapeRefuted e24.c e24.L)
    {m : Nat} (p : Snake9.Snake m) : m ≤ 234 :=
  upper_234_of_shapes (refutedE_of_remaining h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h14 h15 h19 h24) p

end S235.T235

#print axioms S235.T235.upper_234_of_shapes
#print axioms S235.T235.upper_234_of_remaining
