module

public import Snake9
import C230Final
import G230

/-! The bound 230 in Lean 4.35 (K7 route), assembled from certificate interfaces (lean435/tools/assemble230.py). -/

namespace Snake9

public theorem upper_230_435 : ∀ {m : Nat}, Snake m → m ≤ 230 :=
  upper_230_of_refutedK7 LocalWindow.allTab230 LocalWindow.allShare230

end Snake9

#print axioms Snake9.upper_230_435
