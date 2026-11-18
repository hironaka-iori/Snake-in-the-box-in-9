import CubeCut

set_option Elab.async false

namespace CutAxis237
open CubeCut237

/- The axis-pair identity with the first axis fixed to 1.
The other three axes retain their full quantification over the nine axes. -/
set_option maxHeartbeats 1000000 in
theorem axis_001 :
    ∀ j ∈ axes, ∀ a ∈ axes, ∀ b ∈ axes,
      1 < j → 1 ^^^ j = a ^^^ b →
        (1 = a ∧ j = b) ∨ (1 = b ∧ j = a) := by
  decide

#print axioms axis_001

end CutAxis237
