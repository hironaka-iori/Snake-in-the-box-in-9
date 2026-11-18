import CubeCut

set_option Elab.async false

namespace CutAxis237
open CubeCut237

/- The axis-pair identity with the first axis fixed to 256.
The other three axes retain their full quantification over the nine axes. -/
set_option maxHeartbeats 1000000 in
theorem axis_256 :
    ∀ j ∈ axes, ∀ a ∈ axes, ∀ b ∈ axes,
      256 < j → 256 ^^^ j = a ^^^ b →
        (256 = a ∧ j = b) ∨ (256 = b ∧ j = a) := by
  decide

#print axioms axis_256

end CutAxis237
