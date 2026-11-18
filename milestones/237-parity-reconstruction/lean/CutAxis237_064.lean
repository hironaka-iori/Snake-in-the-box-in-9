import CubeCut

set_option Elab.async false

namespace CutAxis237
open CubeCut237

/- The axis-pair identity with the first axis fixed to 64.
The other three axes retain their full quantification over the nine axes. -/
set_option maxHeartbeats 1000000 in
theorem axis_064 :
    ∀ j ∈ axes, ∀ a ∈ axes, ∀ b ∈ axes,
      64 < j → 64 ^^^ j = a ^^^ b →
        (64 = a ∧ j = b) ∨ (64 = b ∧ j = a) := by
  decide

#print axioms axis_064

end CutAxis237
