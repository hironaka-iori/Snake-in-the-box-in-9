import CubeCut

set_option Elab.async false

namespace CutAxis237
open CubeCut237

/- The axis-pair identity with the first axis fixed to 16.
The other three axes retain their full quantification over the nine axes. -/
set_option maxHeartbeats 1000000 in
theorem axis_016 :
    ∀ j ∈ axes, ∀ a ∈ axes, ∀ b ∈ axes,
      16 < j → 16 ^^^ j = a ^^^ b →
        (16 = a ∧ j = b) ∨ (16 = b ∧ j = a) := by
  decide

#print axioms axis_016

end CutAxis237
