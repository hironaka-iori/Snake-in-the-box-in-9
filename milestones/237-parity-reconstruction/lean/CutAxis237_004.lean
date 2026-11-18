import CubeCut

set_option Elab.async false

namespace CutAxis237
open CubeCut237

/- The axis-pair identity with the first axis fixed to 4.
The other three axes retain their full quantification over the nine axes. -/
set_option maxHeartbeats 1000000 in
theorem axis_004 :
    ∀ j ∈ axes, ∀ a ∈ axes, ∀ b ∈ axes,
      4 < j → 4 ^^^ j = a ^^^ b →
        (4 = a ∧ j = b) ∨ (4 = b ∧ j = a) := by
  decide

#print axioms axis_004

end CutAxis237
