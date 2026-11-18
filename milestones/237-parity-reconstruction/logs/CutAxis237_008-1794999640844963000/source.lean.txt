import CubeCut

set_option Elab.async false

namespace CutAxis237
open CubeCut237

/- The axis-pair identity with the first axis fixed to 8.
The other three axes retain their full quantification over the nine axes. -/
set_option maxHeartbeats 1000000 in
theorem axis_008 :
    ∀ j ∈ axes, ∀ a ∈ axes, ∀ b ∈ axes,
      8 < j → 8 ^^^ j = a ^^^ b →
        (8 = a ∧ j = b) ∨ (8 = b ∧ j = a) := by
  decide

#print axioms axis_008

end CutAxis237
