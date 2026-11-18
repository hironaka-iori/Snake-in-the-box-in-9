import CubeCut

set_option Elab.async false

namespace CutAxis237
open CubeCut237

/- The axis-pair identity with the first axis fixed to 2.
The other three axes retain their full quantification over the nine axes. -/
set_option maxHeartbeats 1000000 in
theorem axis_002 :
    ∀ j ∈ axes, ∀ a ∈ axes, ∀ b ∈ axes,
      2 < j → 2 ^^^ j = a ^^^ b →
        (2 = a ∧ j = b) ∨ (2 = b ∧ j = a) := by
  decide

#print axioms axis_002

end CutAxis237
