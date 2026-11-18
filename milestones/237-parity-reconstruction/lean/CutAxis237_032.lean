import CubeCut

set_option Elab.async false

namespace CutAxis237
open CubeCut237

/- The axis-pair identity with the first axis fixed to 32.
The other three axes retain their full quantification over the nine axes. -/
set_option maxHeartbeats 1000000 in
theorem axis_032 :
    ∀ j ∈ axes, ∀ a ∈ axes, ∀ b ∈ axes,
      32 < j → 32 ^^^ j = a ^^^ b →
        (32 = a ∧ j = b) ∨ (32 = b ∧ j = a) := by
  decide

#print axioms axis_032

end CutAxis237
