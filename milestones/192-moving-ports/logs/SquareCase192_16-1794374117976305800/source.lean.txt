import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case16 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠191 → conflict 231 (pick original alternate x i)=false) : False := by
  have z175 : x 175=true := forceOld original alternate x 231 175 (he 175 (by decide) (by decide)) (by decide +kernel)
  have z184 : x 184=true := propagate original alternate x 175 184 (hs 175 184 (by decide) (by decide) (by decide)) (by decide +kernel) z175
  have z181 : x 181=true := propagate original alternate x 184 181 (hs 184 181 (by decide) (by decide) (by decide)) (by decide +kernel) z184
  have z190 : x 190=true := propagate original alternate x 181 190 (hs 181 190 (by decide) (by decide) (by decide)) (by decide +kernel) z181
  have z187 : x 187=true := propagate original alternate x 190 187 (hs 190 187 (by decide) (by decide) (by decide)) (by decide +kernel) z190
  have z180 : x 180=true := propagate original alternate x 187 180 (hs 187 180 (by decide) (by decide) (by decide)) (by decide +kernel) z187
  have z173 : x 173=true := propagate original alternate x 180 173 (hs 180 173 (by decide) (by decide) (by decide)) (by decide +kernel) z180
  have hn : x 173=false := forbidNew original alternate x 231 173 (he 173 (by decide) (by decide)) (by decide +kernel)
  rw [z173] at hn
  contradiction
#print axioms case16
end SquareChoice192
