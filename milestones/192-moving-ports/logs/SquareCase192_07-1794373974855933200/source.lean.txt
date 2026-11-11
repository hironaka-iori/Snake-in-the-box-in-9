import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case07 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠0 → conflict 128 (pick original alternate x i)=false) : False := by
  have z144 : x 144=true := forceOld original alternate x 128 144 (he 144 (by decide) (by decide)) (by decide +kernel)
  have z161 : x 161=true := propagate original alternate x 144 161 (hs 144 161 (by decide) (by decide) (by decide)) (by decide +kernel) z144
  have z176 : x 176=true := propagate original alternate x 161 176 (hs 161 176 (by decide) (by decide) (by decide)) (by decide +kernel) z161
  have z179 : x 179=true := propagate original alternate x 176 179 (hs 176 179 (by decide) (by decide) (by decide)) (by decide +kernel) z176
  have z188 : x 188=true := propagate original alternate x 179 188 (hs 179 188 (by decide) (by decide) (by decide)) (by decide +kernel) z179
  have z191 : x 191=true := propagate original alternate x 188 191 (hs 188 191 (by decide) (by decide) (by decide)) (by decide +kernel) z188
  rw [z191] at h191
  contradiction
#print axioms case07
end SquareChoice192
