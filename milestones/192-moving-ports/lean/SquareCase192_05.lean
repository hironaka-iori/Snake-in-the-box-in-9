import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case05 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠0 → conflict 32 (pick original alternate x i)=false) : False := by
  have z116 : x 116=true := forceOld original alternate x 32 116 (he 116 (by decide) (by decide)) (by decide +kernel)
  have z183 : x 183=true := propagate original alternate x 116 183 (hs 116 183 (by decide) (by decide) (by decide)) (by decide +kernel) z116
  have z174 : x 174=true := propagate original alternate x 183 174 (hs 183 174 (by decide) (by decide) (by decide)) (by decide +kernel) z183
  have z179 : x 179=true := propagate original alternate x 174 179 (hs 174 179 (by decide) (by decide) (by decide)) (by decide +kernel) z174
  have z188 : x 188=true := propagate original alternate x 179 188 (hs 179 188 (by decide) (by decide) (by decide)) (by decide +kernel) z179
  have z191 : x 191=true := propagate original alternate x 188 191 (hs 188 191 (by decide) (by decide) (by decide)) (by decide +kernel) z188
  rw [z191] at h191
  contradiction
#print axioms case05
end SquareChoice192
