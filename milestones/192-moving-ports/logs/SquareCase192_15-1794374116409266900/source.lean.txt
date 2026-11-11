import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case15 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠191 → conflict 39 (pick original alternate x i)=false) : False := by
  have z13 : x 13=true := forceOld original alternate x 39 13 (he 13 (by decide) (by decide)) (by decide +kernel)
  have z150 : x 150=true := propagate original alternate x 13 150 (hs 13 150 (by decide) (by decide) (by decide)) (by decide +kernel) z13
  have z147 : x 147=true := propagate original alternate x 150 147 (hs 150 147 (by decide) (by decide) (by decide)) (by decide +kernel) z150
  have z156 : x 156=true := propagate original alternate x 147 156 (hs 147 156 (by decide) (by decide) (by decide)) (by decide +kernel) z147
  have z183 : x 183=true := propagate original alternate x 156 183 (hs 156 183 (by decide) (by decide) (by decide)) (by decide +kernel) z156
  have z174 : x 174=true := propagate original alternate x 183 174 (hs 183 174 (by decide) (by decide) (by decide)) (by decide +kernel) z183
  have z179 : x 179=true := propagate original alternate x 174 179 (hs 174 179 (by decide) (by decide) (by decide)) (by decide +kernel) z174
  have z188 : x 188=true := propagate original alternate x 179 188 (hs 179 188 (by decide) (by decide) (by decide)) (by decide +kernel) z179
  have z191 : x 191=true := propagate original alternate x 188 191 (hs 188 191 (by decide) (by decide) (by decide)) (by decide +kernel) z188
  rw [z191] at h191
  contradiction
#print axioms case15
end SquareChoice192
