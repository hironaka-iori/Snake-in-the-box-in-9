import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case00 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠0 → conflict 1 (pick original alternate x i)=false) : False := by
  have z16 : x 16=true := forceOld original alternate x 1 16 (he 16 (by decide) (by decide)) (by decide +kernel)
  have z101 : x 101=true := propagate original alternate x 16 101 (hs 16 101 (by decide) (by decide) (by decide)) (by decide +kernel) z16
  have z110 : x 110=true := propagate original alternate x 101 110 (hs 101 110 (by decide) (by decide) (by decide)) (by decide +kernel) z101
  have z105 : x 105=true := propagate original alternate x 110 105 (hs 110 105 (by decide) (by decide) (by decide)) (by decide +kernel) z110
  have z98 : x 98=true := propagate original alternate x 105 98 (hs 105 98 (by decide) (by decide) (by decide)) (by decide +kernel) z105
  have z95 : x 95=true := propagate original alternate x 98 95 (hs 98 95 (by decide) (by decide) (by decide)) (by decide +kernel) z98
  have z86 : x 86=true := propagate original alternate x 95 86 (hs 95 86 (by decide) (by decide) (by decide)) (by decide +kernel) z95
  have z183 : x 183=true := propagate original alternate x 86 183 (hs 86 183 (by decide) (by decide) (by decide)) (by decide +kernel) z86
  have z174 : x 174=true := propagate original alternate x 183 174 (hs 183 174 (by decide) (by decide) (by decide)) (by decide +kernel) z183
  have z179 : x 179=true := propagate original alternate x 174 179 (hs 174 179 (by decide) (by decide) (by decide)) (by decide +kernel) z174
  have z188 : x 188=true := propagate original alternate x 179 188 (hs 179 188 (by decide) (by decide) (by decide)) (by decide +kernel) z179
  have z191 : x 191=true := propagate original alternate x 188 191 (hs 188 191 (by decide) (by decide) (by decide)) (by decide +kernel) z188
  rw [z191] at h191
  contradiction
#print axioms case00
end SquareChoice192
