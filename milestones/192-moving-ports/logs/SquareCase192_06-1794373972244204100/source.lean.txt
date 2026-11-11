import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case06 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠0 → conflict 64 (pick original alternate x i)=false) : False := by
  have z62 : x 62=true := forceOld original alternate x 64 62 (he 62 (by decide) (by decide)) (by decide +kernel)
  have z149 : x 149=true := propagate original alternate x 62 149 (hs 62 149 (by decide) (by decide) (by decide)) (by decide +kernel) z62
  have z158 : x 158=true := propagate original alternate x 149 158 (hs 149 158 (by decide) (by decide) (by decide)) (by decide +kernel) z149
  have z189 : x 189=true := propagate original alternate x 158 189 (hs 158 189 (by decide) (by decide) (by decide)) (by decide +kernel) z158
  have z96 : x 96=true := propagate original alternate x 189 96 (hs 189 96 (by decide) (by decide) (by decide)) (by decide +kernel) z189
  have z99 : x 99=true := propagate original alternate x 96 99 (hs 96 99 (by decide) (by decide) (by decide)) (by decide +kernel) z96
  have z108 : x 108=true := propagate original alternate x 99 108 (hs 99 108 (by decide) (by decide) (by decide)) (by decide +kernel) z99
  have z105 : x 105=true := propagate original alternate x 108 105 (hs 108 105 (by decide) (by decide) (by decide)) (by decide +kernel) z108
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
#print axioms case06
end SquareChoice192
