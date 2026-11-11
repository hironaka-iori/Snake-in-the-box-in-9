import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case08 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠0 → conflict 256 (pick original alternate x i)=false) : False := by
  have z62 : x 62=true := forceOld original alternate x 256 62 (he 62 (by decide) (by decide)) (by decide +kernel)
  have z149 : x 149=true := propagate original alternate x 62 149 (hs 62 149 (by decide) (by decide) (by decide)) (by decide +kernel) z62
  have z158 : x 158=true := propagate original alternate x 149 158 (hs 149 158 (by decide) (by decide) (by decide)) (by decide +kernel) z149
  have z189 : x 189=true := propagate original alternate x 158 189 (hs 158 189 (by decide) (by decide) (by decide)) (by decide +kernel) z158
  have z180 : x 180=true := propagate original alternate x 189 180 (hs 189 180 (by decide) (by decide) (by decide)) (by decide +kernel) z189
  have z173 : x 173=true := propagate original alternate x 180 173 (hs 180 173 (by decide) (by decide) (by decide)) (by decide +kernel) z180
  have z168 : x 168=true := propagate original alternate x 173 168 (hs 173 168 (by decide) (by decide) (by decide)) (by decide +kernel) z173
  have z165 : x 165=true := propagate original alternate x 168 165 (hs 168 165 (by decide) (by decide) (by decide)) (by decide +kernel) z168
  have z174 : x 174=true := propagate original alternate x 165 174 (hs 165 174 (by decide) (by decide) (by decide)) (by decide +kernel) z165
  have z179 : x 179=true := propagate original alternate x 174 179 (hs 174 179 (by decide) (by decide) (by decide)) (by decide +kernel) z174
  have z188 : x 188=true := propagate original alternate x 179 188 (hs 179 188 (by decide) (by decide) (by decide)) (by decide +kernel) z179
  have z191 : x 191=true := propagate original alternate x 188 191 (hs 188 191 (by decide) (by decide) (by decide)) (by decide +kernel) z188
  rw [z191] at h191
  contradiction
#print axioms case08
end SquareChoice192
