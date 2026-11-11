import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case14 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠191 → conflict 71 (pick original alternate x i)=false) : False := by
  have z159 : x 159=true := forceOld original alternate x 71 159 (he 159 (by decide) (by decide)) (by decide +kernel)
  have z164 : x 164=true := propagate original alternate x 159 164 (hs 159 164 (by decide) (by decide) (by decide)) (by decide +kernel) z159
  have z155 : x 155=true := propagate original alternate x 164 155 (hs 164 155 (by decide) (by decide) (by decide)) (by decide +kernel) z164
  have z188 : x 188=true := propagate original alternate x 155 188 (hs 155 188 (by decide) (by decide) (by decide)) (by decide +kernel) z155
  have z191 : x 191=true := propagate original alternate x 188 191 (hs 188 191 (by decide) (by decide) (by decide)) (by decide +kernel) z188
  rw [z191] at h191
  contradiction
#print axioms case14
end SquareChoice192
