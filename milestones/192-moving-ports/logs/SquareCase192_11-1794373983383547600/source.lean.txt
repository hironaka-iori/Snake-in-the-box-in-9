import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case11 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠191 → conflict 99 (pick original alternate x i)=false) : False := by
  have z151 : x 151=true := forceOld original alternate x 99 151 (he 151 (by decide) (by decide)) (by decide +kernel)
  have z182 : x 182=true := propagate original alternate x 151 182 (hs 151 182 (by decide) (by decide) (by decide)) (by decide +kernel) z151
  have z185 : x 185=true := propagate original alternate x 182 185 (hs 182 185 (by decide) (by decide) (by decide)) (by decide +kernel) z182
  have hn : x 185=false := forbidNew original alternate x 99 185 (he 185 (by decide) (by decide)) (by decide +kernel)
  rw [z185] at hn
  contradiction
#print axioms case11
end SquareChoice192
