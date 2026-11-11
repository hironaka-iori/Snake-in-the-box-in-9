import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case03 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠0 → conflict 8 (pick original alternate x i)=false) : False := by
  have z2 : x 2=true := forceOld original alternate x 8 2 (he 2 (by decide) (by decide)) (by decide +kernel)
  have hn : x 2=false := forbidNew original alternate x 8 2 (he 2 (by decide) (by decide)) (by decide +kernel)
  rw [z2] at hn
  contradiction
#print axioms case03
end SquareChoice192
