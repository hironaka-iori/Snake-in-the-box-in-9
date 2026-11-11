import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case12 (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠191 → conflict 111 (pick original alternate x i)=false) : False := by
  have z13 : x 13=true := forceOld original alternate x 111 13 (he 13 (by decide) (by decide)) (by decide +kernel)
  have z150 : x 150=true := propagate original alternate x 13 150 (hs 13 150 (by decide) (by decide) (by decide)) (by decide +kernel) z13
  have z147 : x 147=true := propagate original alternate x 150 147 (hs 150 147 (by decide) (by decide) (by decide)) (by decide +kernel) z150
  have z156 : x 156=true := propagate original alternate x 147 156 (hs 147 156 (by decide) (by decide) (by decide)) (by decide +kernel) z147
  have z183 : x 183=true := propagate original alternate x 156 183 (hs 156 183 (by decide) (by decide) (by decide)) (by decide +kernel) z156
  have hn : x 183=false := forbidNew original alternate x 111 183 (he 183 (by decide) (by decide)) (by decide +kernel)
  rw [z183] at hn
  contradiction
#print axioms case12
end SquareChoice192
