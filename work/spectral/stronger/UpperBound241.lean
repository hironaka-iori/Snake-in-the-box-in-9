import UpperBound242
import W2423AG1Check
import W2423BG1Check
import W2423CG1Check
import W3242AG1Check
/-!
# No (2,4,2,3) or (3,2,4,2) window; hence every snake has at most 241 edges

`upper_241_of_certified_windows` additionally assumes that no four consecutive internal
vertices carry counts `(2,4,2,3)` or `(3,2,4,2)` (`WindowAggregate.QuadExcluded`).
`WinShape.no_quad` splits the five edge directions into the shapes `01203`, `01230`, `01231`,
`01234` and normalises; the certified CNFs `2423` in shapes `01203`, `01230`, `01234`
(`W2423A/B/C`) and `3242` in shape `01203` (`W3242A`) cover every case, the shape `01231` and
the pattern `3242` by reading the window backwards.
-/
namespace WinG1
open Snake9 Snake9.SquareIncidence WinCNF W223G1

open WindowAggregate in
theorem no_quad_excluded {m : Nat} (p : Snake m) (r : Nat) (hr : r + 5 ≤ m) :
    ¬QuadExcluded (localAlpha p ⟨r+1, by omega⟩) (localAlpha p ⟨r+2, by omega⟩)
      (localAlpha p ⟨r+3, by omega⟩) (localAlpha p ⟨r+4, by omega⟩) := by
  rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
  · exact WinShape.no_quad W2423A.refuted W3242A.refuted (Or.inl W2423B.refuted)
      (Or.inl W2423C.refuted) p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact WinShape.no_quad W3242A.refuted W2423A.refuted (Or.inr W2423B.refuted)
      (Or.inr W2423C.refuted) p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

end WinG1

namespace Snake9

/-- **Unconditional bound**: every snake in the 9-cube has at most 241 edges. -/
theorem upper_bound_241 {m : Nat} (p : Snake m) : m ≤ 241 :=
  upper_241_of_certified_windows p (fun r hr => WinG1.no_certified p r hr)
    (fun r hr => WinG1.no_quad_excluded p r hr)

theorem upper_bound_241' : ∀ m, Nonempty (Snake m) → m ≤ 241 :=
  fun _ ⟨p⟩ => upper_bound_241 p

/-- The verified interval: a 191-edge snake exists, and no snake has more than 241 edges. -/
theorem verified_interval_191_241 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 241 :=
  ⟨lower_bound, upper_bound_241'⟩

end Snake9

#print axioms WinG1.no_quad_excluded
#print axioms Snake9.upper_bound_241
#print axioms Snake9.verified_interval_191_241
