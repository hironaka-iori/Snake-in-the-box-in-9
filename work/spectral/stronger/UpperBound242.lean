import WinShape
import W224RepG1Check
import W224DisG1Check
import W232RepG1Check
import W232DisG1Check
import W323RepG1Check
import W323DisG1Check
import W41cRepG1Check
import W41cDisG1Check
/-!
# No certified window occurs in a snake of `Q_9`; hence every snake has at most 242 edges

`upper_242_of_certified_windows` (AggregateWindowConditional) assumes that no three consecutive
internal vertices carry counts `(2,2,3)`, `(2,2,4)`, `(2,3,2)`, `(3,2,3)`, `(4,1,c)` with
`4 ≤ c ≤ 6`, or a reversal of these (`WindowAggregate.Certified`).  Each case is refuted:
* the shape case split and the normalisation of `WinShape.no_tri_fwd` / `no_tri_rev`
  (directions `0120` or `0123`; the window is read backwards for reversed patterns),
* the G1 checker (`WinG1Gen`, `W223G1Sound`), now with count ranges such as `4 ≤ α ≤ 6`,
* kernel-checked RUP refutations of the certified window CNFs `224`, `232`, `323`, `41c`
  (both shapes, modules `W224Rep*` ... `W41cDis*`) and the existing `223` refutations.
-/
namespace WinG1
open Snake9 Snake9.SquareIncidence WinCNF W223G1

theorem ref223R : Refuted3 0 2 2 2 2 3 3 :=
  ⟨tabRep, W223Rep.F, w223_rep_unsat, blocksOK_rep, check_rep, by decide +kernel, by decide⟩
theorem ref223D : Refuted3 3 2 2 2 2 3 3 :=
  ⟨tabDis, W223Dis.F, w223_dis_unsat, blocksOK_dis, check_dis, by decide +kernel, by decide⟩

open WindowAggregate in
/-- No snake has a certified internal window. -/
theorem no_certified {m : Nat} (p : Snake m) (r : Nat) (hr : r + 4 ≤ m) :
    ¬Certified (localAlpha p ⟨r+1, by omega⟩) (localAlpha p ⟨r+2, by omega⟩)
      (localAlpha p ⟨r+3, by omega⟩) := by
  rintro ⟨hE, h222⟩
  have key : ∀ z : Nat, 2 ≤ z → z ≤ 4 → z = 2 ∨ z = 3 ∨ z = 4 := by omega
  unfold Excluded at hE
  rcases hE with ⟨hx, hy, hz1, hz2⟩ | ⟨hz, hy, hx1, hx2⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
    ⟨hx, hy, hz1, hz2⟩ | ⟨hz, hy, hx1, hx2⟩
  · rcases key _ hz1 hz2 with h | h | h
    · exact h222 ⟨hx, hy, h⟩
    · exact W223G1.no_223 p r hr ⟨hx, hy, h⟩
    · exact WinShape.no_tri_fwd W224Rep.refuted W224Dis.refuted p r hr
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rcases key _ hx1 hx2 with h | h | h
    · exact h222 ⟨h, hy, hz⟩
    · exact WinShape.no_tri_rev ref223R ref223D p r hr
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    · exact WinShape.no_tri_rev W224Rep.refuted W224Dis.refuted p r hr
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact WinShape.no_tri_fwd W232Rep.refuted W232Dis.refuted p r hr
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact WinShape.no_tri_fwd W323Rep.refuted W323Dis.refuted p r hr
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact WinShape.no_tri_fwd W41cRep.refuted W41cDis.refuted p r hr
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact WinShape.no_tri_rev W41cRep.refuted W41cDis.refuted p r hr
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

end WinG1

namespace Snake9

/-- **Unconditional bound**: every snake in the 9-cube has at most 242 edges. -/
theorem upper_bound_242 {m : Nat} (p : Snake m) : m ≤ 242 :=
  upper_242_of_certified_windows p (fun r hr => WinG1.no_certified p r hr)

theorem upper_bound_242' : ∀ m, Nonempty (Snake m) → m ≤ 242 :=
  fun _ ⟨p⟩ => upper_bound_242 p

/-- The verified interval: a 191-edge snake exists, and no snake has more than 242 edges. -/
theorem verified_interval_191_242 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 242 :=
  ⟨lower_bound, upper_bound_242'⟩

end Snake9

#print axioms WinG1.no_certified
#print axioms Snake9.upper_bound_242
#print axioms Snake9.verified_interval_191_242
