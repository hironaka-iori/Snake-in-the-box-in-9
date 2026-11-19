import CubeCnf
import Lift4
/-! Bridge, part 1: the assignment read off a `Pit`, and its values on each variable kind. -/
set_option linter.deprecated false
namespace Dim8Lift.Cube
open Dim8Lift.Cnf Snake9.LocalWindow

variable (S : Nat → Bool) (ℓ : Nat → Nat)

def tau0 (v : Nat) : Bool :=
  if v = 0 then false
  else if v ≤ 256 then S (v - 1)
  else if v ≤ 16640 then decide ((v - 257) % 64 + 1 ≤ ℓ ((v - 257) / 64))
  else if v ≤ 147712 then
    S (fx ((v - 16641) / 512) ((v - 16641) % 512 / 64)) &&
      !decide ((v - 16641) % 64 + 1 ≤ ℓ (fx ((v - 16641) / 512) ((v - 16641) % 512 / 64)))
  else if v ≤ 164096 then
    S (fx ((v - 147713) / 64) ((v - 147713) % 64 / 8)) && S (fx ((v - 147713) / 64) ((v - 147713) % 8))
  else if v ≤ 164352 then twoB S (v - 164097)
  else if v ≤ 164608 then anyB S (v - 164353)
  else if v ≤ 164864 then S (v - 164609) && !twoB S (v - 164609)
  else if v ≤ 165120 then S (v - 164865) && !anyB S (v - 164865)
  else false

variable {S ℓ}

theorem t_s {u : Nat} (hu : u < 256) : tau0 S ℓ (sV u) = S u := by
  unfold tau0 sV; rw [if_neg (by omega), if_pos (by omega)]; rfl
theorem t_o {u j : Nat} (hu : u < 256) (hj1 : 1 ≤ j) (hj : j ≤ 64) : tau0 S ℓ (oV u j) = decide (j ≤ ℓ u) := by
  unfold tau0 oV; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have e1 : (257 + 64 * u + (j - 1) - 257) % 64 = j - 1 := by omega
  have e2 : (257 + 64 * u + (j - 1) - 257) / 64 = u := by omega
  rw [e1, e2, show j - 1 + 1 = j by omega]
theorem t_a {u i j : Nat} (hu : u < 256) (hi : i < 8) (hj1 : 1 ≤ j) (hj : j ≤ 64) :
    tau0 S ℓ (aV u i j) = (S (fx u i) && !decide (j ≤ ℓ (fx u i))) := by
  unfold tau0 aV; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have e1 : (16641 + 512 * u + 64 * i + (j - 1) - 16641) / 512 = u := by omega
  have e2 : (16641 + 512 * u + 64 * i + (j - 1) - 16641) % 512 / 64 = i := by omega
  have e3 : (16641 + 512 * u + 64 * i + (j - 1) - 16641) % 64 = j - 1 := by omega
  rw [e1, e2, e3, show j - 1 + 1 = j by omega]
theorem t_p {u a b : Nat} (hu : u < 256) (ha : a < 8) (hb : b < 8) :
    tau0 S ℓ (pV u a b) = (S (fx u a) && S (fx u b)) := by
  unfold tau0 pV; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have e1 : (147713 + 64 * u + 8 * a + b - 147713) / 64 = u := by omega
  have e2 : (147713 + 64 * u + 8 * a + b - 147713) % 64 / 8 = a := by omega
  have e3 : (147713 + 64 * u + 8 * a + b - 147713) % 8 = b := by omega
  rw [e1, e2, e3]
theorem t_two {u : Nat} (hu : u < 256) : tau0 S ℓ (twoV u) = twoB S u := by
  unfold tau0 twoV; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), show 164097 + u - 164097 = u by omega]
theorem t_any {u : Nat} (hu : u < 256) : tau0 S ℓ (anyV u) = anyB S u := by
  unfold tau0 anyV; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), show 164353 + u - 164353 = u by omega]
theorem t_e1 {u : Nat} (hu : u < 256) : tau0 S ℓ (e1V u) = (S u && !twoB S u) := by
  unfold tau0 e1V; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), show 164609 + u - 164609 = u by omega]
theorem t_e0 {u : Nat} (hu : u < 256) : tau0 S ℓ (e0V u) = (S u && !anyB S u) := by
  unfold tau0 e0V; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), show 164865 + u - 164865 = u by omega]

end Dim8Lift.Cube
