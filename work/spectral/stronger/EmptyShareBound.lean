import AggregateSingletonBound

/-!
Empty-square shares (matches `omega_of` / `OmegaModel` in
milestones/10-window-aggregate/scripts/omega_oracle.py).

For a selected vertex x, a direction k and an axis pair {a,b} with k ∉ {a,b}:
  Q = (x ^ e_k) + span(e_a, e_b)   (the square across the edge in direction k),
  P = x + span(e_a, e_b)           (its parallel square through x).
If Q is empty, x receives `shareWeight (#selected in P)` = 6, 3, 2 for 1, 2, 3
selected vertices (0 otherwise).  The oracle only lets k range over directions
not used by the path at x; that restriction is redundant (`shareTerm_eq_zero_of_flip`),
because x ^ e_k ∈ Q.
-/

namespace Snake9.SquareIncidence
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 1000000

def sqCount {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) : Nat :=
  selected p v + selected p (flip ab.val.1 v) + selected p (flip ab.val.2 v) +
    selected p (flip ab.val.2 (flip ab.val.1 v))

def shareWeight (c : Nat) : Nat :=
  if c = 1 then 6 else if c = 2 then 3 else if c = 3 then 2 else 0

def offAxis (k : Coord) (ab : AxisPair) : Prop := k ≠ ab.val.1 ∧ k ≠ ab.val.2

def shareTerm {m : Nat} (p : Snake m) (k : Coord) (ab : AxisPair) (v : Vertex) : Nat :=
  if offAxis k ab then empty p ab (flip k v) * shareWeight (sqCount p ab v) else 0

def vertexShare {m : Nat} (p : Snake m) (v : Vertex) : Nat :=
  ∑ k : Coord, ∑ ab : AxisPair, shareTerm p k ab v

/-- share of the i-th path vertex (integer units: oracle `share`). -/
def share {m : Nat} (p : Snake m) (i : Fin (m+1)) : Nat := vertexShare p (p.vertex i)

/-- oracle `omega(x) = 21 * alpha(x) + share(x)`. -/
def omegaWeight {m : Nat} (p : Snake m) (i : Fin (m+1)) : Nat :=
  21 * localAlpha p i + share p i

theorem shareTerm_eq_zero_of_flip {m : Nat} (p : Snake m) (k : Coord) (ab : AxisPair)
    (v : Vertex) (h : InPath p (flip k v)) : shareTerm p k ab v = 0 := by
  unfold shareTerm empty
  split_ifs with h1 h2 <;> simp_all

theorem empty_flip1 {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) :
    empty p ab (flip ab.val.1 v) = empty p ab v := by
  unfold empty
  simp only [flip_twice, flip_commute ab.val.1 ab.val.2]
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem empty_flip2 {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) :
    empty p ab (flip ab.val.2 v) = empty p ab v := by
  unfold empty
  simp only [flip_twice, flip_commute ab.val.1 ab.val.2]
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem sqCount_flip1 {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) :
    sqCount p ab (flip ab.val.1 v) = sqCount p ab v := by
  unfold sqCount
  simp only [flip_twice, flip_commute ab.val.1 ab.val.2]
  omega

theorem sqCount_flip2 {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) :
    sqCount p ab (flip ab.val.2 v) = sqCount p ab v := by
  unfold sqCount
  simp only [flip_twice, flip_commute ab.val.1 ab.val.2]
  omega

theorem shareTerm_flip1 {m : Nat} (p : Snake m) (k : Coord) (ab : AxisPair) (v : Vertex) :
    shareTerm p k ab (flip ab.val.1 v) = shareTerm p k ab v := by
  unfold shareTerm
  rw [flip_commute k ab.val.1 v, empty_flip1, sqCount_flip1]

theorem shareTerm_flip2 {m : Nat} (p : Snake m) (k : Coord) (ab : AxisPair) (v : Vertex) :
    shareTerm p k ab (flip ab.val.2 v) = shareTerm p k ab v := by
  unfold shareTerm
  rw [flip_commute k ab.val.2 v, empty_flip2, sqCount_flip2]

theorem mul_shareWeight_le (c : Nat) : c * shareWeight c ≤ 6 := by
  unfold shareWeight
  split_ifs <;> subst_vars <;> simp

theorem empty_le_one {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) :
    empty p ab v ≤ 1 := by
  unfold empty; split_ifs <;> simp

/-- the four selected corners of P share at most 6 from (Q,k). -/
theorem quad_share_le {m : Nat} (p : Snake m) (k : Coord) (ab : AxisPair) (v : Vertex) :
    selected p v * shareTerm p k ab v +
      selected p (flip ab.val.1 v) * shareTerm p k ab (flip ab.val.1 v) +
      selected p (flip ab.val.2 v) * shareTerm p k ab (flip ab.val.2 v) +
      selected p (flip ab.val.2 (flip ab.val.1 v)) *
        shareTerm p k ab (flip ab.val.2 (flip ab.val.1 v)) ≤
    (if offAxis k ab then 6 * empty p ab (flip k v) else 0) := by
  rw [shareTerm_flip2 p k ab (flip ab.val.1 v), shareTerm_flip1 p k ab v, shareTerm_flip2 p k ab v]
  have he : selected p v * shareTerm p k ab v +
      selected p (flip ab.val.1 v) * shareTerm p k ab v +
      selected p (flip ab.val.2 v) * shareTerm p k ab v +
      selected p (flip ab.val.2 (flip ab.val.1 v)) * shareTerm p k ab v =
      sqCount p ab v * shareTerm p k ab v := by
    unfold sqCount; ring
  rw [he]
  unfold shareTerm
  split_ifs
  · have h6 := mul_shareWeight_le (sqCount p ab v)
    calc sqCount p ab v * (empty p ab (flip k v) * shareWeight (sqCount p ab v))
        = empty p ab (flip k v) * (sqCount p ab v * shareWeight (sqCount p ab v)) := by ring
      _ ≤ empty p ab (flip k v) * 6 := Nat.mul_le_mul_left _ h6
      _ = 6 * empty p ab (flip k v) := by ring
  · simp

theorem sum_share_dir_le {m : Nat} (p : Snake m) (k : Coord) (ab : AxisPair) :
    4 * (∑ v, selected p v * shareTerm p k ab v) ≤
      (if offAxis k ab then 6 * (∑ v, empty p ab v) else 0) := by
  let h : Vertex → Nat := fun v => selected p v * shareTerm p k ab v
  have h4 : 4 * (∑ v, h v) = ∑ v, (h v + h (flip ab.val.1 v) + h (flip ab.val.2 v) +
      h (flip ab.val.2 (flip ab.val.1 v))) := by
    simp only [Finset.sum_add_distrib, sum_flip, sum_flip_both]; ring
  have hle := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset Vertex)) =>
    quad_share_le p k ab v)
  change 4 * (∑ v, h v) ≤ _
  rw [h4]
  refine le_trans hle ?_
  split_ifs
  · rw [← Finset.mul_sum, sum_flip k (fun v => empty p ab v)]
  · simp

theorem offAxis_count (ab : AxisPair) :
    (∑ k : Coord, if offAxis k ab then 1 else 0) = 7 := by
  rw [Finset.sum_boole]
  have hab : ab.val.1 ≠ ab.val.2 := fun h => (ne_of_lt ab.property) (congrArg Fin.val h)
  have hf : Finset.univ.filter (fun k => offAxis k ab) =
      (Finset.univ.erase ab.val.1).erase ab.val.2 := by
    ext k; simp [offAxis, and_comm]
  rw [hf, Finset.card_erase_of_mem, Finset.card_erase_of_mem] <;> simp [Ne.symm hab]

theorem sum_share_pair_le {m : Nat} (p : Snake m) (ab : AxisPair) :
    4 * (∑ k : Coord, ∑ v, selected p v * shareTerm p k ab v) ≤
      42 * (∑ v, empty p ab v) := by
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum (fun k _ => sum_share_dir_le p k ab)) ?_
  have : (∑ k : Coord, if offAxis k ab then 6 * (∑ v, empty p ab v) else 0) =
      (∑ k : Coord, if offAxis k ab then 1 else 0) * (6 * (∑ v, empty p ab v)) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; split_ifs <;> simp
  rw [this, offAxis_count]; omega

theorem path_sum_eq {m : Nat} (p : Snake m) (f : Vertex → Nat) :
    (∑ i, f (p.vertex i)) = ∑ v, selected p v * f v := by
  have he : Finset.univ.filter (InPath p) = Finset.univ.image p.vertex := by
    ext v; simp [InPath]
  unfold selected
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, he, Finset.sum_image]
  intro i _ j _ h
  exact p.distinct i j h

def totalShare {m : Nat} (p : Snake m) : Nat := ∑ i, share p i

/-- Σ_i share(i) ≤ 42 s0, with 4 s0 = totalEmptyAnchored (each empty square has 4 anchors). -/
theorem totalShare_le {m : Nat} (p : Snake m) :
    4 * totalShare p ≤ 42 * totalEmptyAnchored p := by
  have h1 : totalShare p = ∑ ab : AxisPair, ∑ k : Coord, ∑ v, selected p v * shareTerm p k ab v := by
    unfold totalShare share
    rw [path_sum_eq p (vertexShare p)]
    unfold vertexShare
    calc (∑ v, selected p v * ∑ k : Coord, ∑ ab : AxisPair, shareTerm p k ab v)
        = ∑ v, ∑ k : Coord, ∑ ab : AxisPair, selected p v * shareTerm p k ab v := by
          simp only [Finset.mul_sum]
      _ = ∑ k : Coord, ∑ v, ∑ ab : AxisPair, selected p v * shareTerm p k ab v :=
          Finset.sum_comm
      _ = ∑ k : Coord, ∑ ab : AxisPair, ∑ v, selected p v * shareTerm p k ab v :=
          Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [h1, Finset.mul_sum, totalEmptyAnchored, Finset.mul_sum]
  exact Finset.sum_le_sum (fun ab _ => sum_share_pair_le p ab)

/-- Combined inequality: 21 T + Σ share ≤ 21 (9214 − 35 v), v = m+1, additive form. -/
theorem weighted_identity_bound {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    21 * (∑ i, localAlpha p i) + totalShare p + 735 * (m+1) ≤ 193494 := by
  have hid := global_identity p
  rw [selected_total p] at hid
  have hw := wedge_total_upper p
  have hs := totalShare_le p
  have ht := totalSingleton_eq_path_sum p
  have h1 := singleton_total_lower p
  omega

theorem omegaWeight_sum_le {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    (∑ i, omegaWeight p i) ≤ 21 * (9214 - 35 * (m+1)) ∧
      (∑ i, omegaWeight p i) + 735 * (m+1) ≤ 193494 := by
  have h := weighted_identity_bound p hm
  have he : (∑ i, omegaWeight p i) = 21 * (∑ i, localAlpha p i) + totalShare p := by
    unfold omegaWeight totalShare
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [he]; omega

#print axioms totalShare_le
#print axioms weighted_identity_bound
#print axioms omegaWeight_sum_le
#print axioms shareTerm_eq_zero_of_flip
end
end Snake9.SquareIncidence
