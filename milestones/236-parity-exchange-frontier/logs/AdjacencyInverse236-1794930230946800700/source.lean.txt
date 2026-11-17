import Std

set_option Elab.async false

namespace AdjacencyInverse236

/-- Integer numerator of the proposed inverse at cube distance d. -/
def weight : Nat → Int
  | 1 => 35
  | 3 => -10
  | 5 => 8
  | 7 => -16
  | 9 => 128
  | _ => 0

/-- The five possible same-parity distances in Q9 satisfy the kernel
recurrence. Geometric neighbour multiplicities are a separate obligation. -/
theorem distance_recurrence (k : Nat) (allowed : k ∈ [0, 2, 4, 6, 8]) :
    (k : Int) * weight (k - 1) + (9 - (k : Int)) * weight (k + 1) =
      if k = 0 then 315 else 0 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem sum_congr {V : Type} (xs : List V) (f g : V → Int) :
    (∀ x, x ∈ xs → f x = g x) → (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => intro h; rfl
  | cons x xs ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]

private theorem sum_zero {V : Type} (xs : List V) :
    (xs.map (fun _ => (0 : Int))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Int.zero_add]

private theorem sum_add {V : Type} (xs : List V) (f g : V → Int) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

private theorem mul_sum {V : Type} (xs : List V) (c : Int) (f : V → Int) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Int.mul_add]

private theorem sum_mul {V : Type} (xs : List V) (f : V → Int) (c : Int) :
    (xs.map (fun x => f x * c)).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Int.add_mul]

private theorem sum_swap {V W : Type} (rows : List V) (columns : List W)
    (f : V → W → Int) :
    (rows.map (fun v => (columns.map (fun w => f v w)).sum)).sum =
      (columns.map (fun w => (rows.map (fun v => f v w)).sum)).sum := by
  induction rows with
  | nil =>
      simpa only [List.map_nil, List.sum_nil] using (sum_zero columns).symm
  | cons v rows ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      exact (sum_add columns (fun w => f v w)
        (fun w => (rows.map (fun u => f u w)).sum)).symm

private theorem sum_single {W : Type} [DecidableEq W]
    (columns : List W) (a : W) (c : Int) :
    columns.Nodup → a ∈ columns →
      (columns.map (fun t => if t = a then c else 0)).sum = c := by
  induction columns with
  | nil => intro hn ha; simp at ha
  | cons t columns ih =>
      intro hn ha
      obtain ⟨absent, nodup⟩ := List.nodup_cons.mp hn
      by_cases same : t = a
      · subst t
        have zero : (columns.map (fun t => if t = a then c else 0)).sum = 0 := by
          calc
            _ = (columns.map (fun _ => (0 : Int))).sum := by
              apply sum_congr
              intro t member
              have different : t ≠ a := by
                intro equal
                exact absent (equal ▸ member)
              simp only [if_neg different]
            _ = 0 := sum_zero columns
        simp [zero]
      · have member : a ∈ columns := by
          rcases List.mem_cons.mp ha with equal | member
          · exact False.elim (same equal.symm)
          · exact member
        simp only [List.map_cons, List.sum_cons, if_neg same, Int.zero_add]
        exact ih nodup member

/-- A finite integer left inverse reconstructs a coordinate from all row
observations. The proof expands the observations, interchanges the finite
sums, applies the coefficient identity, and removes the Kronecker delta.
No desired reconstruction equality is assumed. -/
theorem reconstruct {V W : Type} [DecidableEq W]
    (rows : List V) (columns : List W) (incidence : V → W → Int)
    (coefficient : W → V → Int) (z : W → Int) (b : V → Int)
    (scale : Int) (a : W) (nodup : columns.Nodup) (member : a ∈ columns)
    (observations : ∀ v, v ∈ rows →
      b v = (columns.map (fun t => incidence v t * z t)).sum)
    (leftInverse : ∀ t, t ∈ columns →
      (rows.map (fun v => coefficient a v * incidence v t)).sum =
        if t = a then scale else 0) :
    (rows.map (fun v => coefficient a v * b v)).sum = scale * z a := by
  calc
    _ = (rows.map (fun v =>
        (columns.map (fun t => coefficient a v * (incidence v t * z t))).sum)).sum := by
      apply sum_congr
      intro v hv
      rw [observations v hv, mul_sum]
    _ = (columns.map (fun t =>
        (rows.map (fun v => coefficient a v * (incidence v t * z t))).sum)).sum :=
      sum_swap rows columns _
    _ = (columns.map (fun t =>
        (rows.map (fun v => coefficient a v * incidence v t)).sum * z t)).sum := by
      apply sum_congr
      intro t ht
      calc
        _ = (rows.map (fun v => (coefficient a v * incidence v t) * z t)).sum := by
          apply sum_congr
          intro v hv
          exact (Int.mul_assoc _ _ _).symm
        _ = _ := sum_mul rows _ (z t)
    _ = (columns.map (fun t => if t = a then scale * z a else 0)).sum := by
      apply sum_congr
      intro t ht
      rw [leftInverse t ht]
      by_cases same : t = a
      · simp [same]
      · simp [same]
    _ = scale * z a := sum_single columns a (scale * z a) nodup member

#print axioms distance_recurrence
#print axioms reconstruct

end AdjacencyInverse236
