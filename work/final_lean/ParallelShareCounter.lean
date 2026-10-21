import ParallelShareTerm

/-!
Semantic assignments for the clipped upward totalizers used by `share_enc.py`.
The vectors include repeated unary literals. A merge adds all pairs of input
thresholds, clips the output threshold at `cap`, and does not require reverse
implications. `trim` models the discarded overflow bit between centres.
This module proves the counter circuit semantics, not geometric applicability
or identification with any emitted DIMACS file.
-/
namespace Snake9.ParallelShareCounter

def unary (n value : Nat) : List Bool :=
  (List.range n).map fun i => decide (i + 1 ≤ value)

def Represents (xs : List Bool) (value : Nat) : Prop :=
  ∀ i (hi : i < xs.length), xs[i]'hi = decide (i + 1 ≤ value)

theorem unary_length (n value : Nat) : (unary n value).length = n := by
  simp [unary]

theorem unary_represents (n value : Nat) : Represents (unary n value) value := by
  intro i hi
  simp [unary] at hi ⊢

theorem represents_take {xs : List Bool} {value : Nat}
    (h : Represents xs value) (n : Nat) : Represents (xs.take n) value := by
  intro i hi
  have hil : i < xs.length := by simp only [List.length_take] at hi; omega
  simpa using h i hil

/-- Threshold zero is always true; positive thresholds read the unary vector. -/
def input (xs : List Bool) (i : Nat) : Bool :=
  if i = 0 then true else xs.getD (i - 1) false

theorem input_sem {xs : List Bool} {value i : Nat}
    (h : Represents xs value) (hi : i ≤ xs.length) :
    input xs i = decide (i ≤ value) := by
  by_cases hz : i = 0
  · simp [input, hz]
  · have hit : i - 1 < xs.length := by omega
    simp only [input, hz, if_false, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hit, Option.getD_some]
    rw [h _ hit]
    rw [show i - 1 + 1 = i by omega]

/-- The precise upward clause emitted for one pair in `_merge`. -/
def mergeClause (xs ys out : List Bool) (cap i j : Nat) : Bool :=
  !input xs i || !input ys j || out.getD (min (i + j) cap - 1) false

def MergeOK (xs ys out : List Bool) (cap : Nat) : Prop :=
  ∀ i j, i ≤ xs.length → j ≤ ys.length → 0 < i + j →
    mergeClause xs ys out cap i j = true

theorem merge_satisfies {xs ys : List Bool} {a b cap : Nat}
    (hx : Represents xs a) (hy : Represents ys b) (hc : 0 < cap) :
    MergeOK xs ys (unary (min (xs.length + ys.length) cap) (a + b)) cap := by
  intro i j hi hj hij
  have ht : min (i + j) cap - 1 < min (xs.length + ys.length) cap := by omega
  have hout := unary_represents (min (xs.length + ys.length) cap) (a + b)
  have hout' := hout (min (i + j) cap - 1) (by simpa [unary_length] using ht)
  have hidx : min (i + j) cap - 1 <
      (unary (min (xs.length + ys.length) cap) (a + b)).length := by
    simpa [unary_length] using ht
  unfold mergeClause
  rw [input_sem hx hi, input_sem hy hj]
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hidx, Option.getD_some, hout']
  by_cases hia : i ≤ a
  · by_cases hjb : j ≤ b
    · have hab : min (i + j) cap - 1 + 1 ≤ a + b := by omega
      simp [hia, hjb, hab]
    · simp [hjb]
  · simp [hia]

inductive Circuit where
  | leaf (bits : List Bool)
  | merge (left right : Circuit)
  | trim (width : Nat) (child : Circuit)

def Circuit.value : Circuit → Nat
  | .leaf bits => bits.count true
  | .merge left right => left.value + right.value
  | .trim _ child => child.value

def Circuit.Good : Circuit → Prop
  | .leaf bits => Represents bits (bits.count true)
  | .merge left right => left.Good ∧ right.Good
  | .trim _ child => child.Good

def Circuit.output (cap : Nat) : Circuit → List Bool
  | .leaf bits => bits.take cap
  | .merge left right =>
    unary (min ((left.output cap).length + (right.output cap).length) cap)
      (left.value + right.value)
  | .trim width child => (child.output cap).take width

def Circuit.Satisfied (cap : Nat) : Circuit → Prop
  | .leaf _ => True
  | .merge left right => left.Satisfied cap ∧ right.Satisfied cap ∧
      MergeOK (left.output cap) (right.output cap)
        ((Circuit.merge left right).output cap) cap
  | .trim _ child => child.Satisfied cap

theorem Circuit.represents (c : Circuit) (cap : Nat) (h : c.Good) :
    Represents (c.output cap) c.value := by
  induction c with
  | leaf bits => exact represents_take h cap
  | merge left right ihl ihr => exact unary_represents _ _
  | trim width child ih => exact represents_take (ih h) width

/-- One assignment satisfies every merge in a tree, including every clipped or
discarded intermediate output. No cap assumption is used for merge clauses. -/
theorem Circuit.satisfies (c : Circuit) {cap : Nat} (hc : 0 < cap) (h : c.Good) :
    c.Satisfied cap := by
  induction c with
  | leaf bits => trivial
  | merge left right ihl ihr =>
    exact ⟨ihl h.1, ihr h.2, merge_satisfies (left.represents cap h.1)
      (right.represents cap h.2) hc⟩
  | trim width child ih => exact ih h

/-- The negative overflow unit is true whenever the semantic sum is below cap. -/
theorem overflow_false {xs : List Bool} {value cap : Nat}
    (h : Represents xs value) (hv : value < cap) :
    xs.getD (cap - 1) false = false := by
  by_cases hi : cap - 1 < xs.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      h _ hi]
    have hn : ¬ (cap - 1 + 1 ≤ value) := by omega
    simp [hn]
  · have hn : xs.length ≤ cap - 1 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hn]
    rfl

/-- The sequential centre merge, with the overflow bit discarded at each step. -/
def accumulate (bound : Nat) : Circuit → List Circuit → Circuit
  | acc, [] => acc
  | acc, c :: cs => accumulate bound (.trim bound (.merge acc c)) cs

def PrefixBounds (cap : Nat) : Circuit → List Circuit → Prop
  | acc, [] => acc.value < cap
  | acc, c :: cs =>
      acc.value + c.value < cap ∧ PrefixBounds cap (.trim (cap - 1) (.merge acc c)) cs

theorem accumulate_good (bound : Nat) (acc : Circuit) (cs : List Circuit)
    (ha : acc.Good) (hs : ∀ c ∈ cs, c.Good) : (accumulate bound acc cs).Good := by
  induction cs generalizing acc with
  | nil => exact ha
  | cons c cs ih =>
    apply ih (.trim bound (.merge acc c))
    · exact ⟨ha, hs c (by simp)⟩
    · intro d hd; exact hs d (by simp [hd])

theorem prefix_bounds (cap : Nat) (acc : Circuit) (cs : List Circuit)
    (h : acc.value + (cs.map Circuit.value).sum < cap) : PrefixBounds cap acc cs := by
  induction cs generalizing acc with
  | nil => simpa [PrefixBounds] using h
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons] at h
    constructor
    · omega
    · apply ih
      simp only [Circuit.value]
      omega

/-- Every overflow unit actually emitted by the sequential centre merge. -/
def OverflowUnits (cap : Nat) : Circuit → List Circuit → Prop
  | _, [] => True
  | acc, c :: cs =>
      ((Circuit.merge acc c).output cap).getD (cap - 1) false = false ∧
      OverflowUnits cap (.trim (cap - 1) (.merge acc c)) cs

theorem overflow_units (bound : Nat) (acc : Circuit) (cs : List Circuit)
    (ha : acc.Good) (hs : ∀ c ∈ cs, c.Good)
    (hb : PrefixBounds (bound + 1) acc cs) : OverflowUnits (bound + 1) acc cs := by
  induction cs generalizing acc with
  | nil => trivial
  | cons c cs ih =>
    have hc : c.Good := hs c (by simp)
    have hm : (Circuit.merge acc c).Good := ⟨ha, hc⟩
    constructor
    · exact overflow_false ((Circuit.merge acc c).represents _ hm) hb.1
    · exact ih (.trim bound (.merge acc c)) hm
        (fun d hd => hs d (by simp [hd])) hb.2

/-- All sequential centre merges have satisfying assignments if their unary
leaves are valid; a bound on the total also makes every overflow unit true. -/
theorem sequential_counter_sound (bound : Nat) (acc : Circuit) (cs : List Circuit)
    (ha : acc.Good) (hs : ∀ c ∈ cs, c.Good)
    (hbound : acc.value + (cs.map Circuit.value).sum ≤ bound) :
    (accumulate bound acc cs).Satisfied (bound + 1) ∧
    OverflowUnits (bound + 1) acc cs := by
  exact ⟨Circuit.satisfies _ (by omega) (accumulate_good bound acc cs ha hs),
    overflow_units bound acc cs ha hs (prefix_bounds _ _ _ (by omega))⟩

open Snake9.ParallelShareTerm

/-- The six-bit leaves used when none of the three other corners is fixed. -/
def leaves (e a b c : Bool) : List Bool :=
  [e, e, gate1 e a b c, gate3 e a b c, gate3 e a b c, gate3 e a b c]

theorem leaves_eq_unary : ∀ e a b c : Bool,
    leaves e a b c = unary 6 ((leaves e a b c).count true) := by
  decide +kernel

theorem leaves_good (e a b c : Bool) : (Circuit.leaf (leaves e a b c)).Good := by
  change Represents (leaves e a b c) _
  have h := leaves_eq_unary e a b c
  have hr := unary_represents 6 ((leaves e a b c).count true)
  rw [← h] at hr
  exact hr

theorem one_fixed_eq_unary : ∀ e a b : Bool,
    [e, e, gate1 e true a b] = unary 3 ([e, e, gate1 e true a b].count true) := by
  decide +kernel

theorem one_fixed_good (e a b : Bool) :
    (Circuit.leaf [e, e, gate1 e true a b]).Good := by
  change Represents [e, e, gate1 e true a b] _
  have h := one_fixed_eq_unary e a b
  have hr := unary_represents 3 ([e, e, gate1 e true a b].count true)
  rw [← h] at hr
  exact hr

theorem two_fixed_good (e : Bool) : (Circuit.leaf [e, e]).Good := by
  cases e <;> intro i hi <;> simp only [List.length_cons, List.length_nil] at hi
  all_goals have h : i = 0 ∨ i = 1 := by omega
  all_goals rcases h with rfl | rfl <;> simp

theorem leaves_weight : ∀ e a b c : Bool, others a b c ≤ 2 →
    (leaves e a b c).count true = if e then 6 / (1 + others a b c) else 0 := by
  decide +kernel

#print axioms merge_satisfies
#print axioms Circuit.satisfies
#print axioms overflow_false
#print axioms sequential_counter_sound
#print axioms leaves_good
#print axioms one_fixed_good
#print axioms two_fixed_good
#print axioms leaves_weight
end Snake9.ParallelShareCounter
