import CoverTree

namespace Snake9.Balanced89
universe u

/-- A literal lookup tree. Correct split sizes are checked independently;
the constructor does not impose a balancing condition. -/
inductive Table (α : Type u) where
  | empty
  | leaf (value : α)
  | node (leftSize : Nat) (left right : Table α)
  deriving Repr

def flatten {α : Type u} : Table α → List α
  | .empty => []
  | .leaf a => [a]
  | .node _ left right => flatten left ++ flatten right

def size {α : Type u} : Table α → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ left right => size left + size right

def lookup {α : Type u} : Table α → Nat → α → α
  | .empty, _, d => d
  | .leaf a, i, d => if i = 0 then a else d
  | .node n left right, i, d =>
      if i < n then lookup left i d else lookup right (i-n) d

def Valid {α : Type u} : Table α → Prop
  | .empty => True
  | .leaf _ => True
  | .node n left right => n = (flatten left).length ∧ Valid left ∧ Valid right

def check {α : Type u} : Table α → Bool
  | .empty => true
  | .leaf _ => true
  | .node n left right => decide (n = size left) && (check left && check right)

theorem size_eq_length_flatten {α : Type u} (t : Table α) :
    size t = (flatten t).length := by
  induction t with
  | empty => rfl
  | leaf a => rfl
  | node n left right ihl ihr => simp only [size,flatten,List.length_append,ihl,ihr]

theorem check_iff_valid {α : Type u} (t : Table α) : check t = true ↔ Valid t := by
  induction t with
  | empty => simp [check,Valid]
  | leaf a => simp [check,Valid]
  | node n left right ihl ihr =>
    simp only [check,Valid,Bool.and_eq_true_iff,decide_eq_true_eq,
      size_eq_length_flatten,ihl,ihr]

instance {α : Type u} (t : Table α) : Decidable (Valid t) :=
  decidable_of_iff (check t = true) (check_iff_valid t)

theorem getD_append_eq {α : Type u} (xs ys : List α) (i : Nat) (d : α) :
    (xs ++ ys).getD i d =
      if i < xs.length then xs.getD i d else ys.getD (i-xs.length) d := by
  by_cases hi : i < xs.length
  · simp only [hi,↓reduceIte,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
  · simp only [hi,↓reduceIte,List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_of_not_gt hi)]

/-- The statement includes all out-of-range indices and any supplied default. -/
theorem lookup_eq_getD {α : Type u} (t : Table α) :
    Valid t → ∀ (i : Nat) (d : α), lookup t i d = (flatten t).getD i d := by
  induction t with
  | empty => intro hv i d; rfl
  | leaf a => intro hv i d; cases i <;> rfl
  | node n left right ihl ihr =>
    intro hv i d
    obtain ⟨hn,hl,hr⟩ := hv
    simp only [lookup,flatten,getD_append_eq,← hn]
    by_cases hi : i < n
    · simp only [hi,↓reduceIte]
      exact ihl hl i d
    · simp only [hi,↓reduceIte]
      exact ihr hr (i-n) d

/-- One checked flatten equality transports every lookup to an original list. -/
theorem lookup_eq_list {α : Type u} (t : Table α) (xs : List α)
    (ht : check t = true) (hf : flatten t = xs) (i : Nat) (d : α) :
    lookup t i d = xs.getD i d := by
  rw [lookup_eq_getD t ((check_iff_valid t).mp ht) i d,hf]

#print axioms size_eq_length_flatten
#print axioms check_iff_valid
#print axioms getD_append_eq
#print axioms lookup_eq_getD
#print axioms lookup_eq_list
end Snake9.Balanced89
