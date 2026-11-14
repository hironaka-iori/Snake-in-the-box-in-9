import Std

namespace Entry87.Matching

abbrev Shape := Fin 256

def value (w : Shape → Nat) (s : Option Shape) : Nat :=
  match s with
  | none => 0
  | some t => w t

def choose (w : Shape → Nat) (a b : Option Shape) : Option Shape :=
  if value w a ≥ value w b then a else b

theorem choose_value (w : Shape → Nat) (a b : Option Shape) :
    value w (choose w a b) = max (value w a) (value w b) := by
  simp only [choose]
  split <;> omega

theorem choice_bound (w : Shape → Nat) (a b selected : Option Shape)
    (valid : selected = none ∨ selected = a ∨ selected = b) :
    value w selected ≤ value w (choose w a b) := by
  rw [choose_value]
  rcases valid with h | h | h
  · simp [h,value]
  · rw [h]; omega
  · rw [h]; omega

def total (w : Shape → Nat) (l : List (Option Shape)) := (l.map (value w)).sum
def choices (w : Shape → Nat) (l : List (Option Shape × Option Shape)) :=
  l.map (fun p => choose w p.1 p.2)

inductive Legal : List (Option Shape) → List (Option Shape × Option Shape) → Prop
  | nil : Legal [] []
  | cons {s a b xs ps} : (s=none ∨ s=a ∨ s=b) → Legal xs ps → Legal (s::xs) ((a,b)::ps)

theorem independent_matching (w : Shape → Nat) (allowed : List (Option Shape × Option Shape))
    (selected : List (Option Shape))
    (ok : Legal selected allowed) :
    total w selected ≤ total w (choices w allowed) := by
  induction ok with
  | nil => simp [total,choices]
  | cons h _ ih =>
    obtain bound := choice_bound w _ _ _ h
    simpa only [total,choices,List.map_cons,List.sum_cons] using Nat.add_le_add bound ih

#print axioms choose_value
#print axioms independent_matching
end Entry87.Matching
