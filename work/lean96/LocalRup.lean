import Std

namespace Snake9.LocalRup
abbrev Lit := Nat × Bool
def value (p : Nat → Bool) (l : Lit) : Bool := p l.1 == l.2
def clause (p : Nat → Bool) (c : List Lit) : Bool := c.any (value p)
def prune (c a : List Lit) : List Lit := c.filter (fun l => !a.contains l)
def check : List (List Lit) → List Lit → Bool
  | [], _ => false
  | c::cs, a =>
    match prune c a with
    | [] => true
    | [l] => check cs ((l.1,!l.2)::a)
    | _ => false

theorem prune_true (p : Nat → Bool) (c a : List Lit)
    (hc : clause p c = true) (ha : ∀ l ∈ a, value p l = false) :
    clause p (prune c a) = true := by
  obtain ⟨l,hl,hv⟩ := List.any_eq_true.mp hc
  apply List.any_eq_true.mpr
  refine ⟨l,List.mem_filter.mpr ⟨hl,?_⟩,hv⟩
  have hn : l ∉ a := by
    intro h
    have he := ha l h
    rw [hv] at he
    contradiction
  simp [hn]

theorem check_sound (p : Nat → Bool) (cs : List (List Lit)) (a : List Lit)
    (hs : ∀ c ∈ cs, clause p c = true) (ha : ∀ l ∈ a, value p l = false)
    (hc : check cs a = true) : False := by
  induction cs generalizing a with
  | nil => contradiction
  | cons c cs ih =>
    have hp := prune_true p c a (hs c (by simp)) ha
    have ht : ∀ c ∈ cs, clause p c = true := fun c h => hs c (List.mem_cons_of_mem _ h)
    unfold check at hc
    split at hc
    · rename_i he
      simp only [he,clause,List.any_nil] at hp
      contradiction
    · rename_i l he
      apply ih _ ht _ hc
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · simp only [he,clause,List.any_cons,List.any_nil,Bool.or_false] at hp
        rcases l with ⟨i,b⟩
        cases b <;> cases hpi : p i <;> simp_all [value]
      · exact ha k hk
    · contradiction

theorem prove_clause (cs : List (List Lit)) (target : List Lit)
    (hc : check cs target = true) (p : Nat → Bool)
    (hs : ∀ c ∈ cs, clause p c = true) : clause p target = true := by
  cases ht : clause p target with
  | true => rfl
  | false =>
    exfalso
    apply check_sound p cs target hs _ hc
    intro l hl
    have hn : ¬ value p l = true := by
      intro hv
      have : clause p target = true := List.any_eq_true.mpr ⟨l,hl,hv⟩
      rw [ht] at this
      contradiction
    exact Bool.eq_false_iff.mpr hn

theorem sat_nil (p : Nat → Bool) : ∀ c ∈ ([] : List (List Lit)), clause p c = true := by simp

theorem sat_cons {p : Nat → Bool} {c : List Lit} {cs : List (List Lit)}
    (hc : clause p c = true) (hs : ∀ x ∈ cs, clause p x = true) :
    ∀ x ∈ c::cs, clause p x = true := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hc
  · exact hs x hx

#print axioms prove_clause
end Snake9.LocalRup
