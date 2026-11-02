import WindowAutomatonDefs
import Mathlib.Tactic

namespace Snake9.Direction77
open Snake9.WindowAutomaton

theorem prefixes_append_subset (xs ys : List Nat) :
    prefixes xs ⊆ prefixes (xs ++ ys) := by
  induction xs with
  | nil => simp [prefixes]
  | cons a xs ih =>
    intro seg h
    simp only [prefixes, List.cons_append, List.mem_cons, List.mem_map] at h ⊢
    rcases h with h | ⟨t, ht, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ih ht, rfl⟩

theorem blocks_append_subset (xs ys : List Nat) :
    blocks xs ⊆ blocks (xs ++ ys) := by
  induction xs with
  | nil => simp [blocks]
  | cons a xs ih =>
    intro seg h
    simp only [blocks, List.cons_append, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (prefixes_append_subset (a::xs) ys h)
    · exact Or.inr (ih h)

theorem induced_prefix (xs ys : List Nat) (h : inducedPattern (xs ++ ys) = true) :
    inducedPattern xs = true := by
  apply List.all_eq_true.mpr
  intro seg hs
  exact List.all_eq_true.mp h seg (blocks_append_subset xs ys hs)

/-- Rejection of a non-induced prefix is safe for every completion. -/
def allPruned : Nat → Nat → List Nat → (List Nat → Bool) → Bool
  | 0, _, pre, p => !inducedPattern pre || p pre
  | n+1, bound, pre, p => !inducedPattern pre ||
      allBelow (bound+1) (fun a => allPruned n
        (if bound < a+1 then a+1 else bound) (pre ++ [a]) p)

theorem allPruned_spec : ∀ (n bound : Nat) (pre : List Nat) (p : List Nat → Bool),
    allPruned n bound pre p = true → ∀ (tail : List Nat),
    tail.length = n → isRGS tail bound = true →
    inducedPattern (pre ++ tail) = true → p (pre ++ tail) = true
  | 0, bound, pre, p, h, [], _, _, hind => by
    have hi : inducedPattern pre = true := by simpa using hind
    simpa [allPruned, hi] using h
  | 0, _, _, _, _, _ :: _, hlen, _, _ => by simp at hlen
  | n+1, _, _, _, _, [], hlen, _, _ => by simp at hlen
  | n+1, bound, pre, p, h, a::tail, hlen, hrgs, hind => by
    have hpre := induced_prefix pre (a::tail) hind
    simp only [allPruned, hpre, Bool.not_true, Bool.false_or] at h
    simp only [isRGS, Bool.and_eq_true, decide_eq_true_eq] at hrgs
    have ha := allBelow_spec (bound+1) _ h a (by omega)
    have hi := allPruned_spec n _ (pre ++ [a]) p ha tail
      (by simpa using hlen) hrgs.2 (by simpa [List.append_assoc] using hind)
    simpa [List.append_assoc] using hi

#print axioms prefixes_append_subset
#print axioms blocks_append_subset
#print axioms induced_prefix
#print axioms allPruned_spec
end Snake9.Direction77
