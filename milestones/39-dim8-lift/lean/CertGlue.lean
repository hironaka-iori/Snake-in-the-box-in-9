import LocalWindowModel
/-! Glue between an LRAT replay of a compacted core (the repository's checker proves `Unsat core'`)
and `Unsat full` for a large CNF generated in Lean.

* `unsat_of_rename`: `core'` is `core` with variables renamed through `back` (new variable v' stands for
  old variable `back[v'-1]`); no injectivity is needed.
* `unsat_of_walk`: `core` (with indices) is a sub-list of `full`, checked by one ordered walk. -/
namespace Dim8Lift.CertGlue
open Snake9.LocalWindow

def renOk (back : List Nat) (l' l : Int) : Bool :=
  (decide (0 < l') == decide (0 < l)) && decide (l' ≠ 0) && decide (l ≠ 0) && (back.getD (l'.natAbs - 1) 0 == l.natAbs)

def renChk (back : List Nat) : List (List Int) → List (List Int) → Bool
  | [], [] => true
  | c' :: cs', c :: cs => c'.length == c.length && (List.zip c' c).all (fun p => renOk back p.1 p.2) && renChk back cs' cs
  | _, _ => false

theorem lit_ren (τ : Nat → Bool) (back : List Nat) {l' l : Int} (h : renOk back l' l = true) :
    litTrue (fun v => τ (back.getD (v - 1) 0)) l' = litTrue τ l := by
  unfold renOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, decide_eq_decide] at h
  obtain ⟨⟨⟨hs, h1⟩, h2⟩, hb⟩ := h
  unfold litTrue
  by_cases p : 0 < l'
  · have q : 0 < l := hs.mp p
    rw [if_pos p, if_pos q]
    have e1 : l'.toNat = l'.natAbs := by omega
    have e2 : l.toNat = l.natAbs := by omega
    simp only [e1, e2, ← hb]
  · have q : ¬ 0 < l := fun hq => p (hs.mpr hq)
    rw [if_neg p, if_neg q]
    have e1 : (-l').toNat = l'.natAbs := by omega
    have e2 : (-l).toNat = l.natAbs := by omega
    simp only [e1, e2, ← hb]

theorem clause_ren (τ : Nat → Bool) (back : List Nat) : ∀ (c' c : List Int), c'.length = c.length →
    (List.zip c' c).all (fun p => renOk back p.1 p.2) = true →
    clauseTrue (fun v => τ (back.getD (v - 1) 0)) c' = clauseTrue τ c
  | [], [], _, _ => rfl
  | l' :: c', l :: c, hlen, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    simp only [clauseTrue, List.any_cons] at *
    rw [lit_ren τ back h.1]
    have := clause_ren τ back c' c (by simp at hlen; omega) h.2
    unfold clauseTrue at this; rw [this]
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

theorem unsat_of_rename (back : List Nat) : ∀ (core' core : List (List Int)), renChk back core' core = true →
    Unsat core' → Unsat core := by
  intro core' core h hU τ
  have key : ∀ (a b : List (List Int)), renChk back a b = true →
      cnfTrue (fun v => τ (back.getD (v - 1) 0)) a = cnfTrue τ b := by
    intro a
    induction a with
    | nil => intro b hb; cases b with
      | nil => rfl
      | cons _ _ => simp [renChk] at hb
    | cons c' cs' ih =>
      intro b hb
      cases b with
      | nil => simp [renChk] at hb
      | cons c cs =>
        simp only [renChk, Bool.and_eq_true, beq_iff_eq] at hb
        simp only [cnfTrue, List.all_cons] at *
        rw [clause_ren τ back c' c hb.1.1 hb.1.2]
        have := ih cs hb.2; unfold cnfTrue at this; rw [this]
  rw [← key core' core h]; exact hU _

def walk : List (List Int) → Nat → List (Nat × List Int) → Bool
  | _, _, [] => true
  | [], _, _ :: _ => false
  | f :: fs, i, (j, c) :: cs =>
    if i = j then (f == c) && walk fs (i + 1) cs
    else if i < j then walk fs (i + 1) ((j, c) :: cs) else false

theorem walk_mem : ∀ (full : List (List Int)) (i : Nat) (core : List (Nat × List Int)), walk full i core = true →
    ∀ p ∈ core, p.2 ∈ full
  | _, _, [], _, p, hp => by simp at hp
  | [], _, _ :: _, h, _, _ => by simp [walk] at h
  | f :: fs, i, (j, c) :: cs, h, p, hp => by
    unfold walk at h
    by_cases e : i = j
    · rw [if_pos e] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [h.1]
      · exact List.mem_cons_of_mem _ (walk_mem fs (i + 1) cs h.2 p hp)
    · rw [if_neg e] at h
      by_cases l : i < j
      · rw [if_pos l] at h
        exact List.mem_cons_of_mem _ (walk_mem fs (i + 1) ((j, c) :: cs) h p hp)
      · rw [if_neg l] at h; simp at h

theorem unsat_of_walk (full : List (List Int)) (core : List (Nat × List Int)) (h : walk full 0 core = true)
    (hU : Unsat (core.map Prod.snd)) : Unsat full := by
  intro τ
  cases hf : cnfTrue τ full
  · rfl
  · exfalso
    have hc : cnfTrue τ (core.map Prod.snd) = true := by
      unfold cnfTrue at *
      rw [List.all_eq_true] at *
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact hf _ (walk_mem full 0 core h p hp)
    rw [hU τ] at hc; exact absurd hc (by simp)

end Dim8Lift.CertGlue

#print axioms Dim8Lift.CertGlue.unsat_of_rename
#print axioms Dim8Lift.CertGlue.unsat_of_walk
