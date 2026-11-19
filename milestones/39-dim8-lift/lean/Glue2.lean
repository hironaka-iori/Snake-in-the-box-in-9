import Moves
/-! Glue, part 3: from cube UNSATs and a cover statement to `NoPit 13 L 64`. -/
set_option linter.deprecated false
namespace Dim8Lift.Sym
open Dim8Lift Dim8Lift.Cube Snake9.LocalWindow

def cntT (S : Nat → Bool) (t : Nat × Nat × Bool × Bool) : Nat := cntSub S t.1 t.2.1 t.2.2.1 t.2.2.2

def maxL {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | x :: xs, f => max (f x) (maxL xs f)

theorem maxL_ge {α : Type} (f : α → Nat) : ∀ (l : List α) (x : α), x ∈ l → f x ≤ maxL l f
  | [], _, h => absurd h (by simp)
  | y :: ys, x, h => by
    unfold maxL
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (maxL_ge f ys x h) (Nat.le_max_right _ _)

theorem maxL_att {α : Type} (f : α → Nat) : ∀ (l : List α), l ≠ [] → ∃ x ∈ l, f x = maxL l f
  | [], h => absurd rfl h
  | y :: ys, _ => by
    unfold maxL
    by_cases hy : maxL ys f ≤ f y
    · exact ⟨y, by simp, by rw [Nat.max_eq_left hy]⟩
    · have hne : ys ≠ [] := by intro e; subst e; simp [maxL] at hy
      obtain ⟨x, hx, e⟩ := maxL_att f ys hne
      exact ⟨x, List.mem_cons_of_mem _ hx, by rw [Nat.max_eq_right (by omega), e]⟩

def kmax (S : Nat → Bool) : Nat := maxL (moves.map Prod.fst) (cntT S)

theorem inSub_comm (a b : Nat) (va vb : Bool) (u : Nat) : inSub a b va vb u = inSub b a vb va u := by
  unfold inSub; cases u.testBit a == va <;> cases u.testBit b == vb <;> rfl

set_option maxRecDepth 100000 in
theorem allT_F : ∀ a b : Fin 8, ∀ va vb : Bool, a.val < b.val → (a.val, b.val, va, vb) ∈ moves.map Prod.fst := by
  decide

theorem mem_allT {a b : Nat} {va vb : Bool} (h : a < b) (hb : b < 8) : (a, b, va, vb) ∈ moves.map Prod.fst :=
  allT_F ⟨a, by omega⟩ ⟨b, hb⟩ va vb h

theorem maxSub_kmax (S : Nat → Bool) : MaxSub S (kmax S) := by
  unfold MaxSub; intro a b ha hb hab va vb
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact maxL_ge (cntT S) _ (a, b, va, vb) (mem_allT h hb)
  · have e : cntSub S a b va vb = cntSub S b a vb va := by
      unfold cntSub; congr 1; funext u; rw [inSub_comm]
    rw [e]; exact maxL_ge (cntT S) _ (b, a, vb, va) (mem_allT h ha)

theorem cnt_word : ∀ (w : List Nat), (∀ c ∈ w, c < 36) → ∀ (p : Nat → Bool),
    cnt 256 (fun u => p (applyW w u)) = cnt 256 p
  | [], _, _ => rfl
  | c :: w, hw, p => by
    have e : (fun u => p (applyW (c :: w) u)) = (fun u => (fun v => p (gen c v)) (applyW w u)) := by
      funext u; rfl
    rw [e, cnt_word w (fun c' h' => hw c' (by simp [h'])) (fun v => p (gen c v)), cnt_perm (hw c (by simp))]

theorem split4 (S : Nat → Bool) : cntSub S 6 7 false false + cntSub S 6 7 true false + cntSub S 6 7 false true +
    cntSub S 6 7 true true = cnt 256 S := by
  unfold cntSub cnt
  rw [← sm_add, ← sm_add, ← sm_add]
  apply sm_congr; intro u _
  unfold inSub
  cases h : S u <;> cases h6 : u.testBit 6 <;> cases h7 : u.testBit 7 <;> simp [h, h6, h7]

theorem kmax_ge (S : Nat → Bool) {L : Nat} (hL : 113 ≤ L) (hc : L ≤ cnt 256 S) : 29 ≤ kmax S := by
  have h := split4 S
  have := maxSub_kmax S
  unfold MaxSub at this
  have h1 := this 6 7 (by omega) (by omega) (by omega) false false
  have h2 := this 6 7 (by omega) (by omega) (by omega) true false
  have h3 := this 6 7 (by omega) (by omega) (by omega) false true
  have h4 := this 6 7 (by omega) (by omega) (by omega) true true
  omega

/-- after the stored move, copy 0 holds exactly `kmax S` vertices and is a largest 6-subcube -/
theorem move_max (S : Nat → Bool) : ∃ w : List Nat, (∀ c ∈ w, c < 36) ∧
    cnt 256 (fun u => S (applyW w u) && decide (u < 64)) = kmax S := by
  have hne : moves.map Prod.fst ≠ [] := by simp [moves]
  obtain ⟨t, ht, e⟩ := maxL_att (cntT S) _ hne
  obtain ⟨⟨t', w⟩, hm, rfl⟩ := List.mem_map.mp ht
  have hok := moves_ok _ hm
  obtain ⟨hw, hmv⟩ := hok
  have hw' : ∀ c ∈ w, c < 36 := by
    intro c hc; have := List.all_eq_true.mp hw c hc; simpa using this
  refine ⟨w, hw', ?_⟩
  unfold kmax; rw [← e]
  unfold cntT cntSub
  rw [← cnt_word w hw' (fun v => S v && inSub t'.1 t'.2.1 t'.2.2.1 t'.2.2.2 v)]
  unfold cnt; apply sm_congr; intro u hu
  have h := hmv ⟨u, hu⟩
  simp only at h
  show (if (S (applyW w u) && decide (u < 64)) = true then 1 else 0) = _
  rw [h]

theorem filter_cnt (P S : Nat → Bool) : ∀ n, (((List.range n).filter P).filter S).length = cnt n (fun u => S u && P u) := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.filter_append, List.length_append, ih, cnt_succ]
    cases hP : P n <;> cases hS : S n <;> simp [hP, hS]

theorem hsub_of_max {S : Nat → Bool} {k : Nat} (h : MaxSub S k) :
    ∀ q, ((subcubes.getD q []).filter S).length ≤ k := by
  intro q
  unfold subcubes; rw [List.getD_eq_getElem?_getD]
  cases e : (List.flatMap _ pairs8)[q]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    have hm := List.mem_of_getElem? e
    simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at hm
    obtain ⟨⟨a, b⟩, hab, v, _, hv⟩ := hm
    rw [mem_pairs8] at hab
    split at hv
    · simp at hv
    · simp only [Option.some.injEq] at hv; subst hv
      unfold R256; rw [filter_cnt]
      unfold MaxSub at h
      have := h a b (by omega) hab.2 (by omega) (v % 2 == 1) (v / 2 == 1)
      unfold cntSub inSub at this; exact this

/-- The cover statement: a largest-copy normalised Pit is, after a further symmetry, one of `reps`
(pairs `(size, mask)`) on copy 0. -/
def CoverOK (L : Nat) (reps : List (Nat × Nat)) : Prop :=
  ∀ (S : Nat → Bool) (ℓ : Nat → Nat) (k : Nat), Pit 13 L 64 S ℓ → 29 ≤ k → MaxSub S k →
    cnt 256 (fun u => S u && decide (u < 64)) = k →
    ∃ w : List Nat, (∀ c ∈ w, c < 36) ∧ ∃ r ∈ reps, r.1 = k ∧ ∀ u, u < 64 → S (applyW w u) = r.2.testBit u

/-- **Glue.** Cube UNSATs for every representative and the cover statement give `NoPit 13 L 64`. -/
theorem noPit_of_cubes {L : Nat} (reps : List (Nat × Nat)) (h113 : 113 ≤ L) (h255 : L ≤ 255)
    (hcov : CoverOK L reps) (hcubes : ∀ r ∈ reps, Unsat (cubeCnfC4 13 L r.2 r.1)) : NoPit 13 L 64 := by
  intro S ℓ hp
  obtain ⟨w, hw, hcnt⟩ := move_max S
  have hp1 := pit_word w hw hp
  have hm1 := maxSub_word w hw (maxSub_kmax S)
  have hk := kmax_ge S h113 hp.card
  obtain ⟨w2, hw2, r, hr, hrk, hA⟩ := hcov _ _ _ hp1 hk hm1 hcnt
  have hp2 := pit_word w2 hw2 hp1
  have hm2 := maxSub_word w2 hw2 hm1
  rw [← hrk] at hm2
  exact no_pit_of_unsat (hcubes r hr) (by omega) h255 (by omega) hp2 hA (hsub_of_max hm2)

end Dim8Lift.Sym

#print axioms Dim8Lift.Sym.noPit_of_cubes
