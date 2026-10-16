import DfsDecide
namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option exponentiation.threshold 600

/- A bounded-work variant. Exhausted fuel falls back to safe upper bounds. -/
def boundFast (head ban : Nat) : Nat :=
  let F := freeOf ban
  let R0 := expand (2 ^ head) &&& F
  match reach F 32 R0 with
  | some R =>
    if (R0 &&& R) == R0 then
      let a := kcount (R &&& parMask (!bitParity head)) 128
      let b := kcount (R &&& parMask (bitParity head)) 128
      min (min a (b + 1) + min b a) (peelB head (R ||| 2 ^ head) 32)
    else 512
  | none => 512

theorem boundFast_sound {head ban : Nat} {xs : List Nat} (v : ValidExt head ban xs)
    (hban : ban.testBit head = true) : xs.length ≤ boundFast head ban := by
  have hlt := v.lt
  have hnd := v.nodup
  have fallback : xs.length ≤ 512 := by
    rw [← countBits_full]
    apply length_le_countBits full 512 xs hnd
    intro y hy
    refine ⟨hlt y hy, ?_⟩
    unfold full; rw [Nat.testBit_two_pow_sub_one]; simp [hlt y hy]
  cases xs with
  | nil => simp
  | cons x0 xs0 =>
  have hh : head < 512 := by cases v with | cons _ _ _ _ _ _ hh _ _ _ => exact hh
  unfold boundFast
  simp only
  split
  · rename_i R hR
    split
    · rename_i hcheck
      have hclosed := reach_closed 32 _ R hR
      have hstart : ∀ z : Fin 512, (expand (2 ^ head) &&& freeOf ban).testBit z.val = true →
          R.testBit z.val = true := by
        intro z hz
        have e := beq_iff_eq.mp hcheck
        rw [← e, Nat.testBit_and, Bool.and_eq_true] at hz
        exact hz.2
      have hR : ∀ y ∈ x0 :: xs0, R.testBit y = true :=
        fun y hy => v.in_region hclosed hstart (Or.inl rfl) (fun _ h => h) y hy
      have hnotin : head ∉ x0 :: xs0 := by
        intro hm
        have := v.not_banned head hm
        rw [hban] at this; exact absurd this (by decide)
      apply Nat.le_min.mpr
      constructor
      · -- parity bound
        obtain ⟨c1, c2⟩ := v.parity_counts
        have ha : ((x0 :: xs0).filter (fun x => bitParity x != bitParity head)).length ≤
            kcount (R &&& parMask (!bitParity head)) 128 := by
          apply length_le_kcount 128 _ _ (hnd.sublist List.filter_sublist)
          intro y hy
          obtain ⟨hy, hp⟩ := List.mem_filter.mp hy
          refine ⟨hlt y hy, ?_⟩
          rw [Nat.testBit_and, hR y hy, parMask_testBit _ ⟨y, hlt y hy⟩]
          simp only at hp ⊢
          revert hp; cases bitParity y <;> cases bitParity head <;> decide
        have hb : ((x0 :: xs0).filter (fun x => bitParity x == bitParity head)).length ≤
            kcount (R &&& parMask (bitParity head)) 128 := by
          apply length_le_kcount 128 _ _ (hnd.sublist List.filter_sublist)
          intro y hy
          obtain ⟨hy, hp⟩ := List.mem_filter.mp hy
          refine ⟨hlt y hy, ?_⟩
          rw [Nat.testBit_and, hR y hy, parMask_testBit _ ⟨y, hlt y hy⟩]
          simp only at hp ⊢
          revert hp; cases bitParity y <;> cases bitParity head <;> decide
        rw [c1] at ha; rw [c2] at hb
        simp only [Nat.min_def]
        split <;> split <;> omega
      · -- leaf-peeling bound
        apply peel_sound head hh 32 _ _ v.walk
        · exact List.nodup_cons.mpr ⟨hnotin, hnd⟩
        · exact hlt
        · rw [Nat.testBit_or, Nat.testBit_two_pow]; simp
        · intro y hy; rw [Nat.testBit_or, hR y hy]; rfl
    · exact fallback
  · exact fallback

def searchFast (head ban need : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun need rec head ban =>
      if boundFast head ban < need + 1 then false
      else anyBelow (fun k => !(ban.testBit (head ^^^ 2 ^ k)) &&
        rec (head ^^^ 2 ^ k) (ban ||| cnMask head)) 9) need head ban

theorem searchFast_zero (head ban : Nat) : searchFast head ban 0 = true := rfl
theorem searchFast_succ (head ban need : Nat) : searchFast head ban (need + 1) =
    if boundFast head ban < need + 1 then false
    else anyBelow (fun k => !(ban.testBit (head ^^^ 2 ^ k)) &&
      searchFast (head ^^^ 2 ^ k) (ban ||| cnMask head) need) 9 := rfl

theorem searchFast_sound : ∀ need head ban, ban.testBit head = true →
    searchFast head ban need = false → ∀ xs, ValidExt head ban xs → xs.length < need := by
  intro need
  induction need with
  | zero => intro head ban _ h; rw [searchFast_zero] at h; exact absurd h (by simp)
  | succ need ih =>
    intro head ban hban h xs v
    rw [searchFast_succ] at h
    split at h
    · have := boundFast_sound v hban
      omega
    · cases v with
      | nil => simp
      | cons _ _ x xs k hk hh hx hfree rest =>
        have hf := anyBelow_false 9 h k hk
        rw [← hx, hfree] at hf
        simp only [Bool.not_false, Bool.true_and] at hf
        have hban' : (ban ||| cnMask head).testBit x = true := by
          rw [Nat.testBit_or, hx, cnMask_nbr head k hk]; simp
        have := ih x (ban ||| cnMask head) hban' hf xs rest
        simp only [List.length_cons]
        omega

theorem searchFast_of_children (head ban need : Nat)
    (h : ∀ k, k < 9 → (ban.testBit (head ^^^ 2 ^ k) = true ∨
      searchFast (head ^^^ 2 ^ k) (ban ||| cnMask head) need = false)) :
    searchFast head ban (need + 1) = false := by
  rw [searchFast_succ]
  split
  · rfl
  · have : ∀ n, n ≤ 9 → anyBelow (fun k => !(ban.testBit (head ^^^ 2 ^ k)) &&
        searchFast (head ^^^ 2 ^ k) (ban ||| cnMask head) need) n = false := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        rw [anyBelow_succ, ih (by omega)]
        rcases h n (by omega) with hb | hs
        · rw [hb]; rfl
        · rw [hs]; simp
    exact this 9 (Nat.le_refl 9)

/-- Version 2 of `no192_from_prefix` (prefix of at least two vertices). -/
theorem no192_from_prefixFast (pre : Array Nat) (K : Nat) (hK2 : 2 ≤ K) (hK : K ≤ 193)
    (hs : searchFast pre[K - 1]! (banFrom (fun i => pre[i]!) (K - 1)) (193 - K) = false) :
    ¬ ∃ p : Snake 192, ∀ i (h : i < K), (p.vertex ⟨i, by omega⟩).val = pre[i]! := by
  rintro ⟨p, hp⟩
  have hv : ∀ i, i < K → vals p i = pre[i]! := by
    intro i hi
    have hi1 : i < 193 := by omega
    simp only [vals, hi1, dite_true]
    exact hp i hi
  have hban : banFrom (vals p) (K - 1) = banFrom (fun i => pre[i]!) (K - 1) :=
    banFrom_congr _ _ _ (fun i hi => hv i (by omega))
  have hhead : vals p (K - 1) = pre[K - 1]! := hv (K - 1) (by omega)
  -- the head lies in the ban mask: it is a neighbour of the previous vertex
  have hin : (banFrom (vals p) (K - 1)).testBit (vals p (K - 1)) = true := by
    have e : K - 1 = (K - 2) + 1 := by omega
    rw [e, banFrom_succ, Nat.testBit_or]
    have h1 : K - 2 < 193 := by omega
    have h2 : K - 2 + 1 < 193 := by omega
    have hadj : Adj (p.vertex ⟨K - 2, h1⟩) (p.vertex ⟨K - 2 + 1, h2⟩) :=
      (p.induced ⟨K - 2, h1⟩ ⟨K - 2 + 1, h2⟩ (by simp)).mpr rfl
    obtain ⟨k, hk, hke⟩ := (adj_iff_coordinate_flip _ _).mp hadj
    have ev1 : vals p (K - 2) = (p.vertex ⟨K - 2, h1⟩).val := by simp [vals, h1]
    have ev2 : vals p (K - 2 + 1) = (p.vertex ⟨K - 2 + 1, h2⟩).val := by simp [vals, h2]
    rw [ev1, ev2, hke]
    have := cnMask_nbr (p.vertex ⟨K - 2, h1⟩).val k hk
    simp only [Bool.or_eq_true]; exact Or.inr this
  have hvalid := tail_valid p (192 - (K - 1)) (K - 1) (by omega)
  rw [hban, hhead] at hvalid hin
  have := searchFast_sound (193 - K) _ _ hin hs _ hvalid
  rw [tailList_length] at this
  omega

#print axioms peel_sound
#print axioms boundFast_sound
#print axioms searchFast_sound
#print axioms searchFast_of_children
#print axioms no192_from_prefixFast
end Snake9.Dfs
