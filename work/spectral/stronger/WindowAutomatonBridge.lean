/-
Bridge from `Snake9.Snake` to the direction/parity formulation.

* `pathDir p j` is the coordinate flipped by the edge from vertex `j` to `j+1`.
* The XOR of the unit vectors of a block of directions has, in bit `b`, the
  parity of the number of occurrences of `b`; so a block with all even
  multiplicities returns to its start, and one with exactly one odd
  multiplicity ends adjacent to its start.  `distinct` and `induced` then give
  `inducedPattern` for every seven-direction window of a snake.

Core Lean only; imports the standard-library core project.
-/
import PathStructure
import WindowAutomatonSequence

namespace Snake9.WindowAutomaton

/-! ### Directions of path edges -/

/-- The coordinate below `n` in which `u` and `v` differ (0 if none). -/
def dirSearch (u v : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if v = u ^^^ 2 ^ k then k else dirSearch u v k

theorem dirSearch_lt (u v : Nat) : ∀ n, 1 ≤ n → dirSearch u v n < n
  | 0, h => by omega
  | k + 1, _ => by
    unfold dirSearch
    split
    · omega
    · by_cases hk : k = 0
      · subst hk; simp [dirSearch]
      · have := dirSearch_lt u v k (by omega)
        omega

theorem dirSearch_spec (u v : Nat) : ∀ n, (∃ k, k < n ∧ v = u ^^^ 2 ^ k) →
    v = u ^^^ 2 ^ dirSearch u v n
  | 0, ⟨k, hk, _⟩ => by omega
  | n + 1, ⟨k, hk, he⟩ => by
    unfold dirSearch
    split
    · assumption
    · rename_i hne
      have hkn : k < n := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
        · exact h
        · subst h; exact absurd he hne
      exact dirSearch_spec u v n ⟨k, hkn, he⟩

def dirOf (u v : Vertex) : Nat := dirSearch u.val v.val 9

theorem dirOf_lt (u v : Vertex) : dirOf u v < 9 := dirSearch_lt _ _ 9 (by omega)

theorem adj_dirOf (u v : Vertex) (h : Adj u v) : v.val = u.val ^^^ 2 ^ dirOf u v := by
  obtain ⟨k, hk, he⟩ := (adj_iff_coordinate_flip u v).mp h
  exact dirSearch_spec u.val v.val 9 ⟨k, hk, he⟩

/-! ### Path quantities as total functions -/

variable {m : Nat}

def xv (p : Snake m) (j : Nat) : Nat := if h : j < m + 1 then (p.vertex ⟨j, h⟩).val else 0

/-- Direction of the edge from vertex `j` to `j+1` (0 beyond the path). -/
def pathDir (p : Snake m) (j : Nat) : Nat :=
  if h : j + 1 < m + 1 then dirOf (p.vertex ⟨j, by omega⟩) (p.vertex ⟨j + 1, h⟩) else 0

theorem pathDir_lt (p : Snake m) (j : Nat) : pathDir p j < 9 := by
  unfold pathDir
  split
  · exact dirOf_lt _ _
  · omega

theorem xv_succ (p : Snake m) (j : Nat) (hj : j + 1 ≤ m) :
    xv p (j + 1) = xv p j ^^^ 2 ^ pathDir p j := by
  have h1 : j + 1 < m + 1 := by omega
  have h0 : j < m + 1 := by omega
  have hadj : Adj (p.vertex ⟨j, h0⟩) (p.vertex ⟨j + 1, h1⟩) :=
    (path_adj_iff p _ _).mpr (Or.inl rfl)
  unfold xv pathDir
  rw [dif_pos h1, dif_pos h0, dif_pos h1]
  exact adj_dirOf _ _ hadj

theorem xv_ne (p : Snake m) (i j : Nat) (hi : i ≤ m) (hj : j ≤ m) (hne : i ≠ j) :
    xv p i ≠ xv p j := by
  unfold xv
  rw [dif_pos (by omega), dif_pos (by omega)]
  intro h
  have := p.distinct ⟨i, by omega⟩ ⟨j, by omega⟩ (Fin.ext h)
  exact hne (congrArg Fin.val this)

theorem xv_not_adj (p : Snake m) (i j : Nat) (hij : i < j) (hj : j ≤ m) (h2 : i + 2 ≤ j) :
    ¬ ∃ k, k < 9 ∧ xv p j = xv p i ^^^ 2 ^ k := by
  intro ⟨k, hk, he⟩
  unfold xv at he
  rw [dif_pos (by omega), dif_pos (by omega)] at he
  have hadj : Adj (p.vertex ⟨i, by omega⟩) (p.vertex ⟨j, by omega⟩) :=
    (adj_iff_coordinate_flip _ _).mpr ⟨k, hk, he⟩
  have := (p.induced ⟨i, by omega⟩ ⟨j, by omega⟩ hij).mp hadj
  simp at this
  omega

/-! ### Block XOR and parity -/

def vxor (seg : List Nat) : Nat := seg.foldl (fun acc t => acc ^^^ 2 ^ t) 0

theorem parity_succ (c : Nat) : ((c + 1) % 2 == 1) = !(c % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [Nat.add_mod, h]

theorem testBit_foldl (seg : List Nat) : ∀ (acc b : Nat),
    (seg.foldl (fun a t => a ^^^ 2 ^ t) acc).testBit b = (acc.testBit b ^^ (seg.count b % 2 == 1)) := by
  induction seg with
  | nil => intro acc b; simp
  | cons t seg ih =>
    intro acc b
    simp only [List.foldl_cons, List.count_cons]
    rw [ih, Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases h : t = b
    · subst h
      simp only [beq_self_eq_true, if_true, decide_true, Bool.xor_true]
      rw [parity_succ]
      cases acc.testBit t <;> cases (seg.count t % 2 == 1) <;> rfl
    · have h' : (t == b) = false := by simpa using h
      simp [h, h']

theorem testBit_vxor (seg : List Nat) (b : Nat) : (vxor seg).testBit b = (seg.count b % 2 == 1) := by
  unfold vxor
  rw [testBit_foldl]
  simp

theorem vxor_eq_zero (seg : List Nat) (h : ∀ b, seg.count b % 2 = 0) : vxor seg = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_vxor, Nat.zero_testBit, h b]
  rfl

theorem vxor_eq_pow (seg : List Nat) (b : Nat) (hb : seg.count b % 2 = 1)
    (huniq : ∀ c, seg.count c % 2 = 1 → c = b) : vxor seg = 2 ^ b := by
  apply Nat.eq_of_testBit_eq
  intro c
  rw [testBit_vxor, Nat.testBit_two_pow]
  by_cases hc : c = b
  · subst hc; simp [hb]
  · have : seg.count c % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (seg.count c) with h | h
      · exact h
      · exact absurd (huniq c h) hc
    simp [this, Ne.symm hc]

theorem vxor_append (l : List Nat) (x : Nat) : vxor (l ++ [x]) = vxor l ^^^ 2 ^ x := by
  unfold vxor
  rw [List.foldl_append]
  rfl

/-! ### `oddCount` versus parity of counts -/

theorem mem_firsts_of_mem_seen : ∀ (seen l : List Nat) (d : Nat), d ∈ seen → d ∈ firsts seen l
  | seen, [], d, h => by simpa [firsts] using h
  | seen, e :: l, d, h => by
    unfold firsts
    split
    · exact mem_firsts_of_mem_seen seen l d h
    · exact mem_firsts_of_mem_seen _ l d (List.mem_cons_of_mem _ h)

theorem mem_firsts_of_mem : ∀ (seen l : List Nat) (d : Nat), d ∈ l → d ∈ firsts seen l
  | seen, [], d, h => by simp at h
  | seen, e :: l, d, h => by
    rcases List.mem_cons.mp h with rfl | h
    · unfold firsts
      split
      · exact mem_firsts_of_mem_seen seen l d (by assumption)
      · exact mem_firsts_of_mem_seen _ l d List.mem_cons_self
    · unfold firsts
      split <;> exact mem_firsts_of_mem _ l d h

theorem filter_length_one (p : Nat → Bool) : ∀ (l : List Nat), (l.filter p).length = 1 →
    ∃ b ∈ l, p b = true ∧ ∀ c ∈ l, p c = true → c = b
  | [], h => by simp at h
  | a :: l, h => by
    rw [List.filter_cons] at h
    split at h
    · rename_i hpa
      simp only [List.length_cons, Nat.add_left_eq_self, List.length_eq_zero,
        List.filter_eq_nil_iff] at h
      refine ⟨a, List.mem_cons_self, hpa, ?_⟩
      intro c hc hpc
      rcases List.mem_cons.mp hc with rfl | hc
      · rfl
      · exact absurd hpc (by simpa using h c hc)
    · rename_i hpa
      obtain ⟨b, hb, hpb, huniq⟩ := filter_length_one p l h
      refine ⟨b, List.mem_cons_of_mem _ hb, hpb, ?_⟩
      intro c hc hpc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact absurd hpc (by simpa using hpa)
      · exact huniq c hc hpc

theorem oddCount_zero (seg : List Nat) (h : oddCount seg = 0) : ∀ b, seg.count b % 2 = 0 := by
  intro b
  unfold oddCount at h
  rw [List.length_eq_zero, List.filter_eq_nil_iff] at h
  by_cases hb : b ∈ seg
  · have := h b (mem_firsts_of_mem [] seg b hb)
    rcases Nat.mod_two_eq_zero_or_one (seg.count b) with h0 | h1
    · exact h0
    · exact absurd (by simpa using h1) this
  · rw [List.count_eq_zero_of_not_mem hb]

theorem oddCount_one (seg : List Nat) (h : oddCount seg = 1) :
    ∃ b, seg.count b % 2 = 1 ∧ ∀ c, seg.count c % 2 = 1 → c = b := by
  unfold oddCount at h
  obtain ⟨b, _, hpb, huniq⟩ := filter_length_one _ _ h
  refine ⟨b, by simpa using hpb, ?_⟩
  intro c hc
  have hcm : c ∈ seg := List.count_pos_iff.mp (by omega)
  exact huniq c (mem_firsts_of_mem [] seg c hcm) (by simpa using hc)

/-- A block whose endpoints are distinct and (for length at least two)
non-adjacent is admissible. -/
theorem blockOK_of_path (seg : List Nat) (u w : Nat) (hw : w = u ^^^ vxor seg) (hne : u ≠ w)
    (hadj : 2 ≤ seg.length → ¬ ∃ k, k < 9 ∧ w = u ^^^ 2 ^ k) (h9 : ∀ t ∈ seg, t < 9) :
    blockOK seg = true := by
  unfold blockOK
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h0
    apply hne
    rw [hw, vxor_eq_zero seg (oddCount_zero seg h0), Nat.xor_zero]
  · by_cases hl : seg.length < 2
    · exact Or.inl hl
    · right
      intro h1
      obtain ⟨b, hb, huniq⟩ := oddCount_one seg h1
      have hb9 : b < 9 := h9 b (List.count_pos_iff.mp (by omega))
      exact hadj (by omega) ⟨b, hb9, by rw [hw, vxor_eq_pow seg b hb huniq]⟩

/-! ### Blocks of a window are path blocks -/

def blockList (p : Snake m) (s len : Nat) : List Nat := (List.range' s len).map (pathDir p)

theorem blockList_succ (p : Snake m) (s len : Nat) :
    blockList p s (len + 1) = blockList p s len ++ [pathDir p (s + len)] := by
  unfold blockList
  rw [List.range'_concat, List.map_append]
  simp

theorem chain (p : Snake m) (s : Nat) : ∀ len, s + len ≤ m →
    xv p (s + len) = xv p s ^^^ vxor (blockList p s len)
  | 0, _ => by simp [blockList, vxor]
  | len + 1, h => by
    show xv p (s + len + 1) = _
    rw [blockList_succ, vxor_append, ← Nat.xor_assoc, ← chain p s len (by omega)]
    exact xv_succ p (s + len) (by omega)

theorem drop_range' : ∀ (s n i : Nat), (List.range' s n).drop i = List.range' (s + i) (n - i)
  | s, 0, i => by simp
  | s, n + 1, 0 => by simp
  | s, n + 1, i + 1 => by
    rw [List.range'_succ, List.drop_succ_cons, drop_range' (s + 1) n i]
    simp only [Nat.add_sub_add_right]
    congr 1
    omega

theorem take_range' : ∀ (s n i : Nat), i ≤ n → (List.range' s n).take i = List.range' s i
  | s, n, 0, _ => by simp
  | s, 0, i + 1, h => by omega
  | s, n + 1, i + 1, h => by
    rw [List.range'_succ, List.take_succ_cons, take_range' (s + 1) n i (by omega)]
    rfl

theorem drop_take_blockList (p : Snake m) (i s len n : Nat) (h : s + len ≤ n) :
    ((blockList p i n).drop s).take len = blockList p (i + s) len := by
  unfold blockList
  rw [← List.map_drop, ← List.map_take, drop_range', take_range' _ _ _ (by omega)]

theorem win7_eq (p : Snake m) (i : Nat) : win7 (pathDir p) i = blockList p i 7 := rfl

theorem mem_prefixes_eq : ∀ (l seg : List Nat), seg ∈ prefixes l →
    ∃ len, 1 ≤ len ∧ len ≤ l.length ∧ seg = l.take len
  | [], seg, h => by simp [prefixes] at h
  | a :: l, seg, h => by
    simp only [prefixes, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · exact ⟨1, Nat.le_refl _, by simp, rfl⟩
    · obtain ⟨len, h1, h2, rfl⟩ := mem_prefixes_eq l q hq
      exact ⟨len + 1, by omega, by simp; omega, by simp [List.take_succ_cons]⟩

theorem mem_blocks_eq : ∀ (l seg : List Nat), seg ∈ blocks l →
    ∃ s len, 1 ≤ len ∧ s + len ≤ l.length ∧ seg = (l.drop s).take len
  | [], seg, h => by simp [blocks] at h
  | a :: l, seg, h => by
    simp only [blocks, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨len, h1, h2, rfl⟩ := mem_prefixes_eq _ seg h
      exact ⟨0, len, h1, by simpa using h2, rfl⟩
    · obtain ⟨s, len, h1, h2, rfl⟩ := mem_blocks_eq l seg h
      exact ⟨s + 1, len, h1, by simp; omega, by simp [List.drop_succ_cons]⟩

/-- Every seven-direction window of a snake has the induced parity pattern. -/
theorem snake_inducedPattern (p : Snake m) (i : Nat) (hi : i + 7 ≤ m) :
    inducedPattern (win7 (pathDir p) i) = true := by
  unfold inducedPattern
  rw [List.all_eq_true, win7_eq]
  intro seg hseg
  obtain ⟨s, len, h1, h2, rfl⟩ := mem_blocks_eq _ seg hseg
  have hlen : (blockList p i 7).length = 7 := by simp [blockList, List.length_range']
  rw [hlen] at h2
  rw [drop_take_blockList p i s len 7 h2]
  apply blockOK_of_path _ (xv p (i + s)) (xv p (i + s + len))
  · exact chain p (i + s) len (by omega)
  · exact xv_ne p _ _ (by omega) (by omega) (by omega)
  · intro h2len
    simp only [blockList, List.length_map, List.length_range'] at h2len
    exact xv_not_adj p (i + s) (i + s + len) (by omega) (by omega) (by omega)
  · intro t ht
    simp only [blockList, List.mem_map] at ht
    obtain ⟨_, _, rfl⟩ := ht
    exact pathDir_lt p _

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.snake_inducedPattern
