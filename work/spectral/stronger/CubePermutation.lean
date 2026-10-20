/-
Coordinate permutations of the 9-cube and their action on snakes.

For a permutation `σ` of the coordinates `Coord = Fin 9`, `permV σ` sends a vertex
`v : Vertex = Fin 512` to the vertex whose bit `σ a` is bit `a` of `v`.  Together with
the existing translation `translate p x` (vertex `i` ↦ `vxor x (p.vertex i)`), the
cube automorphism `φ(v) = σ(v xor x)` acts on snakes by `cubeMap σ x`.

Proved here:
1. `permV σ` is a bijection (`permVEquiv`), commutes with `vxor`, sends `unit a` to
   `unit (σ a)`, preserves adjacency (`adj_permV`) and Hamming weight/distance.
2. `permSnake σ p` / `cubeMap σ x p` are snakes of the same length `m` (by construction
   of the type `Snake m`), with vertices `permV σ (vxor x (p.vertex i))`.
3. `pathDir` of the image is `σ` applied to `pathDir` of the original.
4. `localAlpha`, `countSeq` and `totalSingleton` are invariant.

Mathlib + core project; compiled against the strengthened-k6-resume build directory.
-/
import SingletonAlphaBridge
import WindowAutomatonBridge
import AggregateWindowConditional

namespace Snake9.CubePerm
open SquareIncidence Finset

/-! ### Building a number from its bits -/

/-- `ofBits f n` has bit `j` equal to `f j` for `j < n` and no other bits. -/
def ofBits (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => ofBits f n ||| (if f n then 2 ^ n else 0)

theorem ofBits_lt (f : Nat → Bool) : ∀ n, ofBits f n < 2 ^ n
  | 0 => by simp [ofBits]
  | n + 1 => by
    unfold ofBits
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le (ofBits_lt f n) (Nat.pow_le_pow_right (by norm_num) (by omega))
    · split
      · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      · exact Nat.two_pow_pos _

theorem testBit_ofBits (f : Nat → Bool) : ∀ n j, (ofBits f n).testBit j = (decide (j < n) && f j)
  | 0, j => by simp [ofBits]
  | n + 1, j => by
    unfold ofBits
    rw [Nat.testBit_or, testBit_ofBits f n j]
    by_cases hjn : j = n
    · subst hjn
      split <;> simp_all [Nat.testBit_two_pow]
    · have h1 : decide (j < n + 1) = decide (j < n) := by
        by_cases hj : j < n
        · simp [hj, show j < n + 1 by omega]
        · simp [hj, show ¬ j < n + 1 by omega]
      rw [h1]
      split
      · rw [Nat.testBit_two_pow]
        simp [Ne.symm hjn]
      · simp

/-! ### Vertices as bit vectors -/

theorem vertex_testBit_high (v : Vertex) (j : Nat) (hj : 9 ≤ j) : v.val.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le v.isLt
    (by simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj))

theorem vertex_ext (u v : Vertex) (h : ∀ a : Coord, u.val.testBit a.val = v.val.testBit a.val) :
    u = v := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 9
  · exact h ⟨j, hj⟩
  · rw [vertex_testBit_high u j (by omega), vertex_testBit_high v j (by omega)]

theorem testBit_vxor (u v : Vertex) (j : Nat) :
    (vxor u v).val.testBit j = (u.val.testBit j ^^ v.val.testBit j) :=
  Nat.testBit_xor u.val v.val j

theorem testBit_unit (a : Coord) (j : Nat) : (unit a).val.testBit j = decide (a.val = j) :=
  Nat.testBit_two_pow

/-! ### The coordinate permutation on vertices -/

/-- `permV σ v` has bit `σ a` equal to bit `a` of `v`. -/
def permV (σ : Equiv.Perm Coord) (v : Vertex) : Vertex :=
  ⟨ofBits (fun j => if h : j < 9 then v.val.testBit (σ.symm ⟨j, h⟩).val else false) 9,
    ofBits_lt _ 9⟩

theorem testBit_permV (σ : Equiv.Perm Coord) (v : Vertex) (b : Coord) :
    (permV σ v).val.testBit b.val = v.val.testBit (σ.symm b).val := by
  unfold permV
  rw [testBit_ofBits]
  simp [b.isLt]

theorem testBit_permV_apply (σ : Equiv.Perm Coord) (v : Vertex) (a : Coord) :
    (permV σ v).val.testBit (σ a).val = v.val.testBit a.val := by
  rw [testBit_permV, Equiv.symm_apply_apply]

theorem permV_symm_permV (σ : Equiv.Perm Coord) (v : Vertex) : permV σ.symm (permV σ v) = v := by
  apply vertex_ext
  intro a
  rw [testBit_permV, Equiv.symm_symm, testBit_permV_apply]

theorem permV_permV_symm (σ : Equiv.Perm Coord) (v : Vertex) : permV σ (permV σ.symm v) = v := by
  simpa using permV_symm_permV σ.symm v

/-- The vertex map of a coordinate permutation, as a bijection of the cube. -/
def permVEquiv (σ : Equiv.Perm Coord) : Vertex ≃ Vertex where
  toFun := permV σ
  invFun := permV σ.symm
  left_inv := permV_symm_permV σ
  right_inv := permV_permV_symm σ

theorem permV_bijective (σ : Equiv.Perm Coord) : Function.Bijective (permV σ) :=
  (permVEquiv σ).bijective

theorem permV_injective (σ : Equiv.Perm Coord) {u v : Vertex} (h : permV σ u = permV σ v) :
    u = v := (permV_bijective σ).1 h

theorem permV_vxor (σ : Equiv.Perm Coord) (u v : Vertex) :
    permV σ (vxor u v) = vxor (permV σ u) (permV σ v) := by
  apply vertex_ext
  intro b
  rw [testBit_permV, testBit_vxor, testBit_vxor, testBit_permV, testBit_permV]

theorem permV_unit (σ : Equiv.Perm Coord) (a : Coord) : permV σ (unit a) = unit (σ a) := by
  apply vertex_ext
  intro b
  rw [testBit_permV, testBit_unit, testBit_unit]
  apply decide_eq_decide.mpr
  rw [Fin.val_inj, Fin.val_inj]
  constructor
  · intro h; rw [h, Equiv.apply_symm_apply]
  · intro h; rw [← h, Equiv.symm_apply_apply]

theorem permV_zero (σ : Equiv.Perm Coord) : permV σ 0 = 0 := by
  apply vertex_ext
  intro b
  rw [testBit_permV]
  simp

theorem permV_flip (σ : Equiv.Perm Coord) (a : Coord) (v : Vertex) :
    permV σ (SquareIncidence.flip a v) = SquareIncidence.flip (σ a) (permV σ v) := by
  unfold SquareIncidence.flip
  rw [permV_vxor, permV_unit]

/-! ### Adjacency, weight and distance -/

theorem adj_iff_vxor_unit (u v : Vertex) : Adj u v ↔ ∃ a : Coord, v = vxor u (unit a) := by
  rw [adj_iff_coordinate_flip]
  constructor
  · rintro ⟨k, hk, he⟩
    exact ⟨⟨k, hk⟩, Fin.ext he⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, a.isLt, rfl⟩

theorem adj_permV (σ : Equiv.Perm Coord) (u v : Vertex) :
    Adj (permV σ u) (permV σ v) ↔ Adj u v := by
  rw [adj_iff_vxor_unit, adj_iff_vxor_unit]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨σ.symm b, ?_⟩
    have h := congrArg (permV σ.symm) hb
    rwa [permV_symm_permV, permV_vxor, permV_symm_permV, permV_unit] at h
  · rintro ⟨a, rfl⟩
    exact ⟨σ a, by rw [permV_vxor, permV_unit]⟩

/-- Hamming weight (same formula as `RadiusThreeForest.weight` in the core project). -/
def weight (v : Vertex) : Nat := ((List.range 9).filter (fun k => v.val.testBit k)).length

/-- Hamming distance. -/
def dist (u v : Vertex) : Nat := weight (vxor u v)

theorem length_filter_range (p : Nat → Bool) : ∀ n,
    ((List.range n).filter p).length = ∑ i ∈ Finset.range n, if p i then 1 else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range p n,
      Finset.sum_range_succ]
    cases h : p n <;> simp [h]

theorem weight_eq_sum (v : Vertex) :
    weight v = ∑ a : Coord, if v.val.testBit a.val then 1 else 0 := by
  unfold weight
  rw [length_filter_range]
  exact (Fin.sum_univ_eq_sum_range (fun i => if v.val.testBit i then 1 else 0) 9).symm

theorem weight_permV (σ : Equiv.Perm Coord) (v : Vertex) : weight (permV σ v) = weight v := by
  rw [weight_eq_sum, weight_eq_sum]
  rw [← Equiv.sum_comp σ (fun b => if (permV σ v).val.testBit b.val then 1 else 0)]
  simp only [testBit_permV_apply]

theorem dist_permV (σ : Equiv.Perm Coord) (u v : Vertex) :
    dist (permV σ u) (permV σ v) = dist u v := by
  unfold dist
  rw [← permV_vxor, weight_permV]

theorem weight_vxor_self (t v : Vertex) : weight (vxor t v) = dist t v := rfl

theorem dist_vxor (t u v : Vertex) : dist (vxor t u) (vxor t v) = dist u v := by
  unfold dist
  congr 1
  apply Fin.ext
  change (t.val ^^^ u.val) ^^^ (t.val ^^^ v.val) = u.val ^^^ v.val
  rw [Nat.xor_assoc, ← Nat.xor_assoc u.val, Nat.xor_comm u.val t.val, Nat.xor_assoc t.val,
    ← Nat.xor_assoc t.val t.val, Nat.xor_self, Nat.zero_xor]

/-- The full cube automorphism `φ(v) = σ(v xor x)`. -/
def cubeAut (σ : Equiv.Perm Coord) (x v : Vertex) : Vertex := permV σ (vxor x v)

theorem cubeAut_bijective (σ : Equiv.Perm Coord) (x : Vertex) :
    Function.Bijective (cubeAut σ x) := by
  constructor
  · intro u v h
    exact vxor_injective x (permV_injective σ h)
  · intro w
    refine ⟨vxor x (permV σ.symm w), ?_⟩
    unfold cubeAut
    rw [vxor_cancel, permV_permV_symm]

theorem adj_cubeAut (σ : Equiv.Perm Coord) (x u v : Vertex) :
    Adj (cubeAut σ x u) (cubeAut σ x v) ↔ Adj u v := by
  unfold cubeAut
  rw [adj_permV, adj_vxor]

theorem dist_cubeAut (σ : Equiv.Perm Coord) (x u v : Vertex) :
    dist (cubeAut σ x u) (cubeAut σ x v) = dist u v := by
  unfold cubeAut
  rw [dist_permV, dist_vxor]

/-! ### Snakes -/

/-- The image of a snake under a coordinate permutation: a snake of the same length. -/
def permSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) : Snake m where
  vertex i := permV σ (p.vertex i)
  distinct i j h := p.distinct i j (permV_injective σ h)
  induced i j hij := by rw [adj_permV]; exact p.induced i j hij

/-- The image of a snake under the cube automorphism `v ↦ σ(v xor x)`. -/
def cubeMap {m : Nat} (σ : Equiv.Perm Coord) (x : Vertex) (p : Snake m) : Snake m :=
  permSnake σ (translate p x)

theorem permSnake_vertex {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (i : Fin (m+1)) :
    (permSnake σ p).vertex i = permV σ (p.vertex i) := rfl

theorem cubeMap_vertex {m : Nat} (σ : Equiv.Perm Coord) (x : Vertex) (p : Snake m)
    (i : Fin (m+1)) : (cubeMap σ x p).vertex i = cubeAut σ x (p.vertex i) := rfl

theorem permSnake_symm {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) :
    (permSnake σ.symm (permSnake σ p)).vertex = p.vertex := by
  funext i
  exact permV_symm_permV σ (p.vertex i)

theorem inPath_permV_iff {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (v : Vertex) :
    InPath (permSnake σ p) (permV σ v) ↔ InPath p v := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, permV_injective σ hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-! ### Directions -/

theorem dirOf_vxor_unit (u : Vertex) (a : Coord) :
    WindowAutomaton.dirOf u (vxor u (unit a)) = a.val := by
  have hadj : Adj u (vxor u (unit a)) := flip_adj a u
  have h := WindowAutomaton.adj_dirOf u _ hadj
  change u.val ^^^ 2 ^ a.val = u.val ^^^ 2 ^ WindowAutomaton.dirOf u (vxor u (unit a)) at h
  have h2 : 2 ^ a.val = 2 ^ WindowAutomaton.dirOf u (vxor u (unit a)) := by
    have := congrArg (fun z => u.val ^^^ z) h
    simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using this
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

/-- Consecutive snake vertices differ in the coordinate `pathDir p j`. -/
theorem vertex_succ_eq {m : Nat} (p : Snake m) (j : Nat) (hj : j < m) :
    p.vertex ⟨j+1, by omega⟩ =
      vxor (p.vertex ⟨j, by omega⟩) (unit ⟨WindowAutomaton.pathDir p j,
        WindowAutomaton.pathDir_lt p j⟩) := by
  apply Fin.ext
  have h := WindowAutomaton.xv_succ p j (by omega)
  unfold WindowAutomaton.xv at h
  rw [dif_pos (by omega), dif_pos (by omega)] at h
  exact h

theorem pathDir_permSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (j : Nat)
    (hj : j < m) :
    WindowAutomaton.pathDir (permSnake σ p) j =
      (σ ⟨WindowAutomaton.pathDir p j, WindowAutomaton.pathDir_lt p j⟩).val := by
  have hs := vertex_succ_eq p j hj
  unfold WindowAutomaton.pathDir
  rw [dif_pos (by omega), permSnake_vertex, permSnake_vertex, hs, permV_vxor, permV_unit,
    dirOf_vxor_unit]
  rfl

theorem pathDir_eq {m : Nat} (q : Snake m) (j : Nat) (hj : j < m) :
    WindowAutomaton.pathDir q j =
      WindowAutomaton.dirOf (q.vertex ⟨j, by omega⟩) (q.vertex ⟨j+1, by omega⟩) := by
  unfold WindowAutomaton.pathDir
  rw [dif_pos (by omega)]

theorem pathDir_translate {m : Nat} (x : Vertex) (p : Snake m) (j : Nat) :
    WindowAutomaton.pathDir (translate p x) j = WindowAutomaton.pathDir p j := by
  by_cases hj : j < m
  · rw [pathDir_eq _ j hj]
    change WindowAutomaton.dirOf (vxor x (p.vertex _)) (vxor x (p.vertex _)) = _
    rw [vertex_succ_eq p j hj, vxor_assoc', dirOf_vxor_unit]
  · unfold WindowAutomaton.pathDir
    rw [dif_neg (by omega), dif_neg (by omega)]

theorem pathDir_cubeMap {m : Nat} (σ : Equiv.Perm Coord) (x : Vertex) (p : Snake m) (j : Nat)
    (hj : j < m) :
    WindowAutomaton.pathDir (cubeMap σ x p) j =
      (σ ⟨WindowAutomaton.pathDir p j, WindowAutomaton.pathDir_lt p j⟩).val := by
  unfold cubeMap
  rw [pathDir_permSnake σ _ j hj]
  congr 3
  exact pathDir_translate x p j

/-! ### Square counts -/

/-- The axis pair `{σ a, σ b}`, sorted. -/
def permPair (σ : Equiv.Perm Coord) (ab : AxisPair) : AxisPair :=
  if h : (σ ab.val.1).val < (σ ab.val.2).val then ⟨(σ ab.val.1, σ ab.val.2), h⟩
  else ⟨(σ ab.val.2, σ ab.val.1), by
    have hne : σ ab.val.1 ≠ σ ab.val.2 := fun he =>
      (ne_of_lt ab.property) (congrArg Fin.val (σ.injective he))
    have hne' : (σ ab.val.1).val ≠ (σ ab.val.2).val := fun he => hne (Fin.ext he)
    show (σ ab.val.2).val < (σ ab.val.1).val
    omega⟩

theorem permPair_symm (σ : Equiv.Perm Coord) (ab : AxisPair) :
    permPair σ.symm (permPair σ ab) = ab := by
  rcases ab with ⟨⟨a, b⟩, hab⟩
  have hab' : a.val < b.val := hab
  unfold permPair
  dsimp only
  split
  · rw [dif_pos (by simpa using hab')]
    simp
  · rw [dif_neg (by simp only [Equiv.symm_apply_apply]; omega)]
    simp

def permPairEquiv (σ : Equiv.Perm Coord) : AxisPair ≃ AxisPair where
  toFun := permPair σ
  invFun := permPair σ.symm
  left_inv := permPair_symm σ
  right_inv ab := by simpa using permPair_symm σ.symm ab

theorem singleton_swap {m : Nat} (p : Snake m) (a b : Coord) (v : Vertex) :
    (InPath p v ∧ ¬ InPath p (SquareIncidence.flip a v) ∧ ¬ InPath p (SquareIncidence.flip b v) ∧
      ¬ InPath p (SquareIncidence.flip b (SquareIncidence.flip a v))) ↔
    (InPath p v ∧ ¬ InPath p (SquareIncidence.flip b v) ∧ ¬ InPath p (SquareIncidence.flip a v) ∧
      ¬ InPath p (SquareIncidence.flip a (SquareIncidence.flip b v))) := by
  rw [flip_commute a b v]
  tauto

open Classical in
theorem singleton_permSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (ab : AxisPair)
    (v : Vertex) :
    SquareIncidence.singleton (permSnake σ p) (permPair σ ab) (permV σ v) =
      SquareIncidence.singleton p ab v := by
  unfold permPair
  split
  · unfold SquareIncidence.singleton
    dsimp only
    repeat rw [← permV_flip]
    repeat rw [inPath_permV_iff]
  · unfold SquareIncidence.singleton
    dsimp only
    repeat rw [← permV_flip]
    repeat rw [inPath_permV_iff]
    exact if_congr (singleton_swap p _ _ v).symm rfl rfl

/-- Local singleton counts are invariant under coordinate permutations. -/
theorem localAlpha_permSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (i : Fin (m+1)) :
    localAlpha (permSnake σ p) i = localAlpha p i := by
  unfold localAlpha
  rw [← Equiv.sum_comp (permPairEquiv σ)]
  apply Finset.sum_congr rfl
  intro ab _
  exact singleton_permSnake σ p ab (p.vertex i)

theorem localAlpha_cubeMap {m : Nat} (σ : Equiv.Perm Coord) (x : Vertex) (p : Snake m)
    (i : Fin (m+1)) : localAlpha (cubeMap σ x p) i = localAlpha p i := by
  unfold cubeMap
  rw [localAlpha_permSnake, localAlpha_translate]

theorem countSeq_cubeMap {m : Nat} (σ : Equiv.Perm Coord) (x : Vertex) (p : Snake m) (k : Nat) :
    countSeq (cubeMap σ x p) k = countSeq p k := by
  unfold countSeq
  split
  · exact localAlpha_cubeMap σ x p _
  · rfl

theorem countSeq_permSnake {m : Nat} (σ : Equiv.Perm Coord) (p : Snake m) (k : Nat) :
    countSeq (permSnake σ p) k = countSeq p k := by
  unfold countSeq
  split
  · exact localAlpha_permSnake σ p _
  · rfl

theorem totalSingleton_cubeMap {m : Nat} (σ : Equiv.Perm Coord) (x : Vertex) (p : Snake m) :
    totalSingleton (cubeMap σ x p) = totalSingleton p := by
  rw [totalSingleton_eq_path_sum, totalSingleton_eq_path_sum]
  exact Finset.sum_congr rfl (fun i _ => localAlpha_cubeMap σ x p i)

/-- The no-`2,2,3` window premise of `upper_244_of_no_two_two_three` transfers along any
cube automorphism: it suffices to exclude the pattern for the normalised snake. -/
theorem no223_window_cubeMap {m : Nat} (σ : Equiv.Perm Coord) (x : Vertex) (p : Snake m)
    (r : Nat) (hr : r + 4 ≤ m) :
    (localAlpha (cubeMap σ x p) ⟨r+1, by omega⟩ = 2 ∧
      localAlpha (cubeMap σ x p) ⟨r+2, by omega⟩ = 2 ∧
      localAlpha (cubeMap σ x p) ⟨r+3, by omega⟩ = 3) ↔
    (localAlpha p ⟨r+1, by omega⟩ = 2 ∧ localAlpha p ⟨r+2, by omega⟩ = 2 ∧
      localAlpha p ⟨r+3, by omega⟩ = 3) := by
  simp only [localAlpha_cubeMap]

/-! ### Normalisation: choosing the automorphism -/

/-- Any duplicate-free list of coordinates can be relabelled to `0,1,2,…` by a permutation. -/
theorem exists_perm_relabel (l : List Coord) (hl : l.Nodup) :
    ∃ σ : Equiv.Perm Coord, ∀ i (h : i < l.length), (σ l[i]).val = i := by
  have hlen : l.length ≤ 9 := by
    simpa using hl.length_le_card
  have key : ∀ n (hn : n ≤ l.length), ∃ σ : Equiv.Perm Coord, ∀ i (h : i < n),
      (σ (l[i]'(by omega))).val = i := by
    intro n
    induction n with
    | zero => intro _; exact ⟨1, fun i h => absurd h (Nat.not_lt_zero i)⟩
    | succ n ih =>
      intro hn
      obtain ⟨σ, hσ⟩ := ih (by omega)
      let c : Coord := ⟨n, by omega⟩
      refine ⟨σ.trans (Equiv.swap (σ (l[n]'(by omega))) c), ?_⟩
      intro i hi
      rw [Equiv.trans_apply]
      by_cases hin : i = n
      · subst hin
        rw [Equiv.swap_apply_left]
      · have hi' : i < n := by omega
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact hσ i hi'
        · intro he
          have he2 := σ.injective he
          have := (List.Nodup.getElem_inj_iff hl).mp he2
          omega
        · intro he
          have := congrArg Fin.val he
          rw [hσ i hi'] at this
          exact hin this
  obtain ⟨σ, hσ⟩ := key l.length (le_refl _)
  exact ⟨σ, fun i h => hσ i h⟩

/-- Normalisation of a window: for a vertex index `r` and a list of edge positions whose
directions are pairwise distinct, some cube automorphism sends vertex `r` to `0` and the
listed directions to `0,1,2,…` in order, keeping all local singleton counts. -/
theorem exists_normalizing_cubeMap {m : Nat} (p : Snake m) (r : Fin (m+1)) (l : List Nat)
    (hnd : (l.map (fun j => (⟨WindowAutomaton.pathDir p j, WindowAutomaton.pathDir_lt p j⟩ :
      Coord))).Nodup)
    (hl : ∀ j ∈ l, j < m) :
    ∃ (σ : Equiv.Perm Coord) (x : Vertex), (cubeMap σ x p).vertex r = 0 ∧
      (∀ i (h : i < l.length), WindowAutomaton.pathDir (cubeMap σ x p) l[i] = i) ∧
      (∀ k : Fin (m+1), localAlpha (cubeMap σ x p) k = localAlpha p k) := by
  obtain ⟨σ, hσ⟩ := exists_perm_relabel _ hnd
  refine ⟨σ, p.vertex r, ?_, ?_, fun k => localAlpha_cubeMap σ _ p k⟩
  · rw [cubeMap_vertex]
    unfold cubeAut
    rw [vxor_self, permV_zero]
  · intro i h
    rw [pathDir_cubeMap σ _ p _ (hl _ (List.getElem_mem h))]
    have := hσ i (by simpa using h)
    simpa using this

end Snake9.CubePerm

#print axioms Snake9.CubePerm.permV_bijective
#print axioms Snake9.CubePerm.permV_vxor
#print axioms Snake9.CubePerm.permV_unit
#print axioms Snake9.CubePerm.adj_permV
#print axioms Snake9.CubePerm.weight_permV
#print axioms Snake9.CubePerm.dist_permV
#print axioms Snake9.CubePerm.cubeAut_bijective
#print axioms Snake9.CubePerm.adj_cubeAut
#print axioms Snake9.CubePerm.dist_cubeAut
#print axioms Snake9.CubePerm.permSnake
#print axioms Snake9.CubePerm.cubeMap
#print axioms Snake9.CubePerm.pathDir_permSnake
#print axioms Snake9.CubePerm.pathDir_translate
#print axioms Snake9.CubePerm.pathDir_cubeMap
#print axioms Snake9.CubePerm.localAlpha_permSnake
#print axioms Snake9.CubePerm.localAlpha_cubeMap
#print axioms Snake9.CubePerm.countSeq_cubeMap
#print axioms Snake9.CubePerm.totalSingleton_cubeMap
#print axioms Snake9.CubePerm.no223_window_cubeMap
#print axioms Snake9.CubePerm.exists_perm_relabel
#print axioms Snake9.CubePerm.exists_normalizing_cubeMap
