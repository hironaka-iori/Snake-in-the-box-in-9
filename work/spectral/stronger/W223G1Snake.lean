import W223G1Sound
import AggregateSingletonBound
/-!
# G1: the vertex set of a snake satisfies the generic clause facts

For a snake `q`, `sel q n` says that vertex number `n` lies on `q`.  Proved here:
* `sel_bad`: a vertex set flagged by `badSet` (a vertex with three neighbours in the set, or a
  nonempty set where every vertex has two neighbours) is never contained in the snake;
* `sel_deg`: every snake vertex has a neighbour on the snake (if `m ≥ 1`);
* `endSem_sel`: a snake vertex with at most one snake neighbour is an endpoint of the path;
* counter-block counts for ball and endpoint literals (`cnt_negBall_eq`, ...);
* `localAlpha_eq_corners`: at an internal vertex, `localAlpha` is the number of the 21
  "free" corners (`v xor e_a xor e_b`, `a, b` not path directions at `v`) off the snake.
-/
namespace W223G1
open Snake9 Snake9.SquareIncidence WinCNF
open Classical

noncomputable section

variable {m : Nat} (q : Snake m)

/-- Vertex number `n` lies on the snake. -/
def sel (n : Nat) : Bool := decide (∃ i, (q.vertex i).val = n)

theorem sel_iff {n : Nat} : sel q n = true ↔ ∃ i, (q.vertex i).val = n := by
  unfold sel; exact decide_eq_true_iff

theorem sel_vertex (i : Fin (m+1)) : sel q (q.vertex i).val = true := (sel_iff q).mpr ⟨i, rfl⟩

theorem inPath_iff_sel (v : Vertex) : InPath q v ↔ sel q v.val = true := by
  rw [sel_iff]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, hi⟩; exact ⟨i, Fin.ext hi⟩

theorem adjN_of_adj {u v : Vertex} (h : Adj u v) : adjN u.val v.val = true := h

theorem mem_nbrs_of_adj {u v : Vertex} (h : Adj u v) : v.val ∈ nbrs u.val :=
  (mem_nbrs_iff _ _).mpr h

/-! ### Small list facts -/

theorem exists_three {l : List Nat} (hnd : l.Nodup) (h : 3 ≤ l.length) :
    ∃ a b c, a ∈ l ∧ b ∈ l ∧ c ∈ l ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  match l, hnd, h with
  | a :: b :: c :: _, hnd, _ =>
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    exact ⟨a, b, c, by simp, by simp, by simp, hnd.1.1, hnd.1.2.1, hnd.2.1.1⟩

theorem exists_two {l : List Nat} (hnd : l.Nodup) (h : 2 ≤ l.length) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ a ≠ b := by
  match l, hnd, h with
  | a :: b :: _, hnd, _ =>
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    exact ⟨a, b, by simp, by simp, hnd.1.1⟩

theorem length_le_two {l : List Nat} (hnd : l.Nodup) {a b : Nat}
    (h : ∀ x ∈ l, x = a ∨ x = b) : l.length ≤ 2 := by
  match l, hnd, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | [_, _], _, _ => simp
  | x :: y :: z :: _, hnd, h =>
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    have hx := h x (by simp)
    have hy := h y (by simp)
    have hz := h z (by simp)
    exfalso
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      simp_all

/-! ### Snake facts -/

theorem sel_bad (X : List Nat) (hnd : X.Nodup) (hb : badSet X = true)
    (hX : ∀ x ∈ X, sel q x = true) : False := by
  have hidx : ∀ x ∈ X, ∃ i : Fin (m+1), (q.vertex i).val = x :=
    fun x hx => (sel_iff q).mp (hX x hx)
  unfold badSet at hb
  simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    List.all_eq_true, Bool.not_eq_true'] at hb
  rcases hb with ⟨v, hv, h3⟩ | ⟨hne, h2⟩
  · unfold nbrCnt at h3
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := exists_three (hnd.filter _) h3
    rw [List.mem_filter] at ha hb hc
    obtain ⟨iv, rfl⟩ := hidx v hv
    obtain ⟨ia, rfl⟩ := hidx _ ha.1
    obtain ⟨ib, rfl⟩ := hidx _ hb.1
    obtain ⟨ic, rfl⟩ := hidx _ hc.1
    rcases three_neighbors_repeat q iv ia ib ic ha.2 hb.2 hc.2 with h | h | h
    · exact hab (by rw [h])
    · exact hac (by rw [h])
    · exact hbc (by rw [h])
  · obtain ⟨x0, hx0⟩ : ∃ x, x ∈ X := by
      cases X with
      | nil => simp at hne
      | cons x _ => exact ⟨x, by simp⟩
    have hP : ∃ k, ∃ i : Fin (m+1), i.val = k ∧ (q.vertex i).val ∈ X := by
      obtain ⟨i, hi⟩ := hidx x0 hx0
      exact ⟨i.val, i, rfl, hi ▸ hx0⟩
    obtain ⟨i0, hi0, hmem⟩ := Nat.find_spec hP
    have hmin : ∀ j : Fin (m+1), (q.vertex j).val ∈ X → Nat.find hP ≤ j.val :=
      fun j hj => Nat.find_min' hP ⟨j, rfl, hj⟩
    have h2' := h2 _ hmem
    unfold nbrCnt at h2'
    obtain ⟨a, b, ha, hb, hab⟩ := exists_two (hnd.filter _) h2'
    rw [List.mem_filter] at ha hb
    obtain ⟨ia, rfl⟩ := hidx _ ha.1
    obtain ⟨ib, rfl⟩ := hidx _ hb.1
    have hia := (path_adj_iff q i0 ia).mp ha.2
    have hib := (path_adj_iff q i0 ib).mp hb.2
    have h1 := hmin ia ha.1
    have h2'' := hmin ib hb.1
    have hiab : ia = ib := Fin.ext (by omega)
    exact hab (by rw [hiab])

theorem sel_deg (hm : 1 ≤ m) (w : Nat) (hw : sel q w = true) :
    ∃ n ∈ nbrs w, sel q n = true := by
  obtain ⟨i, rfl⟩ := (sel_iff q).mp hw
  by_cases hi : i.val < m
  · exact ⟨(q.vertex ⟨i.val+1, by omega⟩).val,
      mem_nbrs_of_adj ((path_adj_iff q _ _).mpr (Or.inl rfl)), sel_vertex q _⟩
  · exact ⟨(q.vertex ⟨i.val-1, by omega⟩).val,
      mem_nbrs_of_adj ((path_adj_iff q _ _).mpr (Or.inr (by simp only; omega))), sel_vertex q _⟩

theorem endSem_sel (w : Nat) (h : endSem (sel q) w = true) :
    w = (q.vertex 0).val ∨ w = (q.vertex (Fin.last m)).val := by
  unfold endSem at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hw, hle⟩ := h
  obtain ⟨i, rfl⟩ := (sel_iff q).mp hw
  by_cases h0 : i.val = 0
  · left; rw [show i = 0 from Fin.ext h0]
  by_cases hm : i.val = m
  · right; rw [show i = Fin.last m from Fin.ext hm]
  exfalso
  have ha := mem_nbrs_of_adj ((path_adj_iff q i ⟨i.val - 1, by omega⟩).mpr
    (Or.inr (by simp only; omega)))
  have hb := mem_nbrs_of_adj ((path_adj_iff q i ⟨i.val + 1, by omega⟩).mpr (Or.inl rfl))
  have hab : (q.vertex ⟨i.val - 1, by omega⟩).val ≠ (q.vertex ⟨i.val + 1, by omega⟩).val := by
    intro he
    have := congrArg Fin.val (q.distinct _ _ (Fin.ext he))
    simp only at this
    omega
  have := two_le_length (List.mem_filter.mpr ⟨ha, sel_vertex q _⟩)
    (List.mem_filter.mpr ⟨hb, sel_vertex q _⟩) hab
  omega

/-- At most two listed (distinct) vertices are endpoints in the sense of `endSem`. -/
theorem endSem_count (l : List Nat) (hnd : l.Nodup) :
    (l.filter (endSem (sel q))).length ≤ 2 :=
  length_le_two (hnd.filter _) (fun x hx => endSem_sel q x (List.mem_filter.mp hx).2)

end

/-! ### Counter-block counts -/

section
variable {T : Tables} {S : Nat → Bool}

def posEnd (T : Tables) : Lit → Bool
  | .ofNat v => isEnd T v
  | _ => false

def litE (T : Tables) (l : Lit) : Nat := ev T l.natAbs

theorem baseVal_ball {v : Nat} (h : isBall T v = true) : baseVal T S v = S (bv T v) := by
  simp only [isBall, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold baseVal
  rw [if_neg (by omega), if_pos h.2]

theorem baseVal_end {v : Nat} (h : isEnd T v = true) : baseVal T S v = endSem S (ev T v) := by
  simp only [isEnd, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold baseVal
  rw [if_neg (by omega), if_neg (by omega), if_pos h.2]

theorem cnt_negBall_eq : ∀ {lits : List Lit}, lits.all (negBall T) = true →
    cnt (baseVal T S) lits = ((lits.map (litV T)).filter (fun x => !S x)).length
  | [], _ => rfl
  | l :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := cnt_negBall_eq h.2
    unfold cnt at ih ⊢
    match l, h with
    | .negSucc n, h =>
      have hb : isBall T (n + 1) = true := h.1
      simp only [List.filter_cons, List.map_cons, litSat, baseVal_ball hb, litV]
      rw [show (Int.negSucc n).natAbs = n + 1 from rfl]
      split <;> simp_all

theorem cnt_posBall_eq : ∀ {lits : List Lit}, lits.all (posBall T) = true →
    cnt (baseVal T S) lits = ((lits.map (litV T)).filter S).length
  | [], _ => rfl
  | l :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := cnt_posBall_eq h.2
    unfold cnt at ih ⊢
    match l, h with
    | .ofNat v, h =>
      have hb : isBall T v = true := h.1
      simp only [List.filter_cons, List.map_cons, litSat, baseVal_ball hb, litV]
      split <;> simp_all

theorem cnt_posEnd_eq : ∀ {lits : List Lit}, lits.all (posEnd T) = true →
    cnt (baseVal T S) lits = ((lits.map (litE T)).filter (endSem S)).length
  | [], _ => rfl
  | l :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := cnt_posEnd_eq h.2
    unfold cnt at ih ⊢
    match l, h with
    | .ofNat v, h =>
      have hb : isEnd T v = true := h.1
      simp only [List.filter_cons, List.map_cons, litSat, baseVal_end hb, litE]
      split <;> simp_all

end

/-! ### Local singleton counts as corner counts -/

/-- The corner `c xor e_a xor e_b` of the axis pair `ab`. -/
def cornerOf (c : Nat) (ab : AxisPair) : Nat := c ^^^ 2 ^ ab.val.1.val ^^^ 2 ^ ab.val.2.val

/-- The 21 free corners at `c` (pairs avoiding the path directions `u1, u2`), lexicographic. -/
def cornerVerts (c u1 u2 : Nat) : List Nat :=
  (List.range 9).flatMap fun a => (List.range 9).filterMap fun b =>
    if a < b ∧ a ≠ u1 ∧ a ≠ u2 ∧ b ≠ u1 ∧ b ≠ u2 then some (c ^^^ 2 ^ a ^^^ 2 ^ b) else none

def freePairs (u1 u2 : Coord) : Finset AxisPair :=
  Finset.univ.filter fun ab => ab.val.1 ≠ u1 ∧ ab.val.1 ≠ u2 ∧ ab.val.2 ≠ u1 ∧ ab.val.2 ≠ u2

section
variable {m : Nat} (q : Snake m)

/-- The neighbours of an internal snake vertex on the snake are exactly the two path
neighbours. -/
theorem nbr_inPath_iff (i ip inx : Fin (m+1)) (hip : ip.val + 1 = i.val)
    (hin : inx.val = i.val + 1) (u1 u2 : Coord)
    (hp : q.vertex ip = flip u1 (q.vertex i)) (hn : q.vertex inx = flip u2 (q.vertex i))
    (a : Coord) : InPath q (flip a (q.vertex i)) ↔ (a = u1 ∨ a = u2) := by
  constructor
  · rintro ⟨j, hj⟩
    have hadj : Adj (q.vertex i) (q.vertex j) := hj ▸ flip_adj a (q.vertex i)
    rcases (path_adj_iff q i j).mp hadj with h | h
    · have : j = inx := Fin.ext (by omega)
      rw [this, hn] at hj
      exact Or.inr (flip_inj_coord _ hj).symm
    · have : j = ip := Fin.ext (by omega)
      rw [this, hp] at hj
      exact Or.inl (flip_inj_coord _ hj).symm
  · rintro (rfl | rfl)
    · exact ⟨ip, hp⟩
    · exact ⟨inx, hn⟩

theorem localAlpha_eq_corners (i ip inx : Fin (m+1)) (hip : ip.val + 1 = i.val)
    (hin : inx.val = i.val + 1) (u1 u2 : Coord)
    (hp : q.vertex ip = flip u1 (q.vertex i)) (hn : q.vertex inx = flip u2 (q.vertex i))
    (cs : List Nat)
    (hcs : (freePairs u1 u2).image (cornerOf (q.vertex i).val) = cs.toFinset)
    (hinj : ∀ a ∈ freePairs u1 u2, ∀ b ∈ freePairs u1 u2,
      cornerOf (q.vertex i).val a = cornerOf (q.vertex i).val b → a = b)
    (hnd : cs.Nodup) :
    localAlpha q i = (cs.filter (fun x => !sel q x)).length := by
  have hN := nbr_inPath_iff q i ip inx hip hin u1 u2 hp hn
  have hv : InPath q (q.vertex i) := ⟨i, rfl⟩
  have hs : ∀ ab : AxisPair, SquareIncidence.singleton q ab (q.vertex i) =
      if ab ∈ freePairs u1 u2 ∧ sel q (cornerOf (q.vertex i).val ab) = false then 1 else 0 := by
    intro ab
    unfold SquareIncidence.singleton
    have hc : InPath q (flip ab.val.2 (flip ab.val.1 (q.vertex i))) ↔
        sel q (cornerOf (q.vertex i).val ab) = true := inPath_iff_sel q _
    have hf : ab ∈ freePairs u1 u2 ↔
        (ab.val.1 ≠ u1 ∧ ab.val.1 ≠ u2 ∧ ab.val.2 ≠ u1 ∧ ab.val.2 ≠ u2) := by
      simp [freePairs]
    apply if_congr _ rfl rfl
    rw [hN, hN, hc, hf]
    simp only [not_or, Bool.not_eq_true]
    tauto
  unfold localAlpha
  rw [Finset.sum_congr rfl (fun ab _ => hs ab), Finset.sum_boole]
  simp only [Nat.cast_id]
  have h1 : (Finset.univ.filter fun ab : AxisPair =>
      ab ∈ freePairs u1 u2 ∧ sel q (cornerOf (q.vertex i).val ab) = false) =
      (freePairs u1 u2).filter (fun ab => sel q (cornerOf (q.vertex i).val ab) = false) := by
    ext ab; simp
  rw [h1]
  have h2 : ((freePairs u1 u2).filter
      (fun ab => sel q (cornerOf (q.vertex i).val ab) = false)).card =
      (((freePairs u1 u2).image (cornerOf (q.vertex i).val)).filter
        (fun x => sel q x = false)).card := by
    rw [Finset.filter_image, Finset.card_image_of_injOn]
    intro a ha b hb hab
    exact hinj a (Finset.mem_of_mem_filter a ha) b (Finset.mem_of_mem_filter b hb) hab
  rw [h2, hcs, ← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter]
  congr 1
  ext x
  simp

end

end W223G1
