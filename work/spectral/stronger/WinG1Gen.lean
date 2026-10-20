import W223G1Inst
/-!
# Generic G1 instances: windows of three or four centres, count ranges, both orientations

`tabOK T sp` (kernel-decidable) classifies every counter block of a window CNF table `T`: the
endpoint budget (at most two of the listed interior vertices are endpoints), or an upper
bound `alpha ≤ hi` (block over the negated 21 free corners of a centre, width `≥ hi`), or a
lower bound `alpha ≥ lo` (block over the corners, width `≥ 21 - lo`).  `sp` lists for each
centre its corner list and its count range `[lo, hi]`, so ranges such as `4 ≤ alpha ≤ 6` are
covered.  `win_false`: a snake whose vertex set contains the window and whose centre counts lie
in the ranges contradicts an unsatisfiable CNF all of whose clauses pass the checker.

`Refuted3` / `Refuted4` package such a refutation for the normalised windows
`0,1,3,7,x` and `0,1,3,7,x,y`; `tri_fwd`, `tri_rev`, `quad_fwd`, `quad_rev` apply it to a
snake running through the window forwards or backwards (positions `r..r+k+1` or `r+k+1..r`).
-/
namespace WinG1
open Snake9 Snake9.SquareIncidence WinCNF W223G1
open Classical

/-- A centre: its list of 21 free corners and its count range `[lo, hi]`. -/
abbrev Spec := List Nat × Nat × Nat

def specOK (T : Tables) (sp : List Spec) (b : Block) : Bool :=
  (b.lits.all (posEnd T) && decide (b.lits.map (litE T) = T.ends) && decide (b.k = 2)) ||
  sp.any (fun s =>
    (b.lits.all (negBall T) && decide (b.lits.map (litV T) = s.1) && decide (s.2.2 ≤ b.k)) ||
    (b.lits.all (posBall T) && decide (b.lits.map (litV T) = s.1) && decide (21 - s.2.1 ≤ b.k)))

def tabOK (T : Tables) (sp : List Spec) : Bool := nodupB T.ends && T.blocks.all (specOK T sp)

/-- The count facts of a centre for a selection `S`. -/
def SpecHolds (S : Nat → Bool) (s : Spec) : Prop :=
  (s.1.filter (fun x => !S x)).length ≤ s.2.2 ∧ (s.1.filter S).length ≤ 21 - s.2.1

theorem blocks_of_tabOK {T : Tables} {sp : List Spec} {S : Nat → Bool} (hT : tabOK T sp = true)
    (hsp : ∀ s ∈ sp, SpecHolds S s)
    (hend : ∀ l : List Nat, l.Nodup → (l.filter (endSem S)).length ≤ 2) :
    ∀ b ∈ T.blocks, cnt (baseVal T S) b.lits ≤ b.k := by
  simp only [tabOK, Bool.and_eq_true, List.all_eq_true] at hT
  intro b hb
  have h := hT.2 b hb
  simp only [specOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨s, hs, (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)⟩
  · rw [cnt_posEnd_eq h1, h2, h3]; exact hend _ (nodupB_nodup hT.1)
  · rw [cnt_negBall_eq h1, h2]; exact Nat.le_trans (hsp s hs).1 h3
  · rw [cnt_posBall_eq h1, h2]; have := (hsp s hs).2; omega

theorem win_false {m : Nat} (q : Snake m) (hm : 1 ≤ m) {T : Tables} {sp : List Spec} {F : CNF}
    (hF : unsat F) (hok : blocksOK T = true) (hc : F.all (check T) = true)
    (hT : tabOK T sp = true) (hw : ∀ w ∈ T.window, sel q w = true)
    (hsp : ∀ s ∈ sp, SpecHolds (sel q) s) : False :=
  no_hyp hF hok hc ⟨hw, sel_bad q, sel_deg q hm, blocks_of_tabOK hT hsp (endSem_count q)⟩

/-! ### Centres -/

def CornerOK (c : Nat) (u1 u2 : Coord) (cs : List Nat) : Prop :=
  (freePairs u1 u2).image (cornerOf c) = cs.toFinset ∧
  (∀ a ∈ freePairs u1 u2, ∀ b ∈ freePairs u1 u2, cornerOf c a = cornerOf c b → a = b) ∧
  nodupB cs = true ∧ cs.length = 21

theorem freePairs_comm (u1 u2 : Coord) : freePairs u1 u2 = freePairs u2 u1 := by
  ext ab
  simp only [freePairs, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem CornerOK.swap {c : Nat} {u1 u2 : Coord} {cs : List Nat} (h : CornerOK c u1 u2 cs) :
    CornerOK c u2 u1 cs := by
  unfold CornerOK at *; rw [freePairs_comm u2 u1]; exact h

/-- Count facts at the internal snake vertex `ip + 1`, whose path neighbours are `flip u1 c`
(position `ip`) and `flip u2 c` (position `ip + 2`). -/
theorem centre {m : Nat} (q : Snake m) (ip : Nat) (hi : ip + 2 ≤ m) (c : Vertex) (u1 u2 : Coord)
    (hc : q.vertex ⟨ip+1, by omega⟩ = c) (hp : q.vertex ⟨ip, by omega⟩ = flip u1 c)
    (hn : q.vertex ⟨ip+2, by omega⟩ = flip u2 c) {cs : List Nat} (hcs : CornerOK c.val u1 u2 cs)
    {lo hi' : Nat} (ha : lo ≤ localAlpha q ⟨ip+1, by omega⟩ ∧ localAlpha q ⟨ip+1, by omega⟩ ≤ hi') :
    SpecHolds (sel q) (cs, lo, hi') := by
  obtain ⟨e1, e2, e3, e4⟩ := hcs
  have h := center_counts q ⟨ip+1, by omega⟩ ⟨ip, by omega⟩ ⟨ip+2, by omega⟩ rfl rfl c u1 u2
    hc hp hn cs e1 e2 (nodupB_nodup e3) e4 _ rfl
  unfold SpecHolds
  simp only
  omega

theorem cok1 : CornerOK 1 0 1 (cornerVerts 1 0 1) := ⟨cv1, inj1, nd1⟩
theorem cok3 : CornerOK 3 1 2 (cornerVerts 3 1 2) := ⟨cv3, inj3, nd3⟩
theorem cok7r : CornerOK 7 2 0 (cornerVerts 7 2 0) := ⟨cv7r, inj7r, nd7r⟩
theorem cok7d : CornerOK 7 2 3 (cornerVerts 7 2 3) := ⟨cv7d, inj7d, nd7d⟩
theorem cok6 : CornerOK 6 0 3 (cornerVerts 6 0 3) := by unfold CornerOK; decide +kernel
theorem cok15a : CornerOK 15 3 0 (cornerVerts 15 3 0) := by unfold CornerOK; decide +kernel
theorem cok15b : CornerOK 15 3 4 (cornerVerts 15 3 4) := by unfold CornerOK; decide +kernel

/-! ### Packaged refutations of the normalised windows -/

/-- Some checked, refuted window CNF has window `0,1,3,7,flip u3 7` and centre ranges
`[lo1,hi1]`, `[lo2,hi2]`, `[lo3,hi3]` at `1, 3, 7`. -/
def Refuted3 (u3 : Coord) (lo1 hi1 lo2 hi2 lo3 hi3 : Nat) : Prop :=
  ∃ (T : Tables) (F : CNF), unsat F ∧ blocksOK T = true ∧ F.all (check T) = true ∧
    tabOK T [(cornerVerts 1 0 1, lo1, hi1), (cornerVerts 3 1 2, lo2, hi2),
      (cornerVerts 7 2 u3, lo3, hi3)] = true ∧
    T.window = [0, 1, 3, 7, (flip u3 7).val]

/-- As `Refuted3` for four centres `1, 3, 7, x` with `x = flip u3 7`, window ending in
`y = flip u4 x`. -/
def Refuted4 (u3 u4 : Coord) (lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat) : Prop :=
  ∃ (T : Tables) (F : CNF), unsat F ∧ blocksOK T = true ∧ F.all (check T) = true ∧
    tabOK T [(cornerVerts 1 0 1, lo1, hi1), (cornerVerts 3 1 2, lo2, hi2),
      (cornerVerts 7 2 u3, lo3, hi3), (cornerVerts (flip u3 7).val u3 u4, lo4, hi4)] = true ∧
    T.window = [0, 1, 3, 7, (flip u3 7).val, (flip u4 (flip u3 7)).val]

section
variable {m : Nat} (q : Snake m)

theorem sel_at (i : Fin (m+1)) {v : Vertex} (h : q.vertex i = v) : sel q v.val = true := by
  rw [← h]; exact sel_vertex q i

/-- A forward three-centre window: positions `r..r+4` carry `0,1,3,7,x`. -/
theorem tri_fwd {u3 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 : Nat}
    (hR : Refuted3 u3 lo1 hi1 lo2 hi2 lo3 hi3) (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = flip u3 7)
    (a1 : lo1 ≤ localAlpha q ⟨r+1, by omega⟩ ∧ localAlpha q ⟨r+1, by omega⟩ ≤ hi1)
    (a2 : lo2 ≤ localAlpha q ⟨r+2, by omega⟩ ∧ localAlpha q ⟨r+2, by omega⟩ ≤ hi2)
    (a3 : lo3 ≤ localAlpha q ⟨r+3, by omega⟩ ∧ localAlpha q ⟨r+3, by omega⟩ ≤ hi3) : False := by
  obtain ⟨T, F, hF, hok, hc, hT, hw⟩ := hR
  refine win_false q (by omega) hF hok hc hT ?_ ?_
  · rw [hw]; intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
    · exact sel_at q _ h4
  · intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact centre q r (by omega) 1 0 1 h1 (by rw [h0]; decide) (by rw [h2]; decide) cok1 a1
    · exact centre q (r+1) (by omega) 3 1 2 h2 (by rw [h1]; decide) (by rw [h3]; decide) cok3 a2
    · exact centre q (r+2) (by omega) 7 2 u3 h3 (by rw [h2]; decide) h4 h7 a3

/-- A backward three-centre window: positions `r+4..r` carry `0,1,3,7,x`. -/
theorem tri_rev {u3 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 : Nat}
    (hR : Refuted3 u3 lo1 hi1 lo2 hi2 lo3 hi3) (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r+4, by omega⟩ = 0) (h1 : q.vertex ⟨r+3, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+1, by omega⟩ = 7)
    (h4 : q.vertex ⟨r, by omega⟩ = flip u3 7)
    (a1 : lo1 ≤ localAlpha q ⟨r+3, by omega⟩ ∧ localAlpha q ⟨r+3, by omega⟩ ≤ hi1)
    (a2 : lo2 ≤ localAlpha q ⟨r+2, by omega⟩ ∧ localAlpha q ⟨r+2, by omega⟩ ≤ hi2)
    (a3 : lo3 ≤ localAlpha q ⟨r+1, by omega⟩ ∧ localAlpha q ⟨r+1, by omega⟩ ≤ hi3) : False := by
  obtain ⟨T, F, hF, hok, hc, hT, hw⟩ := hR
  refine win_false q (by omega) hF hok hc hT ?_ ?_
  · rw [hw]; intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
    · exact sel_at q _ h4
  · intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact centre q (r+2) (by omega) 1 1 0 h1 (by rw [h2]; decide) (by rw [h0]; decide)
        cok1.swap a1
    · exact centre q (r+1) (by omega) 3 2 1 h2 (by rw [h3]; decide) (by rw [h1]; decide)
        cok3.swap a2
    · exact centre q r (by omega) 7 u3 2 h3 h4 (by rw [h2]; decide) h7.swap a3

/-- A forward four-centre window: positions `r..r+5` carry `0,1,3,7,x,y`. -/
theorem quad_fwd {u3 u4 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat}
    (hR : Refuted4 u3 u4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4)
    (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (hx : CornerOK (flip u3 7).val u3 u4 (cornerVerts (flip u3 7).val u3 u4))
    (r : Nat) (hr : r + 5 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = flip u3 7)
    (h5 : q.vertex ⟨r+5, by omega⟩ = flip u4 (flip u3 7))
    (a1 : lo1 ≤ localAlpha q ⟨r+1, by omega⟩ ∧ localAlpha q ⟨r+1, by omega⟩ ≤ hi1)
    (a2 : lo2 ≤ localAlpha q ⟨r+2, by omega⟩ ∧ localAlpha q ⟨r+2, by omega⟩ ≤ hi2)
    (a3 : lo3 ≤ localAlpha q ⟨r+3, by omega⟩ ∧ localAlpha q ⟨r+3, by omega⟩ ≤ hi3)
    (a4 : lo4 ≤ localAlpha q ⟨r+4, by omega⟩ ∧ localAlpha q ⟨r+4, by omega⟩ ≤ hi4) : False := by
  obtain ⟨T, F, hF, hok, hc, hT, hw⟩ := hR
  refine win_false q (by omega) hF hok hc hT ?_ ?_
  · rw [hw]; intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
    · exact sel_at q _ h4
    · exact sel_at q _ h5
  · intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact centre q r (by omega) 1 0 1 h1 (by rw [h0]; decide) (by rw [h2]; decide) cok1 a1
    · exact centre q (r+1) (by omega) 3 1 2 h2 (by rw [h1]; decide) (by rw [h3]; decide) cok3 a2
    · exact centre q (r+2) (by omega) 7 2 u3 h3 (by rw [h2]; decide) h4 h7 a3
    · exact centre q (r+3) (by omega) (flip u3 7) u3 u4 h4
        (by rw [h3, flip_twice]) h5 hx a4

/-- A backward four-centre window: positions `r+5..r` carry `0,1,3,7,x,y`. -/
theorem quad_rev {u3 u4 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat}
    (hR : Refuted4 u3 u4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4)
    (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (hx : CornerOK (flip u3 7).val u3 u4 (cornerVerts (flip u3 7).val u3 u4))
    (r : Nat) (hr : r + 5 ≤ m)
    (h0 : q.vertex ⟨r+5, by omega⟩ = 0) (h1 : q.vertex ⟨r+4, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+3, by omega⟩ = 3) (h3 : q.vertex ⟨r+2, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+1, by omega⟩ = flip u3 7)
    (h5 : q.vertex ⟨r, by omega⟩ = flip u4 (flip u3 7))
    (a1 : lo1 ≤ localAlpha q ⟨r+4, by omega⟩ ∧ localAlpha q ⟨r+4, by omega⟩ ≤ hi1)
    (a2 : lo2 ≤ localAlpha q ⟨r+3, by omega⟩ ∧ localAlpha q ⟨r+3, by omega⟩ ≤ hi2)
    (a3 : lo3 ≤ localAlpha q ⟨r+2, by omega⟩ ∧ localAlpha q ⟨r+2, by omega⟩ ≤ hi3)
    (a4 : lo4 ≤ localAlpha q ⟨r+1, by omega⟩ ∧ localAlpha q ⟨r+1, by omega⟩ ≤ hi4) : False := by
  obtain ⟨T, F, hF, hok, hc, hT, hw⟩ := hR
  refine win_false q (by omega) hF hok hc hT ?_ ?_
  · rw [hw]; intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
    · exact sel_at q _ h4
    · exact sel_at q _ h5
  · intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact centre q (r+3) (by omega) 1 1 0 h1 (by rw [h2]; decide) (by rw [h0]; decide)
        cok1.swap a1
    · exact centre q (r+2) (by omega) 3 2 1 h2 (by rw [h3]; decide) (by rw [h1]; decide)
        cok3.swap a2
    · exact centre q (r+1) (by omega) 7 u3 2 h3 h4 (by rw [h2]; decide) h7.swap a3
    · exact centre q r (by omega) (flip u3 7) u4 u3 h4 h5
        (by rw [h3, flip_twice]) hx.swap a4

end

end WinG1
