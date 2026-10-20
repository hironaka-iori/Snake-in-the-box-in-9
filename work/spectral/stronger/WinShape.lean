import UpperBound244
import WinG1Gen
/-!
# Window shapes and normalisation for three- and four-centre windows

Along a snake, edge directions `d_j = dirC p j` satisfy `d_j ≠ d_{j+1}`, `d_j ≠ d_{j+2}`
(`W223G1.dir_ne_succ`, `dir_ne_succ_succ`) and, for five consecutive edges, not
`d_{j+3} = d_j ∧ d_{j+4} = d_{j+1}` (`dir_chord`: the path would have a chord).
Hence, up to relabelling, a three-centre window (four edges) has shape `0120` or `0123`, and a
four-centre window (five edges) has shape `01203`, `01230`, `01231` or `01234`.
`norm` (from `CubePerm.exists_normalizing_cubeMap`) moves a window to the normal position,
forwards (vertex `r ↦ 0`) or backwards (vertex `r+k+1 ↦ 0`, edges read in reverse), keeping
all local singleton counts.  `no_tri_fwd`, `no_tri_rev`, `no_quad` then combine the shape case
split with packaged refutations (`WinG1.Refuted3/4`) of the normalised windows.
-/
namespace WinShape
open Snake9 Snake9.SquareIncidence WinCNF W223G1 WinG1

section
variable {m : Nat}

theorem norm (p : Snake m) (b : Nat) (hb : b ≤ m) (l : List Nat)
    (hnd : (l.map (dirC p)).Nodup) (hl : ∀ j ∈ l, j < m) :
    ∃ q : Snake m, q.vertex ⟨b, by omega⟩ = 0 ∧
      (∀ i (h : i < l.length), WindowAutomaton.pathDir q l[i] = i) ∧
      (∀ k, localAlpha q k = localAlpha p k) ∧
      (∀ j j', j < m → j' < m → dirC p j = dirC p j' →
        WindowAutomaton.pathDir q j = WindowAutomaton.pathDir q j') := by
  obtain ⟨σ, x, h0, hd, ha⟩ := CubePerm.exists_normalizing_cubeMap p ⟨b, by omega⟩ l hnd hl
  refine ⟨_, h0, hd, ha, fun j j' hj hj' he => ?_⟩
  rw [CubePerm.pathDir_cubeMap σ x p j hj, CubePerm.pathDir_cubeMap σ x p j' hj']
  exact congrArg (fun c => (σ c).val) he

theorem stepF (q : Snake m) (j : Nat) (hj : j < m) (a : Coord) {v w : Vertex}
    (hd : WindowAutomaton.pathDir q j = a.val) (hv : q.vertex ⟨j, by omega⟩ = v)
    (hw : flip a v = w) : q.vertex ⟨j+1, by omega⟩ = w := by
  rw [vertex_succ_dir q j hj a hd, hv, ← hw]; rfl

theorem stepB (q : Snake m) (j : Nat) (hj : j < m) (a : Coord) {v w : Vertex}
    (hd : WindowAutomaton.pathDir q j = a.val) (hv : q.vertex ⟨j+1, by omega⟩ = v)
    (hw : flip a v = w) : q.vertex ⟨j, by omega⟩ = w := by
  rw [vertex_succ_dir q j hj a hd] at hv
  rw [← hw, ← hv]
  exact (flip_twice a _).symm

/-- Five consecutive edges never have directions `a b c a b`. -/
theorem dir_chord (p : Snake m) (j : Nat) (hj : j + 5 ≤ m)
    (h30 : dirC p (j+3) = dirC p j) (h41 : dirC p (j+4) = dirC p (j+1)) : False := by
  have e1 := vertex_succ_dir p j (by omega) (dirC p j) rfl
  have e2 := vertex_succ_dir p (j+1) (by omega) (dirC p (j+1)) rfl
  have e3 := vertex_succ_dir p (j+2) (by omega) (dirC p (j+2)) rfl
  have e4 := vertex_succ_dir p (j+3) (by omega) (dirC p j) (by rw [← h30]; rfl)
  have e5 := vertex_succ_dir p (j+4) (by omega) (dirC p (j+1)) (by rw [← h41]; rfl)
  have hv : p.vertex ⟨j+5, by omega⟩ = flip (dirC p (j+2)) (p.vertex ⟨j, by omega⟩) := by
    rw [e5, e4, e3, e2, e1]
    change SquareIncidence.flip _ (SquareIncidence.flip _ (SquareIncidence.flip _ (SquareIncidence.flip _ (SquareIncidence.flip _ _)))) = _
    rw [flip_commute (dirC p (j+1)) (dirC p j) (p.vertex _),
      flip_commute (dirC p (j+2)) (dirC p j), flip_twice,
      flip_commute (dirC p (j+2)) (dirC p (j+1)), flip_twice]
  have hadj : Adj (p.vertex ⟨j, by omega⟩) (p.vertex ⟨j+5, by omega⟩) := by
    rw [hv]; exact flip_adj _ _
  have := (p.induced ⟨j, by omega⟩ ⟨j+5, by omega⟩ (by simp)).mp hadj
  simp at this

theorem nodup3 {a b c : Coord} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : [a, b, c].Nodup := by
  simp [List.nodup_cons, hab, hac, hbc]

theorem nodup4 {a b c d : Coord} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : [a, b, c, d].Nodup := by
  simp [List.nodup_cons, hab, hac, had, hbc, hbd, hcd]

theorem nodup5 {a b c d e : Coord} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    [a, b, c, d, e].Nodup := by
  simp [List.nodup_cons, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]

/-! ### Three-centre windows -/

/-- Counts in `[lo1,hi1], [lo2,hi2], [lo3,hi3]` at `r+1, r+2, r+3` are impossible, given
refutations of the forward pattern in both shapes. -/
theorem no_tri_fwd {lo1 hi1 lo2 hi2 lo3 hi3 : Nat}
    (hR : Refuted3 0 lo1 hi1 lo2 hi2 lo3 hi3) (hD : Refuted3 3 lo1 hi1 lo2 hi2 lo3 hi3)
    (p : Snake m) (r : Nat) (hr : r + 4 ≤ m)
    (a1 : lo1 ≤ localAlpha p ⟨r+1, by omega⟩ ∧ localAlpha p ⟨r+1, by omega⟩ ≤ hi1)
    (a2 : lo2 ≤ localAlpha p ⟨r+2, by omega⟩ ∧ localAlpha p ⟨r+2, by omega⟩ ≤ hi2)
    (a3 : lo3 ≤ localAlpha p ⟨r+3, by omega⟩ ∧ localAlpha p ⟨r+3, by omega⟩ ≤ hi3) : False := by
  have n01 : dirC p r ≠ dirC p (r+1) := dir_ne_succ p r (by omega)
  have n12 : dirC p (r+1) ≠ dirC p (r+2) := dir_ne_succ p (r+1) (by omega)
  have n23 : dirC p (r+2) ≠ dirC p (r+3) := dir_ne_succ p (r+2) (by omega)
  have n02 : dirC p r ≠ dirC p (r+2) := dir_ne_succ_succ p r (by omega)
  have n13 : dirC p (r+1) ≠ dirC p (r+3) := dir_ne_succ_succ p (r+1) (by omega)
  by_cases h30 : dirC p (r+3) = dirC p r
  · obtain ⟨q, v0, hd, ha, htr⟩ := norm p r (by omega) [r, r+1, r+2] (nodup3 n01 n02 n12)
      (by intro j hj; simp at hj; omega)
    have d0 : WindowAutomaton.pathDir q r = (0 : Coord).val := hd 0 (by simp)
    have d1 : WindowAutomaton.pathDir q (r+1) = (1 : Coord).val := hd 1 (by simp)
    have d2 : WindowAutomaton.pathDir q (r+2) = (2 : Coord).val := hd 2 (by simp)
    have d3 : WindowAutomaton.pathDir q (r+3) = (0 : Coord).val :=
      (htr _ _ (by omega) (by omega) h30).trans d0
    have v1 := stepF q r (by omega) 0 d0 v0 (w := 1) (by decide)
    have v2 := stepF q (r+1) (by omega) 1 d1 v1 (w := 3) (by decide)
    have v3 := stepF q (r+2) (by omega) 2 d2 v2 (w := 7) (by decide)
    have v4 := stepF q (r+3) (by omega) 0 d3 v3 rfl
    exact tri_fwd q hR cok7r r hr v0 v1 v2 v3 v4 (by simpa only [ha] using a1)
      (by simpa only [ha] using a2) (by simpa only [ha] using a3)
  · obtain ⟨q, v0, hd, ha, -⟩ := norm p r (by omega) [r, r+1, r+2, r+3]
      (nodup4 n01 n02 (Ne.symm h30) n12 n13 n23) (by intro j hj; simp at hj; omega)
    have d0 : WindowAutomaton.pathDir q r = (0 : Coord).val := hd 0 (by simp)
    have d1 : WindowAutomaton.pathDir q (r+1) = (1 : Coord).val := hd 1 (by simp)
    have d2 : WindowAutomaton.pathDir q (r+2) = (2 : Coord).val := hd 2 (by simp)
    have d3 : WindowAutomaton.pathDir q (r+3) = (3 : Coord).val := hd 3 (by simp)
    have v1 := stepF q r (by omega) 0 d0 v0 (w := 1) (by decide)
    have v2 := stepF q (r+1) (by omega) 1 d1 v1 (w := 3) (by decide)
    have v3 := stepF q (r+2) (by omega) 2 d2 v2 (w := 7) (by decide)
    have v4 := stepF q (r+3) (by omega) 3 d3 v3 rfl
    exact tri_fwd q hD cok7d r hr v0 v1 v2 v3 v4 (by simpa only [ha] using a1)
      (by simpa only [ha] using a2) (by simpa only [ha] using a3)

/-- The reversed pattern: counts in `[lo3,hi3], [lo2,hi2], [lo1,hi1]` at `r+1, r+2, r+3`. -/
theorem no_tri_rev {lo1 hi1 lo2 hi2 lo3 hi3 : Nat}
    (hR : Refuted3 0 lo1 hi1 lo2 hi2 lo3 hi3) (hD : Refuted3 3 lo1 hi1 lo2 hi2 lo3 hi3)
    (p : Snake m) (r : Nat) (hr : r + 4 ≤ m)
    (a3 : lo3 ≤ localAlpha p ⟨r+1, by omega⟩ ∧ localAlpha p ⟨r+1, by omega⟩ ≤ hi3)
    (a2 : lo2 ≤ localAlpha p ⟨r+2, by omega⟩ ∧ localAlpha p ⟨r+2, by omega⟩ ≤ hi2)
    (a1 : lo1 ≤ localAlpha p ⟨r+3, by omega⟩ ∧ localAlpha p ⟨r+3, by omega⟩ ≤ hi1) : False := by
  have n01 : dirC p r ≠ dirC p (r+1) := dir_ne_succ p r (by omega)
  have n12 : dirC p (r+1) ≠ dirC p (r+2) := dir_ne_succ p (r+1) (by omega)
  have n23 : dirC p (r+2) ≠ dirC p (r+3) := dir_ne_succ p (r+2) (by omega)
  have n02 : dirC p r ≠ dirC p (r+2) := dir_ne_succ_succ p r (by omega)
  have n13 : dirC p (r+1) ≠ dirC p (r+3) := dir_ne_succ_succ p (r+1) (by omega)
  by_cases h03 : dirC p r = dirC p (r+3)
  · obtain ⟨q, v0, hd, ha, htr⟩ := norm p (r+4) (by omega) [r+3, r+2, r+1]
      (nodup3 (Ne.symm n23) (Ne.symm n13) (Ne.symm n12)) (by intro j hj; simp at hj; omega)
    have d0 : WindowAutomaton.pathDir q (r+3) = (0 : Coord).val := hd 0 (by simp)
    have d1 : WindowAutomaton.pathDir q (r+2) = (1 : Coord).val := hd 1 (by simp)
    have d2 : WindowAutomaton.pathDir q (r+1) = (2 : Coord).val := hd 2 (by simp)
    have d3 : WindowAutomaton.pathDir q r = (0 : Coord).val :=
      (htr _ _ (by omega) (by omega) h03).trans d0
    have v1 := stepB q (r+3) (by omega) 0 d0 v0 (w := 1) (by decide)
    have v2 := stepB q (r+2) (by omega) 1 d1 v1 (w := 3) (by decide)
    have v3 := stepB q (r+1) (by omega) 2 d2 v2 (w := 7) (by decide)
    have v4 := stepB q r (by omega) 0 d3 v3 rfl
    exact tri_rev q hR cok7r r hr v0 v1 v2 v3 v4 (by simpa only [ha] using a1)
      (by simpa only [ha] using a2) (by simpa only [ha] using a3)
  · obtain ⟨q, v0, hd, ha, -⟩ := norm p (r+4) (by omega) [r+3, r+2, r+1, r]
      (nodup4 (Ne.symm n23) (Ne.symm n13) (Ne.symm h03) (Ne.symm n12) (Ne.symm n02)
        (Ne.symm n01)) (by intro j hj; simp at hj; omega)
    have d0 : WindowAutomaton.pathDir q (r+3) = (0 : Coord).val := hd 0 (by simp)
    have d1 : WindowAutomaton.pathDir q (r+2) = (1 : Coord).val := hd 1 (by simp)
    have d2 : WindowAutomaton.pathDir q (r+1) = (2 : Coord).val := hd 2 (by simp)
    have d3 : WindowAutomaton.pathDir q r = (3 : Coord).val := hd 3 (by simp)
    have v1 := stepB q (r+3) (by omega) 0 d0 v0 (w := 1) (by decide)
    have v2 := stepB q (r+2) (by omega) 1 d1 v1 (w := 3) (by decide)
    have v3 := stepB q (r+1) (by omega) 2 d2 v2 (w := 7) (by decide)
    have v4 := stepB q r (by omega) 3 d3 v3 rfl
    exact tri_rev q hD cok7d r hr v0 v1 v2 v3 v4 (by simpa only [ha] using a1)
      (by simpa only [ha] using a2) (by simpa only [ha] using a3)

/-! ### Four-centre windows -/

theorem cok6' : CornerOK (SquareIncidence.flip 0 7).val 0 3
    (cornerVerts (SquareIncidence.flip 0 7).val 0 3) := cok6
theorem cok15a' : CornerOK (SquareIncidence.flip 3 7).val 3 0
    (cornerVerts (SquareIncidence.flip 3 7).val 3 0) := cok15a
theorem cok15b' : CornerOK (SquareIncidence.flip 3 7).val 3 4
    (cornerVerts (SquareIncidence.flip 3 7).val 3 4) := cok15b

/-- Counts in `[lo_i, hi_i]` at `r+1..r+4` are impossible, given refutations of the pattern in
shape `01203` (forward), of the reversed pattern in shape `01203` (this covers shape `01231`
backwards), and of the pattern or its reversal in shapes `01230` and `01234`. -/
theorem no_quad {lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat}
    (hA : Refuted4 0 3 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4)
    (hA' : Refuted4 0 3 lo4 hi4 lo3 hi3 lo2 hi2 lo1 hi1)
    (hB : Refuted4 3 0 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 ∨ Refuted4 3 0 lo4 hi4 lo3 hi3 lo2 hi2 lo1 hi1)
    (hC : Refuted4 3 4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 ∨ Refuted4 3 4 lo4 hi4 lo3 hi3 lo2 hi2 lo1 hi1)
    (p : Snake m) (r : Nat) (hr : r + 5 ≤ m)
    (a1 : lo1 ≤ localAlpha p ⟨r+1, by omega⟩ ∧ localAlpha p ⟨r+1, by omega⟩ ≤ hi1)
    (a2 : lo2 ≤ localAlpha p ⟨r+2, by omega⟩ ∧ localAlpha p ⟨r+2, by omega⟩ ≤ hi2)
    (a3 : lo3 ≤ localAlpha p ⟨r+3, by omega⟩ ∧ localAlpha p ⟨r+3, by omega⟩ ≤ hi3)
    (a4 : lo4 ≤ localAlpha p ⟨r+4, by omega⟩ ∧ localAlpha p ⟨r+4, by omega⟩ ≤ hi4) : False := by
  have n01 : dirC p r ≠ dirC p (r+1) := dir_ne_succ p r (by omega)
  have n12 : dirC p (r+1) ≠ dirC p (r+2) := dir_ne_succ p (r+1) (by omega)
  have n23 : dirC p (r+2) ≠ dirC p (r+3) := dir_ne_succ p (r+2) (by omega)
  have n34 : dirC p (r+3) ≠ dirC p (r+4) := dir_ne_succ p (r+3) (by omega)
  have n02 : dirC p r ≠ dirC p (r+2) := dir_ne_succ_succ p r (by omega)
  have n13 : dirC p (r+1) ≠ dirC p (r+3) := dir_ne_succ_succ p (r+1) (by omega)
  have n24 : dirC p (r+2) ≠ dirC p (r+4) := dir_ne_succ_succ p (r+2) (by omega)
  have hl5 : ∀ l : List Nat, (∀ j ∈ l, j ≤ r + 4) → ∀ j ∈ l, j < m :=
    fun l h j hj => by have := h j hj; omega
  by_cases h30 : dirC p (r+3) = dirC p r
  · -- shape 01203, forward
    have h41 : dirC p (r+4) ≠ dirC p (r+1) := fun h => dir_chord p r hr h30 h
    have h40 : dirC p (r+4) ≠ dirC p r := fun h => n34 (h30.trans h.symm)
    obtain ⟨q, v0, hd, ha, htr⟩ := norm p r (by omega) [r, r+1, r+2, r+4]
      (nodup4 n01 n02 (Ne.symm h40) n12 (Ne.symm h41) n24)
      (hl5 _ (by intro j hj; simp at hj; omega))
    have d0 : WindowAutomaton.pathDir q r = (0 : Coord).val := hd 0 (by simp)
    have d1 : WindowAutomaton.pathDir q (r+1) = (1 : Coord).val := hd 1 (by simp)
    have d2 : WindowAutomaton.pathDir q (r+2) = (2 : Coord).val := hd 2 (by simp)
    have d4 : WindowAutomaton.pathDir q (r+4) = (3 : Coord).val := hd 3 (by simp)
    have d3 : WindowAutomaton.pathDir q (r+3) = (0 : Coord).val :=
      (htr _ _ (by omega) (by omega) h30).trans d0
    have v1 := stepF q r (by omega) 0 d0 v0 (w := 1) (by decide)
    have v2 := stepF q (r+1) (by omega) 1 d1 v1 (w := 3) (by decide)
    have v3 := stepF q (r+2) (by omega) 2 d2 v2 (w := 7) (by decide)
    have v4 := stepF q (r+3) (by omega) 0 d3 v3 rfl
    have v5 := stepF q (r+4) (by omega) 3 d4 v4 rfl
    exact quad_fwd q hA cok7r cok6' r hr v0 v1 v2 v3 v4 v5 (by simpa only [ha] using a1)
      (by simpa only [ha] using a2) (by simpa only [ha] using a3) (by simpa only [ha] using a4)
  by_cases h40 : dirC p (r+4) = dirC p r
  · -- shape 01230
    have h41 : dirC p (r+4) ≠ dirC p (r+1) := by rw [h40]; exact n01
    rcases hB with hB | hB
    · obtain ⟨q, v0, hd, ha, htr⟩ := norm p r (by omega) [r, r+1, r+2, r+3]
        (nodup4 n01 n02 (Ne.symm h30) n12 n13 n23) (hl5 _ (by intro j hj; simp at hj; omega))
      have d0 : WindowAutomaton.pathDir q r = (0 : Coord).val := hd 0 (by simp)
      have d1 : WindowAutomaton.pathDir q (r+1) = (1 : Coord).val := hd 1 (by simp)
      have d2 : WindowAutomaton.pathDir q (r+2) = (2 : Coord).val := hd 2 (by simp)
      have d3 : WindowAutomaton.pathDir q (r+3) = (3 : Coord).val := hd 3 (by simp)
      have d4 : WindowAutomaton.pathDir q (r+4) = (0 : Coord).val :=
        (htr _ _ (by omega) (by omega) h40).trans d0
      have v1 := stepF q r (by omega) 0 d0 v0 (w := 1) (by decide)
      have v2 := stepF q (r+1) (by omega) 1 d1 v1 (w := 3) (by decide)
      have v3 := stepF q (r+2) (by omega) 2 d2 v2 (w := 7) (by decide)
      have v4 := stepF q (r+3) (by omega) 3 d3 v3 rfl
      have v5 := stepF q (r+4) (by omega) 0 d4 v4 rfl
      exact quad_fwd q hB cok7d cok15a' r hr v0 v1 v2 v3 v4 v5 (by simpa only [ha] using a1)
        (by simpa only [ha] using a2) (by simpa only [ha] using a3) (by simpa only [ha] using a4)
    · obtain ⟨q, v0, hd, ha, htr⟩ := norm p (r+5) (by omega) [r+4, r+3, r+2, r+1]
        (nodup4 (Ne.symm n34) (Ne.symm n24) h41 (Ne.symm n23) (Ne.symm n13) (Ne.symm n12))
        (hl5 _ (by intro j hj; simp at hj; omega))
      have d0 : WindowAutomaton.pathDir q (r+4) = (0 : Coord).val := hd 0 (by simp)
      have d1 : WindowAutomaton.pathDir q (r+3) = (1 : Coord).val := hd 1 (by simp)
      have d2 : WindowAutomaton.pathDir q (r+2) = (2 : Coord).val := hd 2 (by simp)
      have d3 : WindowAutomaton.pathDir q (r+1) = (3 : Coord).val := hd 3 (by simp)
      have d4 : WindowAutomaton.pathDir q r = (0 : Coord).val :=
        (htr _ _ (by omega) (by omega) h40.symm).trans d0
      have v1 := stepB q (r+4) (by omega) 0 d0 v0 (w := 1) (by decide)
      have v2 := stepB q (r+3) (by omega) 1 d1 v1 (w := 3) (by decide)
      have v3 := stepB q (r+2) (by omega) 2 d2 v2 (w := 7) (by decide)
      have v4 := stepB q (r+1) (by omega) 3 d3 v3 rfl
      have v5 := stepB q r (by omega) 0 d4 v4 rfl
      exact quad_rev q hB cok7d cok15a' r hr v0 v1 v2 v3 v4 v5 (by simpa only [ha] using a4)
        (by simpa only [ha] using a3) (by simpa only [ha] using a2) (by simpa only [ha] using a1)
  by_cases h41 : dirC p (r+4) = dirC p (r+1)
  · -- shape 01231, backward it is 01203 with the reversed pattern
    obtain ⟨q, v0, hd, ha, htr⟩ := norm p (r+5) (by omega) [r+4, r+3, r+2, r]
      (nodup4 (Ne.symm n34) (Ne.symm n24) h40 (Ne.symm n23) h30 (Ne.symm n02))
      (hl5 _ (by intro j hj; simp at hj; omega))
    have d0 : WindowAutomaton.pathDir q (r+4) = (0 : Coord).val := hd 0 (by simp)
    have d1 : WindowAutomaton.pathDir q (r+3) = (1 : Coord).val := hd 1 (by simp)
    have d2 : WindowAutomaton.pathDir q (r+2) = (2 : Coord).val := hd 2 (by simp)
    have d4 : WindowAutomaton.pathDir q r = (3 : Coord).val := hd 3 (by simp)
    have d3 : WindowAutomaton.pathDir q (r+1) = (0 : Coord).val :=
      (htr _ _ (by omega) (by omega) h41.symm).trans d0
    have v1 := stepB q (r+4) (by omega) 0 d0 v0 (w := 1) (by decide)
    have v2 := stepB q (r+3) (by omega) 1 d1 v1 (w := 3) (by decide)
    have v3 := stepB q (r+2) (by omega) 2 d2 v2 (w := 7) (by decide)
    have v4 := stepB q (r+1) (by omega) 0 d3 v3 rfl
    have v5 := stepB q r (by omega) 3 d4 v4 rfl
    exact quad_rev q hA' cok7r cok6' r hr v0 v1 v2 v3 v4 v5 (by simpa only [ha] using a4)
      (by simpa only [ha] using a3) (by simpa only [ha] using a2) (by simpa only [ha] using a1)
  · -- shape 01234
    rcases hC with hC | hC
    · obtain ⟨q, v0, hd, ha, -⟩ := norm p r (by omega) [r, r+1, r+2, r+3, r+4]
        (nodup5 n01 n02 (Ne.symm h30) (Ne.symm h40) n12 n13 (Ne.symm h41) n23 n24 n34)
        (hl5 _ (by intro j hj; simp at hj; omega))
      have d0 : WindowAutomaton.pathDir q r = (0 : Coord).val := hd 0 (by simp)
      have d1 : WindowAutomaton.pathDir q (r+1) = (1 : Coord).val := hd 1 (by simp)
      have d2 : WindowAutomaton.pathDir q (r+2) = (2 : Coord).val := hd 2 (by simp)
      have d3 : WindowAutomaton.pathDir q (r+3) = (3 : Coord).val := hd 3 (by simp)
      have d4 : WindowAutomaton.pathDir q (r+4) = (4 : Coord).val := hd 4 (by simp)
      have v1 := stepF q r (by omega) 0 d0 v0 (w := 1) (by decide)
      have v2 := stepF q (r+1) (by omega) 1 d1 v1 (w := 3) (by decide)
      have v3 := stepF q (r+2) (by omega) 2 d2 v2 (w := 7) (by decide)
      have v4 := stepF q (r+3) (by omega) 3 d3 v3 rfl
      have v5 := stepF q (r+4) (by omega) 4 d4 v4 rfl
      exact quad_fwd q hC cok7d cok15b' r hr v0 v1 v2 v3 v4 v5 (by simpa only [ha] using a1)
        (by simpa only [ha] using a2) (by simpa only [ha] using a3) (by simpa only [ha] using a4)
    · obtain ⟨q, v0, hd, ha, -⟩ := norm p (r+5) (by omega) [r+4, r+3, r+2, r+1, r]
        (nodup5 (Ne.symm n34) (Ne.symm n24) h41 h40 (Ne.symm n23) (Ne.symm n13) h30
          (Ne.symm n12) (Ne.symm n02) (Ne.symm n01))
        (hl5 _ (by intro j hj; simp at hj; omega))
      have d0 : WindowAutomaton.pathDir q (r+4) = (0 : Coord).val := hd 0 (by simp)
      have d1 : WindowAutomaton.pathDir q (r+3) = (1 : Coord).val := hd 1 (by simp)
      have d2 : WindowAutomaton.pathDir q (r+2) = (2 : Coord).val := hd 2 (by simp)
      have d3 : WindowAutomaton.pathDir q (r+1) = (3 : Coord).val := hd 3 (by simp)
      have d4 : WindowAutomaton.pathDir q r = (4 : Coord).val := hd 4 (by simp)
      have v1 := stepB q (r+4) (by omega) 0 d0 v0 (w := 1) (by decide)
      have v2 := stepB q (r+3) (by omega) 1 d1 v1 (w := 3) (by decide)
      have v3 := stepB q (r+2) (by omega) 2 d2 v2 (w := 7) (by decide)
      have v4 := stepB q (r+1) (by omega) 3 d3 v3 rfl
      have v5 := stepB q r (by omega) 4 d4 v4 rfl
      exact quad_rev q hC cok7d cok15b' r hr v0 v1 v2 v3 v4 v5 (by simpa only [ha] using a4)
        (by simpa only [ha] using a3) (by simpa only [ha] using a2) (by simpa only [ha] using a1)

end

end WinShape
