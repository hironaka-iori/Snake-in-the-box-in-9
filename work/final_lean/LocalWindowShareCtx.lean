import LocalWindowShareBridge
import LocalWindowTagsSW

/-!
# Context share certificates: a share cap on a trailing range of centres

Milestone 35 (`milestones/35-231-lean/DESIGN.md`, items a and b).  A *context share threshold*
(`milestones/28-combined-identities/share7.py`, ctx 7 / ctx 8) bounds the M = 12 share sum of
the **trailing five centres** of a longer window (7 or 8 directions) from below.  The local
window model is the one of the 5-window share certificates, except that the share cap is put on
the centres `(centresOf window bounds).drop k` only (all centres keep their count bounds):

* `RefutedShareFrom window bounds M cap k`: no normalized snake vertex set around the window
  satisfies the window axioms `Axioms` (all centres, with their bounds) and has share sum at most
  `cap` on the centres from index `k` on.  For `k = 0` it is `RefutedShare`
  (`refutedShareFrom_zero_iff`).
* **Clause soundness** (`TagsSW.checkAllSC`, `TagsSW.soundSC`): the checker of
  `LocalWindowTagsSW` with one change: the totalizers are checked against the centre list
  `(centresK w b).drop k` (`TagsSW.totOK` is reused unchanged; only its `.cap` kind reads the
  centre list), while the counters are checked against all centres.  All clause-family lemmas
  of `LocalWindowTagsSW` are reused unchanged: they are stated for an arbitrary centre list.
  `TagsSW.refutedShareFrom_of_sat` turns the `sat` theorem and the LRAT replay of the core into
  `RefutedShareFrom`.
* **Bridge** (`refuted_share_from_bridge`, `refuted_share_from_dir`): on every snake window mapped
  onto the canonical window (direction relabelling by a duplicate-free coordinate list, as
  `refuted_share_dir`) whose counts lie in `bounds`, the share sum of the snake vertices
  `r + k + 1 .. r + bounds.length` is at least `cap + 1`.  The bounds are an arbitrary list, so a
  free count (`(1, 21)`, ctx 8) is allowed; the oriented use (no reversal) is the caller's.
-/

namespace Snake9.LocalWindow

/-- What a context share certificate proves: the window axioms on all centres together with a
cap on the share sum of the centres from index `k` on are contradictory. -/
def RefutedShareFrom (window : List Nat) (bounds : List (Nat × Nat)) (M cap k : Nat) : Prop :=
  ∀ S E : Nat → Bool, Axioms S E window (centresOf window bounds) →
    shareSum M S ((centresOf window bounds).drop k) ≤ cap → False

theorem refutedShareFrom_zero_iff {window : List Nat} {bounds : List (Nat × Nat)} {M cap : Nat} :
    RefutedShareFrom window bounds M cap 0 ↔ RefutedShare window bounds M cap := by
  constructor
  · intro h S E ax
    exact h S E ax.toAxioms (by simpa using ax.share_le)
  · intro h S E ax hs
    exact h S E ⟨ax, by simpa using hs⟩

/-- A refuted cap refutes every smaller cap. -/
theorem RefutedShareFrom.anti {window : List Nat} {bounds : List (Nat × Nat)} {M cap cap' k : Nat}
    (h : RefutedShareFrom window bounds M cap k) (hc : cap' ≤ cap) :
    RefutedShareFrom window bounds M cap' k :=
  fun S E ax hs => h S E ax (Nat.le_trans hs hc)

end Snake9.LocalWindow

namespace Snake9.LocalWindow.TagsSW

open Snake9.LocalWindow
open Snake9.LocalWindow.Tags (MT Kind Ctr Tag dfltCtr dfltCentre centresK centresK_eq MS TotKind Tot dfltTot TagS)
open Snake9.LocalWindow.TagsW

noncomputable section

/-- The context share checker: counters against all centres, totalizers (hence the cap
totalizer) against the centres from index `k` on, one tag per core clause. -/
def checkAllSC (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (b : List (Nat × Nat)) (k cap : Nat) (tags : List TagS) (raw : List (List Nat)) : Bool :=
  allK (ctrOKK M (centresK w b)) cs && tots.all (totOK M X w ((centresK w b).drop k)) &&
    ckAllS M X Mr cs tots w cap tags raw

section Ctx

variable {S E : Nat → Bool} {M : Nat → MT} {X : Nat → MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
  {w : List Nat}

/-- `sound_clauseS` with two centre lists: `cens` for the counters and the window axioms,
`cens'` for the totalizers and the cap. -/
theorem sound_clauseSC {cens cens' : List Centre} {cap : Nat} {t : TagS} {cl : List Nat}
    (h : ckClauseS M X Mr cs tots w cap t cl = true)
    (hcs : cs.all (ctrOK M cens) = true) (ht : tots.all (totOK M X w cens') = true)
    (ax : Axioms S E w cens) (hcap : shareSum Mr S cens' ≤ cap) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  cases t with
  | old t =>
    simp only [ckClauseS, Bool.and_eq_true, ckClauseK_eq] at h
    exact old_clause h.1 (sound_clause h.2 hcs ax)
  | emptyE => exact sound_emptyE h
  | totUp i => exact sound_totUp h ht
  | totDown i => exact sound_totDown h ht
  | shareCl eT dT => exact sound_shareCl h ht ax.window_sel
  | shareCap i => exact sound_shareCap h ht hcap

theorem sound_allSC {cens cens' : List Centre} {cap : Nat} :
    ∀ {tags : List TagS} {raw : List (List Nat)},
    ckAllS M X Mr cs tots w cap tags raw = true →
    cs.all (ctrOK M cens) = true → tots.all (totOK M X w cens') = true →
    Axioms S E w cens → shareSum Mr S cens' ≤ cap →
    ∀ cl ∈ raw, clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true
  | [], [], _, _, _, _, _ => by simp
  | t :: ts, cl :: cls, h, hcs, ht, ax, hc => by
    simp only [ckAllS, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact sound_clauseSC h.1 hcs ht ax hc
    · exact sound_allSC h.2 hcs ht ax hc x hx
  | [], _ :: _, h, _, _, _, _ => by simp [ckAllS] at h
  | _ :: _, [], h, _, _, _, _ => by simp [ckAllS] at h

end Ctx

/-- Main soundness theorem for context share certificates. -/
theorem soundSC (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (b : List (Nat × Nat)) (k cap : Nat) (tags : List TagS) (raw : List (List Nat))
    (h : checkAllSC M X Mr cs tots w b k cap tags raw = true) (S E : Nat → Bool)
    (ax : Axioms S E w (centresOf w b)) (hc : shareSum Mr S ((centresOf w b).drop k) ≤ cap) :
    cnfTrue (tauS S E M X Mr cs tots) (raw.map (·.map decodeLit)) = true := by
  have hk : ctrOKK M (centresK w b) = ctrOK M (centresK w b) := funext (ctrOKK_eq M _)
  simp only [checkAllSC, Bool.and_eq_true, allK_eq, hk] at h
  rw [centresK_eq] at ax hc
  unfold cnfTrue
  rw [List.all_map, List.all_eq_true]
  intro cl hcl
  exact sound_allSC h.2 h.1.1 h.1.2 ax hc cl hcl

/-- `checkAllSC` from the counters, the totalizers and the clauses, checked separately. -/
theorem checkAllSC_of_parts {M : Nat → MT} {X : Nat → MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
    {w : List Nat} {b : List (Nat × Nat)} {k cap : Nat} {tags : List TagS} {raw : List (List Nat)}
    (hc : allK (ctrOKK M (centresK w b)) cs = true)
    (ht : tots.all (totOK M X w ((centresK w b).drop k)) = true)
    (ha : ckAllS M X Mr cs tots w cap tags raw = true) :
    checkAllSC M X Mr cs tots w b k cap tags raw = true := by
  simp only [checkAllSC, Bool.and_eq_true]
  exact ⟨⟨hc, ht⟩, ha⟩

/-- A context share certificate's `sat` theorem and the refutation of its core give
`RefutedShareFrom`. -/
theorem refutedShareFrom_of_sat {window : List Nat} {bounds : List (Nat × Nat)} {Mr cap k : Nat}
    {f : List (List Int)}
    (hsat : ∀ S E : Nat → Bool, Axioms S E window (centresOf window bounds) →
      shareSum Mr S ((centresOf window bounds).drop k) ≤ cap → ∃ τ, cnfTrue τ f = true)
    (hunsat : Unsat f) : RefutedShareFrom window bounds Mr cap k := by
  intro S E ax hc
  obtain ⟨τ, hτ⟩ := hsat S E ax hc
  rw [hunsat τ] at hτ
  exact Bool.false_ne_true hτ

end

end Snake9.LocalWindow.TagsSW

namespace Snake9.LocalWindow
open Snake9

set_option maxHeartbeats 1000000

theorem drop_map_range {α : Type} (f : Nat → α) (n k : Nat) :
    ((List.range n).map f).drop k = (List.range (n - k)).map (fun i => f (k + i)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range]

section Bridge
variable {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)

/-- The share sum of the canonical window's centres from index `k` on is the sum of the snake's
shares at the window's interior vertices `r + k + 1, r + k + 2, …`. -/
theorem shareSum_window_from {W cs : List Nat} {bounds : List (Nat × Nat)} (hc : Canon W cs)
    (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0) (M k : Nat) :
    shareSum M (sel p (amap P (vx p r))) ((centresOf W bounds).drop k) =
      ((List.range (bounds.length - k)).map fun i => coreShare M p (r + k + i + 1)).sum := by
  unfold shareSum centresOf
  rw [drop_map_range, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  show shareLocal M (sel p (amap P (vx p r))) (W.getD (k + i + 1) 0) = coreShare M p (r + k + i + 1)
  rw [frame_window p P r hc hr hP (k + i + 1) (by omega), show r + (k + i + 1) = r + k + i + 1 by omega]
  exact shareLocal_frame p P _ (vx_lt p r) (vx_lt p _) M

/-- A context share certificate with cap `K` forces the share sum of the centres from index `k`
on above `K`, on every window of a snake mapped onto the canonical one by `P` whose counts lie
in `bounds`. -/
theorem refuted_share_from_bridge {W cs : List Nat} {bounds : List (Nat × Nat)} {M K k : Nat}
    (href : RefutedShareFrom W bounds M K k)
    (hc : Canon W cs) (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0)
    (hb : ∀ i, i < bounds.length → (bounds.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (bounds.getD i (0, 21)).2) :
    K + 1 ≤ ((List.range (bounds.length - k)).map fun i => coreShare M p (r + k + i + 1)).sum := by
  apply Nat.succ_le_of_lt
  apply Nat.lt_of_not_le
  intro hle
  exact href _ _ (frame_axioms p P r hc hlen hr hP hb)
    (by rw [shareSum_window_from p P r hc hlen hr hP M k]; exact hle)

end Bridge

/-- A context share certificate keyed by a direction list (as `refuted_share_dir`, with an
arbitrary bounds list): on every snake window relabelled onto `cs` by the duplicate-free
coordinate list `u` whose counts lie in `bounds`, the share sum of the vertices
`r + k + 1 … r + bounds.length` exceeds the cap. -/
theorem refuted_share_from_dir {cs u : List Nat} {bounds : List (Nat × Nat)} {M K k : Nat}
    (h : RefutedShareFrom (winOf cs) bounds M K k)
    {m : Nat} (p : Snake m) (r : Nat) (hlen : bounds.length + 1 = cs.length)
    (hr : r + cs.length ≤ m) (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j, j < cs.length → cs.getD j 0 < u.length ∧ u.getD (cs.getD j 0) 0 = dir p (r + j))
    (hb : ∀ i, i < bounds.length → (bounds.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (bounds.getD i (0, 21)).2) :
    K + 1 ≤ ((List.range (bounds.length - k)).map fun i => coreShare M p (r + k + i + 1)).sum := by
  have hlen9 : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hsp := mkPerm_spec hu hu9 hlen9
  exact refuted_share_from_bridge p (mkPerm u) r h (canon_winOf cs) hlen hr
    (by
      intro j hj
      obtain ⟨h1, h2⟩ := hcs j hj
      rw [← h2]
      exact hsp _ h1) hb

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.refutedShareFrom_zero_iff
#print axioms Snake9.LocalWindow.TagsSW.soundSC
#print axioms Snake9.LocalWindow.TagsSW.refutedShareFrom_of_sat
#print axioms Snake9.LocalWindow.refuted_share_from_bridge
#print axioms Snake9.LocalWindow.refuted_share_from_dir
