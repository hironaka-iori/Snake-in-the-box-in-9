import LocalWindowTags

/-!
# Checking the clause tags of a core in parts

`Tags.checkAll M cs w b tags raw` (`LocalWindowTags`) is one Bool: every counter passes
`ctrOK`, and every clause of `raw` passes `ckClause` with its tag.  A certificate module checks
it by one `decide +kernel`, and the kernel keeps all its work for one declaration in caches
that are only freed at its end.  On the radius-4 H9 windows of the seven-centre bound
(`milestones/25-k7-234`) that is too much for one declaration:

* the endpoint counter of an H9 window has about 350 literals, and `ctrOK` checks their order
  with `pw`, which compares every pair: about 60,000 comparisons, 14 s and 1.2 GB of kernel
  caches;
* the clause checks need about 0.2 MB of kernel caches per literal, and H9 cores have up to
  about 18,000 literals.

This module lets a certificate check the same `checkAll` in several declarations:

* `checkAll_of_parts`: the counters and the clauses separately;
* `ckAll_append`: the clauses in consecutive parts (`tags = tags₁ ++ tags₂`,
  `raw = raw₁ ++ raw₂`), each part one declaration with its own caches;
* `ctrOKL`: `ctrOK` with the order of the endpoint counter checked on adjacent entries only
  (`pwL`, linear), and `ctrOK_of_ctrOKL`.

Nothing here changes what is proved: `check : checkAll … = true` is still the hypothesis of
`Tags.sound`, and the certificate modules keep their names and statements.
-/

namespace Snake9.LocalWindow.Tags

open Snake9.LocalWindow

/-- Strictly increasing, checked on adjacent entries. -/
def pwL : List Nat → Bool
  | a :: b :: t => decide (a < b) && pwL (b :: t)
  | _ => true

theorem pw_of_pwL : ∀ {l : List Nat}, pwL l = true → pw l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    simp only [pwL, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih : pw (b :: t) = true := pw_of_pwL h.2
    have hp := pw_pairwise ih
    simp only [pw, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_cons] at ih ⊢
    refine ⟨?_, ih⟩
    intro x hx
    rcases hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons hp hx)

/-- `ctrOK` with `pwL` in place of `pw` for the endpoint counter. -/
def ctrOKL (M : MT) (cens : List Centre) (ct : Ctr) : Bool :=
  ct.lits.all (baseOK M) &&
  match ct.kind with
  | .ends => ct.k == 2 && ct.lits.all (posE M) && pwL (ct.lits.map (vl M))
  | .hi ci => decide (ci < cens.length) && ct.lits.all (negP M) &&
      ct.k == (cens.getD ci dfltCentre).hi && ct.lits.map (vl M) == corners (cens.getD ci dfltCentre)
  | .lo ci => decide (ci < cens.length) && ct.lits.all (posP M) &&
      ct.k + (cens.getD ci dfltCentre).lo ==
        (freePairs (cens.getD ci dfltCentre).d₁ (cens.getD ci dfltCentre).d₂).length &&
      ct.lits.map (vl M) == corners (cens.getD ci dfltCentre)

theorem ctrOK_of_ctrOKL {M : MT} {cens : List Centre} {ct : Ctr} (h : ctrOKL M cens ct = true) :
    ctrOK M cens ct = true := by
  unfold ctrOKL at h
  unfold ctrOK
  cases hk : ct.kind with
  | ends =>
    simp only [hk, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ⟨h.2.1, pw_of_pwL h.2.2⟩⟩
  | hi ci => simpa only [hk] using h
  | lo ci => simpa only [hk] using h

theorem all_ctrOK_of_ctrOKL {M : MT} {cens : List Centre} {cs : List Ctr}
    (h : cs.all (ctrOKL M cens) = true) : cs.all (ctrOK M cens) = true := by
  rw [List.all_eq_true] at h ⊢
  exact fun ct hct => ctrOK_of_ctrOKL (h ct hct)

/-- Two consecutive parts of the clauses, checked separately. -/
theorem ckAll_append (M : MT) (cs : List Ctr) (w : List Nat) :
    ∀ (t₁ : List Tag) (r₁ : List (List Nat)) (t₂ : List Tag) (r₂ : List (List Nat)),
      ckAll M cs w t₁ r₁ = true → ckAll M cs w t₂ r₂ = true →
      ckAll M cs w (t₁ ++ t₂) (r₁ ++ r₂) = true
  | [], [], _, _, _, h₂ => h₂
  | t :: ts, cl :: cls, t₂, r₂, h₁, h₂ => by
    simp only [ckAll, Bool.and_eq_true, List.cons_append] at h₁ ⊢
    exact ⟨h₁.1, ckAll_append M cs w ts cls t₂ r₂ h₁.2 h₂⟩
  | [], _ :: _, _, _, h₁, _ => by simp [ckAll] at h₁
  | _ :: _, [], _, _, h₁, _ => by simp [ckAll] at h₁

/-- `checkAll` from the counters (checked by `ctrOKL`) and the clauses. -/
theorem checkAll_of_parts {M : MT} {cs : List Ctr} {w : List Nat} {b : List (Nat × Nat)}
    {tags : List Tag} {raw : List (List Nat)}
    (hc : cs.all (ctrOKL M (centresK w b)) = true) (ha : ckAll M cs w tags raw = true) :
    checkAll M cs w b tags raw = true := by
  simp only [checkAll, Bool.and_eq_true]
  exact ⟨all_ctrOK_of_ctrOKL hc, ha⟩

end Snake9.LocalWindow.Tags
