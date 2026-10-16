import DfsDecide

/- Sound rules for reusing completed searches. The cache and the producer are
untrusted: every reuse must provide a checked equality or containment proof. -/
namespace Snake9.Dfs

def NoExtension (head ban need : Nat) : Prop :=
  ∀ xs, ValidExt head ban xs → xs.length < need

theorem ValidExt.change_ban {head ban : Nat} {xs : List Nat}
    (v : ValidExt head ban xs) : ∀ ban',
    (∀ x ∈ xs, ban'.testBit x = false) → ValidExt head ban' xs := by
  induction v with
  | nil h ban => intro ban' _; exact ValidExt.nil h ban'
  | cons h ban x xs k hk hh hx hf rest ih =>
    intro ban' hall
    apply ValidExt.cons h ban' x xs k hk hh hx (hall x (by simp))
    apply ih
    intro y hy
    rw [Nat.testBit_or, hall y (by simp [hy])]
    have hc := testBit_or_right (rest.not_banned y hy)
    rw [hc]; rfl

theorem NoExtension.mono {head ban ban' need need' : Nat}
    (h : NoExtension head ban need)
    (hmask : ban &&& ban' = ban) (hn : need ≤ need') :
    NoExtension head ban' need' := by
  intro xs v
  have w : ValidExt head ban xs := v.change_ban ban (by
    intro x hx
    have hb := v.not_banned x hx
    have he := congrArg (fun b : Nat => b.testBit x) hmask
    dsimp only at he
    rw [Nat.testBit_and, hb, Bool.and_false] at he
    exact he.symm)
  exact Nat.lt_of_lt_of_le (h xs w) hn

theorem noExtension_of_search2 {head ban need : Nat}
    (hb : ban.testBit head = true) (hs : search2 head ban need = false) :
    NoExtension head ban need := search2_sound need head ban hb hs

theorem noExtension_of_bound2 {head ban need : Nat}
    (hb : ban.testBit head = true) (hbound : bound2 head ban < need) :
    NoExtension head ban need := by
  intro xs v
  exact Nat.lt_of_le_of_lt (bound2_sound v hb) hbound

theorem noExtension_of_children (head ban need : Nat)
    (h : ∀ k, k < 9 → ban.testBit (head ^^^ 2 ^ k) = true ∨
      NoExtension (head ^^^ 2 ^ k) (ban ||| cnMask head) need) :
    NoExtension head ban (need + 1) := by
  intro xs v
  cases v with
  | nil => simp
  | cons _ _ x xs k hk hh hx hf rest =>
    rcases h k hk with hb | hc
    · rw [← hx, hf] at hb; contradiction
    · rw [← hx] at hc
      have := hc xs rest
      simp only [List.length_cons]
      omega

/-- All vertices outside a supplied closed reachable region can be banned.
This allows searches with different inaccessible regions to share a certificate. -/
theorem noExtension_of_region {head ban R need : Nat}
    (hclosed : expand R &&& freeOf ban = R)
    (hstart : (expand (2 ^ head) &&& freeOf ban) &&& R =
      expand (2 ^ head) &&& freeOf ban)
    (h : NoExtension head (freeOf R) need) : NoExtension head ban need := by
  intro xs v
  have hR : ∀ x ∈ xs, R.testBit x = true := by
    apply v.in_region hclosed ?_ (Or.inl rfl) (fun _ h => h)
    intro z hz
    have he := congrArg (fun b : Nat => b.testBit z.val) hstart
    dsimp only at he
    rw [Nat.testBit_and, hz, Bool.true_and] at he
    exact he
  apply h xs
  apply v.change_ban
  intro x hx
  rw [freeOf_testBit R ⟨x, v.lt x hx⟩, hR x hx]
  rfl

theorem no192_from_noExtension (pre : Array Nat) (K : Nat)
    (hK1 : 1 ≤ K) (hK : K ≤ 193)
    (hs : NoExtension pre[K - 1]! (banFrom (fun i => pre[i]!) (K - 1)) (193 - K)) :
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
  have hvalid := tail_valid p (192 - (K - 1)) (K - 1) (by omega)
  rw [hban, hhead] at hvalid
  have := hs _ hvalid
  rw [tailList_length] at this
  omega

#print axioms ValidExt.change_ban
#print axioms NoExtension.mono
#print axioms noExtension_of_region
#print axioms no192_from_noExtension
end Snake9.Dfs
