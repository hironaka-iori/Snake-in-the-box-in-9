import DfsCertificate
import DfsParity

/- Version 2 of the kernel-checked regrowth search: same search, stronger verified bound.

`bound2` is the minimum of two bounds on the number of new vertices of any extension,
both evaluated on the closed reachable region R of `DfsCertificate`:

* parity: an extension alternates between the two parity classes of the cube;
* leaf peeling: remove all vertices of R (never the head) that have at most one
  neighbour in R ∪ {head}, repeat, and count the rounds; a path that enters a vertex
  with at most one neighbour in the current set must end there, so
  `peelB S = peelB (S \ leaves S) + 1` and `peelB S = |S \ {head}|` when no leaves remain.

Compared with the reachable count used in version 1, this cuts the search on the bank
by a factor of 5 to 7 at 152 and 144 fixed vertices. -/
namespace Snake9.Dfs

set_option maxRecDepth 100000
set_option exponentiation.threshold 600

/-! ### Set difference, parity masks, neighbour counting -/

def sdiff (S X : Nat) : Nat := S ^^^ (S &&& X)

theorem sdiff_testBit (S X y : Nat) : (sdiff S X).testBit y = (S.testBit y && !X.testBit y) := by
  unfold sdiff; rw [Nat.testBit_xor, Nat.testBit_and]
  cases S.testBit y <;> cases X.testBit y <;> rfl

def parMask (b : Bool) : Nat := if b then 7877703466965951741784356862959128443265788382021580589009765834561689170293574700951863729220303088751879007905492507289381878411509378061636115163081110 else 5530104462976645357789668135246717684213577438570812788713795609160074859779972275850010568946600338938152850280993543564372004400437191884797533843002985

theorem parMask_testBit : ∀ b : Bool, ∀ y : Fin 512,
    (parMask b).testBit y.val = (bitParity y.val == b) := by decide

/-- First component: vertices with a neighbour in S (via coordinates < n);
second component: vertices with two such neighbours. -/
def onesTwos (S : Nat) (n : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (0, 0)
    (fun k acc => (acc.1 ||| xorShift S k, acc.2 ||| (acc.1 &&& xorShift S k))) n

theorem onesTwos_succ (S n : Nat) : onesTwos S (n + 1) =
    ((onesTwos S n).1 ||| xorShift S n, (onesTwos S n).2 ||| ((onesTwos S n).1 &&& xorShift S n)) := rfl

theorem onesTwos_spec (S : Nat) (y : Fin 512) : ∀ n, n ≤ 9 →
    ((onesTwos S n).1.testBit y.val = true ↔ ∃ k, k < n ∧ S.testBit (y.val ^^^ 2 ^ k) = true) ∧
    ((onesTwos S n).2.testBit y.val = false → ∀ k1 k2, k1 < n → k2 < n →
      S.testBit (y.val ^^^ 2 ^ k1) = true → S.testBit (y.val ^^^ 2 ^ k2) = true → k1 = k2) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · have e : (onesTwos S 0).1 = 0 := rfl
      rw [e, Nat.zero_testBit]
      constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨k, hk, _⟩; omega
    · intro _ k1 k2 h1; omega
  | succ n ih =>
    intro hn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hx := xorShift_testBit S ⟨n, by omega⟩ y
    simp only at hx
    rw [onesTwos_succ]
    refine ⟨?_, ?_⟩
    · simp only [Nat.testBit_or, Bool.or_eq_true, ih1, hx]
      constructor
      · rintro (⟨k, hk, h⟩ | h)
        · exact ⟨k, by omega, h⟩
        · exact ⟨n, by omega, h⟩
      · rintro ⟨k, hk, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact Or.inl ⟨k, hk, h⟩
        · exact Or.inr h
    · intro h2 k1 k2 hk1 hk2 hb1 hb2
      simp only [Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h2
      obtain ⟨h2a, h2b⟩ := h2
      rw [hx] at h2b
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk1 with hk1 | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk2 with hk2 | rfl
      · exact ih2 h2a k1 k2 hk1 hk2 hb1 hb2
      · rcases h2b with h | h
        · have := (ih1).mpr ⟨k1, hk1, hb1⟩; rw [this] at h; exact absurd h (by decide)
        · rw [hb2] at h; exact absurd h (by decide)
      · rcases h2b with h | h
        · have := (ih1).mpr ⟨k2, hk2, hb2⟩; rw [this] at h; exact absurd h (by decide)
        · rw [hb1] at h; exact absurd h (by decide)
      · rfl

/-- Vertices of S other than `h` with at most one neighbour in S. -/
def leaves (S h : Nat) : Nat := sdiff (sdiff S (onesTwos S 9).2) (2 ^ h)

/-- Leaf-peeling bound on the number of path vertices other than `h` inside S. -/
def peelB (h : Nat) (S : Nat) (fuel : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => kcount (sdiff S (2 ^ h)) 512)
    (fun _ rec S => if leaves S h == 0 then kcount (sdiff S (2 ^ h)) 512
      else rec (sdiff S (leaves S h)) + 1) fuel S

theorem peelB_zero (h S : Nat) : peelB h S 0 = kcount (sdiff S (2 ^ h)) 512 := rfl
theorem peelB_succ (h S f : Nat) : peelB h S (f + 1) =
    if leaves S h == 0 then kcount (sdiff S (2 ^ h)) 512
    else peelB h (sdiff S (leaves S h)) f + 1 := rfl

/-! ### Walks -/

inductive Walk : Nat → List Nat → Prop
  | nil (u : Nat) : Walk u []
  | cons (u x : Nat) (xs : List Nat) (k : Nat) (hk : k < 9) (hx : x = u ^^^ 2 ^ k)
      (rest : Walk x xs) : Walk u (x :: xs)

def lastOf (u : Nat) (l : List Nat) : Nat := (u :: l).getLast (List.cons_ne_nil _ _)

theorem lastOf_mem (u : Nat) (l : List Nat) : lastOf u l ∈ u :: l := List.getLast_mem _

theorem Walk.append : ∀ (l1 l2 : List Nat) (u : Nat), Walk u (l1 ++ l2) →
    Walk u l1 ∧ Walk (lastOf u l1) l2
  | [], l2, u, w => ⟨Walk.nil u, by simpa [lastOf] using w⟩
  | a :: l1, l2, u, w => by
    cases w with
    | cons _ _ _ k hk hx rest =>
      obtain ⟨w1, w2⟩ := Walk.append l1 l2 a rest
      refine ⟨Walk.cons u a l1 k hk hx w1, ?_⟩
      have : lastOf u (a :: l1) = lastOf a l1 := by
        simp [lastOf, List.getLast_cons]
      rw [this]; exact w2

theorem ValidExt.walk {h ban : Nat} {xs : List Nat} (v : ValidExt h ban xs) : Walk h xs := by
  induction v with
  | nil => exact Walk.nil _
  | cons h ban x xs k hk hh hx _ _ ih => exact Walk.cons h x xs k hk hx ih

theorem nodup_append_ne {A B : List Nat} (hnd : (A ++ B).Nodup) {a b : Nat}
    (ha : a ∈ A) (hb : b ∈ B) : a ≠ b :=
  (List.pairwise_append.mp hnd).2.2 a ha b hb

theorem length_le_kcount_sdiff (S h : Nat) (xs : List Nat) (hnd : (h :: xs).Nodup)
    (hlt : ∀ x ∈ xs, x < 512) (hin : ∀ x ∈ xs, S.testBit x = true) :
    xs.length ≤ kcount (sdiff S (2 ^ h)) 512 := by
  have hnd' := (List.nodup_cons.mp hnd)
  apply length_le_kcount 512 _ xs hnd'.2
  intro y hy
  refine ⟨hlt y hy, ?_⟩
  rw [sdiff_testBit, hin y hy, Nat.testBit_two_pow]
  have : h ≠ y := fun e => hnd'.1 (e ▸ hy)
  simp [this]

/-- A walk into a vertex with at most one neighbour in S cannot continue inside S. -/
theorem leaf_ends {S h u y z : Nat} (hy512 : y < 512) (hu : S.testBit u = true)
    (hz : S.testBit z = true) (hleaf : (leaves S h).testBit y = true) (hne : u ≠ z)
    (k1 : Nat) (hk1 : k1 < 9) (hy : y = u ^^^ 2 ^ k1)
    (k2 : Nat) (hk2 : k2 < 9) (hzy : z = y ^^^ 2 ^ k2) : False := by
  have hu' : u = y ^^^ 2 ^ k1 := by rw [hy, xor_xor_cancel]
  unfold leaves at hleaf
  rw [sdiff_testBit, sdiff_testBit] at hleaf
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hleaf
  have := (onesTwos_spec S ⟨y, hy512⟩ 9 (Nat.le_refl 9)).2 hleaf.1.2 k1 k2 hk1 hk2
    (by rw [← hu']; exact hu) (by rw [← hzy]; exact hz)
  subst this
  exact hne (hu'.trans hzy.symm)

theorem split_prefix (P : Nat → Bool) : ∀ xs : List Nat, ∃ pre,
    (∀ x ∈ pre, P x = true) ∧ (xs = pre ∨ ∃ y ys, xs = pre ++ y :: ys ∧ P y = false)
  | [] => ⟨[], by simp, Or.inl rfl⟩
  | x :: xs => by
    cases hx : P x with
    | false => exact ⟨[], by simp, Or.inr ⟨x, xs, by simp, hx⟩⟩
    | true =>
      obtain ⟨pre, hpre, hsplit⟩ := split_prefix P xs
      refine ⟨x :: pre, ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact hpre z hz
      · rcases hsplit with e | ⟨y, ys, e, hy⟩
        · exact Or.inl (by rw [e])
        · exact Or.inr ⟨y, ys, by rw [e]; simp, hy⟩

theorem peel_sound (h : Nat) (_hh : h < 512) : ∀ fuel S (xs : List Nat), Walk h xs →
    (h :: xs).Nodup → (∀ x ∈ xs, x < 512) → S.testBit h = true →
    (∀ x ∈ xs, S.testBit x = true) → xs.length ≤ peelB h S fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro S xs _ hnd hlt _ hin
    rw [peelB_zero]; exact length_le_kcount_sdiff S h xs hnd hlt hin
  | succ f ih =>
    intro S xs w hnd hlt hS hin
    rw [peelB_succ]
    split
    · exact length_le_kcount_sdiff S h xs hnd hlt hin
    · have hS' : (sdiff S (leaves S h)).testBit h = true := by
        rw [sdiff_testBit, hS]
        unfold leaves; rw [sdiff_testBit, Nat.testBit_two_pow]; simp
      obtain ⟨pre, hpre, hsplit⟩ := split_prefix (fun x => (sdiff S (leaves S h)).testBit x) xs
      rcases hsplit with e | ⟨y, ys, e, hy⟩
      · rw [e] at w hnd hlt
        have := ih (sdiff S (leaves S h)) pre w hnd hlt hS' hpre
        rw [e]; omega
      · subst e
        obtain ⟨wpre, wpost⟩ := Walk.append pre (y :: ys) h w
        have hyS : S.testBit y = true := hin y (by simp)
        have hyL : (leaves S h).testBit y = true := by
          have : (sdiff S (leaves S h)).testBit y = false := hy
          rw [sdiff_testBit, hyS] at this
          cases e : (leaves S h).testBit y
          · rw [e] at this; exact absurd this (by decide)
          · rfl
        cases ys with
        | cons z zs =>
          exfalso
          cases wpost with
          | cons _ _ _ k1 hk1 hy1 rest =>
            cases rest with
            | cons _ _ _ k2 hk2 hz2 _ =>
              have hu := lastOf_mem h pre
              have huS : S.testBit (lastOf h pre) = true := by
                rcases List.mem_cons.mp hu with e | e
                · rw [e]; exact hS
                · have := hpre _ e
                  have : (sdiff S (leaves S h)).testBit (lastOf h pre) = true := this
                  rw [sdiff_testBit] at this
                  simp only [Bool.and_eq_true] at this; exact this.1
              have hne : lastOf h pre ≠ z := by
                have hnd2 : ((h :: pre) ++ (y :: z :: zs)).Nodup := by simpa using hnd
                exact nodup_append_ne hnd2 hu (by simp)
              exact leaf_ends (hlt y (by simp)) huS (hin z (by simp)) hyL hne
                k1 hk1 hy1 k2 hk2 hz2
        | nil =>
          have hnd' : (h :: pre).Nodup := by
            have : ((h :: pre) ++ [y]).Nodup := by simpa using hnd
            exact this.sublist (List.sublist_append_left _ _)
          have := ih (sdiff S (leaves S h)) pre wpre hnd' (fun x hx => hlt x (by simp [hx])) hS' hpre
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega

/-! ### Parity alternation -/

theorem ValidExt.parity_counts {h ban : Nat} {xs : List Nat} (v : ValidExt h ban xs) :
    (xs.filter (fun x => bitParity x != bitParity h)).length = (xs.length + 1) / 2 ∧
    (xs.filter (fun x => bitParity x == bitParity h)).length = xs.length / 2 := by
  induction v with
  | nil => simp
  | cons h ban x xs k hk hh hx _ _ ih =>
    have hpx : bitParity x = !bitParity h := by
      rw [hx]; exact bitParity_flip ⟨h, hh⟩ ⟨k, hk⟩
    obtain ⟨ih1, ih2⟩ := ih
    have e1 : xs.filter (fun z => bitParity z != bitParity h) =
        xs.filter (fun z => bitParity z == bitParity x) := by
      apply List.filter_congr; intro z _; rw [hpx]
      cases bitParity z <;> cases bitParity h <;> rfl
    have e2 : xs.filter (fun z => bitParity z == bitParity h) =
        xs.filter (fun z => bitParity z != bitParity x) := by
      apply List.filter_congr; intro z _; rw [hpx]
      cases bitParity z <;> cases bitParity h <;> rfl
    have c1 : (bitParity x != bitParity h) = true := by rw [hpx]; cases bitParity h <;> rfl
    have c2 : (bitParity x == bitParity h) = false := by rw [hpx]; cases bitParity h <;> rfl
    rw [List.filter_cons, List.filter_cons, if_pos c1, if_neg (by simp [c2]), e1, e2]
    simp only [List.length_cons]
    omega

/-! ### The combined bound and the search -/

def bound2 (head ban : Nat) : Nat :=
  let F := freeOf ban
  let R0 := expand (2 ^ head) &&& F
  match reach F 512 R0 with
  | some R =>
    if (R0 &&& R) == R0 then
      let a := kcount (R &&& parMask (!bitParity head)) 512
      let b := kcount (R &&& parMask (bitParity head)) 512
      min (min a (b + 1) + min b a) (peelB head (R ||| 2 ^ head) 512)
    else 512
  | none => 512

theorem bound2_sound {head ban : Nat} {xs : List Nat} (v : ValidExt head ban xs)
    (hban : ban.testBit head = true) : xs.length ≤ bound2 head ban := by
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
  unfold bound2
  simp only
  split
  · rename_i R hR
    split
    · rename_i hcheck
      have hclosed := reach_closed 512 _ R hR
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
            kcount (R &&& parMask (!bitParity head)) 512 := by
          apply length_le_kcount 512 _ _ (hnd.sublist List.filter_sublist)
          intro y hy
          obtain ⟨hy, hp⟩ := List.mem_filter.mp hy
          refine ⟨hlt y hy, ?_⟩
          rw [Nat.testBit_and, hR y hy, parMask_testBit _ ⟨y, hlt y hy⟩]
          simp only at hp ⊢
          revert hp; cases bitParity y <;> cases bitParity head <;> decide
        have hb : ((x0 :: xs0).filter (fun x => bitParity x == bitParity head)).length ≤
            kcount (R &&& parMask (bitParity head)) 512 := by
          apply length_le_kcount 512 _ _ (hnd.sublist List.filter_sublist)
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
        apply peel_sound head hh 512 _ _ v.walk
        · exact List.nodup_cons.mpr ⟨hnotin, hnd⟩
        · exact hlt
        · rw [Nat.testBit_or, Nat.testBit_two_pow]; simp
        · intro y hy; rw [Nat.testBit_or, hR y hy]; rfl
    · exact fallback
  · exact fallback

def search2 (head ban need : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun need rec head ban =>
      if bound2 head ban < need + 1 then false
      else anyBelow (fun k => !(ban.testBit (head ^^^ 2 ^ k)) &&
        rec (head ^^^ 2 ^ k) (ban ||| cnMask head)) 9) need head ban

theorem search2_zero (head ban : Nat) : search2 head ban 0 = true := rfl
theorem search2_succ (head ban need : Nat) : search2 head ban (need + 1) =
    if bound2 head ban < need + 1 then false
    else anyBelow (fun k => !(ban.testBit (head ^^^ 2 ^ k)) &&
      search2 (head ^^^ 2 ^ k) (ban ||| cnMask head) need) 9 := rfl

theorem search2_sound : ∀ need head ban, ban.testBit head = true →
    search2 head ban need = false → ∀ xs, ValidExt head ban xs → xs.length < need := by
  intro need
  induction need with
  | zero => intro head ban _ h; rw [search2_zero] at h; exact absurd h (by simp)
  | succ need ih =>
    intro head ban hban h xs v
    rw [search2_succ] at h
    split at h
    · have := bound2_sound v hban
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

theorem search2_of_children (head ban need : Nat)
    (h : ∀ k, k < 9 → (ban.testBit (head ^^^ 2 ^ k) = true ∨
      search2 (head ^^^ 2 ^ k) (ban ||| cnMask head) need = false)) :
    search2 head ban (need + 1) = false := by
  rw [search2_succ]
  split
  · rfl
  · have : ∀ n, n ≤ 9 → anyBelow (fun k => !(ban.testBit (head ^^^ 2 ^ k)) &&
        search2 (head ^^^ 2 ^ k) (ban ||| cnMask head) need) n = false := by
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
theorem no192_from_prefix2 (pre : Array Nat) (K : Nat) (hK2 : 2 ≤ K) (hK : K ≤ 193)
    (hs : search2 pre[K - 1]! (banFrom (fun i => pre[i]!) (K - 1)) (193 - K) = false) :
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
  have := search2_sound (193 - K) _ _ hin hs _ hvalid
  rw [tailList_length] at this
  omega

#print axioms peel_sound
#print axioms bound2_sound
#print axioms search2_sound
#print axioms search2_of_children
#print axioms no192_from_prefix2
end Snake9.Dfs
