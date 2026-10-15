import Snake9

/- A kernel-checkable exhaustive regrowth search with a proof of soundness.

Vertex sets are 512-bit natural numbers (bit v set means v is in the set).  The search
`search head ban need` extends an induced path whose last vertex is `head` and whose
earlier closed neighbourhoods are `ban`.  It prunes with a reachable-region bound: the
region R is computed by unverified bit-parallel iteration, and only its closure property
is checked and used.  `search_sound` shows that a `false` answer excludes every
extension with `need` or more new vertices; `no192_from_prefix` turns this into a
statement about `Snake9.Snake 192`. -/
namespace Snake9.Dfs

set_option maxRecDepth 100000
set_option exponentiation.threshold 600

/-! ### Bit-level primitives -/

/-- Closed neighbourhood of `v` in the nine-cube, as a bit mask. -/
def cnMask (v : Nat) : Nat :=
  (List.range 9).foldl (fun acc k => acc ||| 2 ^ (v ^^^ 2 ^ k)) (2 ^ v)

/-- Vertices below 512 whose coordinate `k` is zero. -/
def lowMask : Nat → Nat
  | 0 => 4469269309980865699858008332735282042493121940197464459241187147907254676691182325600624766055634475896677286062162016951251294270648856648811216335361365
  | 1 => 2681561585988519419914804999641169225495873164118478675544712288744352806014709395360374859633380685538006371637297210170750776562389313989286729801216819
  | 2 => 788694584114270417622001470482696831028197989446611375160209496689515531180796880988345546950994319275884226952146238285514934283055680585084332294475535
  | 3 => 52170458871371973150093482483291230068013096578180518979469110675960171323243373450590950576524916061050707619402669458574917831953099493954994743214335
  | 4 => 204583791292591926691396081575382549208529011407180575518006033900266475884974090617542369930984076593222635430161375266700549045759594884514604711935
  | 5 => 3121748549589153507255220667214744133005063442417264435278786581112765113115492710770662312255297115872319494912905282327171554901817584187867135
  | 6 => 726838724295606890509921801691610055143498307623095356558689689527106077364635040561028680485123622079561121241075102686324128571457535
  | 7 => 39402006196394479212279040100143613804963947181228130472524722419237033863644280909115546629308921431406146628878335
  | 8 => 115792089237316195423570985008687907853269984665640564039457584007913129639935
  | _ => 0

def full : Nat := 2 ^ 512 - 1

/-- Moves every vertex v of S to v xor 2^k. -/
def xorShift (S k : Nat) : Nat :=
  ((S &&& lowMask k) <<< 2 ^ k) ||| ((S >>> 2 ^ k) &&& lowMask k)

/-- S together with all of its neighbours. -/
def expand (S : Nat) : Nat :=
  (List.range 9).foldl (fun acc k => acc ||| xorShift S k) S

/-- Vertices below 512 that are not banned. -/
def freeOf (ban : Nat) : Nat := full ^^^ (ban &&& full)

/- The functions evaluated by the kernel are written with `Nat.rec` directly: structural
recursion compiles through `brecOn`, whose kernel evaluation builds quadratically large
terms.  Their defining equations are recorded as `rfl` lemmas. -/

def reach (F : Nat) (n : Nat) : Nat → Option Nat :=
  Nat.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun _ rec R => if expand R &&& F == R then some R else rec (expand R &&& F)) n

theorem reach_zero (F R : Nat) : reach F 0 R = none := rfl
theorem reach_succ (F n R : Nat) : reach F (n + 1) R =
    if expand R &&& F == R then some R else reach F n (expand R &&& F) := rfl

def countBits (R : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc + (if R.testBit k then 1 else 0)) n

theorem countBits_zero (R : Nat) : countBits R 0 = 0 := rfl
theorem countBits_succ (R n : Nat) :
    countBits R (n + 1) = countBits R n + (if R.testBit n then 1 else 0) := rfl

/-- Number of set bits, by repeatedly clearing one (`R &&& (R - 1)`); the cost is the
number of set bits rather than 512.  Out of fuel it returns the safe value 512. -/
def kcount (R : Nat) (fuel : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun R => if R == 0 then 0 else 512)
    (fun _ rec R => if R == 0 then 0 else rec (R &&& (R - 1)) + 1) fuel R

theorem kcount_zero (R : Nat) : kcount R 0 = if R == 0 then 0 else 512 := rfl
theorem kcount_succ (R f : Nat) :
    kcount R (f + 1) = if R == 0 then 0 else kcount (R &&& (R - 1)) f + 1 := rfl

/-- Upper bound on the number of new vertices of any extension from `head`. -/
def bound (head ban : Nat) : Nat :=
  let F := freeOf ban
  let R0 := expand (2 ^ head) &&& F
  match reach F 512 R0 with
  | some R => if (R0 &&& R) == R0 then kcount R 512 else 512
  | none => 512

def anyBelow (f : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => acc || f k) n

theorem anyBelow_succ (f : Nat → Bool) (n : Nat) : anyBelow f (n + 1) = (anyBelow f n || f n) := rfl

/-- `false` means: no induced extension with at least `need` new vertices exists. -/
def search (head ban need : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun need rec head ban =>
      if bound head ban < need + 1 then false
      else anyBelow (fun k => !(ban.testBit (head ^^^ 2 ^ k)) &&
        rec (head ^^^ 2 ^ k) (ban ||| cnMask head)) 9) need head ban

theorem search_zero (head ban : Nat) : search head ban 0 = true := rfl
theorem search_succ (head ban need : Nat) : search head ban (need + 1) =
    if bound head ban < need + 1 then false
    else anyBelow (fun k => !(ban.testBit (head ^^^ 2 ^ k)) &&
      search (head ^^^ 2 ^ k) (ban ||| cnMask head) need) 9 := rfl

/-- Ban mask of the first `n` vertices of a vertex sequence. -/
def banFrom (f : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc ||| cnMask (f i)) 0

/-! ### Extensions -/

/-- `xs` is a valid continuation of a path with head `h` and ban mask `ban`. -/
inductive ValidExt : Nat → Nat → List Nat → Prop
  | nil (h ban : Nat) : ValidExt h ban []
  | cons (h ban x : Nat) (xs : List Nat) (k : Nat) (hk : k < 9) (hh : h < 512)
      (hx : x = h ^^^ 2 ^ k) (hfree : ban.testBit x = false)
      (rest : ValidExt x (ban ||| cnMask h) xs) : ValidExt h ban (x :: xs)

/-! ### Finite facts, checked by the kernel -/

theorem xor_lt : ∀ h : Fin 512, ∀ k : Fin 9, h.val ^^^ 2 ^ k.val < 512 := by decide

theorem lowMask_testBit : ∀ k : Fin 9, ∀ y : Fin 512,
    (lowMask k.val).testBit y.val = !y.val.testBit k.val := by decide

theorem bit_facts : ∀ k : Fin 9, ∀ y : Fin 512,
    (y.val.testBit k.val = true → 2 ^ k.val ≤ y.val ∧
        y.val ^^^ 2 ^ k.val = y.val - 2 ^ k.val) ∧
    (y.val.testBit k.val = false → (2 ^ k.val ≤ y.val → (y.val - 2 ^ k.val).testBit k.val = true) ∧
        y.val ^^^ 2 ^ k.val = 2 ^ k.val + y.val) := by decide

theorem countBits_full : countBits full 512 = 512 := by decide

/-! ### Bit lemmas -/

theorem testBit_foldl_or (g : Nat → Nat) (l : List Nat) (a y : Nat) :
    (l.foldl (fun acc k => acc ||| g k) a).testBit y =
      (a.testBit y || l.any (fun k => (g k).testBit y)) := by
  induction l generalizing a with
  | nil => simp
  | cons k l ih => simp [List.foldl, ih, Nat.testBit_or, Bool.or_assoc]

theorem cnMask_self (v : Nat) : (cnMask v).testBit v = true := by
  unfold cnMask; rw [testBit_foldl_or]; simp [Nat.testBit_two_pow]

theorem cnMask_nbr (v k : Nat) (hk : k < 9) : (cnMask v).testBit (v ^^^ 2 ^ k) = true := by
  unfold cnMask; rw [testBit_foldl_or]
  simp only [Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨k, List.mem_range.mpr hk, by simp [Nat.testBit_two_pow]⟩

theorem cnMask_testBit_true {v y : Nat} (h : (cnMask v).testBit y = true) :
    y = v ∨ ∃ k, k < 9 ∧ y = v ^^^ 2 ^ k := by
  unfold cnMask at h; rw [testBit_foldl_or] at h
  simp only [Bool.or_eq_true, List.any_eq_true, Nat.testBit_two_pow, decide_eq_true_eq,
    List.mem_range] at h
  rcases h with h | ⟨k, hk, he⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨k, hk, he.symm⟩

theorem lowMask_lt (k : Nat) : lowMask k < 2 ^ 512 := by
  have h : ∀ k : Fin 10, lowMask k.val < 2 ^ 512 := by decide
  by_cases hk : k < 10
  · exact h ⟨k, hk⟩
  · unfold lowMask; split <;> first | omega | decide

theorem testBit_ge {x j : Nat} (hx : x < 2 ^ 512) (hj : 512 ≤ j) : x.testBit j = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hj)

theorem sub_lt512 (y : Fin 512) (a : Nat) : y.val - a < 512 :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) y.isLt

theorem xorShift_testBit (S : Nat) (k : Fin 9) (y : Fin 512) :
    (xorShift S k.val).testBit y.val = S.testBit (y.val ^^^ 2 ^ k.val) := by
  unfold xorShift
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_shiftRight]
  have hf := bit_facts k y
  have hy := y.isLt
  cases hb : y.val.testBit k.val with
  | true =>
    obtain ⟨hle, hxe⟩ := hf.1 hb
    have hm : (lowMask k.val).testBit (y.val - 2 ^ k.val) = true := by
      have := lowMask_testBit k ⟨y.val - 2 ^ k.val, sub_lt512 y _⟩
      simp only at this; rw [this]
      have h2 := bit_facts k ⟨y.val - 2 ^ k.val, sub_lt512 y _⟩
      cases hb2 : (y.val - 2 ^ k.val).testBit k.val with
      | false => rfl
      | true =>
        obtain ⟨hle2, hxe2⟩ := h2.1 hb2
        simp only at hle2 hxe2
        exfalso
        -- y - 2^k and y would both have bit k set, but they differ by exactly 2^k
        have hp : 0 < 2 ^ k.val := Nat.two_pow_pos _
        have e1 : (y.val - 2 ^ k.val) ^^^ 2 ^ k.val = y.val := by
          rw [← hxe, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        omega
    have hm2 : (lowMask k.val).testBit y.val = false := by
      rw [lowMask_testBit k y, hb]; rfl
    rw [hm, hm2, hxe]
    simp [hle]
  | false =>
    obtain ⟨hsub, hxe⟩ := hf.2 hb
    have hm2 : (lowMask k.val).testBit y.val = true := by
      rw [lowMask_testBit k y, hb]; rfl
    have hfirst : (decide (y.val ≥ 2 ^ k.val) && (S.testBit (y.val - 2 ^ k.val) &&
        (lowMask k.val).testBit (y.val - 2 ^ k.val))) = false := by
      by_cases hle : 2 ^ k.val ≤ y.val
      · have := lowMask_testBit k ⟨y.val - 2 ^ k.val, sub_lt512 y _⟩
        simp only at this
        rw [this, hsub hle]; simp
      · simp [hle]
    rw [hfirst, hm2, hxe]
    simp

theorem mem_expand (S : Nat) (y : Fin 512) (k : Nat) (hk : k < 9)
    (h : S.testBit (y.val ^^^ 2 ^ k) = true) : (expand S).testBit y.val = true := by
  unfold expand; rw [testBit_foldl_or]
  simp only [Bool.or_eq_true, List.any_eq_true]
  refine Or.inr ⟨k, List.mem_range.mpr hk, ?_⟩
  rw [xorShift_testBit S ⟨k, hk⟩ y]; exact h

theorem freeOf_testBit (ban : Nat) (y : Fin 512) :
    (freeOf ban).testBit y.val = !ban.testBit y.val := by
  unfold freeOf full
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  simp [y.isLt]

theorem xor_xor_cancel (h k : Nat) : (h ^^^ 2 ^ k) ^^^ 2 ^ k = h := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem testBit_or_left {a b y : Nat} (h : (a ||| b).testBit y = false) : a.testBit y = false := by
  rw [Nat.testBit_or] at h; simp only [Bool.or_eq_false_iff] at h; exact h.1

theorem testBit_or_right {a b y : Nat} (h : (a ||| b).testBit y = false) : b.testBit y = false := by
  rw [Nat.testBit_or] at h; simp only [Bool.or_eq_false_iff] at h; exact h.2

/-! ### Properties of valid extensions -/

theorem ValidExt.lt {h ban : Nat} {xs : List Nat} (v : ValidExt h ban xs) :
    ∀ x ∈ xs, x < 512 := by
  induction v with
  | nil => simp
  | cons h ban x xs k hk hh hx _ _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hx]; exact xor_lt ⟨h, hh⟩ ⟨k, hk⟩
    · exact ih y hy

theorem ValidExt.not_banned {h ban : Nat} {xs : List Nat} (v : ValidExt h ban xs) :
    ∀ x ∈ xs, ban.testBit x = false := by
  induction v with
  | nil => simp
  | cons h ban x xs k hk hh hx hfree _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hfree
    · exact testBit_or_left (ih y hy)

theorem ValidExt.nodup {h ban : Nat} {xs : List Nat} (v : ValidExt h ban xs) : xs.Nodup := by
  induction v with
  | nil => exact List.nodup_nil
  | cons h ban x xs k hk hh hx hfree rest ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro hmem
    have h1 := testBit_or_right (rest.not_banned x hmem)
    rw [hx, cnMask_nbr h k hk] at h1
    exact Bool.noConfusion h1

theorem length_le_countBits (R : Nat) :
    ∀ n (l : List Nat), l.Nodup → (∀ y ∈ l, y < n ∧ R.testBit y = true) →
      l.length ≤ countBits R n := by
  intro n
  induction n with
  | zero =>
    intro l _ hl
    cases l with
    | nil => simp [countBits_zero]
    | cons a l => exact absurd (hl a (List.mem_cons_self ..)).1 (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hnd hl
    by_cases hn : n ∈ l
    · have hR : R.testBit n = true := (hl n hn).2
      have hlen := List.length_erase_of_mem hn
      have hsub := ih (l.erase n) (hnd.erase n) (by
        intro y hy
        obtain ⟨hne, hy⟩ := (hnd.mem_erase_iff).mp hy
        obtain ⟨hlt, hb⟩ := hl y hy
        exact ⟨by omega, hb⟩)
      have hpos : 0 < l.length := List.length_pos_of_mem hn
      rw [countBits_succ, hR, if_pos rfl]
      omega
    · have hsub := ih l hnd (by
        intro y hy
        obtain ⟨hlt, hb⟩ := hl y hy
        have : y ≠ n := fun e => hn (e ▸ hy)
        exact ⟨by omega, hb⟩)
      rw [countBits_succ]
      omega


/-! ### Counting set bits -/

/-- Subtracting one leaves bit `y` unchanged when a lower bit is set. -/
theorem testBit_pred {R y b : Nat} (hb : b < y) (hRb : R.testBit b = true) :
    (R - 1).testBit y = R.testBit y := by
  have hpos : 0 < 2 ^ y := Nat.two_pow_pos y
  have hmod : R % 2 ^ y ≠ 0 := by
    intro h0
    have := Nat.testBit_mod_two_pow R y b
    rw [h0, Nat.zero_testBit, hRb] at this
    simp [hb] at this
  have hlt := Nat.mod_lt R hpos
  have hdm := Nat.div_add_mod R (2 ^ y)
  have e1 : R - 1 = 2 ^ y * (R / 2 ^ y) + (R % 2 ^ y - 1) := by omega
  rw [e1, Nat.testBit_two_pow_mul_add _ (by omega)]
  conv => rhs; rw [← hdm]
  rw [Nat.testBit_two_pow_mul_add _ hlt]
  simp

theorem exists_min_mem : ∀ (l : List Nat), l ≠ [] → ∃ m ∈ l, ∀ y ∈ l, m ≤ y
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min_mem (b :: l) (by simp)
    by_cases hle : a ≤ m
    · refine ⟨a, by simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · exact Nat.le_trans hle (hmin y hy)
    · refine ⟨m, List.mem_cons_of_mem _ hm, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact hmin y hy

theorem length_le_kcount :
    ∀ f R (l : List Nat), l.Nodup → (∀ y ∈ l, y < 512 ∧ R.testBit y = true) →
      l.length ≤ kcount R f := by
  intro f
  induction f with
  | zero =>
    intro R l hnd hl
    rw [kcount_zero]
    split
    · rename_i h0
      have hR : R = 0 := beq_iff_eq.mp h0
      cases l with
      | nil => simp
      | cons a l =>
        have := (hl a (List.mem_cons_self ..)).2
        rw [hR, Nat.zero_testBit] at this; exact absurd this (by simp)
    · rw [← countBits_full]
      apply length_le_countBits full 512 l hnd
      intro y hy
      refine ⟨(hl y hy).1, ?_⟩
      unfold full; rw [Nat.testBit_two_pow_sub_one]; simp [(hl y hy).1]
  | succ f ih =>
    intro R l hnd hl
    rw [kcount_succ]
    split
    · rename_i h0
      have hR : R = 0 := beq_iff_eq.mp h0
      cases l with
      | nil => simp
      | cons a l =>
        have := (hl a (List.mem_cons_self ..)).2
        rw [hR, Nat.zero_testBit] at this; exact absurd this (by simp)
    · by_cases hnil : l = []
      · subst hnil; simp
      obtain ⟨m, hm, hmin⟩ := exists_min_mem l hnil
      have hsub := ih (R &&& (R - 1)) (l.erase m) (hnd.erase m) (by
        intro y hy
        obtain ⟨hne, hy⟩ := (hnd.mem_erase_iff).mp hy
        obtain ⟨hlt, hb⟩ := hl y hy
        refine ⟨hlt, ?_⟩
        have hmy : m < y := Nat.lt_of_le_of_ne (hmin y hy) (fun e => hne e.symm)
        rw [Nat.testBit_and, hb, testBit_pred hmy (hl m hm).2, hb]
        rfl)
      have hlen := List.length_erase_of_mem hm
      have hpos : 0 < l.length := List.length_pos_of_mem hm
      omega

theorem reach_closed {F : Nat} : ∀ n R0 R, reach F n R0 = some R → expand R &&& F = R := by
  intro n
  induction n with
  | zero => intro R0 R h; rw [reach_zero] at h; exact absurd h (by simp)
  | succ n ih =>
    intro R0 R h
    rw [reach_succ] at h
    split at h
    · rename_i heq
      simp only [Option.some.injEq] at h
      subst h
      exact beq_iff_eq.mp heq
    · exact ih _ _ h

/-- Every vertex of an extension lies in any closed region containing the first step. -/
theorem ValidExt.in_region {head ban0 R : Nat}
    (hclosed : expand R &&& freeOf ban0 = R)
    (hstart : ∀ y : Fin 512, (expand (2 ^ head) &&& freeOf ban0).testBit y.val = true →
      R.testBit y.val = true) :
    ∀ {h ban : Nat} {xs : List Nat}, ValidExt h ban xs →
      (h = head ∨ R.testBit h = true) → (∀ y, ban0.testBit y = true → ban.testBit y = true) →
      ∀ x ∈ xs, R.testBit x = true := by
  intro h ban xs v
  induction v with
  | nil => intros; simp_all
  | cons h ban x xs k hk hh hx hfree rest ih =>
    intro hpos hmono
    have hxlt : x < 512 := by rw [hx]; exact xor_lt ⟨h, hh⟩ ⟨k, hk⟩
    have hb0 : ban0.testBit x = false := by
      cases e : ban0.testBit x with
      | false => rfl
      | true => rw [hmono x e] at hfree; exact absurd hfree (by decide)
    have hF : (freeOf ban0).testBit x = true := by
      rw [freeOf_testBit ban0 ⟨x, hxlt⟩, hb0]; rfl
    have hxR : R.testBit x = true := by
      have hcancel : x ^^^ 2 ^ k = h := by rw [hx]; exact xor_xor_cancel h k
      rcases hpos with rfl | hR
      · apply hstart ⟨x, hxlt⟩
        rw [Nat.testBit_and, hF, Bool.and_true]
        apply mem_expand _ ⟨x, hxlt⟩ k hk
        simp only; rw [hcancel, Nat.testBit_two_pow]; simp
      · rw [← hclosed, Nat.testBit_and, hF, Bool.and_true]
        apply mem_expand _ ⟨x, hxlt⟩ k hk
        simp only; rw [hcancel]; exact hR
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxR
    · exact ih (Or.inr hxR) (fun z hz => by rw [Nat.testBit_or, hmono z hz]; rfl) y hy

theorem bound_sound {head ban : Nat} {xs : List Nat} (v : ValidExt head ban xs) :
    xs.length ≤ bound head ban := by
  have hlt := v.lt
  have hnd := v.nodup
  have fallback : xs.length ≤ 512 := by
    rw [← countBits_full]
    apply length_le_countBits full 512 xs hnd
    intro y hy
    refine ⟨hlt y hy, ?_⟩
    unfold full; rw [Nat.testBit_two_pow_sub_one]; simp [hlt y hy]
  unfold bound
  simp only
  split
  · rename_i R hR
    split
    · rename_i hcheck
      apply length_le_kcount 512 R xs hnd
      intro y hy
      refine ⟨hlt y hy, ?_⟩
      have hclosed := reach_closed 512 _ R hR
      have hstart : ∀ z : Fin 512, (expand (2 ^ head) &&& freeOf ban).testBit z.val = true →
          R.testBit z.val = true := by
        intro z hz
        have e := beq_iff_eq.mp hcheck
        rw [← e, Nat.testBit_and, Bool.and_eq_true] at hz
        exact hz.2
      exact v.in_region hclosed hstart (Or.inl rfl) (fun _ h => h) y hy
    · exact fallback
  · exact fallback

theorem anyBelow_false {f : Nat → Bool} :
    ∀ n, anyBelow f n = false → ∀ k, k < n → f k = false := by
  intro n
  induction n with
  | zero => intro _ k hk; omega
  | succ n ih =>
    intro h k hk
    rw [anyBelow_succ, Bool.or_eq_false_iff] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih h.1 k hk
    · exact h.2

/-- Soundness of the exhaustive search. -/
theorem search_sound : ∀ need head ban, search head ban need = false →
    ∀ xs, ValidExt head ban xs → xs.length < need := by
  intro need
  induction need with
  | zero => intro head ban h; rw [search_zero] at h; exact absurd h (by simp)
  | succ need ih =>
    intro head ban h xs v
    rw [search_succ] at h
    split at h
    · rename_i hb
      have := bound_sound v
      omega
    · cases v with
      | nil => simp
      | cons _ _ x xs k hk hh hx hfree rest =>
        have hf := anyBelow_false 9 h k hk
        rw [← hx, hfree] at hf
        simp only [Bool.not_false, Bool.true_and] at hf
        have := ih x (ban ||| cnMask head) hf xs rest
        simp only [List.length_cons]
        omega


/-- Splitting rule used to break large certificates into smaller kernel checks: the
search fails at a node if every one of the nine children is banned or fails. -/
theorem search_of_children (head ban need : Nat)
    (h : ∀ k, k < 9 → (ban.testBit (head ^^^ 2 ^ k) = true ∨
      search (head ^^^ 2 ^ k) (ban ||| cnMask head) need = false)) :
    search head ban (need + 1) = false := by
  rw [search_succ]
  split
  · rfl
  · have : ∀ n, n ≤ 9 → anyBelow (fun k => !(ban.testBit (head ^^^ 2 ^ k)) &&
        search (head ^^^ 2 ^ k) (ban ||| cnMask head) need) n = false := by
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

/-! ### Connection to `Snake9.Snake` -/

theorem banFrom_succ (f : Nat → Nat) (n : Nat) :
    banFrom f (n + 1) = banFrom f n ||| cnMask (f n) := by
  unfold banFrom; rw [List.range_succ, List.foldl_append]; rfl

theorem banFrom_congr (f g : Nat → Nat) :
    ∀ n, (∀ i, i < n → f i = g i) → banFrom f n = banFrom g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [banFrom_succ, banFrom_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem banFrom_testBit (f : Nat → Nat) (n y : Nat) (h : (banFrom f n).testBit y = true) :
    ∃ i, i < n ∧ (cnMask (f i)).testBit y = true := by
  unfold banFrom at h; rw [testBit_foldl_or] at h
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range] at h
  exact h

/-- The vertex values of a 192-edge snake, as a total function. -/
def vals (p : Snake 192) (i : Nat) : Nat :=
  if h : i < 193 then (p.vertex ⟨i, h⟩).val else 0

def tailList (p : Snake 192) (t : Nat) : List Nat :=
  (List.range (192 - t)).map (fun j => vals p (t + 1 + j))

theorem tail_valid (p : Snake 192) :
    ∀ d t, t + d = 192 → ValidExt (vals p t) (banFrom (vals p) t) (tailList p t) := by
  intro d
  induction d with
  | zero =>
    intro t ht
    have : 192 - t = 0 := by omega
    simp only [tailList, this, List.range_zero, List.map_nil]
    exact ValidExt.nil _ _
  | succ d ih =>
    intro t ht
    have htl : tailList p t = vals p (t + 1) :: tailList p (t + 1) := by
      simp only [tailList]
      have : 192 - t = (192 - (t + 1)) + 1 := by omega
      rw [this, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 2
      funext j; simp only [Function.comp, Nat.succ_eq_add_one]; congr 1; omega
    rw [htl]
    have ht1 : t < 193 := by omega
    have ht2 : t + 1 < 193 := by omega
    have hvt : vals p t = (p.vertex ⟨t, ht1⟩).val := by simp [vals, ht1]
    have hvt1 : vals p (t + 1) = (p.vertex ⟨t + 1, ht2⟩).val := by simp [vals, ht2]
    have hadj : Adj (p.vertex ⟨t, ht1⟩) (p.vertex ⟨t + 1, ht2⟩) :=
      (p.induced ⟨t, ht1⟩ ⟨t + 1, ht2⟩ (by simp)).mpr rfl
    obtain ⟨k, hk, hke⟩ := (adj_iff_coordinate_flip _ _).mp hadj
    apply ValidExt.cons _ _ _ _ k hk
    · rw [hvt]; exact (p.vertex ⟨t, ht1⟩).isLt
    · rw [hvt, hvt1]; exact hke
    · cases e : (banFrom (vals p) t).testBit (vals p (t + 1)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨i, hi, hci⟩ := banFrom_testBit _ _ _ e
        have hi1 : i < 193 := by omega
        have hvi : vals p i = (p.vertex ⟨i, hi1⟩).val := by simp [vals, hi1]
        rw [hvi, hvt1] at hci
        rcases cnMask_testBit_true hci with heq | ⟨k', hk', he'⟩
        · have := p.distinct ⟨i, hi1⟩ ⟨t + 1, ht2⟩ (Fin.ext heq.symm)
          simp only [Fin.mk.injEq] at this; omega
        · have hadj' : Adj (p.vertex ⟨i, hi1⟩) (p.vertex ⟨t + 1, ht2⟩) :=
            (adj_iff_coordinate_flip _ _).mpr ⟨k', hk', he'⟩
          have := (p.induced ⟨i, hi1⟩ ⟨t + 1, ht2⟩ (by simp; omega)).mp hadj'
          simp at this; omega
    · rw [← banFrom_succ]
      exact ih (t + 1) (by omega)

theorem tailList_length (p : Snake 192) (t : Nat) : (tailList p t).length = 192 - t := by
  simp [tailList]

/-- If the search fails from a prefix of `K` vertices, no 192-edge snake starts with it. -/
theorem no192_from_prefix (pre : Array Nat) (K : Nat) (hK1 : 1 ≤ K) (hK : K ≤ 193)
    (hs : search pre[K - 1]! (banFrom (fun i => pre[i]!) (K - 1)) (193 - K) = false) :
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
  have := search_sound (193 - K) _ _ hs _ hvalid
  rw [tailList_length] at this
  omega

#print axioms search_sound
#print axioms search_of_children
#print axioms no192_from_prefix
end Snake9.Dfs
