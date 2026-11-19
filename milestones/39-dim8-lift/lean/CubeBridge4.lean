import CubeBridge3
/-! Bridge, part 4: the counters, and the bridge theorem: a `Pit` whose copy 0 is `A` and whose other
6-subcubes have at most `k` vertices satisfies `cubeCnfC4 c L A k`. -/
set_option linter.deprecated false
namespace Dim8Lift.Cube
open Dim8Lift.Cnf Snake9.LocalWindow

def b1 (c : Nat) : Nat := cbase + 512 * (2 * c)
def b2 (c L : Nat) : Nat := b1 c + 256 * (256 - L)
def subLits (q : Nat) : List Int := (subcubes.getD q []).map fun u => pos (sV u)

def tauF (S : Nat → Bool) (ℓ : Nat → Nat) (c L k v : Nat) : Bool :=
  if v < cbase then tau0 S ℓ v
  else if v < b1 c then decide ((v - cbase) % (2 * c) + 1 ≤ cl (tau0 S ℓ) endLits ((v - cbase) / (2 * c) + 1))
  else if v < b2 c L then
    decide ((v - b1 c) % (256 - L) + 1 ≤ cl (tau0 S ℓ) unselLits ((v - b1 c) / (256 - L) + 1))
  else
    decide ((v - b2 c L) % (256 * k) % k + 1 ≤
      cl (tau0 S ℓ) (subLits ((v - b2 c L) / (256 * k))) ((v - b2 c L) % (256 * k) / k + 1))

variable {S : Nat → Bool} {ℓ : Nat → Nat}

theorem dec_tau0 : Dec (tau0 S ℓ) S ℓ :=
  ⟨fun _ hu => t_s hu, fun _ _ hu h1 h2 => t_o hu h1 h2, fun _ _ _ hu hi h1 h2 => t_a hu hi h1 h2,
   fun _ _ _ hu ha hb => t_p hu ha hb, fun _ hu => t_two hu, fun _ hu => t_any hu, fun _ hu => t_e1 hu,
   fun _ hu => t_e0 hu⟩

theorem tauF_lo {c L k v : Nat} (h : v < cbase) : tauF S ℓ c L k v = tau0 S ℓ v := by
  unfold tauF; rw [if_pos h]

theorem dec_tauF (c L k : Nat) : Dec (tauF S ℓ c L k) S ℓ := by
  have d := dec_tau0 (S := S) (ℓ := ℓ)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; rw [tauF_lo (by unfold sV cbase; omega)]; exact d.s u hu
  · intro u j hu h1 h2; rw [tauF_lo (by unfold oV cbase; omega)]; exact d.o u j hu h1 h2
  · intro u i j hu hi h1 h2; rw [tauF_lo (by unfold aV cbase; omega)]; exact d.a u i j hu hi h1 h2
  · intro u a b hu ha hb; rw [tauF_lo (by unfold pV cbase; omega)]; exact d.p u a b hu ha hb
  · intro u hu; rw [tauF_lo (by unfold twoV cbase; omega)]; exact d.two u hu
  · intro u hu; rw [tauF_lo (by unfold anyV cbase; omega)]; exact d.any u hu
  · intro u hu; rw [tauF_lo (by unfold e1V cbase; omega)]; exact d.e1 u hu
  · intro u hu; rw [tauF_lo (by unfold e0V cbase; omega)]; exact d.e0 u hu

/-- literals whose variable lies below `cbase` read the same under `tauF` and `tau0` -/
theorem cl_lo {c L k : Nat} (xs : List Int) (hx : ∀ l ∈ xs, l.natAbs < cbase) (i : Nat) :
    cl (tauF S ℓ c L k) xs i = cl (tau0 S ℓ) xs i := by
  unfold cl; congr 1
  apply List.filter_congr; intro l hl
  have h := hx l (List.mem_of_mem_take hl)
  unfold litTrue; split
  · rw [tauF_lo (by omega)]
  · rw [tauF_lo (by omega)]

theorem decomp (x q m : Nat) (hm : 0 < m) (hx : x < m) : (x + q * m) / m = q ∧ (x + q * m) % m = x := by
  constructor
  · rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hx, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem regdec (i j k : Nat) (hk : 0 < k) (hj1 : 1 ≤ j) (hj : j ≤ k) :
    ((i - 1) * k + (j - 1)) / k = i - 1 ∧ ((i - 1) * k + (j - 1)) % k = j - 1 := by
  have := decomp (j - 1) (i - 1) k hk (by omega)
  rw [Nat.add_comm] at this; exact this

theorem endLits_lt : ∀ l ∈ endLits, l.natAbs < cbase ∧ l ≠ 0 := by
  intro l hl
  simp only [endLits, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hl
  obtain ⟨u, hu, h⟩ := hl; rw [mem_R256] at hu
  rcases h with rfl | rfl <;> simp [pos, e1V, e0V, cbase] <;> omega
theorem unselLits_lt : ∀ l ∈ unselLits, l.natAbs < cbase ∧ l ≠ 0 := by
  intro l hl
  simp only [unselLits, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl; rw [mem_R256] at hu
  simp [neg, sV, cbase]; omega
theorem subcubes_lt {q u : Nat} (h : u ∈ subcubes.getD q []) : u < 256 := by
  unfold subcubes at h
  rw [List.getD_eq_getElem?_getD] at h
  cases e : (List.flatMap _ pairs8)[q]? with
  | none => rw [e] at h; simp at h
  | some x =>
    rw [e] at h; simp only [Option.getD_some] at h
    have hm := List.mem_of_getElem? e
    simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at hm
    obtain ⟨_, _, v, _, hv⟩ := hm
    split at hv
    · simp at hv
    · simp only [Option.some.injEq] at hv; subst hv
      exact mem_R256.mp (List.mem_filter.mp h).1
theorem subLits_lt (q : Nat) : ∀ l ∈ subLits q, l.natAbs < cbase ∧ l ≠ 0 := by
  intro l hl
  simp only [subLits, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  have := subcubes_lt hu
  simp [pos, sV, cbase]; omega

theorem cl_full (τ : Nat → Bool) (xs : List Int) : cl τ xs xs.length = (xs.filter (litTrue τ)).length := by
  unfold cl; rw [List.take_of_length_le (Nat.le_refl _)]

theorem flat_count (n : Nat) (f : Nat → List Int) (p : Int → Bool) :
    (((List.range n).flatMap f).filter p).length = sm n (fun u => ((f u).filter p).length) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.filter_append, List.length_append, ih]; simp

theorem ends_count : (endLits.filter (litTrue (tau0 S ℓ))).length = sm 256 (endW S) := by
  unfold endLits R256; rw [flat_count]
  apply sm_congr; intro u hu
  have v1 : 0 < e1V u := by unfold e1V; omega
  have v0 : 0 < e0V u := by unfold e0V; omega
  simp only [List.filter_cons, List.filter_nil]
  rw [litTrue_pos _ v1, litTrue_pos _ v0, t_e1 hu, t_e0 hu]
  unfold endW
  cases S u <;> cases twoB S u <;> cases anyB S u <;> simp

theorem unsel_count : (unselLits.filter (litTrue (tau0 S ℓ))).length + cnt 256 S = 256 := by
  have e : unselLits = (List.range 256).flatMap fun u => [neg (sV u)] := by
    unfold unselLits R256; exact List.map_eq_flatMap
  rw [e, flat_count]
  unfold cnt; rw [← sm_add]
  rw [sm_congr (g := fun _ => 1)]
  · clear e; have : ∀ n, sm n (fun _ => 1) = n := by intro n; induction n <;> simp_all
    exact this 256
  · intro u hu
    have vs : 0 < sV u := by unfold sV; omega
    simp only [List.filter_cons, List.filter_nil]
    rw [litTrue_neg _ vs, t_s hu]
    cases S u <;> simp

theorem sub_count (q : Nat) : ((subLits q).filter (litTrue (tau0 S ℓ))).length =
    ((subcubes.getD q []).filter S).length := by
  unfold subLits
  rw [List.filter_map, List.length_map]
  congr 1; apply List.filter_congr; intro u hu
  have vs : 0 < sV u := by unfold sV; omega
  simp only [Function.comp, litTrue_pos _ vs, t_s (subcubes_lt hu)]

end Dim8Lift.Cube
