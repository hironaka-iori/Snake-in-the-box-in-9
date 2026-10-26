import Mathlib.Tactic
namespace Snake9.FiniteBlockBudget

/-- A, B, C denote disjoint groups within each block; cross demands join consecutive blocks. -/
theorem block_budget (A B C Z : Nat → Nat) (n : Nat)
    (hz : ∀ k, k≤n → A k+B k+C k≤Z k)
    (hb : ∀ k, k≤n → 96≤B k)
    (hc : ∀ k, k<n → 96≤C k+A (k+1)) :
    96*(2*n+1)+A 0+C n ≤ ∑ k ∈ Finset.range (n+1), Z k := by
  induction n with
  | zero =>
    have h0 := hz 0 (by omega)
    have b0 := hb 0 (by omega)
    simpa using (show 96+A 0+C 0≤Z 0 by omega)
  | succ n ih =>
    have prev := ih (fun k hk => hz k (by omega)) (fun k hk => hb k (by omega))
      (fun k hk => hc k (by omega))
    have z := hz (n+1) (by omega)
    have b := hb (n+1) (by omega)
    have c := hc n (by omega)
    rw [show n.succ+1=(n+1)+1 by omega, Finset.sum_range_succ]
    omega

theorem finite_charge (p T S : Nat) (hp : 1≤p)
    (ht : 65*p≤T) (hs : 96*(2*p-1)≤S) :
    24*73*p ≤ 24*T+S+96 := by omega

/-- The outside-count and share premises still need to be supplied by an actual snake run. -/
theorem run_budget (v p T S : Nat) (hp : 1≤p)
    (ht : v+49*p+6≤T) (hs : 96*(2*p-1)≤S)
    (hg : 24*T+S+840*v≤221136) : 864*v+1368*p≤221088 := by omega

theorem excludes_thirteen_blocks_at_235 (p : Nat)
    (hp : 13≤p) (h : 864*236+1368*p≤221088) : False := by omega

#print axioms block_budget
#print axioms finite_charge
#print axioms run_budget
#print axioms excludes_thirteen_blocks_at_235
end Snake9.FiniteBlockBudget
