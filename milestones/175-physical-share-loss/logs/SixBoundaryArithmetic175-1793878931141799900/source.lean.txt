import Std
namespace SixBoundaryArithmetic175
private theorem triple_bound (a b c : Nat)
    (hp : 1≤a ∧ 1≤b ∧ 1≤c)
    (hab : (a=1 → 4≤b) ∧ (b=1 → 4≤a))
    (hbc : (b=1 → 4≤c) ∧ (c=1 → 4≤b))
    (hn : ¬(a=2 ∧ b=2 ∧ c=2)) :
    6≤a+b+c ∧ (a+b+c=6 → a=1 ∧ b=4 ∧ c=1) := by omega


private theorem pair_bound (a b : Nat) (ha : 1≤a) (hb : 1≤b)
    (h : (a=1 → 4≤b) ∧ (b=1 → 4≤a)) : 4≤a+b := by omega

theorem six_count_minimum (a b c d e f : Nat)
    (hp : 1≤a ∧ 1≤b ∧ 1≤c ∧ 1≤d ∧ 1≤e ∧ 1≤f)
    (hab : (a=1 → 4≤b) ∧ (b=1 → 4≤a))
    (hbc : (b=1 → 4≤c) ∧ (c=1 → 4≤b))
    (hcd : (c=1 → 4≤d) ∧ (d=1 → 4≤c))
    (hde : (d=1 → 4≤e) ∧ (e=1 → 4≤d))
    (hef : (e=1 → 4≤f) ∧ (f=1 → 4≤e))
    (hn1 : ¬(a=2 ∧ b=2 ∧ c=2)) (hn2 : ¬(d=2 ∧ e=2 ∧ f=2)) :
    14≤a+b+c+d+e+f := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  have ht1 := triple_bound a b c ⟨ha,hb,hc⟩ hab hbc hn1
  have ht2 := triple_bound d e f ⟨hd,he,hf⟩ hde hef hn2
  have hp1 := pair_bound a b ha hb hab
  have hp2 := pair_bound e f he hf hef
  have hs1 := ht1.1
  have hs2 := ht2.1
  have hx1 : a+b+c=6 → c=1 := fun h => (ht1.2 h).2.2
  have hx2 : d+e+f=6 → d=1 := fun h => (ht2.2 h).1
  clear ht1 ht2 hab hbc hde hef hn1 hn2 ha hb hc hd he hf
  omega

theorem retained_census (m T s B : Nat) (hm : 7≤m)
    (hboundary : B+22≤T) (hwalk : 4*(m-7)≤B+7)
    (hcensus : T+2*s+35*(m+1)=9214) :
    4*m≤T+13 ∧ 39*m+2*s≤9192 := by omega

theorem critical_empty_squares (m T s B : Nat) (hm : 235≤m)
    (hboundary : B+22≤T) (hwalk : 4*(m-7)≤B+7)
    (hcensus : T+2*s+35*(m+1)=9214) : m=235 ∧ s≤13 := by omega

theorem fourteen_empty_squares_excludes_235 (m T s B : Nat) (hm : 7≤m)
    (hboundary : B+22≤T) (hwalk : 4*(m-7)≤B+7)
    (hcensus : T+2*s+35*(m+1)=9214) (hs : 14≤s) : m≤234 := by omega

#print axioms six_count_minimum
#print axioms retained_census
#print axioms critical_empty_squares
#print axioms fourteen_empty_squares_excludes_235
end SixBoundaryArithmetic175
