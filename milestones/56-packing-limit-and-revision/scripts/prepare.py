from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
source=ROOT/'milestones/55-critical-share-family/covered/data/analysis-share.json'
r=json.loads(source.read_text());cycle=r['cycle'];counts=[x['counts'][-1] for x in cycle]
assert len(cycle)==25 and sum(counts)==102 and all(x['share_lower']==0 for x in cycle)
for j,e in enumerate(cycle):assert e['next_state']==cycle[(j+1)%25]['state']
(HERE/'data').mkdir(parents=True,exist_ok=True);(HERE/'lean').mkdir(exist_ok=True);(HERE/'logs').mkdir(exist_ok=True)
(HERE/'data/zero-credit-cycle.json').write_text(json.dumps(dict(source=source.relative_to(ROOT).as_posix(),
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),counts=counts,cycle=cycle,
    scope='A cycle in the current finite relaxation with zero recorded credit; no actual-snake realization is claimed.'),indent=2)+'\n')
lean='''import Mathlib.Tactic
namespace Snake9.PackingLimit56

def counts : List Nat := COUNTS
def count (i : Nat) : Int := (counts.getD i 0 : Int)

theorem count_sum : (∑ i ∈ Finset.range 25, count i) = 102 := by decide

theorem potential_sum (c phi : Nat → Int) (A B : Int) (n : Nat)
    (h : ∀ i, i<n → A+phi (i+1) ≤ B*c i+phi i) :
    (n : Int)*A+phi n ≤ B*(∑ i ∈ Finset.range n, c i)+phi 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := ih (fun i hi => h i (by omega))
    have step := h n (by omega)
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

theorem cycle_mean_ceiling (phi : Nat → Int) (A B : Int)
    (hc : phi 25=phi 0)
    (h : ∀ i, i<25 → A+phi (i+1) ≤ B*count i+phi i) : 25*A ≤ 102*B := by
  have hs := potential_sum count phi A B 25 h
  rw [count_sum,hc] at hs
  norm_num at hs
  omega

/-- Any choice of a subset of zero credits has zero total credit. -/
theorem zero_credit_packing (credit : Nat → Nat) (J : Finset Nat)
    (h : ∀ i ∈ J, credit i=0) : (∑ i ∈ J, credit i)=0 := by
  exact Finset.sum_eq_zero h

/-- Even zero potential loss cannot exclude 235 at the recorded cycle ceiling. -/
theorem cannot_exclude_235 (num den loss : Nat) (h : 25*num ≤ 2448*den) :
    (num+840*den)*235 ≤ 219960*den+7*num+loss := by omega

#print axioms count_sum
#print axioms potential_sum
#print axioms cycle_mean_ceiling
#print axioms zero_credit_packing
#print axioms cannot_exclude_235
end Snake9.PackingLimit56
'''.replace('COUNTS',str(counts))
(HERE/'lean/PackingLimit.lean').write_text(lean,encoding='utf-8')
check=(ROOT/'milestones/53-shares-on-sat-obstruction/scripts/check_lean.py').read_text().replace('FiniteBlockBudget','PackingLimit').replace("[HERE/'lean/PackingLimit.lean']", "[HERE/'lean/PackingLimit.lean',HERE/'lean/PaperArithmetic.lean']")
(HERE/'scripts/check_lean.py').write_text(check)
