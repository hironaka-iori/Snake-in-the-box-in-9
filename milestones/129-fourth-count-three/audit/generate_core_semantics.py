"""Generate concrete semantic checks for the fixed, renamed 3500-clause core."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
data_path=HERE/'data/selected-core-semantics.json'
d=json.loads(data_path.read_text())
cnf_path=HERE/'lean/Recovered129G/LocalWindowCnf/Triple129.lean'
assert sha(cnf_path)==d['cnf_source_sha256']
body=cnf_path.read_text().split('noncomputable def raw : List (List Nat) := ',1)[1].split('\nnoncomputable def cnf',1)[0]
assert json.loads(body)==d['raw']
assert len(d['raw'])==len(d['tags'])==3500
assert d['used_counter_indices']==[0,4,11,12] and len(d['counters'])==13
meaning={int(k):v for k,v in d['meaning'].items()}
maximum=max(meaning)
assert maximum==d['max_semantic_variable']==2415
assert all(c['index']==i for i,c in enumerate(d['counters']))
assert all(c.get('dummy',False)==(i not in [0,4,11,12]) for i,c in enumerate(d['counters']))
for c in d['counters']:
    for lit in c.get('literals',[]):
        assert meaning[abs(lit)][0] in {'p','e'}
assert {x//2 for row in d['raw'] for x in row} <= set(meaning)

def natlist(xs):return '['+','.join(map(str,xs))+']'
def tree(r,s):
    if r+s>maximum:
        m=meaning.get(r)
        return '.z' if m is None else '(.'+' '.join(map(str,m))+')'
    left,right=tree(r,2*s),tree(r+s,2*s)
    return '.z' if left==right=='.z' else f'(.n {left} {right})'
def counter(c):
    if c.get('dummy'):return 'dfltCtr'
    kind=c['kind']
    kind='.'+kind[0]+(' '+str(kind[1]) if len(kind)>1 else '') if kind[0] in ['ends','lo','hi'] else '.ends'
    return '⟨'+natlist([2*abs(x)+(x<0) for x in c['literals']])+','+str(c['upper'])+','+kind+'⟩'
def tags(ts):return '['+','.join('(.'+' '.join(map(str,t))+')' for t in ts)+']'
def rows(rs):return '['+','.join(natlist(row) for row in rs)+']'

source='''import Recovered129G.LocalWindowCnf.Triple129
import ActualTriple129
import ActualBounds125

namespace Snake9.CoreSemantics129
open Finset
open scoped BigOperators
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.LocalWindow.Tags

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

-- Certificate data; metadata-only inputs remain present even outside the core.
noncomputable def meaning : MT :=
  __MEANING__

noncomputable def counters : List Ctr := [__COUNTERS__]
noncomputable def tags : List Tag := __TAGS__

theorem ordinary_checked :
    (counters.take 12).all (ctrOK meaning
      (centresOf Triple129.window Triple129.bounds)) = true := by
  rw [centresK_eq]
  decide +kernel

#print axioms ordinary_checked

theorem triple_checked :
    (counters.getD 12 dfltCtr).lits.all (negP meaning) = true ∧
    ((counters.getD 12 dfltCtr).lits.map (vl meaning)).Perm
      (([⟨7,2,0,0,21⟩,⟨14,3,2,0,21⟩,⟨10,2,4,0,21⟩] : List Centre).flatMap corners) ∧
    (counters.getD 12 dfltCtr).k = 11 := by
  decide +kernel

#print axioms triple_checked

private theorem checked_append (M : MT) (cs : List Ctr) (w : List Nat)
    {ta tb : List Tag} {ra rb : List (List Nat)}
    (ha : ckAll M cs w ta ra = true) (hb : ckAll M cs w tb rb = true) :
    ckAll M cs w (ta ++ tb) (ra ++ rb) = true := by
  induction ta generalizing ra with
  | nil =>
    cases ra with
    | nil => exact hb
    | cons c rs => simp [ckAll] at ha
  | cons t ts ih =>
    cases ra with
    | nil => simp [ckAll] at ha
    | cons c rs =>
      simp only [ckAll, Bool.and_eq_true] at ha
      simp only [List.cons_append, ckAll, Bool.and_eq_true]
      exact ⟨ha.1,ih ha.2⟩

__GROUPS__

theorem tags_checked : ckAll meaning counters Triple129.window tags Triple129.raw = true := by
  change ckAll meaning counters Triple129.window (__T_JOIN__) (__R_JOIN__) = true
  exact __CHAIN__

#print axioms tags_checked

private theorem counters_split :
    counters = counters.take 12 ++ [counters.getD 12 dfltCtr] := by rfl

theorem actual_satisfies_core {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hfourth : coreAlpha p (r+4) = 3)
    (htriple : coreAlpha p (r+3)+coreAlpha p (r+5)+coreAlpha p (r+6) ≤ 11) :
    ∃ τ : Nat → Bool, cnfTrue τ Triple129.cnf = true := by
  obtain ⟨P,hP⟩ := ActualTriple129.actual_normalized_frame p r hr hshape
  let S := sel p (amap P (vx p r))
  let E := frameE p P (vx p r)
  have ax : Axioms S E Triple129.window (centresOf Triple129.window Triple129.bounds) :=
    ActualTriple129.actual_window_axioms p P r hr hP hfourth
  have hg : JointTags.Good S E meaning (counters.getD 12 dfltCtr) :=
    ActualTriple129.actual_three_counter_good p P r hr hP htriple E meaning
      (counters.getD 12 dfltCtr) triple_checked.1 triple_checked.2.1 triple_checked.2.2
  have he : ∀ ct ∈ [counters.getD 12 dfltCtr], JointTags.Good S E meaning ct := by
    intro ct hc
    have heq : ct = counters.getD 12 dfltCtr := by simpa using hc
    simpa only [heq] using hg
  have hv := JointTags.valid_append (old := counters.take 12)
    (extra := [counters.getD 12 dfltCtr]) ordinary_checked he ax
  have hv' : JointTags.Valid S E meaning counters := by
    simpa only [← counters_split] using hv
  exact ⟨tau S E meaning counters,
    JointTags.sound meaning counters Triple129.window
      (centresOf Triple129.window Triple129.bounds) tags Triple129.raw
      tags_checked S E hv' ax⟩

#print axioms actual_satisfies_core

theorem actual_triple_lower (hunsat : Unsat Triple129.cnf)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hfourth : coreAlpha p (r+4) = 3) :
    12 ≤ coreAlpha p (r+3)+coreAlpha p (r+5)+coreAlpha p (r+6) := by
  by_contra hn
  obtain ⟨τ,ht⟩ := actual_satisfies_core p r hr hshape hfourth (by omega)
  rw [hunsat τ] at ht
  exact Bool.false_ne_true ht

#print axioms actual_triple_lower

theorem actual_six_lower (hunsat : Unsat Triple129.cnf)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hfourth : coreAlpha p (r+4) = 3) :
    23 ≤ ∑ j ∈ range 6, coreAlpha p (r+j+1) := by
  have ht := actual_triple_lower hunsat p r hr hshape hfourth
  have hp := (ActualBounds125.prefix_and_suffix p r hr hshape).1
  have h14 := ActualBounds125.first_fourth_exclusion p r (by omega) hp
  have hpair := ActualPair121.actual_pair_sum p r (by omega) hp
  have h1 : 3 ≤ coreAlpha p (r+1) := by omega
  have h2 : 5 ≤ coreAlpha p (r+2) := by omega
  have h23 : 23 ≤ coreAlpha p (r+1)+coreAlpha p (r+2)+coreAlpha p (r+3)+
      coreAlpha p (r+4)+coreAlpha p (r+5)+coreAlpha p (r+6) := by omega
  simpa [Finset.sum_range_succ,Nat.add_assoc] using h23

#print axioms actual_six_lower
end Snake9.CoreSemantics129
'''
source=source.replace('__MEANING__',tree(0,1)).replace('__COUNTERS__',','.join(counter(c) for c in d['counters']))
source=source.replace('__TAGS__',tags(d['tags']))
count=(len(d['raw'])+63)//64
groups=[]
for i in range(count):
    groups.append(f'private noncomputable def ts{i} : List Tag := '+tags(d['tags'][64*i:64*(i+1)])+'\n'+
      f'private noncomputable def rs{i} : List (List Nat) := '+rows(d['raw'][64*i:64*(i+1)])+'\n'+
      f'private theorem checked{i} : ckAll meaning counters Triple129.window ts{i} rs{i} = true := by decide +kernel\n')
source=source.replace('__GROUPS__','\n'.join(groups))
source=source.replace('__T_JOIN__',' ++ '.join(f'ts{i}' for i in range(count)))
source=source.replace('__R_JOIN__',' ++ '.join(f'rs{i}' for i in range(count)))
chain=f'checked{count-1}'
for i in reversed(range(count-1)):chain=f'(checked_append meaning counters Triple129.window checked{i} {chain})'
source=source.replace('__CHAIN__',chain)
target=HERE/'lean/CoreSemantics129.lean'
assert not target.exists(),'Preserve an already generated source and its attempt first.'
target.write_text(source,encoding='utf-8',newline='\n')
record=dict(status='GENERATED_NOT_YET_CHECKED',source=str(target),source_sha256=sha(target),
  generator_sha256=sha(__file__),metadata_sha256=sha(data_path),cnf_source_sha256=sha(cnf_path),
  clauses=3500,clause_groups=count,max_group_length=64,used_counters=[0,4,11,12],
  semantic_meanings=len(meaning),max_semantic_variable=maximum,
  scope='Finite clause/counter checks and actual satisfaction; lower bounds remain conditional on Unsat of this exact CNF.')
(HERE/'audit/core-semantics-generation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
