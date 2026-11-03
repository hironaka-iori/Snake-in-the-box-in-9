"""Generate a pair-only tagged semantic certificate from the saved exact data."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
data_path = HERE / 'data/pair-counter.json'
data = json.loads(data_path.read_text())
preparation = json.loads((HERE / 'data/preparation.json').read_text())
assert sha(data_path) == preparation['counter_sha256']
assert data['counter_index'] == 8 and data['upper'] == 34
assert len(data['literals']) == 42 and len(data['tags']) == len(data['clauses']) == 2863
assert data['literals'] == [v+1 for v in data['vertices']]
assert len(set(data['vertices'])) == 37
registers = {int(k):v for k,v in data['registers'].items()}
assert set(registers) == set(range(7278,8706))
assert all(v[0] == 'r' and v[1] == 8 for v in registers.values())
meaning = {v+1:['p',v] for v in range(512)} | registers
assert {abs(x) for c in data['clauses'] for x in c} <= set(meaning)
assert all(t[0] in {'first','zero','mono','step','over'} and t[1] == 8 for t in data['tags'])

def tree(r, s):
    if r+s > 8705:
        m = meaning.get(r)
        return '.z' if m is None else '(.' + ' '.join(map(str,m)) + ')'
    left, right = tree(r,2*s), tree(r+s,2*s)
    return '.z' if left == right == '.z' else f'(.n {left} {right})'

def natlist(xs):
    return '[' + ','.join(map(str,xs)) + ']'

source = '''import PairLower128

namespace Snake9.PairClauses128
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79
open Snake9.LocalWindow.Tags

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

-- These are certificate data for the added counter only.
def meaning : MT :=
  MEANING

def counter : Ctr := ⟨LITERALS,34,.ends⟩
def counters : List Ctr := List.replicate 8 dfltCtr ++ [counter]
def raw : List (List Nat) := [
RAW
]
def tags : List Tag := [
TAGS
]

theorem literal_check :
    counter.lits.all (posP meaning) = true ∧
    counter.lits.map (vl meaning) = VERTICES ∧ counter.k = 34 := by
  decide +kernel

#print axioms literal_check

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
      exact ⟨ha.1, ih ha.2⟩

GROUPS

theorem tags_checked : ckAll meaning counters [] tags raw = true := by
  change ckAll meaning counters [] (__T_JOIN__) (__R_JOIN__) = true
  exact __PROOF_CHAIN__

#print axioms tags_checked

private theorem checked_window (M : MT) (cs : List Ctr) (w : List Nat)
    (ts : List Tag) (rs : List (List Nat))
    (ht : ts.all (fun t => match t with
      | .first _ _ | .zero _ _ | .mono _ _ _ | .step _ _ _ | .over _ _ => true
      | _ => false) = true) :
    ckAll M cs w ts rs = ckAll M cs [] ts rs := by
  induction ts generalizing rs with
  | nil => cases rs <;> rfl
  | cons t ts ih =>
    cases rs with
    | nil => rfl
    | cons c rs =>
      simp only [List.all_cons, Bool.and_eq_true] at ht
      have hr := ih rs ht.2
      cases t <;> simp_all [ckAll,ckClause]

-- Every tag is a counter tag, hence the checker result is independent of the window.
theorem tags_checked_window (w : List Nat) :
    ckAll meaning counters w tags raw = true := by
  rw [checked_window meaning counters w tags raw (by decide +kernel)]
  exact tags_checked

#print axioms tags_checked_window

theorem actual_pair_clauses {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hP : ∀ j, j < 7 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2,4] : List Nat).getD j 0) :
    cnfTrue (tau (sel p (amap P (vx p r))) (frameE p P (vx p r))
      meaning counters) (raw.map (·.map decodeLit)) = true := by
  have hg := PairLower128.actual_counter_good p P r hr hshape hP
    (frameE p P (vx p r)) meaning counter
    literal_check.1 literal_check.2.1 literal_check.2.2
  have hv : JointTags.Valid (sel p (amap P (vx p r)))
      (frameE p P (vx p r)) meaning counters := by
    apply JointTags.valid_of_all
    intro ct hc
    have hmem : ct = dfltCtr ∨ ct = counter := by simpa [counters] using hc
    rcases hmem with rfl | rfl
    · simp [JointTags.Good,dfltCtr]
    · exact hg
  have hc : Canon (winOf [0,1,2,0,3,2,4]) [0,1,2,0,3,2,4] := canon_winOf _
  have hb : ∀ i, i < ([(0,21),(0,21),(0,21),(0,21),(0,21),(0,21)] : List (Nat × Nat)).length →
      (([(0,21),(0,21),(0,21),(0,21),(0,21),(0,21)] : List (Nat × Nat)).getD i (0,21)).1 ≤
        coreAlpha p (r+i+1) ∧ coreAlpha p (r+i+1) ≤
      (([(0,21),(0,21),(0,21),(0,21),(0,21),(0,21)] : List (Nat × Nat)).getD i (0,21)).2 := by
    intro i hi
    change i < 6 at hi
    have upper := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp_all [Nat.add_assoc]
  have ax := frame_axioms p P r hc (by decide) hr hP hb
  exact JointTags.sound meaning counters _ _ tags raw
    (tags_checked_window _) _ _ hv ax

#print axioms actual_pair_clauses
end Snake9.PairClauses128
'''
source = source.replace('MEANING',tree(0,1)).replace('LITERALS',natlist([2*x for x in data['literals']]))
source = source.replace('VERTICES',natlist(data['vertices']))
source = source.replace('RAW',',\n'.join('  '+natlist([2*abs(x)+(x<0) for x in c]) for c in data['clauses']))
source = source.replace('TAGS',',\n'.join('  (.'+' '.join(map(str,t))+')' for t in data['tags']))
parts = []
count = (len(data['clauses'])+63)//64
for i in range(count):
    tags = '[' + ','.join('(.'+' '.join(map(str,t))+')' for t in data['tags'][64*i:64*(i+1)]) + ']'
    raw = '[' + ','.join(natlist([2*abs(x)+(x<0) for x in c]) for c in data['clauses'][64*i:64*(i+1)]) + ']'
    parts.append(f'private def ts{i} : List Tag := {tags}\nprivate def rs{i} : List (List Nat) := {raw}\nprivate theorem checked{i} : ckAll meaning counters [] ts{i} rs{i} = true := by decide +kernel\n')
source = source.replace('GROUPS','\n'.join(parts))
source = source.replace('__T_JOIN__',' ++ '.join('ts'+str(i) for i in range(count)))
source = source.replace('__R_JOIN__',' ++ '.join('rs'+str(i) for i in range(count)))
chain = f'checked{count-1}'
for i in reversed(range(count-1)):
    chain = f'(checked_append meaning counters [] checked{i} {chain})'
source = source.replace('__PROOF_CHAIN__',chain)
source = re.sub(r'(?m)^(private )?def ',lambda m:(m.group(1) or '')+'noncomputable def ',source)
path = HERE / 'lean/PairClauses128.lean'
previous_sha256 = sha(path) if path.exists() else None
assert previous_sha256 in {None,'8c46fe4b97412da891a6717815b1b5d4bb4eb2d548779c18e5d3500c1f8aeb0f','669f339956bf0aefbb59600b6606afdaf6e345b82ffc505ce8c9917491d4b692'}, 'Preserve any later source revision.'
path.write_text(source,encoding='utf-8',newline='\n')
record = dict(status='GENERATED_NOT_YET_LEAN_CHECKED',
    source=str(path),source_sha256=sha(path),generator_sha256=sha(__file__),
    previous_source_sha256=previous_sha256,optimization='Noncomputable certificate data, empty-tree compression,64-clause checked groups; unchanged raw data and kernel checks.',
    counter_data_sha256=sha(data_path),preparation_sha256=sha(HERE/'data/preparation.json'),
    clauses=2863,counter_index=8,first_new_variable=7278,last_new_variable=8705,
    all_clause_variables_in_selected_or_new_registers=True,
    scope='The pair-only certificate keeps counter8 and primary/register variable numbers. Older counters are dummy and old auxiliary variables absent. This does not certify the preceding101666 clauses or their conjunction.')
(HERE/'audit/concrete-pair-generation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
