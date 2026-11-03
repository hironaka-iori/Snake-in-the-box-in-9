"""Generate selected-clause semantics; no solver or Lean invocation."""
from pathlib import Path
import hashlib, importlib.util, json, sys

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
sys.dont_write_bytecode = True
helper = R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py'
spec = importlib.util.spec_from_file_location('semantics132_helper', helper)
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)
s = json.loads((H/'data/selected-core-semantics.json').read_text(encoding='utf-8-sig'))
meaning = {int(k): tuple(v) for k,v in s['meaning'].items()}
tags = s['base_tags']
raw = s['base_raw']
assert len(tags) == len(raw) == 676
units = [c[0] for c in s['endpoint_raw']]
assert all(len(c) == 1 for c in s['endpoint_raw']) and len(units) == 7
assert all(meaning[a//2][0] == 'e' and a%2 == 1 for a in units)
assert [meaning[a//2][1] for a in units] == [0,10,18,34,66,130,258]
assert s['counters'][0]['dummy'] and s['counters'][1]['upper'] == 9
pair = s['counters'][1]['literals']
assert len(pair) == 42 and len(set(pair)) == 37 and all(x < 0 for x in pair)
assert s['used_counter_indices'] == [1]

src = '''import Recovered132G.LocalWindowCnf.Endpoint132
import ActualCounters132

namespace Snake9.CoreSemantics132
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.LocalWindow.Tags

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable def meaning : MT :=
  '''+g.lean_tree_terms(meaning,max(meaning))+'''

noncomputable def counters : List Ctr := [dfltCtr,
  ⟨'''+str([g.code(x) for x in pair])+''',9,.ends⟩]

theorem pair_checked :
    (counters.getD 1 dfltCtr).lits.all (negP meaning) = true ∧
    ((counters.getD 1 dfltCtr).lits.map (vl meaning)).Perm
      (([⟨3,1,2,0,21⟩,⟨6,0,3,0,21⟩] : List Centre).flatMap corners) ∧
    (counters.getD 1 dfltCtr).k = 9 := by
  decide +kernel

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

'''
chunks = (len(raw)+63)//64
for n in range(chunks):
    a,b = 64*n, min(64*(n+1),len(raw))
    src += f'private noncomputable def ts{n} : List Tag := ['+','.join(g.lean_tag(t) for t in tags[a:b])+']\n'
    src += f'private noncomputable def rs{n} : List (List Nat) := '+str(raw[a:b])+'\n'
    src += f'private theorem checked{n} : ckAll meaning counters Endpoint132.window ts{n} rs{n} = true := by decide +kernel\n\n'
tags_expr = ' ++ '.join(f'ts{i}' for i in range(chunks))
raw_expr = ' ++ '.join(f'rs{i}' for i in range(chunks))
proof = 'checked0'
for i in range(1,chunks):
    proof = f'(checked_append meaning counters Endpoint132.window {proof} checked{i})'
src += f'''private noncomputable def tags : List Tag := {tags_expr}

theorem tags_checked : ckAll meaning counters Endpoint132.window tags Endpoint132.baseRaw = true := by
  change ckAll meaning counters Endpoint132.window ({tags_expr}) ({raw_expr}) = true
  exact {proof}

private noncomputable def units : List Nat := {units}

theorem units_checked : units.all (negE meaning) = true ∧
    units.map (vl meaning) = [0,10,18,34,66,130,258] := by
  decide +kernel

private theorem units_raw : Endpoint132.endpointRaw = units.map (fun a => [a]) := by rfl

theorem actual_satisfies_core {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+6 ≤ m)
    (hP : ∀ j, j < 6 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2] : List Nat).getD j 0)
    (hpair : coreAlpha p (r+2)+coreAlpha p (r+4) ≤ 9)
    (hnone : ∀ v ∈ ([0,10,18,34,66,130,258] : List Nat),
      frameE p P (vx p r) v = false) :
    ∃ τ : Nat → Bool, cnfTrue τ Endpoint132.cnf = true := by
  let S := sel p (amap P (vx p r))
  let E := frameE p P (vx p r)
  have ax : Axioms S E Endpoint132.window (centresOf Endpoint132.window Endpoint132.bounds) :=
    ActualCounters132.actual_window_axioms p P r hr hP
  have hg : JointTags.Good S E meaning (counters.getD 1 dfltCtr) :=
    ActualCounters132.actual_pair_counter_good p P r hr hP hpair E meaning
      (counters.getD 1 dfltCtr) pair_checked.1 pair_checked.2.1 pair_checked.2.2
  have hv : JointTags.Valid S E meaning counters := by
    apply JointTags.valid_of_all
    intro ct hc
    change ct ∈ [dfltCtr,counters.getD 1 dfltCtr] at hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · simp [JointTags.Good,dfltCtr]
    · exact hg
  refine ⟨tau S E meaning counters,?_⟩
  change cnfTrue (tau S E meaning counters)
    ((Endpoint132.baseRaw ++ Endpoint132.endpointRaw).map (·.map decodeLit)) = true
  unfold cnfTrue
  rw [List.all_map,List.all_eq_true]
  intro cl hcl
  rcases List.mem_append.mp hcl with hb | hu
  · exact JointTags.sound_all tags_checked hv ax cl hb
  · rw [units_raw] at hu
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
    have hn := List.all_eq_true.mp units_checked.1 a ha
    have hm : vl meaning a ∈ ([0,10,18,34,66,130,258] : List Nat) := by
      rw [← units_checked.2]
      exact List.mem_map.mpr ⟨a,ha,rfl⟩
    have hf : E (vl meaning a) = false := hnone _ hm
    change clauseTrue (tau S E meaning counters) [decodeLit a] = true
    apply List.any_eq_true.mpr
    refine ⟨decodeLit a,by simp,?_⟩
    rw [lit_negE hn,hf]
    rfl

theorem actual_frame_endpoint (hunsat : Unsat Endpoint132.cnf)
    {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+6 ≤ m)
    (hP : ∀ j, j < 6 → P.fwd (dir p (r+j)) =
      ([0,1,2,0,3,2] : List Nat).getD j 0)
    (hpair : coreAlpha p (r+2)+coreAlpha p (r+4) ≤ 9) :
    ∃ v, v ∈ ([0,10,18,34,66,130,258] : List Nat) ∧
      frameE p P (vx p r) v = true := by
  by_contra hn
  have hnone : ∀ v ∈ ([0,10,18,34,66,130,258] : List Nat),
      frameE p P (vx p r) v = false := by
    intro v hv
    cases he : frameE p P (vx p r) v with
    | false => rfl
    | true => exact False.elim (hn ⟨v,hv,he⟩)
  obtain ⟨τ,ht⟩ := actual_satisfies_core p P r hr hP hpair hnone
  rw [hunsat τ] at ht
  exact Bool.false_ne_true ht

#print axioms pair_checked
#print axioms tags_checked
#print axioms units_checked
#print axioms actual_satisfies_core
#print axioms actual_frame_endpoint
end Snake9.CoreSemantics132
'''
out = H/'lean/CoreSemantics132.lean'
with out.open('x',encoding='utf-8',newline='\n') as f:
    f.write(src)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipt = dict(status='GENERATED_LEAN_NOT_RUN',base_clauses=676,endpoint_units=7,
    counter_occurrences=42,counter_distinct_literals=37,used_counter_indices=[1],
    chunks=chunks,parity_premises=False,
    source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [Path(__file__),helper,H/'data/selected-core-semantics.json',out]},
    check_order=['ActualCounters132','Recovered132G.LocalWindowCnf.Endpoint132','CoreSemantics132',
        'Recovered132G.LocalWindowUnsat.Endpoint132','ActualEndpoint132'],
    limitations='Semantic source and final geometric assembly require successful Lean checks. No native solver or Lean process was started by this generator.')
with (H/'data/semantic-preparation.json').open('x',encoding='utf-8') as f:
    json.dump(receipt,f,indent=2); f.write('\n')
print(json.dumps(receipt,indent=2))
