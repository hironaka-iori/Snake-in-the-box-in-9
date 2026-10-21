"""Emit a kernel-checkable applicability pilot for the exact core's gate clauses.

The Python trace is untrusted metadata. Lean checks the resulting clauses under
the displayed meanings and window units. This is not full CNF applicability.
"""
import collections
import json
import re
import sys
import runner

HERE=runner.HERE
ROOT=runner.ROOT

def square(q):
    v=min(q)
    ds=[i for i in range(9) if v^(1<<i) in q]
    assert len(ds)==2
    a,b=ds
    assert sorted(q)==sorted([v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)])
    return f'(square {v} {a} {b})'

def main():
    manifest=runner.read(HERE/'runtime/manifest.json')
    runner.validate(manifest)
    src=HERE/'build/frozen/upstream/scripts/share_enc.py'
    text=src.read_text(encoding='utf-8')
    # Record each fresh gate's geometric arguments without changing any clauses.
    for g,kind in [('g1','one'),('g3','zero')]:
        old=f'{g} = self.fresh()'
        assert text.count(old)==1
        text=text.replace(old,old+f'; self.gvars[{g}] = ("{kind}", Q, P)')
    sys.path.insert(0,str(src.parent))
    namespace={'__name__':'parallel_gate_trace','__file__':str(src)}
    exec(compile(text,str(src),'exec'),namespace)
    rec=manifest['cases'][1]
    window=namespace['window_from_dirs'](rec['dirs'])
    enc=namespace['ShareEncoding'](window,[(0,21)]*6,3,20,counter='stot',exact=True)
    cuts=runner.read(HERE/'build/frozen/upstream/data/share/final_a_X20.jsonl.cuts.json')
    for cut in cuts[','.join(map(str,rec['dirs']))]:enc.add_cycle_cut(cut)
    cnf=(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode('ascii')
    assert runner.hashbytes(cnf)==rec['cnf_sha256']
    mapping=runner.read(HERE/'data/kernel-pilot-01-mapping.json')
    ids=mapping['original_variable_ids']; inverse={v:i+1 for i,v in enumerate(ids)}
    compact=[]
    for ci in mapping['original_clause_ids']:
        compact.append([2*inverse[abs(v)]+int(v<0) for v in enc.clauses[ci-1]])
    core_path=HERE/'lean/LocalWindowCnf/ParallelShare01.lean'
    body=core_path.read_text().split('noncomputable def raw : List (List Nat) := ',1)[1].split('\n',1)[0]
    assert compact==json.loads(body)
    meanings={v:f'(.sel {q})' for q,v in enc.var.items()}
    meanings.update({v:square(q) for q,v in enc.esq.items()})
    for v,(kind,q,p) in enc.gvars.items():
        meanings[v]=f'({kind} {square(q)} '+' '.join(map(str,p))+')'
    selected=[i for i,ci in enumerate(mapping['original_clause_ids']) if enc.kinds[ci-1]
        in ['empty->unselected','selected_or_empty','g1_def','g3_def']]
    kinds=collections.Counter(enc.kinds[mapping['original_clause_ids'][i]-1] for i in selected)
    assert dict(kinds)=={'selected_or_empty':2,'g1_def':4}
    mean='['+', '.join('some '+meanings[v] if v in meanings else 'none' for v in ids)+']'
    source=f'''import ParallelShareBoolean
import LocalWindowCnf.ParallelShare01

/-! Exact gate-clause subset of the committed Boolean pilot. Totalizer and
degree clauses still require their separate applicability proofs. -/
namespace Snake9.LocalWindow.ParallelShare01GatePilot
open Snake9.ParallelShareBoolean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def window : List Nat := {window}
def meanings : List (Option Formula) := {mean}
def meaning (n : Nat) : Option Formula := meanings.getD (n - 1) none
def indices : List Nat := {selected}
noncomputable def gateCnf : List (List Int) :=
  indices.map fun i => (ParallelShare01.raw.getD i []).map decodeLit

theorem checked : gateCnf.all (checkClause 8 window meaning) = true := by decide +kernel

theorem gates_sound (S : Nat → Bool) (hw : ∀ v ∈ window, S v = true) :
    cnfTrue (assignment meaning S) gateCnf = true :=
  checkClauses_sound 8 window meaning gateCnf checked S hw

/-- Removing the empty-square alternative from the first actual clause is rejected. -/
theorem rejects_missing_empty_bit :
    checkClause 8 window meaning ((gateCnf.getD 0 []).drop 1) = false := by decide +kernel

#print axioms checked
#print axioms gates_sound
#print axioms rejects_missing_empty_bit
end Snake9.LocalWindow.ParallelShare01GatePilot
'''
    dest=HERE/'lean/LocalWindowSat/ParallelShare01Gates.lean'
    dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(source,encoding='utf-8',newline='\n')
    receipt=dict(scope='Six exact square/gate core clauses only; full arbitrary-snake applicability remains unresolved',
        cnf_sha256=rec['cnf_sha256'],encoder_sha256=runner.digest(src),
        core_source_sha256=runner.hashbytes(core_path.read_text().replace('\r\n','\n').encode()),
        mapping_sha256=runner.digest(HERE/'data/kernel-pilot-01-mapping.json'),
        generated_source_sha256=runner.digest(dest),window=window,indices=selected,
        original_clause_ids=[mapping['original_clause_ids'][i] for i in selected],
        kinds=dict(kinds),generated_at=runner.now())
    runner.atomic(HERE/'data/parallel-share-gate-pilot-inputs.json',receipt)
    print(json.dumps(receipt))

if __name__=='__main__':main()
