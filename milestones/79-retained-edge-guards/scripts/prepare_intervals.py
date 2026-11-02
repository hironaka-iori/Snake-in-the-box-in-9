"""Pin existing milestone72 proof objects and emit their graph guard assembly."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/72-four-count-proof-closure'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
audit=json.loads((OLD/'data/proof-audit.json').read_text())
assert audit['status']=='PASS_COMPLETED_CHAINS'
cases=audit['completed'];build=OLD/'build/950fed501ad64859af6f7f46cf3857db'
records={}
for f in (OLD/'logs').glob('build-record*.json'):
    r=json.loads(f.read_text())
    if Path(r['build'])==build:
        for row in r['records']:
            if row['exit_code']==0:records[row['module']]=row
assert records
modules={}
for case in cases:
    for name,digest in case['source_sha256'].items():
        source=OLD/'lean'/(name+'.lean');obj=build/(name+'.olean')
        assert sha(source)==digest==records[name]['source_sha256'],name
        log=OLD/'logs'/(name.replace('/','-')+'.log')
        assert obj.is_file()
        modules[name]=dict(source=str(source),source_sha256=digest,
            object=str(obj),object_sha256=sha(obj),log=str(log),log_sha256=sha(log))
# Pin any additional local Lean imports, including the shared LRAT checker.
todo=list(modules)
while todo:
    name=todo.pop()
    source=Path(modules[name]['source'])
    for line in source.read_text(encoding='utf-8-sig').splitlines():
        if not line.startswith('import '):continue
        for token in line.split()[1:]:
            dep=token.replace('.','/');src=OLD/'lean'/(dep+'.lean')
            if dep in modules or not src.is_file():continue
            obj=build/(dep+'.olean');assert obj.is_file(),dep
            assert dep in records and records[dep]['source_sha256']==sha(src),dep
            modules[dep]=dict(source=str(src),source_sha256=sha(src),object=str(obj),object_sha256=sha(obj))
            todo.append(dep)
out=dict(status='PINNED_EXISTING_INTERVAL_PROOFS',build=str(build),cases=[c['case'] for c in cases],
    upstream_audit_sha256=sha(OLD/'data/proof-audit.json'),modules=modules,
    scope='Existing source-matched objects, newly hashed. No clean replay of their full dependency closure.')
(HERE/'data/interval-support.json').write_text(json.dumps(out,indent=2)+'\n')
literal=lambda x:str(x).replace('(','(').replace(')',')')
src=['import IntervalGuards']+[f"import CycleExclusion{c['case']}" for c in cases]
src+=['','namespace Snake9.Guards79','open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow',
      'open Snake9.GraphWalk78','set_option maxHeartbeats 2000000','']
entries=[]
for c in cases:
    bounds='['+','.join(f'({a},{b})' for a,b in c['bounds'])+']'
    entries.append('('+literal(c['dirs'])+','+bounds+')')
src+=['def intervalKeys72 : List (List Nat × List (Nat × Nat)) := [',',\n'.join(entries),']','',
'''theorem interval_catalogue : ∀ key ∈ intervalKeys72,
    key.2.length = 4 ∧
    (∀ i, i < key.2.length → (key.2.getD i (0,21)).1 ≤ 6 ∧
      ((key.2.getD i (0,21)).2 < 6 ∨ (key.2.getD i (0,21)).2 = 21)) ∧
    Refuted (winOf key.1) key.2 := by
  intro key hk
  simp only [intervalKeys72, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with '''+' | '.join(['rfl']*len(cases))]
for c in cases:
    src+=['  · refine ⟨rfl, ?_, ?_⟩','    · intro i hi','      change i < 4 at hi',
          '      interval_cases i <;> decide',f"    · exact CycleWindow{c['case']}.refuted"]
src+=['', '''theorem interval_forward_retention {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 2) :
    ∀ key ∈ intervalKeys72,
      canon (((canon (dsOf p r 9)).drop (s+2)).take 5) = key.1 →
      ¬ intervalHit (sixCode p r) s 4 false key.2 := by
  intro key hk hshape hhit
  obtain ⟨hlen,hends,href⟩ := interval_catalogue key hk
  exact encoded_interval_forward_exclusion p r s 4 hr (by omega) (by omega)
    key.1 key.2 hlen hends href hshape hhit

theorem interval_reverse_retention {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 2) :
    ∀ key ∈ intervalKeys72,
      canon ((((canon (dsOf p r 9)).drop (s+2)).take 5).reverse) = key.1 →
      ¬ intervalHit (sixCode p r) s 4 true key.2 := by
  intro key hk hshape hhit
  obtain ⟨hlen,hends,href⟩ := interval_catalogue key hk
  exact encoded_interval_reverse_exclusion p r s 4 hr (by omega) (by omega)
    key.1 key.2 hlen hends href hshape hhit

#print axioms interval_catalogue
#print axioms interval_forward_retention
#print axioms interval_reverse_retention
end Snake9.Guards79
''']
(HERE/'lean/IntervalCatalogue.lean').write_text('\n'.join(src))
print('Pinned',len(modules),'interval proof modules; emitted ten-case guard assembly')
import runpy
runpy.run_path(str(HERE/'scripts/pin_lrat14.py'))
