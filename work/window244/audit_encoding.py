"""Untrusted but reproducible structural audit and independent LRAT replay."""
import collections, hashlib, importlib.util, json, pathlib, sys
ROOT=pathlib.Path(__file__).resolve().parents[2]
SRC=ROOT/'milestones/07-window-223/scripts'
sys.path.insert(0,str(SRC))
from window_cnf import encode
from audit_window_encoding import replay

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out={}
for shape in ['repeated','distinct']:
    prefix=ROOT/f'milestones/07-window-223/data/window_223_{shape}_compact'
    data=json.loads(prefix.with_suffix('.json').read_text())
    original=json.loads((prefix.parent/f'window_223_{shape}_r3.json').read_text())
    assert data==encode(original,True),shape+' encoding differs'
    clauses=[list(map(int,l.split()[:-1])) for l in prefix.with_suffix('.cnf').read_text().splitlines() if l and not l.startswith(('p','c'))]
    assert clauses==data['clauses']
    core=json.loads(pathlib.Path(str(prefix)+'_core.json').read_text())
    for i,c,r in zip(core['original_clause_indices'],core['clauses'],core['reasons'],strict=True):
        assert c==data['clauses'][i-1] and r==data['reasons'][i-1]
    for reason in data['reasons']:
        if reason[0]=='cycle':
            cycle=reason[1]
            assert len(cycle)>=4 and len(set(cycle))==len(cycle)
            assert all(sum((a^b).bit_count()==1 for b in cycle)==2 for a in cycle)
    # Replay trimmed proof independently, using explicit unit propagation.
    db={i:c for i,c in enumerate(core['clauses'],1)}
    for ident,c,hints in core['proof']:
        assert ident not in db
        assignment={abs(l):l<0 for l in c};closed=False
        assert len(assignment)==len(c)
        for h in hints:
            assert h>0 and h in db
            clause=db[h]
            assert not any(assignment.get(abs(l))==(l>0) for l in clause if abs(l) in assignment)
            unknown=[l for l in clause if abs(l) not in assignment]
            assert len(unknown)<=1
            if not unknown:closed=True;break
            l=unknown[0];assignment[abs(l)]=l>0
        assert closed
        db[ident]=c
    assert core['proof'][-1][1]==[]
    out[shape]=dict(original_lrat=replay(str(prefix)),core_steps=len(core['proof']),
        core_clauses=len(core['clauses']),families=dict(collections.Counter(r[0] for r in data['reasons'])),
        variables=dict(collections.Counter('selected' if n.startswith('x') else 'endpoint' if n.startswith('end') else 'endpoint_counter' if n.startswith('prefix') else 'missing_counter' for n in data['variables'])),
        core_sha256=sha(pathlib.Path(str(prefix)+'_core.json')))
report=dict(status='PASSED_EXECUTABLE_AUDIT',evidence_level='Executable replay and structural checks; not a Lean geometric theorem',shapes=out,code_sha256=sha(pathlib.Path(__file__)))
(ROOT/'outputs/window244/encoding-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
