"""Audit the checked coverage module, pinned support, and catalogue identity."""
from pathlib import Path
import ast,collections,hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
source=HERE/'lean/SixShapeCoverage.lean';text=source.read_text();record=read(HERE/'logs/build-record.json');support=read(HERE/'data/support.json')
assert record['exit_code']==0
assert record['source_sha256']==sha(source)
assert record['support_record_sha256']==sha(HERE/'data/support.json')
assert record['olean_sha256']==sha(HERE/'build/SixShapeCoverage.olean')
assert sha(Path(support['receipt_path']))==support['receipt_sha256']
for r in support['modules']:
    pinned=HERE/'upstream'/(r['module']+'.lean')
    assert sha(pinned)==r['source_sha256']
    assert sha(Path(r['olean_path']))==r['olean_sha256']
    assert sha(Path(r['inherited_log_path']))==r['inherited_log_sha256']
    assert not re.search(r'\b(sorry|admit|native_decide)\b',pinned.read_text())
assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
log=(HERE/'logs/SixShapeCoverage.log').read_text()
assert all(x not in log for x in ['error:','sorryAx','failed to delete'])
rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)+[(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
assert len(rows)==len(re.findall(r'^#print axioms ',text,re.M))==4
checks=[]
for name,axioms in rows:
    axs=re.findall(r'[A-Za-z][\w.]*',axioms)
    assert set(axs)<={'propext','Classical.choice','Quot.sound'}
    checks.append(dict(theorem=name,axioms=axs))
reps=ast.literal_eval(re.search(r'def representatives : List \(List Nat\) :=\s*(.*?)\n\ndef represented',text,re.S).group(1))
catalogue=ROOT/'milestones/72-four-count-proof-closure/critical-current/data/all-six-direction-shapes.json'
saved=read(catalogue);assert reps==saved['up_to_reversal']
def rgs(n,bound=0):
    if not n:yield ();return
    for a in range(bound+1):
        for tail in rgs(n-1,max(bound,a+1)):yield (a,)+tail
def induced(w):
    return all(sum(n%2 for n in collections.Counter(w[i:j]).values())>1 for i in range(len(w)) for j in range(i+2,len(w)+1))
allwords=list(rgs(6));valid=[list(w) for w in allwords if induced(w)]
assert len(allwords)==203 and valid==saved['oriented'] and len(valid)==12
out=dict(status='PASS_SIX_TRANSITION_COVERAGE',source_sha256=sha(source),olean_sha256=record['olean_sha256'],theorem_audits=checks,
    representatives=reps,representatives_match_catalogue=True,catalogue_sha256=sha(catalogue),
    enumeration_crosscheck=dict(restricted_growth_words=203,induced_orientations=12,scope='Independent Python cross-check of enumeration sizes; universal coverage itself is checked by the Lean theorem.'),
    normalization_support_record_sha256=sha(HERE/'data/support.json'),
    scope='Lean-checked finite canonical coverage and actual-snake canonical six-transition window coverage, including canonical reversal. Coordinate adapters to the nine local share statements and the larger history graph remain separate. Existing normalization and cube support was reused after source and artifact hash checks; no full inherited rebuild is claimed.')
(HERE/'data/proof-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(checks),'theorem audits;203-word table;actual-snake canonical coverage.',flush=True)
