"""Independently count exact older-key alternatives and verify the next small core."""
from pathlib import Path
import ast,gzip,hashlib,io,json,re,subprocess,tarfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
PIN='7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(path):return subprocess.check_output(['git','-c','core.commitGraph=false','show',PIN+':'+path],cwd=ROOT)
def save_upstream(path,raw):
    p=HERE/'upstream'/path;p.parent.mkdir(exist_ok=True,parents=True)
    if p.exists():assert p.read_bytes()==raw
    else:p.write_bytes(raw)
union=json.loads((ROOT/'milestones/85-reference-catalogue-union/data/reference-union.json').read_text())['rows']
indices={(tuple(r['directions']),tuple(r['symbols'])):i for i,r in enumerate(union)}
roots={};keysets={};source_hashes={}
archive=subprocess.check_output(['git','-c','core.commitGraph=false','archive','--format=tar',PIN,
 'milestones/10-window-aggregate/data/lean_core_direction',
 'milestones/10-window-aggregate/data/lean_core_direction5'],cwd=ROOT)
with tarfile.open(fileobj=io.BytesIO(archive)) as t:
    metadata={m.name:t.extractfile(m).read() for m in t.getmembers() if m.isfile() and m.name.endswith('.json')}
selected_metadata={}
for family,suffix,expected in [('direction','',145),('direction5','5',175)]:
    texts={}
    for kind in ['Keys','Sat','Unsat']:
        path=f'work/final_lean/LocalWindowDir{kind}{suffix}.lean';raw=git(path)
        save_upstream(path,raw);source_hashes[path]=sha(raw);texts[kind]=raw.decode()
    keys=[(tuple(ast.literal_eval(a)),tuple(ast.literal_eval(b))) for a,b in
        re.findall(r'\(\s*(\[[\d, ]*\])\s*,\s*(\[[\d, ]*\])\s*\)',texts['Keys'])]
    proofroots=re.findall(r'\b(D\d+A\d+)\.unsat\b',texts['Unsat'])
    semantic=re.findall(r'Tags\.refuted_of_sat\s+(D\d+A\d+)\.sat\s+h\d+',texts['Sat'])
    assert len(keys)==expected and len(set(keys))==expected and proofroots==semantic and len(proofroots)==expected
    keysets[family]=set(keys)
    metas={}
    for path,raw in metadata.items():
        if Path(path).parent.name!='lean_core_'+family:continue
        m=json.loads(raw)
        if 'dirs' not in m or 'syms' not in m:continue
        key=(tuple(m['dirs']),tuple(m['syms']));metas[key]=(path,raw,m)
    assert set(keys)<=set(metas)
    for key,root in zip(keys,proofroots):
        path,raw,m=metas[key];selected_metadata[path]=raw
        assert m['module'].split('.')[-1]==root
        assert len(set(m['core_ids']))==len(m['core_ids']) and all(1<=i<=m['cnf_clauses'] for i in m['core_ids'])
        if key not in indices:continue
        row=dict(union_index=indices[key],directions=key[0],symbols=key[1],root=root,
            metadata_path=path,metadata_sha256=sha(raw),core_clauses=len(m['core_ids']),
            recorded_proof=m['lrat'],family=family,name=m['name'])
        roots.setdefault(key,[]).append(row)
assert len(selected_metadata)==320
digest=sha(''.join(path+' '+sha(raw)+'\n' for path,raw in sorted(selected_metadata.items())).encode())
assert digest=='8dc8dfe5b80754fdad2061ac8c9ed188cc382a92e69b09ee71e856265234b72d'
matches={k:len(v & set(indices)) for k,v in keysets.items()}
assert matches==dict(direction=90,direction5=134) and len(roots)==143
assert len(keysets['direction'] & keysets['direction5'] & set(indices))==81
all_candidates=[r for rs in roots.values() for r in rs]
best=min(all_candidates,key=lambda r:r['recorded_proof']['hints'])
assert best['union_index']==472 and best['root']=='D012304A22623' and best['core_clauses']==120
name=best['name'];meta=json.loads(metadata[best['metadata_path']]);save_upstream(best['metadata_path'],metadata[best['metadata_path']])
paths=[f'work/final_lean/LocalWindowCnf/{best["root"]}.lean',f'work/final_lean/LocalWindowSat/{best["root"]}.lean',
    f'milestones/10-window-aggregate/certificates/direction/{name}.cnf.gz']
saved={}
for path in paths:
    raw=git(path);save_upstream(path,raw);saved[path]=raw;source_hashes[path]=sha(raw)
cnf=gzip.decompress(saved[paths[-1]])
clauses=[[int(v) for v in line.split()[:-1]] for line in cnf.decode().splitlines() if line and not line.startswith(('p','c'))]
source=saved[paths[0]].decode()
body=source.split('def raw : List (List Nat) :=',1)[1].split('def cnf',1)[0].replace('noncomputable','').strip()
encoded=ast.literal_eval(body);decoded=[[v//2 if v%2==0 else -(v//2) for v in c] for c in encoded]
assert decoded==[clauses[i-1] for i in meta['core_ids']] and len(decoded)==120
assert len(clauses)==29055 and max(abs(x) for c in decoded for x in c)==2374
out=dict(status='EXACT_OLDER_ALTERNATIVES_NOT_REFUTATIONS',pin=PIN,catalogue_sizes={k:len(v) for k,v in keysets.items()},
    exact_matches=matches,distinct_matching_keys=143,additional_keys_after_first=142,
    metadata_count=320,metadata_hash_chain=digest,source_hashes=source_hashes,
    candidates=sorted(all_candidates,key=lambda r:(r['union_index'],r['family'])),next_candidate=best,
    next_candidate_clauses_match=True,next_candidate_full_cnf_sha256=sha(cnf),
    scope='Exact source keys, wrapper targets and metadata correspondence; next candidate raw-clause identity checked. No alternative root was solved or checked in Lean here.')
(HERE/'data/older-alternatives.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['candidates','source_hashes']},indent=2))
