"""Audit the endpoint search condition; this does not replay a contradiction."""
from pathlib import Path
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages')]
from wincert import Encoding
from gen_lean_sat import TaggedEncoding
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(((R/'milestones/121-replacement-window-pressure/data/endpoint-probes')).glob('*.json')):
    a=read(p);assert a['radius']==9 and a['cycle_cuts']==[]
    assert a['status']=='UNSAT_UNCERTIFIED' and a['selected'] is None
    assert a['script_sha256']==sha(R/'milestones/121-replacement-window-pressure/scripts/probe_endpoint.py')
    for f,d in a['source_files_sha256'].items():assert sha(R/f)==d
    window=[0]
    for k in a['directions']:window.append(window[-1]^(1<<k))
    centres=[window[2],window[4]]
    common=[v for v in range(512) if all((v^c).bit_count()==2 for c in centres)]
    assert window==a['window'] and centres==a['counted_centres'] and common==a['common_sphere']
    assert len(common)==14
    enc=Encoding(window,[tuple(b) for b in a['bounds']],9)
    tagged=TaggedEncoding(window,[tuple(b) for b in a['bounds']],9)
    assert enc.clauses==tagged.clauses and enc.nv==tagged.nv
    outside=[513+v for v in range(512) if v not in common]
    assert all(tagged.meaning[513+v]==('e',v) for v in range(512))
    assert outside==a['outside_endpoint_flags']
    clauses=enc.clauses+[outside]
    assert len(clauses)==a['clauses'] and enc.nv==a['variables']
    raw=(f'p cnf {enc.nv} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)).encode()
    name='end'+p.stem[-2:]
    plan=read(H/'data'/(name+'-plan.json'));solver=read(H/'data'/(name+'-solver.json'))
    assert (H/'work'/name/(name+'.cnf')).read_bytes()==raw
    assert hashlib.sha256(raw).hexdigest()==plan['cnf_sha256']==solver['cnf_sha256']
    assert sha(H/'work'/name/(name+'.lrat'))==plan['lrat_sha256']
    assert sha(H/'work'/name/'raw.lrat')==solver['raw_sha256']
    assert plan['script_sha256']==sha(H/'scripts/certify_endpoint.py')
    assert solver['status']=='NATIVE_UNSAT_LEAN_PENDING' and solver['exit_code']==20
    assert plan['generation']['hints']==plan['hints']
    for row in plan['ports']:
        src=H/row['original'];dst=H/row['isolated']
        assert sha(src)==row['source_sha256'] and sha(dst)==row['isolated_sha256']
        assert dst.read_text().replace('import Recovered122G.','import ')==src.read_text()
    rows.append(dict(probe=p.relative_to(R).as_posix(),sha256=sha(p),bounds=a['bounds'],cnf_sha256=hashlib.sha256(raw).hexdigest(),variables=enc.nv,clauses=len(clauses),common_sphere=common,endpoint_clause_size=len(outside),native_lemmas=plan['lemmas'],native_hints=plan['hints'],modules=len(plan['modules']),status=solver['status'],seconds=solver['seconds']))
out=H/'data/certificate-input-audit.json';assert not out.exists()
out.write_text(json.dumps(dict(status='PASS_ENDPOINT_CERTIFICATE_INPUTS_AND_EXPORTS',probes=rows,script_sha256=sha(Path(__file__)),scope='Plain and tagged base clauses coincide; the added clause demands an actual endpoint flag outside the intersection of the two exact distance-two spheres. Native RUP export simulations completed; this audit checks inputs, provenance and ports. Lean replay receipts are audited separately. The universal endpoint theorem remains pending.'),indent=2)+'\n',encoding='utf-8')
print('Checked endpoint-condition encodings:',len(rows))
