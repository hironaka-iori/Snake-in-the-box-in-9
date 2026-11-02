"""Count syntactically identical proposed checks; this is not a Lean certificate."""
from pathlib import Path
import hashlib, json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cp=ROOT/'milestones/101-context-specialization/data/generated-contexts.json'
bp=ROOT/'milestones/102-potential-block-reduction/data/candidates.json'
data=read(cp);blocks=read(bp)['blocks'];result={}
for profile in ['completed','conditional']:
    groups={}
    for c in data['contexts']:
        key=(c['root'],blocks[profile][c['source_base']//7776],
            blocks[profile][c['target_base']//7776],c['geometric'],
            tuple(c['selected']),c['conditioned'],c[profile])
        groups.setdefault(key,[]).append([c['direction'],c['history']])
    result[profile]=dict(contexts=len(data['contexts']),unique_checks=len(groups),
        duplicate_contexts=sum(len(v)-1 for v in groups.values()),
        groups=[dict(key=list(k[:4])+[list(k[4]),k[5],k[6]],contexts=v) for k,v in groups.items()])
out=dict(status='NUMERICAL_SOURCE_GROUPING_ONLY',inputs_sha256={p.relative_to(ROOT).as_posix():sha(p) for p in [cp,bp]},
    profiles=result,scope='Potential roots, acceptance root and exact weight-expression inputs agree within each group. Reuse still requires the generated Lean theorem to elaborate and pass the kernel.')
(HERE/'data/group-analysis.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
for p,r in result.items():print(p,r['contexts'],r['unique_checks'],r['duplicate_contexts'])
