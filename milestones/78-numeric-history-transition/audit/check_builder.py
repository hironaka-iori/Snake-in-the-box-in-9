"""Compare the exact builder assignments with the proved strict-scan algorithm."""
from pathlib import Path
import ast,hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
builder=ROOT/'milestones/70-proof-supported-share-model/scripts/build.py'
metadata=ROOT/'milestones/67-critical-family-charge/data/full-model.json'
tables=ROOT/'milestones/77-direction-state-coverage/data/tables.json'
md=json.loads(metadata.read_text());tb=json.loads(tables.read_text())
prefixes=[tuple(p) for p in md['prefixes']]
assert len(prefixes)==75 and prefixes[0]==() and len(set(prefixes))==75
nodes=[]
for node in ast.walk(ast.parse(builder.read_text())):
    if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in {'hist','choices','nq'}:
        nodes.append(node)
nodes.sort(key=lambda n:(n.lineno,n.col_offset))
assert [n.targets[0].id for n in nodes]==['hist','choices','nq']
code=compile(ast.Module(body=nodes,type_ignores=[]),str(builder),'exec')
next_bytes=bytearray();nonempty=0;compatible=0;fallback=0
for q,prefix in enumerate(prefixes):
    for di in range(505):
        env=dict(prefixes=prefixes,prefix=prefix,di=di)
        exec(code,env)
        hist=prefix+(di,);best=0
        for j,p in enumerate(prefixes):
            eligible=bool(p) and len(p)<=len(hist) and hist[len(hist)-len(p):]==p
            if eligible and len(prefixes[best])<len(p):best=j
        actual=env['nq'];assert actual==best and 0<=actual<75
        choices=env['choices']
        if choices:
            maxlen=max(len(prefixes[j]) for j in choices)
            maxima=[j for j in choices if len(prefixes[j])==maxlen]
            assert maxima==[best]
        else:assert best==0;fallback+=1
        nonempty+=best!=0;next_bytes.append(best)
        if q==0 or md['compatible_shapes'][q]==tb['source_ids'][di]:
            compatible+=1
            if best:assert md['compatible_shapes'][best]==tb['target_ids'][di]
assert len(next_bytes)==37875
assert md['states']==1601856
base=json.loads((ROOT/'milestones/59-extended-share-window/extended/data/model.json').read_text())
assert base['states']==132*7776==1026432
(HERE/'data/history-next.u8').write_bytes(next_bytes)
result=dict(status='PASS_EXACT_BUILDER_SELECTOR_COMPARISON',input_pairs=len(next_bytes),nonempty_updates=nonempty,
    fallback_updates=fallback,source_compatible_pairs=compatible,unique_maximum=True,
    output_layout='row major q=0..74, directionID=0..504; one unsigned byte per next-history index',
    output_sha256=sha(HERE/'data/history-next.u8'),builder_sha256=sha(builder),metadata_sha256=sha(metadata),
    ordered_direction_tables_sha256=sha(tables),extracted_assignments=[ast.unparse(n) for n in nodes],
    limits='Executable comparison of exact Python assignments and the strict scan; Lean checks the scan theorem separately. No retained-edge or weight audit.')
(HERE/'data/builder-comparison.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],len(next_bytes),'pairs;',nonempty,'nonempty;',compatible,'source-compatible')
