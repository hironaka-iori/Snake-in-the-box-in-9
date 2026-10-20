"""All 256 selected sets of Q3: compare the solver model to graph traversal."""
import hashlib, json, pathlib, subprocess, time
from research import solve_model
P=pathlib.Path(__file__).resolve().parents[1]; R=P.parents[1]
out=P/'runs/encoding-audit'; out.mkdir(exist_ok=False)
records=[]; start=time.monotonic()
for mask in range(256):
    selected=[i for i in range(8) if mask>>i&1]
    adj={v:[w for w in selected if (v^w).bit_count()==1] for v in selected}
    reached=set(); todo=selected[:1]
    while todo:
        v=todo.pop()
        if v not in reached:
            reached.add(v); todo.extend(adj[v])
    expected=(len(selected)>=2 and len(reached)==len(selected) and
              sum(len(adj[v])==1 for v in selected)==2 and all(1<=len(adj[v])<=2 for v in selected))
    spec={'n':3,'fixed_set':selected,'seconds':1}
    result=solve_model(spec,out/f'mask-{mask:03}.log')
    assert result['status'] in ['OPTIMAL','INFEASIBLE']
    assert (result['status']=='OPTIMAL')==expected,(mask,result['status'],expected)
    records.append({'mask':mask,'input':spec,'expected_path':expected,
                    'status':result['status'],'wall_seconds':result['wall_seconds'],
                    'model_sha256':result['model_sha256'],
                    'log_sha256':hashlib.sha256((out/f'mask-{mask:03}.log').read_bytes()).hexdigest()})
receipt={'status':'PASS','cases':len(records),'feasible':sum(r['expected_path'] for r in records),
         'scope':'Every subset of Q3, path must have at least two vertices; computational encoding audit',
         'git':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
         'code_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
         'model_code_sha256':hashlib.sha256((P/'scripts/research.py').read_bytes()).hexdigest(),
         'solver':result['solver'],'version':result['version'],'threads':1,'seed':20261020,
         'seconds':time.monotonic()-start,'results':records}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS',len(records),'cases;',receipt['feasible'],'path sets;',receipt['seconds'],'seconds')
