"""Search the saved 191-edge bank for actual all-four runs; verify each path."""
import hashlib,itertools,json
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
path=ROOT/'work/bank9.json';bank=json.loads(path.read_text());best=0;examples=[];pairs=list(itertools.combinations(range(9),2))
for k,row in enumerate(bank):
    vs=row['vertex_sequence'];S=set(vs);assert len(vs)==len(S) and all(0<=v<512 for v in vs)
    for i,a in enumerate(vs):
        for j in range(i+1,len(vs)):assert ((a^vs[j]).bit_count()==1)==(j==i+1)
    alpha=[sum(all(v not in S for v in (c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b))) for a,b in pairs) for c in vs]
    run=0
    for j in range(1,len(vs)-1):
        run=run+1 if alpha[j]==4 else 0
        if run>best:
            best=run;examples=[dict(bank_index=k,start=j-run+1,length=run,counts=alpha[j-run+1:j+1],vertices=vs)]
        elif run==best and run>0 and len(examples)<3:examples.append(dict(bank_index=k,start=j-run+1,length=run,counts=alpha[j-run+1:j+1]))
out=dict(bank_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),verified_snakes=len(bank),maximum_run_found=best,examples=examples,
         scope='Finite bank observation, not an upper bound for all snakes.')
(HERE/'data/bank-runs.json').write_text(json.dumps(out,indent=2)+'\n');print(len(bank),best,flush=True)
