"""Compare contracted optimization with an independent exhaustive subset oracle."""
import itertools,json,random,time
from pathlib import Path
from contracted import HERE,sha,check,solve
def all_path_sets(n):
    size=1<<n;answer=[]
    for mask in range(1,1<<size):
        vertices=[v for v in range(size) if mask>>v&1]
        if len(vertices)<2:continue
        adj={v:[w for w in vertices if (v^w).bit_count()==1] for v in vertices}
        if sum(len(a)==1 for a in adj.values())!=2 or any(len(a) not in (1,2) for a in adj.values()):continue
        reached={vertices[0]};todo=[vertices[0]]
        while todo:
            v=todo.pop()
            for w in adj[v]:
                if w not in reached:reached.add(w);todo.append(w)
        if len(reached)==len(vertices):answer.append(mask)
    return answer
def main():
    begin=time.monotonic();rng=random.Random(192);results=[]
    scenarios=[(2,[0,1,3],list(range(16))),(3,[0,1,3],list(range(256))),(3,[0,1,3,7,6],list(range(256))),(4,[0,1,3,7,6],sorted({0,65535,*rng.sample(range(65536),62)}))]
    cache={}
    for n,seed,masks in scenarios:
        check(seed,n)
        if n not in cache:cache[n]=all_path_sets(n)
        seedmask=sum(1<<v for v in seed);full=(1<<(1<<n))-1
        for region in masks:
            outside=full^region
            expected=max(mask.bit_count()-1 for mask in cache[n] if mask&outside==seedmask&outside)
            inside={v for v in range(1<<n) if region>>v&1}
            r=solve(n,seed,inside,3)
            assert r['status']=='OPTIMAL' and r['edges']==expected,(n,seed,region,expected,r)
            results.append({'n':n,'seed':seed,'region_mask':region,'oracle_edges':expected,'model_edges':r['edges'],'internal_vertices':r['contracted_internal_vertices']})
        print(json.dumps({'n':n,'seed_edges':len(seed)-1,'cases':len(masks),'status':'PASSED'}),flush=True)
    report={'status':'PASSED','script_sha256_lf':sha(Path(__file__)),'model_sha256_lf':sha(HERE/'scripts/contracted.py'),'cases':results,'seconds':time.monotonic()-begin,'scope':'Exhaustive induced-subset oracle in dimensions 2,3,4; all regions for Q2/Q3 scenarios and 64 deterministic Q4 regions. Finite controls, not a general proof of contraction equivalence.'}
    (HERE/'data').mkdir(exist_ok=True,parents=True);(HERE/'data/small-controls.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
if __name__=='__main__':main()
