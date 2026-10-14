"""Exhaustive endpoint regrowth within an explicitly restricted class."""
import json,time,argparse
from pathlib import Path

N=512
NB=[[v^(1<<k) for k in range(9)] for v in range(N)]
MASK=[sum(1<<w for w in ns) for ns in NB]

def regrow(seed, removed, node_limit):
    prefix=seed[:-removed] if removed else seed[:]
    used=sum(1<<v for v in prefix)
    blocked=used
    for v in prefix[:-1]:
        blocked |= MASK[v]
    nodes=0
    exhausted=False
    result=None
    trail=[]
    def dfs(head,occ,ban,remaining):
        nonlocal nodes,exhausted,result
        nodes+=1
        if nodes>node_limit:
            exhausted=True
            return False
        if remaining==0:
            result=prefix+trail[:]
            return True
        candidates=MASK[head]&~ban
        while candidates:
            bit=candidates&-candidates
            candidates-=bit
            nxt=bit.bit_length()-1
            trail.append(nxt)
            if dfs(nxt,occ|bit,ban|MASK[head]|bit,remaining-1):
                return True
            trail.pop()
            if exhausted:
                return False
        return False
    dfs(prefix[-1],used,blocked,193-len(prefix))
    return {'status':'FOUND' if result else 'UNKNOWN' if exhausted else 'INFEASIBLE',
            'nodes':nodes,'vertices':result}

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--removed',type=int,default=32)
    ap.add_argument('--nodes',type=int,default=200000)
    args=ap.parse_args()
    bank=json.loads(Path('work/bank9.json').read_text())
    results=[]
    begin=time.monotonic()
    for index,snake in enumerate(bank):
        for reverse in [False,True]:
            seed=snake['vertex_sequence'][::-1] if reverse else snake['vertex_sequence']
            r=regrow(seed,args.removed,args.nodes)
            r.update({'class_index':index,'reversed':reverse})
            results.append(r)
            if r['status']=='FOUND':
                from check_snake import verify
                vs=r['vertices']; shift=vs[0]
                check=verify([(u^v).bit_length()-1 for u,v in zip(vs,vs[1:])])
                assert check['vertex_sequence']==[v^shift for v in vs]
                break
        if results[-1]['status']=='FOUND': break
    report={'removed_vertices':args.removed,'fixed_prefix_vertices':192-args.removed,
            'target_edges':192,'elapsed_seconds':time.monotonic()-begin,
            'counts':{s:sum(r['status']==s for r in results) for s in ['FOUND','UNKNOWN','INFEASIBLE']},
            'total_nodes':sum(r['nodes'] for r in results),'results':results}
    Path(f'outputs/regrowth_{args.removed}.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2),flush=True)
