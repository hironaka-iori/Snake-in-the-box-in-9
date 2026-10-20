"""Find a surviving 7/2 cycle after extending direction memory to eight.

This is a small search for an obstruction to improvement, not a full automaton build.
Only the frozen 175-window mask is used. All supplied cycles are checked explicitly.
"""
import hashlib, json, pathlib, subprocess, time
from research import canon, induced, window_key
P=pathlib.Path(__file__).resolve().parents[1]; R=P.parents[1]
D=R/'milestones/10-window-aggregate/data/direction_certificates_k5p.json'
FORB={(tuple(x['dirs']),tuple(map(tuple,x['alpha']))) for x in json.loads(D.read_text())['cases']}

def search(counts,L):
    shapes=[()]
    for _ in range(L):
        shapes=[s+(d,) for s in shapes for d in range(max(s,default=-1)+2) if induced(s+(d,))]
    graph={}
    for s in shapes:
        for phase in range(len(counts)):
            edges=[]
            for d in range(min(9,max(s)+2)):
                ds=s+(d,)
                if not induced(ds): continue
                if any(window_key(ds[-k-1:],[counts[(phase-k+1+t)%len(counts)] for t in range(k)]) in FORB
                       for k in range(2,6)): continue
                edges.append(((canon(ds[1:]),(phase+1)%len(counts)),d))
            graph[(s,phase)]=edges
    active={}; done=set(); chain=[]; es=[]; result=None
    def dfs(u):
        nonlocal result
        active[u]=len(chain); chain.append(u)
        for v,d in graph[u]:
            if result: break
            if v in active:
                result=es[active[v]:]+[(u,v,d)]; break
            if v not in done:
                es.append((u,v,d)); dfs(v); es.pop()
        chain.pop(); active.pop(u); done.add(u)
    for u in graph:
        if not result and u not in done: dfs(u)
    return {'counts_tested':counts,'direction_memory':L,'shapes':len(shapes),
            'status':'CYCLE_FOUND' if result else 'NO_CYCLE_FOR_THIS_PERIOD',
            'cycle':None if not result else [{'shape':u[0],'append_label':d,'count':counts[u[1]],
                                             'next_shape':v[0]} for u,v,d in result]}

start=time.monotonic()
results=[]
for counts in [[1,6],[6,3,3,2],[4,2,6,2,4,3],[2,3,6,2,2,6],[2,6],[3,4]]:
    z=search(counts,8); results.append(z)
    print(counts,z['status'],flush=True)
    if z['cycle']:
        assert 2*sum(e['count'] for e in z['cycle'])==7*len(z['cycle'])
        break
out={'git':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
     'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
     'dependency_sha256':hashlib.sha256((P/'scripts/research.py').read_bytes()).hexdigest(),
     'index_sha256':hashlib.sha256(D.read_bytes()).hexdigest(),
     'threads':1,'seed':None,'solver':'none','time_limit':None,'seconds':time.monotonic()-start,
     'experiments':results,
     'meaning':'A surviving 7/2 cycle prevents a strictly larger asymptotic mean after this refinement alone; it is not a real snake.'}
(P/'runs/value-gate.json').write_text(json.dumps(out,indent=2)+'\n')
print('seconds',out['seconds'])
