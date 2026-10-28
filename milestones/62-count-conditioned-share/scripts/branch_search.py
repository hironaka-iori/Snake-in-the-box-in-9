"""Bounded cardinality case splits, recording only completed proof trees as candidates."""
from pathlib import Path
import itertools,json,math,time,sys
import propagate
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
edges=json.loads((ROOT/'milestones/61-critical-family-share/data/critical-edges.json').read_text())
summary=json.loads((HERE/'data/summary.json').read_text())['results']
def search(edge_id,target=24,limit=3000,seconds=10):
    e=edges[edge_id];W,C=propagate.setup(e);tree=[];start=time.monotonic()
    def visit(S,D):
        if len(tree)>=limit or time.monotonic()-start>seconds:return None
        r=propagate.closure(W,C,seed=(S,D));i=len(tree)
        tree.append(dict(selected=sorted(S),absent=sorted(D),closure=r))
        if r['status']=='CONTRADICTION':tree[i]['result']='CLOSED';return i
        if r['lower']>=target:tree[i]['result']='CREDIT';return i
        S=set(r['selected']);D=set(r['absent']);options=[]
        for k,c in enumerate(C):
            if c['lo']!=c['hi']:continue
            K=set(c['corners']);unknown=sorted(K-S-D);missing=c['lo']-len(K&D)
            if 0<missing<len(unknown):options.append((math.comb(len(unknown),missing),k,unknown,missing))
        if not options:tree[i]['result']='OPEN';return i
        size,k,unknown,missing=min(options)
        if size>200:tree[i]['result']='WIDE';return i
        tree[i]['split']=dict(constraint=k,unknown=unknown,missing=missing,choices=size)
        children=[]
        for absent in itertools.combinations(unknown,missing):
            A=set(absent);child=visit(S|(set(unknown)-A),D|A)
            if child is None:tree[i]['result']='LIMIT';break
            children.append(child)
            if tree[child]['result'] not in ['CLOSED','CREDIT','SPLIT_CLOSED']:
                tree[i]['result']='OPEN';break
        else:tree[i]['result']='SPLIT_CLOSED'
        tree[i]['children']=children
        return i
    root=visit(set(W),set());status=tree[0]['result']
    out=dict(edge=edge_id,target=target,status=status,nodes=len(tree),seconds=round(time.monotonic()-start,3),
             scope='A completed tree is a numerical candidate until Lean checks its case split and deductions; OPEN/WIDE/LIMIT prove nothing.')
    if status in ['CLOSED','CREDIT','SPLIT_CLOSED']:
        (HERE/'data/search-trees').mkdir(exist_ok=True)
        (HERE/f'data/search-trees/e{edge_id:02d}.json').write_text(json.dumps(dict(**out,tree=tree),indent=2)+'\n')
    return out
if __name__=='__main__':
    chosen=[int(x) for x in sys.argv[1:]] or [r['edge'] for r in summary if r['lower'] is not None and r['lower']<24]
    results=[]
    for i in chosen:
        result=search(i);results.append(result);print(result,flush=True)
        (HERE/'data/branch-search.json').write_text(json.dumps(results,indent=2)+'\n')
