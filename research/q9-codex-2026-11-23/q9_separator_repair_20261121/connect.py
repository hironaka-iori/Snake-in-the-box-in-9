import itertools,json,sys,random
from collections import Counter
from prepare import D,R,words,majority,NB,graph,parts
from pysat.solvers import Minicard
def repair(A,c,budget):
    C=set(c['cut']);rm=set(c['remove']);add=set(c['added']);drop=set(c['drop']);new=set(c['new']);k=c['k']
    fixed=(A-drop)|add;allowed=(A-rm)|new;opt=allowed-fixed;cube=range(512)
    carriers={q for q in cube if q.bit_count()%2 and len(NB[q]&fixed)<=2<=len(NB[q]&allowed)}
    pairs={}
    for q in carriers:
        for x,y in itertools.combinations(sorted(NB[q]&allowed),2):
            if (NB[q]&fixed)-{x,y}:continue
            pairs.setdefault((x,y),[]).append(q)
    eid={k:1100+i for i,k in enumerate(pairs)};adj={x:[] for x in allowed}
    with Minicard() as s:
        def exact(l,k):
            if k<0 or k>len(l):s.add_clause([]);return
            s.add_atmost(l,k);s.add_atmost([-a for a in l],len(l)-k)
        exact([-(v+1) for v in sorted(drop-rm)],k-len(rm));exact([v+1 for v in sorted(new-add)],k-len(add))
        for q in c['qs']:
            if q not in carriers:return 'UNSAT',None
            s.add_clause([q+1])
        for q in carriers:
            n=2-len(NB[q]&fixed);vals=sorted(NB[q]&opt)
            for g in itertools.combinations(vals,n+1):s.add_clause([-(q+1),*[-(u+1) for u in g]])
        for (x,y),qs in pairs.items():
            z=eid[x,y]
            for v in (x,y):
                adj[v].append(z)
                if v in opt:s.add_clause([-z,v+1])
            s.add_clause([-z,*[q+1 for q in qs]])
        ends=[]
        for x in allowed:
            es=adj[x];eps=x+513;ends.append(eps);guard=[] if x in fixed else [-(x+1)]
            s.add_clause(guard+es)
            for z in es:s.add_clause(guard+[eps]+[v for v in es if v!=z])
        s.add_atmost(ends,2);root=c['ends'][0]
        while True:
            left=budget-s.accum_stats()['conflicts']
            if left<=0:return 'UNKNOWN',None
            s.conf_budget(left);ans=s.solve_limited()
            if ans is not True:return 'UNSAT' if ans is False else 'UNKNOWN',None
            model=set(s.get_model());B=fixed|{v for v in opt if v+1 in model};G=graph(B)
            assert len(B)==97 and len(A-B)==k and min(map(len,G.values()))>=1 and sum(len(y)==1 for y in G.values())<=2
            failed=False
            for cut in (set(),C):
                for group in parts(G,cut):
                    if root in group:continue
                    boundary=[eid[x,y] for x,y in pairs if x not in cut and y not in cut and ((x in group)!=(y in group))]
                    anchor=next(iter(group))
                    s.add_clause(([] if group&fixed else [-(anchor+1)])+boundary)
                    failed=True
            if not failed:return 'FOUND',sorted(B)
def main():
    gathered=list(map(json.loads,(D/'jobs.jsonl').read_text().splitlines()));rng=random.Random(47031);indices=list(range(len(gathered)));rng.shuffle(indices)
    for i in indices[:int(sys.argv[1])]:
        c=gathered[i];A=majority(words[c['row']]);k=max(1,len(c['remove']),len(c['added']))
        for count in (k,c['k']):
            st,B=repair(A,{**c,'k':count},3200)
            print(json.dumps([i,count,st,B],separators=(',',':')),flush=True)
if __name__=='__main__':main()
