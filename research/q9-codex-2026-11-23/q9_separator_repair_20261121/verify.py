"""Independent graph construction from Hamming-distance-two pairs and Hamilton SAT replay."""
import json,itertools,collections
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
D=Path(__file__).resolve().parent;R=D.parent
def permitted(A):
    g={a:set() for a in A}
    for x,y in itertools.combinations(sorted(A),2):
        mask=x^y
        if mask.bit_count()!=2:continue
        for u in (x^(mask&-mask),y^(mask&-mask)):
            if sum((u^(1<<i)) in A for i in range(9))==2:g[x].add(y);g[y].add(x);break
    return g
def components(g,remove):
    rest=set(g)-set(remove);result=[]
    while rest:
        q=[min(rest)];rest.remove(q[0])
        for v in q:
            for x in sorted(rest&g[v]):rest.remove(x);q.append(x)
        result.append(set(q))
    return result
def demand(G,C):
    groups=components(G,C);tips={v for v,ns in G.items() if len(ns)==1}
    return len(groups),len(C&tips)+sum(max(len(tips&g),2-min(2,len(set.union(*(G[v] for v in g))&C))) for g in groups)
def old_ok(G):
    extra=sum(max(0,sum(len(G[v])<=2 for v in ns)-2) for ns in G.values())
    return len(components(G,set()))==1 and all(G.values()) and sum(len(ns)==1 for ns in G.values())<=2 and extra<=2 and sum(map(len,G.values()))>=2*(len(G)-1)
def hamilton(G):
    dummy=512;adj={v:ns|{dummy} for v,ns in G.items()};adj[dummy]=set(G);pool=IDPool();edges={(v,w):pool.id() for v in sorted(adj) for w in sorted(x for x in adj[v] if x>v)}
    def eid(v,w):return edges[min(v,w),max(v,w)]
    clauses=[]
    for v,ns in adj.items():clauses.extend(CardEnc.equals([eid(v,w) for w in sorted(ns)],2,vpool=pool,encoding=EncType.seqcounter).clauses if len(ns)>=2 else [[]])
    with Solver(name='cadical195',bootstrap_with=clauses) as s:
        cuts=0
        while s.solve():
            pos=set(s.get_model());h={v:{w for w in ns if eid(v,w) in pos} for v,ns in adj.items()}
            groups=components(h,set())
            if len(groups)==1:return True,cuts
            for group in groups:
                s.add_clause([-eid(v,w) for v in group for w in h[v] if w>v]);cuts+=1
        return False,cuts
def good(p):
    return all(0<=x<512 for x in p) and len(set(p))==len(p) and all(((a^b).bit_count()==1)==(i+1==j) for (i,a),(j,b) in itertools.combinations(enumerate(p),2))
def majority(w):
    x=0;A={0}
    for i,d in enumerate(map(int,w)):
        x^=1<<d
        if i%2:A.add(x)
    return A
def lines(file):return list(map(json.loads,(D/file).read_text().splitlines()))
def main():
    words=(R/'q9_three_axis.in').read_text().splitlines();source={tuple(sorted(majority(w))) for w in words}
    certs=lines('certificates.jsonl')
    for c in certs:
        A=majority(words[c['row']]);G=permitted(A);C=set(c['cut']);groups=components(G,C);n,need=demand(G,C)
        assert old_ok(G) and {frozenset(g) for g in groups}=={frozenset(g) for g in c['components']} and sum(c['demand'])+len(C&set(c['leaves']))==need and (need>2 or n>len(C)+1)
    positive=[]
    for fname in ('control.json','strong_control.json'):
        c=json.loads((D/fname).read_text());p=c['witness'];assert good(p) and len(p)==191
        h=permitted(set(p[::2]));assert hamilton(h)[0];positive.append(len(set(c['damaged'])-set(p[::2])))
    relaxed=lines('mosaic_plans.jsonl');wideplans=lines('broadfamilies.jsonl')
    draws=[(r[3],relaxed[r[0]]) for r in lines('mosaic.jsonl') if r[2]=='FOUND']
    draws.extend((r[3],wideplans[r[0]][1]) for r in lines('connected_wide.jsonl') if r[2]=='FOUND')
    seen=set();total=0
    for B,c in draws:
        A=majority(words[c['row']]);B=set(B);C=set(c['cut']);G=permitted(B);g=permitted(A);gs=components(g,C)
        assert len(B)==97 and len(A-B)==c['k'] and set(c['remove'])<=A-B and set(c['added'])<=B-A
        assert set(c['ends'])<=B and C<=B and len(components(G,C))==len(components(G,set()))==1 and sum(len(ns)==1 for ns in G.values())<=2
        for q in c['qs']:assert sum((q^(1<<i)) in B for i in range(9))==2
        assert any(set(c['ends'])&s for s in gs) and sum(bool(set(c['ends'])&s) for s in gs)>=2
        key=tuple(sorted(B))
        if key in seen:continue
        seen.add(key);sat,cuts=hamilton(G);assert not sat;total+=cuts
    extra=0
    for l in (D/'repairs.sets').read_text().splitlines():
        n,*pts=map(int,l.split());assert n==len(pts)==97
        sat,k=hamilton(permitted(set(pts)));assert not sat;extra+=1
    assert (D/'resolved_exact.log').read_text().splitlines()==['NO']*len(seen) and (D/'repair_exact.log').read_text().splitlines()==['NO']*extra
    print(json.dumps(dict(root_certificates=len(certs),distinct_input_majorities=len(source),positive_swaps=positive,corrected_assignments=len(draws),unique_corrected=len(seen),corrected_not_in_input_as_labelled=len(seen-source),replayed_hamilton_unsat=len(seen),subtour_cuts=total,other_cover_replays=extra),indent=2))
if __name__=='__main__':main()
