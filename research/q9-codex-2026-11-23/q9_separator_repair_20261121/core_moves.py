import itertools,json,random
from prepare import D,NB,graph
from solve import solve
from pysat.formula import IDPool
from pysat.card import EncType,CardEnc
from pysat.solvers import Solver
def possible(G,core,edges=()):
    core=set(core);use=set(G)|set(v for pair in edges for v in pair)
    neigh={x:set(G.get(x,()))|{512} for x in use};neigh[512]=use
    for x,y in edges:neigh[x].add(y);neigh[y].add(x)
    pool=IDPool();formula=[]
    for x in sorted(core):
        lits=[pool.id(tuple(sorted((x,y)))) for y in sorted(neigh[x])]
        if len(lits)<2:return False
        formula.extend(CardEnc.equals(lits,2,vpool=pool,encoding=EncType.seqcounter).clauses)
    with Solver(name='cadical195',bootstrap_with=formula) as s:return s.solve()
def plans(A,core,rng):
    G=graph(A);critical=set(core)-{512}
    assert not possible(G,core)
    candidates=[]
    for x in sorted(critical):
        for q in sorted(NB[x]):
            B=NB[q]&A
            for y in sorted(B-{x}):
                if y in G[x]:continue
                rm=B-{x,y}
                if not rm or rm&critical or len(rm)>5:continue
                candidates.append(([(x,y)],[q],rm,set(),{x,y}))
            # Release a new majority vertex adjacent by an admissible
            # two-step edge to a core vertex. A second mediator supports it.
            for z in sorted(NB[q]-A):
                for h in sorted(NB[z]-{q}):
                    actual=NB[h]&A
                    for y in sorted(actual-{x}):
                        if y in B or x in actual:continue
                        rm=(B-{x})|(actual-{y})
                        if rm&critical or len(rm)>5:continue
                        candidates.append(([(x,z),(z,y)],[q,h],rm,{z},{x,y}))
    rng.shuffle(candidates);candidates.sort(key=lambda t:len(t[2]))
    out=[];types=set();seen={}
    for es,qs,rm,added,ends in candidates:
        key=tuple(sorted(tuple(sorted(e)) for e in es))
        if key not in seen:seen[key]=possible(G,core,es)
        if not seen[key]:continue
        token=len(qs),len(rm)
        if token in types:continue
        types.add(token);out.append((es,qs,rm,added,ends))
        if len(out)==5:break
    return out
def main():
    rows=[set(map(int,l.split()[1:])) for l in (D/'resolved.sets').read_text().splitlines()]
    cores=list(map(json.loads,(D/'degree_cores.jsonl').read_text().splitlines()));rng=random.Random(62899);jobs=[];concrete=[]
    for idx,core in cores:
        if idx%2:continue
        A=rows[idx];G=graph(A)
        for es,qs,rm,added,ends in plans(A,core,rng):
            locked=(set(core)-{512})|ends;ban=set.union(*(NB[q] for q in qs))-ends-added
            if (A&ban)!=rm:continue
            oth=list(sorted(A-rm-locked));rng.shuffle(oth)
            eligible=[v for v in range(512) if v.bit_count()%2==0 and v not in A|ban|added]
            rng.shuffle(eligible);eligible.sort(key=lambda v:min((v^u).bit_count() for u in locked))
            drop=sorted(rm|set(oth[:37]));new=sorted(added|set(eligible[:58]));small=max(1,len(rm),len(added))
            for k in sorted({small,max(5,small)}):
                c=dict(qs=qs,ends=sorted(ends),cut=[],remove=sorted(rm),added=sorted(added),drop=drop,new=new,k=k)
                jobs.append(dict(index=idx,core=core,edges=es,c=c))
                for _ in range(40):
                    deleted=rm|set(rng.sample(sorted(set(drop)-rm),k-len(rm)));born=added|set(rng.sample(sorted(set(new)-added),k-len(added)));B=(A-deleted)|born
                    GG=graph(B)
                    if not possible(GG,core):continue
                    concrete.append([len(jobs)-1,sorted(B)]);break
    (D/'core_jobs.jsonl').write_text(''.join(json.dumps(c,separators=(',',':'))+'\n' for c in jobs))
    (D/'core_concrete.jsonl').write_text(''.join(json.dumps(c,separators=(',',':'))+'\n' for c in concrete))
    for i,r in enumerate(jobs):
        st,n,co,w=solve(rows[r['index']],r['c'],9500);print(json.dumps([i,st,co,w],separators=(',',':')),flush=True)
        if w:return
if __name__=='__main__':main()
