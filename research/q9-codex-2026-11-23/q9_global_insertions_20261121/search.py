"""Choose insertion locations globally while freely rebuilding four hidden bits."""
import argparse,itertools,json,random
from pathlib import Path
from pysat.solvers import Solver
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
here=Path(__file__).resolve().parent
NB=[[v^(1<<i) for i in range(9)] for v in range(512)]
def path(word):
    p=[0]
    for d in map(int,word):p.append(p[-1]^(1<<d))
    return p
def clean(p):
    if len(set(p))!=len(p) or not all(0<=v<512 for v in p):return False
    seen=set()
    for i,v in enumerate(p):
        if i and not (p[i-1] in NB[v] and sum(x in seen for x in NB[v])==1):return False
        seen.add(v)
    return True
def encode(word,axes,extras,budget,control_hint=None,return_clauses=False):
    p=path(word);mask=sum(1<<d for d in axes);S=len(extras);L=len(word);T=L+S;offsets=[0]
    for x in extras:offsets.append(offsets[-1]^(0 if x<0 else 1<<x))
    pool=IDPool(start_from=513);f=[];phase=[];times=[];states=[];occ=[[] for _ in NB]
    def amo(lits):
        if len(lits)<=6:f.extend([-a,-b] for a,b in itertools.combinations(lits,2))
        else:f.extend(CardEnc.atmost(lits,bound=1,vpool=pool,encoding=EncType.seqcounter).clauses)
    colors=[[v for v in range(512) if not(v&~mask) and v.bit_count()%2==par] for par in (0,1)]
    # State k means k additional steps have been taken. At global time t the
    # trace has consumed exactly t-k source steps.
    for t in range(T+1):
        st={k:pool.id() for k in range(max(0,t-L),min(t,S)+1)}
        f.append(list(st.values()));amo(list(st.values()))
        if states:
            for k,z in states[-1].items():f.append([-z,*[st[a] for a in (k,k+1) if a in st]])
        states.append(st);support={}
        for k,tag in st.items():
            fixed=(p[t-k]&~mask)^offsets[k]
            for c in colors[(t^fixed.bit_count())&1]:support.setdefault(fixed|c,[]).append(tag)
        if t==0:support={0:support[0]}
        D={v:pool.id() for v in support};times.append(D);f.append(list(D.values()));amo(list(D.values()))
        for v,z in D.items():
            f.append([-z,*support[v]]);f.append([-z,v+1]);occ[v].append(z)
        for k,tag in st.items():
            f.append([-tag,*[D[v] for v,tags in support.items() if tag in tags]])
    for t,row in enumerate(times):
        prev=times[t-1] if t else {};nxt=times[t+1] if t<T else {}
        for v,z in row.items():
            if nxt:f.append([-z,*[nxt[x] for x in NB[v] if x in nxt]])
            if prev:f.append([-z,*[prev[x] for x in NB[v] if x in prev]])
            for x in NB[v]:
                if occ[x]:f.append([-z,-(x+1),*[D[x] for D in (prev,nxt) if x in D]])
    for v,z in enumerate(occ):
        if z:amo(z);f.append([-(v+1),*z])
    if control_hint is not None:
        witness,indices=control_hint
        for t,v in enumerate(witness):
            k=sum(i<t for i in indices)
            assert v in times[t] and k in states[t]
            phase.extend((times[t][v],states[t][k]))
    else:
        # Choose a coherent starting assignment, without constraining insertion sites.
        idx=[(k+1)*T//(S+1) for k in range(S)]
        add=[];bits=0
        for k,x in enumerate(extras):bits^=(1<<axes[k%4]) if x<0 else 1<<x;add.append(bits)
        for t in range(T+1):
            k=sum(i<t for i in idx);v=p[t-k]^(add[k-1] if k else 0)
            if v in times[t]:phase.extend((times[t][v],states[t][k]))
    if return_clauses:return f
    with Solver(name='cadical195',bootstrap_with=f) as solver:
        solver.set_phases(phase);solver.conf_budget(budget);ans=solver.solve_limited();stats=solver.accum_stats()
        if ans is not True:return ('UNKNOWN' if ans is None else 'UNSAT'),stats['conflicts'],None,None
        model=set(solver.get_model())
    out=[next(v for v,z in row.items() if z in model) for row in times];kvals=[next(k for k,z in st.items() if z in model) for st in states]
    inserted=[i for i,(a,b) in enumerate(zip(kvals,kvals[1:])) if a!=b]
    assert len(out)==T+1 and clean(out) and len(inserted)==S
    assert all((v&~mask)==((p[t-k]&~mask)^offsets[k]) for t,(k,v) in enumerate(zip(kvals,out)))
    return 'FOUND',stats['conflicts'],out,inserted
def jobs(L,salt,count):
    words=(here.parent/f'q9_gap_generations/prior{L}.words').read_text().splitlines()
    rng=random.Random(salt);result=[];seen=set()
    for i in range(count):
        while True:
            row=rng.randrange(len(words));axes=tuple(sorted(rng.sample(range(9),4)));vis=[d for d in range(9) if d not in axes];S=192-L
            if S==1:kinds=[-1] if i%2==0 else [rng.choice(vis)]
            elif i%4==0:kinds=[-1,-1]
            elif i%4==1:kinds=[rng.choice(vis),-1]
            elif i%4==2:kinds=[-1,rng.choice(vis)]
            else:kinds=[rng.choice(vis),rng.choice(vis)]
            key=(row,axes,tuple(kinds))
            if key not in seen:break
        seen.add(key);result.append(key)
    return words,result
def control():
    words=(here.parent/'q9_gap_generations/prior191.words').read_text().splitlines()
    word=words[0];target=path(word)
    assert clean(target)
    for S in (1,2):
        chosen=None
        for row,word in enumerate(words):
            target=path(word)
            candidates=[(i,) for i in range(1,190)] if S==1 else [(i,j) for i in range(3,188) for j in (0,190)]
            candidates.sort(key=lambda x:abs(x[0]-95))
            for idx in candidates:
                idx=tuple(sorted(idx))
                seed=''.join(d for i,d in enumerate(word) if i not in idx)
                if clean(path(seed)):chosen=(seed,idx,word,target);break
            if chosen:break
        if chosen is None:raise RuntimeError('no clean shortened control')
        seed,idx,word,target=chosen;keep=int(word[idx[0]]);omit=int(word[idx[1]]) if S==2 else -1
        axes=tuple(sorted([keep]+[a for a in range(9) if a not in (keep,omit)][:3]))
        extra=[-1 if int(word[i]) in axes else int(word[i]) for i in idx]
        # The known witness is only used to establish that the instance is satisfiable.
        st,c,w,sites=encode(seed,axes,extra,80000)
        assert st=='FOUND' and w is not None
        print(json.dumps([S,row,idx,seed,axes,extra,st,c,sites,w]),flush=True)
    # A second two-step control specifically combines hidden and visible additions.
    word=words[0];idx=(0,1);seed=word[2:];axes=(0,2,3,4);extra=[-1,int(word[1])]
    assert int(word[0]) in axes and extra[1] not in axes and clean(path(seed))
    st,c,w,sites=encode(seed,axes,extra,80000)
    assert st=='FOUND'
    print(json.dumps([2,0,idx,seed,axes,extra,st,c,sites,w]),flush=True)
if __name__=='__main__':
    import sys
    if sys.argv[1]=='control':control()
    else:
        L,count,salt,budget=map(int,sys.argv[1:]);words,tests=jobs(L,salt,count)
        for i,(r,axes,extras) in enumerate(tests):
            assert clean(path(words[r]));st,c,w,loc=encode(words[r],axes,extras,budget)
            print(json.dumps([i,r,axes,extras,st,c,loc,w],separators=(',',':')),flush=True)
            if w:break
