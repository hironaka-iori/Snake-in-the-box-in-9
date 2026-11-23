"""Hybrid hidden-bit/colour SAT model for fixed visible Q9 trajectories."""
import argparse, itertools, json, random
from pathlib import Path
from collections import Counter
from pysat.solvers import Solver
here=Path(__file__).resolve().parent
def vertices(word):
    p=[0]
    for x in word:p.append(p[-1]^(1<<int(x)))
    return p
def norm(word,axes):
    def form(w):
        labels={}
        return bytes(9 if int(x) in axes else labels.setdefault(int(x),len(labels)) for x in w)
    return min(form(word),form(word[::-1]))
def good(p):
    return len(set(p))==len(p) and all(0<=v<512 for v in p) and all(((a^b).bit_count()==1)==(i+1==j) for (i,a),(j,b) in itertools.combinations(enumerate(p),2))
def prepare(word,axes):
    p=vertices(word);mask=sum(1<<i for i in axes);visible=[v&~mask for v in p];ids=[0];hidden=[]
    for x in map(int,word):
        ids.append(ids[-1]+int(x in axes))
        if x in axes:hidden.append(x)
    requirements={};buckets={}
    for i,(v,t) in enumerate(zip(visible,ids)):
        for q in [v]+[v^(1<<i) for i in range(9) if not mask>>i&1]:
            for j,s in buckets.get(q,[]):
                if j==i-1:continue
                need=2-(v!=q)
                if (t-s)%2==0:need=2
                elif need==1:continue
                else:need=3
                if t-s<need:return None
                requirements[(s,t)]=need
        buckets.setdefault(v,[]).append((i,t))
    return visible,ids,hidden,requirements
def solve(word,axes,budget):
    inst=prepare(word,axes)
    if inst is None:return 'UNSAT',0,None,0
    visible,ids,history,req=inst;d=len(axes);N=len(history)+1;nextid=0;clauses=[];phases=[]
    def new():
        nonlocal nextid
        nextid+=1;return nextid
    bits=[[new() for _ in axes] for k in range(N)]
    for b in bits[0]:clauses.append([-b])
    colors=[{v:new() for v in range(1<<d) if v.bit_count()%2==k%2} for k in range(N)]
    for k,D in enumerate(colors):
        clauses.append(list(D.values()))
        for v,l in D.items():
            for j,b in enumerate(bits[k]):clauses.append([-l,b if v>>j&1 else -b])
    # First occurrences of hidden transition labels are ordered. Track which
    # coordinates have appeared so the search retains a representative of every orbit.
    used=[None]*d;catalog={};original=0
    for k,x in enumerate(history):
        labels=[new() for _ in axes];clauses.append(labels)
        clauses.extend([-a,-b] for a,b in itertools.combinations(labels,2))
        for j,change in enumerate(labels):
            u,v=bits[k][j],bits[k+1][j]
            clauses.extend([[-u,-v,-change],[u,v,-change],[u,-v,change],[-u,v,change]])
            if j>0:
                if not k:clauses.append([-change])
                else:clauses.append([-change,prev_used[j-1]])
            new_used=new()
            if not k:clauses.extend([[change,-new_used],[-change,new_used]])
            else:clauses.extend([[-used[j],new_used],[-change,new_used],[used[j],change,-new_used]])
            used[j]=new_used
        prev_used=used.copy()
        coordinate=catalog.setdefault(x,len(catalog));phases.append(labels[coordinate]);phases.append(colors[k][original]);original^=1<<coordinate
    phases.append(colors[-1][original])
    for (k,h),need in req.items():
        for v,a in colors[k].items():
            if need==2:clauses.append([-a,-colors[h][v]])
            else:clauses.extend([-a,-colors[h][v^(1<<j)]] for j in range(d))
    with Solver(name='cadical195',bootstrap_with=clauses) as sat:
        sat.set_phases(phases);sat.conf_budget(budget);s=sat.solve_limited();conf=sat.accum_stats()['conflicts']
        if s is not True:return ('UNSAT' if s is False else 'UNKNOWN'),conf,None,len(req)
        pos=set(sat.get_model())
    labels=[next(v for v,l in row.items() if l in pos) for row in colors]
    w=[x|sum(1<<axes[j] for j in range(d) if labels[k]>>j&1) for x,k in zip(visible,ids)]
    assert good(w)
    return 'FOUND',conf,w,len(req)
def original_word(p):return ''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]))
def old_keys(d):
    bank=[original_word(list(map(int,line.split()))) for line in (here.parent/'q9_threechord_one_paths.txt').read_text().splitlines()]
    hist=[json.loads(l) for l in (here.parent/f'q9_onechord_time{d}.jsonl').read_text().splitlines()]
    # Replay historical shuffled row/axis selections and projection deduplication.
    aset=list(itertools.combinations(range(9),d));order=list(range(len(bank)*len(aset)));random.Random(99).shuffle(order)
    allkeys=set()
    for index in order:
        row,j=divmod(index,len(aset));axes=aset[j];fingerprint=norm(bank[row],axes)
        if fingerprint in allkeys:continue
        rec=hist[len(allkeys)];assert row==rec[1] and tuple(rec[2])==axes
        allkeys.add(fingerprint)
        if len(allkeys)==len(hist):break
    return allkeys
def jobs(d,count,seed):
    words=(here.parent/'q9_three_axis.in').read_text().splitlines();rng=random.Random(seed)
    seen=old_keys(d);pool=set();axeslist=list(itertools.combinations(range(9),d));result=[]
    for _ in range(count*12):
        row=rng.randrange(len(words));w=words[row];axes=rng.choice(axeslist);key=norm(w,axes)
        if key in seen:continue
        seen.add(key);inst=prepare(w,axes)
        if inst is None:continue
        hidden=len(inst[2]);constraints=len(inst[3])
        # High hidden transition count and a low number of global contact
        # constraints per hidden-state pair give more room for alternative lifts.
        density=2*constraints/(hidden*(hidden+1))
        result.append((row,axes,hidden,density))
    result.sort(key=lambda x:(x[3],-x[2]))
    selected=result[:count//2]
    byhidden=sorted(result,key=lambda x:(-x[2],x[3]))
    taken={r[:2] for r in selected}
    for r in byhidden:
        if r[:2] not in taken:selected.append(r);taken.add(r[:2])
        if len(selected)>=count:break
    rng.shuffle(selected);return words,selected
def main():
    parser=argparse.ArgumentParser();parser.add_argument('d',type=int);parser.add_argument('count',type=int);parser.add_argument('seed',type=int);parser.add_argument('budget',type=int);parser.add_argument('--control',action='store_true');args=parser.parse_args()
    if args.control:
        control=json.loads((here.parent/'q9_weight_orbits_20261121/control.json').read_text())
        word=original_word(control['damaged']);axes=tuple(range(args.d));st,c,w,r=solve(word,axes,args.budget)
        assert st=='FOUND' and len(w)==192 and good(w)
        print(json.dumps(['control',args.d,word,axes,st,c,r,w]));return
    words,tests=jobs(args.d,args.count,args.seed);assert len(tests)==args.count
    for i,(row,axes,H,density) in enumerate(tests):
        st,c,w,r=solve(words[row],axes,args.budget)
        print(json.dumps([i,row,axes,H,r,st,c,w],separators=(',',':')),flush=True)
        if w:return
if __name__=='__main__':main()
