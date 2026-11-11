from pathlib import Path
import collections,hashlib,itertools,json,time
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports';start=time.monotonic()
bank=json.loads((R/'work/bank9.json').read_text());seeds=json.loads((R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json').read_text())
def canonical(p):
    t=[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
    def relabel(xs):
        d={};out=[]
        for x in xs:
            if x not in d:d[x]=len(d)
            out.append(d[x])
        return tuple(out)
    return min(relabel(t),relabel(t[::-1]))
known={canonical(row['vertex_sequence']) for row in bank};records=[];valid=[];newclasses={};extensions=[]
def attempt(p,n,indices):
    q=p.copy()
    for i in indices:q[i]=p[i-1]^p[i]^p[i+1]
    chosen=set(q)
    if len(chosen)!=len(q):return None
    for i in indices:
        if {q[i]^(1<<k) for k in range(n)}&chosen!={q[i-1],q[i+1]}:return None
    assert all(((q[i]^q[j]).bit_count()==1)==(j==i+1) for i in range(len(q)) for j in range(i+1,len(q)))
    return q
def remember(q,n,description):
    valid.append(dict(description,path=q))
    if n==9:
        code=canonical(q)
        if code not in known:newclasses.setdefault(code,dict(description,path=q))
        chosen=set(q)
        for rev in [False,True]:
            r=q[::-1] if rev else q
            for k in range(n):
                v=r[-1]^(1<<k)
                if v not in chosen and all((v^u).bit_count()!=1 for u in r[:-1]):extensions.append(dict(description,path=r+[v]))
for n,paths in [(7,[seeds['7']['vertices']]),(8,[seeds['8']['vertices']]),(9,[r['vertex_sequence'] for r in bank])]:
    for index,p in enumerate(paths):
        moves=0;success=0;portcases=0;portsuccess=0;profiles=[]
        for i in range(1,len(p)-1):
            moves+=1;q=attempt(p,n,[i])
            if q is not None:success+=1;remember(q,n,{'dimension':n,'seed_index':index,'kind':'single_square','indices':[i]})
        for k in range(n):
            cuts=[i for i,(u,v) in enumerate(zip(p,p[1:])) if u^v==1<<k]
            if len(cuts)!=2:continue
            options=[[None]+([i] if i>0 else [])+([i+1] if i+1<len(p)-1 else []) for i in cuts]
            for pair in itertools.product(*options):
                indices=[i for i in pair if i is not None]
                if len(indices)!=2:continue
                assert abs(indices[0]-indices[1])>1
                portcases+=1;q=attempt(p,n,indices)
                if q is None:continue
                newcuts=[i for i,(u,v) in enumerate(zip(q,q[1:])) if u^v==1<<k];assert len(newcuts)==2
                portsuccess+=1;profile=[newcuts[0],newcuts[1]-newcuts[0]-1,len(q)-2-newcuts[1]];profiles.append({'coordinate':k,'component_edges':profile})
                remember(q,n,{'dimension':n,'seed_index':index,'kind':'paired_port_slide','coordinate':k,'indices':indices,'component_edges':profile})
        records.append({'dimension':n,'seed_index':index,'single_candidates':moves,'single_valid':success,'paired_candidates':portcases,'paired_valid':portsuccess,'paired_profiles':profiles})
        if extensions:break
out={'status':'COMPLETE' if not extensions else 'LONGER_WITNESS_FOUND','seconds':time.monotonic()-start,'summary':{str(n):{'seeds':sum(r['dimension']==n for r in records),'single_candidates':sum(r['single_candidates'] for r in records if r['dimension']==n),'single_valid':sum(r['single_valid'] for r in records if r['dimension']==n),'paired_candidates':sum(r['paired_candidates'] for r in records if r['dimension']==n),'paired_valid':sum(r['paired_valid'] for r in records if r['dimension']==n)} for n in [7,8,9]},'new_q9_classes':len(newclasses),'extensions':extensions,'rows':records,'scope':'All single two-edge square swaps in the displayed Q7/Q8 seeds and131 saved Q9 paths; all pairs of independent one-square port slides at coordinates crossed exactly twice. Canonicalization uses translation, coordinate permutation and reversal. Does not exhaust larger port moves.'}
(H/'data/port-moves.json').write_text(json.dumps(out,indent=2)+'\n');(H/'data/port-move-witnesses.json').write_text(json.dumps({'valid_moves':valid,'new_classes':list(newclasses.values()),'extensions':extensions},indent=2)+'\n');(H/'scripts/port_moves.py').write_bytes(Path(__file__).read_bytes());print(json.dumps({k:v for k,v in out.items() if k not in ['rows','extensions']},indent=2),flush=True)
