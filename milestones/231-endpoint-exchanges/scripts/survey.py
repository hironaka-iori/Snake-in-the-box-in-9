"""Finite fixed-colour contraction survey; no order or crossing restriction."""
from pathlib import Path
import argparse,collections,hashlib,json,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--seconds',type=float,default=120);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
source=R/'milestones/203-block-symmetry/data/bank9-input.json';bank=json.loads(source.read_bytes())
N=[{v^(1<<j) for j in range(9)} for v in range(512)]
masks=[sum(1<<w for w in n) for n in N]
parts=[[v for v in range(512) if v.bit_count()%2==c] for c in range(2)]
bases={}
for i,row in enumerate(bank):
    p=row['vertex_sequence'];assert len(p)==len(set(p))==192
    assert all(((x^p[j]).bit_count()==1)==(j==k+1) for k,x in enumerate(p) for j in range(k+1,len(p)))
    for c in range(2):
        U=tuple(sorted(v for v in p if v.bit_count()%2==c));assert len(U)==96
        bases.setdefault(U,[]).append(dict(seed=i,parity=c))
out=dict(status='RUNNING',bank_size=len(bank),base_sets=len(bases),source=str(source),source_sha256=sha(source),script_sha256=sha(__file__),bases=[],cases=[],survivors=[],duplicates=[],witness=None,scope='All saved seed parity classes of96vertices enlarged by every possible same-parity vertex. Contract each opposite-parity vertex with exactlytwo neighbours in the97set to a labelled edge. Search graph endpoints are free. Static degree/connectivity exclusions are necessary Hamiltonian conditions, not Lean-certified finite certificates.')
seen={};started=time.monotonic()
for b,(base,origins) in enumerate(bases.items()):
    c=base[0].bit_count()%2;S=set(base);out['bases'].append(dict(id=b,vertices=base,origins=origins))
    for w in parts[c]:
        if w in S:continue
        if time.monotonic()-started>a.seconds:break
        U=tuple(sorted(S|{w}));key=bytes(x//256 for x in U)+bytes(x%256 for x in U)
        if key in seen:out['duplicates'].append(dict(base=b,added=w,case=seen[key]));continue
        ident=len(out['cases']);seen[key]=ident;mask=sum(1<<v for v in U)
        edges=[];adj={v:set() for v in U}
        for z in parts[1-c]:
            n=masks[z]&mask
            if n.bit_count()!=2:continue
            low=n&-n;v=low.bit_length()-1;t=(n^low).bit_length()-1
            edges.append([v,t,z]);adj[v].add(t);adj[t].add(v)
        row=dict(id=ident,base=b,added=w,vertices=97,edges=len(edges),simple_edges=sum(map(len,adj.values()))//2)
        isolated=[v for v in U if not adj[v]];leaves=[v for v in U if len(adj[v])==1]
        if isolated:row.update(status='ISOLATED',certificate=isolated)
        elif len(leaves)>2:row.update(status='TOO_MANY_LEAVES',certificate=leaves)
        else:
            reached={U[0]};stack=[U[0]]
            while stack:
                v=stack.pop()
                for t in adj[v]-reached:reached.add(t);stack.append(t)
            if len(reached)<97:row.update(status='DISCONNECTED',certificate=sorted(reached))
            else:
                row.update(status='OPEN',leaves=leaves)
                out['survivors'].append(dict(id=ident,vertices=U,edges=edges,leaves=leaves))
        out['cases'].append(row)
    else:continue
    break
out['status']='COMPLETE_SURVEY' if len(out['cases'])+len(out['duplicates'])==160*len(bases) else 'TIME_LIMIT'
out['statuses']=dict(collections.Counter(r['status'] for r in out['cases']));out['seconds']=time.monotonic()-started
dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','bank_size','base_sets','statuses','seconds']}),flush=True)
