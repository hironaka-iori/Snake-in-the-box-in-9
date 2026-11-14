"""Emit explicit propositional coverage proofs of the prepared finite models."""
from pathlib import Path
import argparse,hashlib,json
H=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--index',type=int);a=ap.parse_args();indices=range(254) if a.index is None else [a.index]
def lst(xs):return '['+','.join(map(str,xs))+']'
records=[]
for index in indices:
    p=H/'data'/('partition-'+str(index)+'.json');d=json.loads(p.read_bytes());cs=d['constraints'];initial=d['initial'];n=len(initial);leaves=[]
    def make(ds):
        ds=[x[:] for x in ds];steps=[];changed=True
        while changed:
            changed=False
            for e,c in enumerate(cs):
                for rev in [False,True]:
                    x,y=(c['right'],c['left']) if rev else (c['left'],c['right'])
                    for v in ds[x][:]:
                        if any(c['table'][b][v] if rev else c['table'][v][b] for b in ds[y]):continue
                        before=ds[x][:];steps.append((x,y,v,e,rev,before,ds[y][:]));ds[x].remove(v);changed=True
                        if not ds[x]:return dict(steps=steps,dead=x)
        if all(len(s)==1 for s in ds):
            leaf=[s[0] for s in ds]
            if leaf not in leaves:leaves.append(leaf)
            return dict(steps=steps,leaf=leaves.index(leaf))
        x=min((i for i,s in enumerate(ds) if len(s)>1),key=lambda i:(len(ds[i]),i));children=[]
        for v in ds[x]:
            nxt=[s[:] for s in ds];nxt[x]=[v];children.append((v,make(nxt)))
        return dict(steps=steps,variable=x,values=ds[x][:],children=children)
    tree=make(initial);counter=0
    def emit(t,bounds,indent):
        global counter
        bounds=bounds.copy();out=[]
        for x,y,v,e,rev,before,ys in t['steps']:
            counter+=1;bad='b'+str(counter);new='h'+str(counter)
            rel=f'(fun u v => edge r{e} v u)' if rev else f'(edge r{e})'
            out.append(indent+f'have {bad} : a {x} ≠ {v} := exclude {lst(ys)} {rel} (a {x}) (a {y}) {v} {bounds[y]} c{e} (by decide +kernel)')
            after=before[:];after.remove(v)
            out.append(indent+f'have {new} : a {x} ∈ {lst(after)} := remove (a {x}) {v} {lst(before)} {bounds[x]} {bad}')
            bounds[x]=new
        if 'dead' in t:
            x=t['dead'];out.append(indent+f'exact False.elim (impossible (a {x}) {bounds[x]})');return out
        if 'leaf' in t:
            j=t['leaf'];terms=[f'forced (a {i}) {v} {bounds[i]}' for i,v in enumerate(leaves[j])]
            proof=terms[-1]
            for term in terms[-2::-1]:proof=f'And.intro ({term}) ({proof})'
            if j<len(leaves)-1:proof='Or.inl ('+proof+')'
            for _ in range(j):proof='Or.inr ('+proof+')'
            out.append(indent+'exact '+proof);return out
        x=t['variable'];qs=['q'+str(counter+i+1) for i in range(len(t['values']))];counter+=len(qs)
        out.append(indent+'rcases (show '+' ∨ '.join(f'a {x}={v}' for v in t['values'])+f' from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using {bounds[x]}) with '+' | '.join(qs))
        for (v,ch),q in zip(t['children'],qs):
            counter+=1;hb='h'+str(counter);out.append(indent+f'· have {hb} : a {x} ∈ [{v}] := List.mem_singleton.mpr {q}')
            bs=bounds.copy();bs[x]=hb;out.extend(emit(ch,bs,indent+'  '))
        return out
    name='PartitionCover205_'+str(index)
    code='import FiniteDomain205\nnamespace '+name+'\nopen FiniteDomain205\nset_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n'
    for e,c in enumerate(cs):
        rows=[sum((1<<j) for j,b in enumerate(row) if b) for row in c['table']]
        code+=f'def r{e} : Array Nat := #'+lst(rows)+'\n'
    code+='theorem cover (a : Nat → Nat)\n'
    for i,ds in enumerate(initial):code+=f'    (start{i} : a {i} ∈ {lst(ds)})\n'
    for e,c in enumerate(cs):code+=f'    (c{e} : edge r{e} (a {c["left"]}) (a {c["right"]})=true)\n'
    code+='    : '+' ∨\n      '.join('('+' ∧ '.join(f'a {i}={v}' for i,v in enumerate(leaf))+')' for leaf in leaves)+' := by\n'
    code+='\n'.join(emit(tree,{i:'start'+str(i) for i in range(n)},'  '))+'\n#print axioms cover\nend '+name+'\n'
    target=H/'lean'/(name+'.lean')
    if target.exists():assert target.read_bytes()==code.encode('utf-8')
    else:target.write_bytes(code.encode('utf-8'))
    out=dict(index=index,leaves=leaves,proof_steps=counter,source_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scope='Finite encoded domain/compatibility coverage only. Actual cube-domain completeness, table interpretation and leaf isometry require separate proofs.')
    (H/'data'/('cover-'+str(index)+'.json')).write_text(json.dumps(out,indent=2)+'\n');records.append(out)
print('EMITTED',len(records),'coverage modules','steps',sum(r['proof_steps'] for r in records),'leaves',sum(len(r['leaves']) for r in records))
