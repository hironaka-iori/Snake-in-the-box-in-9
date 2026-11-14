"""Prepare fixed absolute-map domains and exact finite compatibility tables."""
from pathlib import Path
import ast,collections,hashlib,itertools,json,math,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sourcecode=R/'milestones/204-cyclic-symmetry/scripts/slice_image_census.py'
tree=ast.parse(sourcecode.read_text(encoding='utf-8'));names={'pack','unpack','relative','canon','valid'}
scope={'itertools':itertools,'math':math};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names],type_ignores=[]),str(sourcecode),'exec'),scope)
pack,unpack,relative,canon,valid=(scope[n] for n in ['pack','unpack','relative','canon','valid'])
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
seedfile=H/'data/lower-dimensional-input.json';v=json.loads(seedfile.read_bytes())['8']['vertices'];start=time.monotonic();records=[]
for m in range(1,8):
    for basecoords in itertools.combinations(range(8),m):
        blockcoords=[x for x in range(8) if x not in basecoords];k=8-m;vertices=[(pack(x,basecoords),pack(x,blockcoords)) for x in v];fibres={}
        for z,u in vertices:fibres.setdefault(z,set()).add(u)
        occupied=sorted(fibres);fi={z:i for i,z in enumerate(occupied)};rels={};edgeinfo=[]
        for z in occupied:
            for w in occupied:
                if z>=w or (z^w).bit_count()!=1 or not fibres[z]&fibres[w]:continue
                ts,info=relative(fibres[z],fibres[w],k);rels[z,w]=ts
                inverses=[]
                for t in ts:
                    inv=[0]*len(t)
                    for i,j in enumerate(t):inv[j]=i
                    inverses.append(tuple(inv))
                rels[w,z]=inverses
        root=occupied[0];domains={root:[tuple(range(1<<k))]};parents=[]
        while len(domains)<len(occupied):
            _,z,w=min((len(domains[w])*len(rels[w,z]),z,w) for z in occupied if z not in domains for w in domains if (w,z) in rels)
            ds=[];seen={};cover=[]
            for parent in domains[w]:
                row=[]
                for r in rels[w,z]:
                    g=tuple(parent[r[u]] for u in range(1<<k));key=tuple(g[u] for u in sorted(fibres[z]))
                    if key not in seen:seen[key]=len(ds);ds.append(g)
                    row.append(seen[key])
                cover.append(row)
            domains[z]=ds;parents.append(dict(child=fi[z],parent=fi[w],relative_maps=rels[w,z],cover=cover))
        constraints=[];initial=[list(range(len(domains[z]))) for z in occupied]
        for z in occupied:
            for w in occupied:
                if z>=w or (z^w).bit_count()!=1:continue
                A=fibres[z];B=fibres[w];common=A&B;table=[]
                for g in domains[z]:
                    ga={g[u] for u in A};row=[]
                    for h in domains[w]:
                        row.append(all(g[u]==h[u] for u in common) and len(ga&{h[u] for u in B})==len(common))
                    table.append(row)
                constraints.append(dict(left=fi[z],right=fi[w],table=table))
        current=[s[:] for s in initial];eliminations=[];changed=True
        while changed:
            changed=False
            for e,c in enumerate(constraints):
                for reverse in [False,True]:
                    x,y=(c['right'],c['left']) if reverse else (c['left'],c['right'])
                    for a in current[x][:]:
                        if any(c['table'][b][a] if reverse else c['table'][a][b] for b in current[y]):continue
                        eliminations.append(dict(variable=x,value=a,edge=e,reverse=reverse,neighbour_values=current[y][:]))
                        current[x].remove(a);changed=True
        assert all(current)
        index=len(records);record=dict(index=index,base_coordinates=basecoords,block_coordinates=blockcoords,occupied=occupied,selected_words=[sorted(fibres[z]) for z in occupied],vertices=vertices,domains=[domains[z] for z in occupied],parents=parents,constraints=constraints,initial=initial,eliminations=eliminations,remaining=current)
        (H/'data'/('partition-'+str(index)+'.json')).write_text(json.dumps(record,separators=(',',':'))+'\n')
        summary=dict(index=index,base_coordinates=basecoords,variables=len(occupied),initial_values=sum(map(len,initial)),remaining_values=sum(map(len,current)),maximum_remaining=max(map(len,current)),eliminations=len(eliminations),table_entries=sum(len(c['table'])*len(c['table'][0]) for c in constraints))
        records.append(summary)
    print('base',m,'partitions',len(records),'maxremaining',max(r['maximum_remaining'] for r in records if len(r['base_coordinates'])==m),flush=True)
out=dict(status='COMPLETE',records=records,seconds=time.monotonic()-start,source_sha256={str(seedfile):sha(seedfile),str(sourcecode):sha(sourcecode)},script_sha256=sha(__file__),resource_gate=gate,scope='Complete fixed-tree absolute selected-image domains; exact pair compatibility; arc-consistency elimination traces. Native preparation only, not Lean certification.')
(H/'data/domain-preparation.json').write_text(json.dumps(out,indent=2)+'\n');print('SAVED',len(records),'partitions',round(out['seconds'],3),'seconds')
