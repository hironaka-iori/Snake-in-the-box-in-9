"""Screen small archived cores for relaxable counter bounds; no proof claims."""
from pathlib import Path
import ast,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
older=read(ROOT/'milestones/107-reference-refutation-recovery/data/older-alternatives.json')
union=read(ROOT/'milestones/105-reference-proof-closure/data/source-selection.json')['rows']
done=set(read(ROOT/'milestones/108-smaller-reference-recovery/data/proof-summary.json')['recovered_reference_indices'])
pin=older['pin'];inputs={}
def source(path):
    raw=subprocess.check_output(['git','-c','core.commitGraph=false','show',pin+':'+path],cwd=ROOT)
    out=HERE/'upstream'/path;out.parent.mkdir(parents=True,exist_ok=True)
    if out.exists():assert out.read_bytes()==raw
    else:out.write_bytes(raw)
    inputs[path]=dict(saved=out.relative_to(ROOT).as_posix(),sha256=sha(raw),bytes=len(raw))
    return raw.decode('utf-8-sig')
groups={}
for row in older['candidates']:
    if row['recorded_proof']['hints']<=5000:groups.setdefault(row['root'],[]).append(row)
assert len(groups)==16
rows=[]
for root,candidates in sorted(groups.items()):
    cnf=source('work/final_lean/LocalWindowCnf/'+root+'.lean')
    sat=source('work/final_lean/LocalWindowSat/'+root+'.lean')
    rawbody=re.split(r'(?:noncomputable )?def cnf',cnf.split('def raw : List (List Nat) :=',1)[1],maxsplit=1)[0].strip()
    clauses=ast.literal_eval(rawbody)
    family=re.search(r'gen_lean_core.py --set (\w+)',cnf).group(1)
    choices=[r for r in candidates if r['family']==family]
    assert len(choices)==1,(root,family,[r['family'] for r in candidates])
    chosen=choices[0];meta=json.loads(source(chosen['metadata_path']))
    assert sha((HERE/'upstream'/chosen['metadata_path']).read_bytes())==chosen['metadata_sha256']
    assert len(clauses)==len(meta['core_ids'])==chosen['core_clauses']
    assert meta['dirs']==chosen['directions'] and meta['syms']==chosen['symbols']
    counters=sat.split('def ctrs : List Ctr := [',1)[1].split('\ndef tags',1)[0]
    pattern=r'⟨\[([^]]*)\],\s*(\d+),\s*(\.?ends|\(\.(hi|lo)\s+(\d+)\))⟩'
    parsed=[]
    for lits,k,kind,which,centre in re.findall(pattern,counters):
        parsed.append(dict(lits=ast.literal_eval('['+lits+']'),k=int(k),kind=which or 'ends',centre=int(centre) if centre else None))
    assert len(parsed)==counters.count('⟨'),(root,len(parsed),counters.count('⟨'))
    tags=sat.split('def tags : List Tag := [',1)[1].split('\ntheorem check',1)[0]
    over=sorted(set(map(int,re.findall(r'\(\.over (\d+) \d+\)',tags))))
    referenced=sorted(set(map(int,re.findall(r'\(\.(?:first|zero|mono|step|over) (\d+)',tags))))
    assert all(i<len(parsed) for i in referenced)
    bounds=[[0,21] for _ in meta['bounds']]
    for i,ct in enumerate(parsed):
        if ct['kind']=='ends':assert ct['k']==2;continue
        j=ct['centre'];assert 0<=j<len(bounds) and len(ct['lits'])==21
        assert ct['k']==(meta['bounds'][j][1] if ct['kind']=='hi' else 21-meta['bounds'][j][0])
        if i in over:
            if ct['kind']=='hi':bounds[j][1]=min(bounds[j][1],ct['k'])
            else:bounds[j][0]=max(bounds[j][0],21-ct['k'])
    changes=[]
    for i,ct in enumerate(parsed):
        if ct['kind']=='ends':continue
        j=ct['centre'];new=bounds[j][1] if ct['kind']=='hi' else 21-bounds[j][0]
        if new!=ct['k']:
            assert i not in over
            changes.append(dict(counter=i,kind=ct['kind'],centre=j,old=ct['k'],new=new,referenced=i in referenced))
    covered=[]
    for u in union:
        if u['directions']!=meta['dirs']:continue
        ub=[(s,s) if s<6 else (6,21) for s in u['symbols']]
        if all(lo<=a and b<=hi for (lo,hi),(a,b) in zip(bounds,ub)):
            covered.append(u['union_index'])
    assert chosen['union_index'] in covered
    rows.append(dict(root=root,source_family=family,representative_index=chosen['union_index'],
        directions=meta['dirs'],original_bounds=meta['bounds'],proposed_bounds=bounds,
        counter_count=len(parsed),over_counters=over,referenced_counters=referenced,changes=changes,
        covered_reference_indices=covered,new_reference_indices=[i for i in covered if i not in done],
        recorded_hints=meta['lrat']['hints'],core_clauses=len(clauses),
        input_paths=['work/final_lean/LocalWindowCnf/'+root+'.lean','work/final_lean/LocalWindowSat/'+root+'.lean',chosen['metadata_path']]))
rows.sort(key=lambda r:(-len(r['new_reference_indices']),r['recorded_hints'],r['root']))
out=dict(status='UNTESTED_RELAXATION_CANDIDATES',pin=pin,roots_screened=len(rows),recorded_hint_limit=5000,
    unique_new_reference_indices=sorted({i for r in rows for i in r['new_reference_indices']}),
    candidates=rows,inputs=inputs,script_sha256=sha(Path(__file__).read_bytes()),
    scope='Source screening only. Bounds are inferred from over-tag limit dependencies and original counter metadata. No new clause-to-full-CNF identity, LRAT replay, relaxed semantic check, catalogue transfer, or additional refutation is claimed. Coverage is same ordered direction word only.')
(HERE/'data/small-core-screen.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('SCREENED',len(rows),'roots; proposed union coverage',len(out['unique_new_reference_indices']))
for row in rows[:6]:print(row['root'],'new',len(row['new_reference_indices']),'hints',row['recorded_hints'],'bounds',row['proposed_bounds'])
