"""Identify exact contributor entry proofs for the existing reference union."""
from pathlib import Path
import ast, collections, hashlib, json, re, subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
pins={'R4b':'74ca83db9c218446211d4f24c5e5a07329fdd847',
      'R4':'7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b',
      'K6':'74ca83db9c218446211d4f24c5e5a07329fdd847'}
catalogues={};upstream=[];trees={}
for kind,pin in pins.items():
    texts={}
    for category in ['Keys','Unsat','Sat']:
        name=f'LocalWindowDir{category}{kind}.lean';path='work/final_lean/'+name
        raw=subprocess.check_output(['git','-c','core.commitGraph=false','show',pin+':'+path],cwd=ROOT)
        dest=HERE/'upstream'/name
        if dest.exists():assert dest.read_bytes()==raw
        else:dest.write_bytes(raw)
        texts[category]=raw.decode('utf-8')
        upstream.append(dict(pin=pin,git_path=path,local_path=dest.relative_to(ROOT).as_posix(),sha256=sha(dest)))
    keys=[(tuple(ast.literal_eval(a)),tuple(ast.literal_eval(b))) for a,b in
        re.findall(r'\(\s*(\[[\d, ]*\])\s*,\s*(\[[\d, ]*\])\s*\)',texts['Keys'])]
    roots=re.findall(r'\b([A-Za-z][A-Za-z0-9]*)\.unsat\b',texts['Unsat'])
    semantic=re.findall(r'Tags\.refuted_of_sat\s+([A-Za-z][A-Za-z0-9]*)\.sat\s+h\d+',texts['Sat'])
    assert len(keys)==len(roots)==len(semantic) and roots==semantic,(kind,len(keys),len(roots),len(semantic))
    assert len(set(keys))==len(keys)
    for key,name in zip(keys,roots):
        m=re.fullmatch(r'[A-Z]+([0-9]+)A([0-9]+)',name);assert m,name
        assert tuple(map(int,m[1]))==key[0] and tuple(map(int,m[2]))==key[1],(kind,key,name)
    catalogues[kind]={k:dict(index=i,root=r) for i,(k,r) in enumerate(zip(keys,roots))}
    if pin not in trees:
        trees[pin]=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-tree','-r','--name-only',pin,'--','work/final_lean'],cwd=ROOT,text=True).splitlines())
union_path=ROOT/'milestones/85-reference-catalogue-union/data/reference-union.json'
union=read(union_path);rows=[]
for i,r in enumerate(union['rows']):
    key=(tuple(r['directions']),tuple(r['symbols']))
    choices=[kind for kind in ['R4','K6','R4b'] if key in catalogues[kind]]
    assert choices,('No direct entry proof for exact canonical key',key)
    kind=choices[0];entry=catalogues[kind][key];root=entry['root'];pin=pins[kind]
    paths={cat:f'work/final_lean/LocalWindow{cat}/{root}.lean' for cat in ['Sat','Unsat']}
    rows.append(dict(union_index=i,directions=key[0],symbols=key[1],source_catalogue=kind,
        source_index=entry['index'],root=root,pin=pin,available_catalogues=choices,
        generated_source_paths=paths,source_present_in_pinned_git={cat:path in trees[pin] for cat,path in paths.items()}))
assert len(rows)==1378 and len({r['root'] for r in rows})==1378
source_sizes={k:len(v) for k,v in catalogues.items()}
selected_counts=dict(collections.Counter(r['source_catalogue'] for r in rows))
source_unique=set().union(*(set(v) for v in catalogues.values()))
selected_keys={(tuple(r['directions']),tuple(r['symbols'])) for r in rows}
all_roots={e['root'] for catalogue in catalogues.values() for e in catalogue.values()}
selected_roots={r['root'] for r in rows}
out=dict(status='EXACT_SOURCE_SELECTION_NOT_CLOSED_REFUTATIONS',upstream=upstream,
    reference_union_sha256=sha(union_path),source_catalogue_sizes=source_sizes,
    selected_counts=selected_counts,selected_entries=len(rows),distinct_full_source_keys=len(source_unique),
    full_source_keys_not_needed=len(source_unique-selected_keys),rows=rows,
    distinct_full_source_roots=len(all_roots),unselected_source_roots=sorted(all_roots-selected_roots),
    absent_generated_semantic_sources=sum(not r['source_present_in_pinned_git']['Sat'] for r in rows),
    absent_generated_refutation_sources=sum(not r['source_present_in_pinned_git']['Unsat'] for r in rows),
    scope='Exact source-name and key-order correspondence against pinned contributor wrappers. No generated proof was reconstructed or checked. This is not a closed reference-union theorem.')
(HERE/'data/source-selection.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],source_sizes,selected_counts,'unused exact keys',out['full_source_keys_not_needed'],
      'full roots',len(all_roots),'unselected roots',len(all_roots-selected_roots),
      'missing generated Sat/Unsat',out['absent_generated_semantic_sources'],out['absent_generated_refutation_sources'])
