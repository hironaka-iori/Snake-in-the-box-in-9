"""Audit the saved Total341 certificate without solver or compiler invocation."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import argparse, ast, hashlib, json, re, sys

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
sys.dont_write_bytecode=True
sys.path[:0]=[str(ROOT/'milestones/10-window-aggregate/scripts'),str(ROOT/'work/share_packages')]
import gen_lean_sat as sat
from wincert import window_from_dirs

pins={}
def sha(path):
    path=Path(path).resolve();digest=hashlib.sha256(path.read_bytes()).hexdigest()
    try:key=path.relative_to(ROOT).as_posix()
    except ValueError:key=str(path)
    if key in pins:assert pins[key]==digest, ('Changed during audit',key)
    pins[key]=digest
    return digest
def read(path):
    sha(path);return json.loads(Path(path).read_text(encoding='utf-8-sig'))
def verify(path,digest):assert sha(path)==digest,str(path)
def cnf(path):
    sha(path);rows=[];nv=nc=None
    for line in Path(path).read_text().splitlines():
        if line.startswith('p '):
            p,kind,nv,nc=line.split();assert kind=='cnf';nv,nc=int(nv),int(nc)
        elif line.strip() and not line.startswith('c'):
            row=list(map(int,line.split()));assert row[-1]==0 and 0 not in row[:-1]
            rows.append(row[:-1])
    assert len(rows)==nc and all(0<abs(x)<=nv for c in rows for x in c)
    return nv,rows
def lrat(path):
    sha(path);rows=[]
    for raw in Path(path).read_bytes().splitlines(keepends=True):
        t=raw.split()
        if len(t)>1 and t[1]==b'd':continue
        row=list(map(int,t));z=row.index(0,1)
        assert row[-1]==0 and all(h>0 for h in row[z+1:-1])
        rows.append((row[0],row[1:z],row[z+1:-1],hashlib.sha256(raw).hexdigest()))
    return rows

plan=read(HERE/'data/total341-plan.json');selection=plan['selection'];choice=selection['choice']
assert choice=='0123041-universal-total24-full'
meta_path=HERE/'data'/(choice+'-certificate.json');meta=read(meta_path)
verify(meta_path,selection['certificate_sha256']);assert selection['original_certificate_sha256']==selection['certificate_sha256']
assert meta['status']=='NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING'
for path,digest in plan['input_pins'].items():verify(path,digest)
for row in plan['artifacts']:verify(HERE/row['path'],row['sha256'])
verify(HERE/'scripts/export_sum.py',plan['exporter_sha256'])
verify(HERE/'scripts/certify_sum.py',meta['script_sha256'])
for path,digest in meta['source_files_sha256'].items():verify(ROOT/path,digest)
probe_path=HERE/'data/probes'/(choice+'.json');probe=read(probe_path);verify(probe_path,meta['probe_sha256'])
assert probe['status']=='UNSAT_UNCERTIFIED' and not probe['cycle_cuts']
solver_path=HERE/'data'/(choice+'-solver.json');solver=read(solver_path);verify(solver_path,meta['solver_record_sha256'])
assert solver['status']=='NATIVE_UNSAT_LEAN_PENDING' and solver['exit_code']==20
verify(HERE/'logs'/(choice+'-solver.stdout.txt'),solver['stdout_sha256'])
verify(HERE/'logs'/(choice+'-solver.stderr.txt'),solver['stderr_sha256'])
assert b's UNSATISFIABLE' in (HERE/'logs'/(choice+'-solver.stdout.txt')).read_bytes()

work=HERE/'work'/choice;export=HERE/'work'/('export-total-'+choice)
verify(work/'full.cnf',meta['cnf_sha256']);verify(work/'core.cnf',meta['core_sha256'])
verify(work/'full.trim.lrat',meta['lrat_sha256']);verify(work/'full.raw.lrat',solver['raw_sha256'])
nv,full=cnf(work/'full.cnf');ids=meta['core_ids']
assert ids==sorted(set(ids)) and len(ids)==meta['core_clauses']==3649
assert cnf(work/'core.cnf')==(nv,[full[i-1] for i in ids])
assert nv==meta['variables']==5072 and len(full)==meta['clauses']==101898
assert meta['directions']==[0,1,2,3,0,4,1]
assert meta['window']==window_from_dirs(meta['directions'])==[0,1,3,7,15,14,30,28]
assert meta['bounds']==[[0,21]]*6 and meta['positions']==list(range(6)) and meta['radius']==9
assert meta['sum_cap']==24 and not meta['cycle_cuts'] and plan['appended_cycle_cuts']==0
assert plan['selected_cycle_input_ids']==[]

# Rebuild the full formula and its sum with repeated occurrences retained.
enc=sat.TaggedEncoding(meta['window'],[(0,21)]*6,radius=9)
assert set(enc.ball)==set(range(512))
corner_lists=[]
for i in range(1,7):
    v=enc.window[i];incident={v^enc.window[i-1],v^enc.window[i+1]}
    assert len(incident)==2
    corners=[v^(1<<a)^(1<<b) for a,b in combinations(range(9),2)
             if (1<<a) not in incident and (1<<b) not in incident]
    assert len(corners)==len(set(corners))==21
    corner_lists.append(corners)
lits=sorted(-enc.var[v] for cs in corner_lists for v in cs)
occurrences=Counter(v for cs in corner_lists for v in cs)
assert len(lits)==meta['literal_occurrences']==plan['literal_occurrences']==126
assert len(set(lits))==meta['distinct_literals']==plan['distinct_literals']==105
enc.atmost(lits,24,('unproved_sum',))
assert enc.nv==nv and enc.clauses==full and len(enc.tags)==len(full)
assert enc.ctrs[-1][0]==lits and enc.ctrs[-1][1]==24

# Check byte-preserving trim, exact dependency closure and each ordered RUP step.
original={cid:(cl,hs,digest) for cid,cl,hs,digest in lrat(work/'full.raw.lrat')}
trim=lrat(work/'full.trim.lrat');db={i:full[i-1] for i in ids}
used_inputs=set();deps={};active={abs(x) for c in db.values() for x in c};last=len(full);hints=0
for cid,cl,hs,digest in trim:
    assert cid>last and all(0<h<cid and h in db for h in hs)
    assert original[cid]==(cl,hs,digest)
    assigned={};contradiction=False
    for x in cl:
        var=abs(x);value=x<0
        if var in assigned and assigned[var]!=value:contradiction=True
        assigned[var]=value
    for h in hs:
        if h<=len(full):used_inputs.add(h)
        if contradiction:continue
        clause=db[h]
        if any(abs(x) in assigned and assigned[abs(x)]==(x>0) for x in clause):continue
        unset={x for x in clause if abs(x) not in assigned}
        assert len(unset)<=1,(cid,h)
        if not unset:contradiction=True
        else:
            x=next(iter(unset));assigned[abs(x)]=x>0
    assert contradiction,cid
    db[cid]=cl;deps[cid]=hs;active.update(map(abs,cl));last=cid;hints+=len(hs)
assert db[last]==[] and len(trim)==meta['lemmas']==5746 and hints==meta['hints']==439766
assert hints<=2_000_000 and sorted(used_inputs)==ids
closure=set();todo=[last]
while todo:
    cid=todo.pop()
    if cid<=len(full) or cid in closure:continue
    closure.add(cid);todo.extend(deps[cid])
assert closure==set(deps)

ren=read(HERE/'data/total341-renumbering.json');rename={int(k):v for k,v in ren['old_to_new'].items()}
order=sorted(active)+sorted(set(range(1,nv+1))-active)
assert rename=={v:i+1 for i,v in enumerate(order)}
assert len(active)==ren['active_variables']==plan['active_variables']==2021
assert max(rename[v] for v in active)==2021<2400
assert ren['selection']==selection and ren['original_cnf_sha256']==meta['cnf_sha256'] and ren['original_proof_sha256']==meta['lrat_sha256']
rlit=lambda x:rename[abs(x)]*(1 if x>0 else -1)
mapped_full=[[rlit(x) for x in c] for c in full]
assert cnf(export/'total341.cnf')==(nv,mapped_full)
mapped=lrat(export/'total341.lrat')
assert len(mapped)==len(trim)
for (cid,cl,hs,_),(mid,mcl,mhs,_) in zip(trim,mapped,strict=True):
    assert (cid,list(map(rlit,cl)),hs)==(mid,mcl,mhs)

# Inspect emitted semantic data, including the extra counter's multiplicities.
generated=HERE/('generated-total-'+choice)
cnf_source=(generated/'LocalWindowCnf/Total341.lean').read_text(encoding='utf-8')
raw=ast.literal_eval(re.search(r'def raw : List \(List Nat\) := (\[.*?\])\s*def cnf',cnf_source,re.S).group(1))
assert raw==[[sat.code(x) for x in mapped_full[i-1]] for i in ids]
semantic=(generated/'LocalWindowSat/Total341.lean').read_text(encoding='utf-8')
meaning=re.search(r'def meaning : MT :=\s*(.*?)\s*def ordinary',semantic,re.S).group(1)
assert meaning==sat.lean_tree_terms({rename[k]:v for k,v in enc.meaning.items()},nv)
terms=[]
for ls,k,kind in enc.ctrs:
    kt='.ends' if kind[0] in ['ends','unproved_sum'] else f'(.{kind[0]} {kind[1]})'
    terms.append(f'⟨{[sat.code(rlit(v)) for v in ls]}, {k}, {kt}⟩')
assert re.search(r'def ordinary : List Ctr := \[(.*?)\]\s*def extra',semantic,re.S).group(1)==', '.join(terms[:-1])
assert re.search(r'def extra : Ctr := (.*?)\s*def selected',semantic,re.S).group(1)==terms[-1]
selected=[f'⟨{enc.window[j+1]}, {meta["directions"][j]}, {meta["directions"][j+1]}, 0, 21⟩' for j in range(6)]
assert re.search(r'def selected : List Centre := \[(.*?)\]\s*def tags',semantic,re.S).group(1)==', '.join(selected)
tags=[enc.tags[i-1] for i in ids]
expected=',\n  '.join(', '.join(sat.lean_tag(t) for t in tags[i:i+8]) for i in range(0,len(tags),8))
assert re.search(r'def tags : List Tag := \[\s*(.*?)\]\s*theorem check',semantic,re.S).group(1)==expected
assert '(extra.lits.map (vl meaning)).Perm (selected.flatMap corners)' in semantic
assert 'SumCountSemantics112.sound_append_sum' in semantic and 'sum ≤ 24' in semantic

assert len(plan['ports'])==len(plan['modules'])==len(set(plan['modules']))==40
texts={}
for port in plan['ports']:
    src=generated/port['original'];dst=HERE/port['isolated']
    verify(src,port['source_sha256']);verify(dst,port['isolated_sha256'])
    source=src.read_text(encoding='utf-8');isolated=dst.read_text(encoding='utf-8')
    assert re.sub(r'^import Recovered124G\.', 'import ',isolated,flags=re.M)==source
    assert not re.search(r'\b(sorry|admit|native_decide)\b',isolated)
    texts[port['original']]=source

# Decode every packed source deduction, checking slot reuse against actual IDs.
checker=plan['checker'];assert checker['module']=='LratFast' and checker['bits']==13 and checker['offset']==2400
assert checker['slots']==3852 and checker['slots']<2**13
verify(checker['object'],checker['object_sha256'])
nums=lambda s:[int(x,0) for x in re.findall(r'nat_lit (0x[0-9a-fA-F]+|[0-9]+)',s)]
data0=texts['LocalWindowUnsat/Total341/Data0.lean']
slots=nums(re.search(r'def inputSlots : List Nat := \[(.*?)\]',data0,re.S).group(1))
assert len(slots)==len(set(slots))==len(ids) and all(0<x<8192 for x in slots)
slot_for=dict(zip(ids,slots,strict=True));resident=dict(zip(slots,ids,strict=True))
segments={}
for text in texts.values():
    for number,body in re.findall(r'def proof([0-9]+) : List Nat := \[(.*?)\]',text,re.S):
        assert int(number) not in segments
        segments[int(number)]=nums(body)
assert sorted(segments)==list(range(1,73))
packed_rows=[v for n in range(1,73) for v in segments[n]]
assert len(packed_rows)==len(mapped)
segment_hints=[];index=0
for n in range(1,73):
    nh=0
    for packed in segments[n]:
        words=[]
        while packed:words.append(packed&8191);packed>>=13
        words.append(0);split=words.index(0,1)
        key=words[0];literal_words=words[1:split];hint_keys=words[split+1:-1]
        clause=[]
        for w in literal_words:
            bit=w-1
            if bit>2400:literal=-(bit-2400)
            else:literal=bit
            assert 0<abs(literal)<2400
            clause.append(literal)
        cid,cl,hs,_=mapped[index]
        assert clause==cl and hint_keys==[slot_for[h] for h in hs]
        assert all(resident[k]==h for k,h in zip(hint_keys,hs,strict=True))
        assert 0<key<8192
        slot_for[cid]=key;resident[key]=cid;nh+=len(hs);index+=1
    segment_hints.append(nh)
assert segment_hints==plan['generation']['seg_hints']
assert plan['generation']['simulated'] and plan['generation']['segments']==72
assert plan['generation']['lemmas']==len(trim) and plan['generation']['hints']==hints

script_sha=sha(Path(__file__))
out=dict(status='PASS_EXACT_FORMULA_MULTIPLICITIES_CORE_RUP_AND_EXPORTED_DATA',
    shape=meta['directions'],window=meta['window'],positions=meta['positions'],sum_cap=24,
    full_formula=dict(variables=nv,clauses=len(full),radius=9,all512_vertices=True,cycle_cuts=0),
    sum=dict(literal_occurrences=len(lits),distinct_literals=len(set(lits)),multiplicity_histogram=dict(sorted(Counter(occurrences.values()).items())),selected_corners=corner_lists,duplicates_preserved=True),
    proof=dict(core_inputs=len(ids),deductions=len(trim),hints=hints,final_empty_id=last,exact_backward_closure=True,trim_rows_identical_to_original=True,ordered_rup_replayed_here=True),
    export=dict(modules=len(plan['modules']),active_variables=len(active),word_bits=13,literal_offset=2400,slots=3852,segments=72,all_packed_deductions_decoded_and_matched=True,all40_source_ports_checked=True,semantic_data_checked=True),
    source_files_sha256=pins,script_sha256=script_sha,
    scope='Exact finite CNF and native ordered-RUP audit for shape0123041 with sum cap24. Generated semantic data, renumbering, packed proof and ports checked; no solver/compiler invocation. Lean receipts and the actual-snake theorem require a separate review. No universal six-count floor follows.')
for path,digest in list(pins.items()):verify(ROOT/path if not Path(path).is_absolute() else path,digest)
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(dict(status=out['status'],proof=out['proof'],export=out['export'],multiplicity_histogram=out['sum']['multiplicity_histogram'],pinned_files=len(pins),output_sha256=hashlib.sha256(args.output.read_bytes()).hexdigest() if args.output else None),indent=2))
