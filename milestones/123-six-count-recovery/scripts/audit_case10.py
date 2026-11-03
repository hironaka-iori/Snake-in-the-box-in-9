"""Bounded read-only case10 audit; --output creates new evidence exclusively.
No solver, Lean compiler, full graph evaluation, or RUP replay is performed.
"""
from pathlib import Path
from fractions import Fraction
import argparse, ast, gzip, hashlib, json, re, sys
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/32-seven-count-four-screen'
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages')]
import gen_lean_sat as sat
from wincert import Encoding,window_from_dirs
import numpy as np
pins={}
def sha(p):
    d=hashlib.sha256(Path(p).read_bytes()).hexdigest();pins[str(Path(p).resolve().relative_to(R)).replace('\\','/')]=d;return d
def read(p):
    sha(p);return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def verify(p,d):assert sha(p)==d,str(p)
def clauses(p):
    return [list(map(int,s.split()))[:-1] for s in p.read_text().splitlines() if s.strip() and not s.startswith(('p','c'))]
def canon(w):
    names={};return [names.setdefault(int(x),len(names)) for x in w]
def decode(c):return [int(c)//6**k%6+1 for k in range(5,-1,-1)]
a=read(H/'data/case10-recovery.json');plan=read(H/'data/case10-plan.json')
verify(H/'scripts/prepare_case10.py',a['script_sha256']);verify(H/'scripts/export_case10.py',plan['script_sha256'])
verify(H/'data/case10-recovery.json',plan['recovery_sha256'])
for rel,d in a['encoding_pins'].items():verify(R/rel,d)
verify(R/a['generator'],a['generator_sha256']);verify(R/plan['generator'],plan['generator_sha256'])
verify(R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',plan['semantics_generator_sha256'])
assert len(a['sources'])==len({x['archive'] for x in a['sources']})==9
archives=[]
for row in a['sources']:
    src,arc=R/row['source'],H/row['archive'];verify(src,row['sha256']);verify(arc,row['archive_sha256'])
    unpacked=gzip.decompress(arc.read_bytes());assert unpacked==src.read_bytes()
    archives.append(dict(source=row['source'],archive=row['archive'],compressed_sha256=row['archive_sha256'],uncompressed_sha256=hashlib.sha256(unpacked).hexdigest()))
initial=read(H/'audit/case10-recovery-initial.json');sha(H/'audit/prepare_case10-initial.py.txt')
initial_names=[x['archive'] for x in initial['sources']]
assert len(initial_names)>len(set(initial_names))
cases=read(P/'data/cases.json');meta=read(P/'data/four10.json')
assert a['case']==cases[10]==dict(dirs=[0,1,2,3,0,4,2],bounds=[[4,4]]*6)
enc=sat.TaggedEncoding(window_from_dirs(cases[10]['dirs']),[(4,4)]*6,radius=4)
plain=Encoding(enc.window,[(4,4)]*6,radius=4)
full=clauses(P/'certificates/four10.full.cnf')
assert plain.clauses==enc.clauses==full
rename={int(k):v for k,v in meta['original_to_new'].items()}
assert set(rename)==set(enc.meaning) and set(rename.values())==set(range(1,enc.nv+1))
rlit=lambda x:(1 if x>0 else -1)*rename[abs(x)]
compact=[[rlit(x) for x in full[i-1]] for i in meta['source_original_clause_ids']]
assert compact==clauses(P/'certificates/four10.cnf')==clauses(H/'work/four10/four10.cnf')
assert len(compact)==4488 and max(abs(x) for c in compact for x in c)==1640
assert enc.nv==a['meaning_variables']==4040
ids=a['retained_core_ids'];assert ids==sorted(set(ids)) and len(ids)==4239 and all(1<=i<=4488 for i in ids)
verify(H/'work/four10/four10.cnf',a['cnf_sha256']);verify(H/'work/four10/four10.lrat',a['lrat_sha256'])
# Independently inspect reduction identity and dependency closure, without RUP replay.
original_rows={};old_n=old_h=0
for line in (P/'certificates/four10.lrat').read_bytes().splitlines(keepends=True):
    t=line.split()
    if len(t)>1 and t[1]==b'd':continue
    z=t.index(b'0',1);key=int(t[0]);old_n+=1;old_h+=len(t)-z-2
    original_rows[key]=hashlib.sha256(line).hexdigest()
assert (old_n,old_h)==(69050,4112390)==(a['original_lemmas'],a['original_hints'])
rows={};hints=0;inputs=set();last_empty=None;maxvar=0
for line in (H/'work/four10/four10.lrat').read_bytes().splitlines(keepends=True):
    tokens=line.split();t=list(map(int,tokens));z=t.index(0,1);key=t[0];hs=t[z+1:-1]
    assert t[-1]==0 and key not in rows and all(0<h<key for h in hs)
    assert hashlib.sha256(line).hexdigest()==original_rows[key]
    assert all(h<=4488 or h in rows for h in hs)
    rows[key]=set(hs);hints+=len(hs);inputs.update(h for h in hs if h<=4488)
    maxvar=max(maxvar,max((abs(x) for x in t[1:z]),default=0))
    if z==1:last_empty=key
assert (len(rows),hints)==(55823,3570165)==(a['trimmed_lemmas'],a['trimmed_hints'])
assert last_empty==max(rows) and sorted(inputs)==ids and maxvar<2400
need=set();stack=[last_empty]
while stack:
    k=stack.pop()
    if k<=4488 or k in need:continue
    need.add(k);stack.extend(rows[k])
assert need==set(rows)
# Compare exact emitted raw clauses and semantic metadata against the mapping.
cnf_src=H/'generated/LocalWindowCnf/SixFour10.lean';src=cnf_src.read_text(encoding='utf-8-sig')
raw=ast.literal_eval(re.search(r'def raw : List \(List Nat\) := (\[.*?\])\s*def cnf',src,re.S).group(1))
assert raw==[[2*x if x>0 else -2*x+1 for x in compact[i-1]] for i in ids]
ss=(H/'generated/LocalWindowSat/SixFour10.lean').read_text(encoding='utf-8-sig')
meaning=re.search(r'def meaning : MT :=\s*(.*?)\s*def ctrs',ss,re.S).group(1)
assert meaning==sat.lean_tree_terms({rename[k]:v for k,v in enc.meaning.items()},enc.nv)
ctr_terms=[]
for ls,k,kind in enc.ctrs:
    kt='.ends' if kind[0]=='ends' else f'(.{kind[0]} {kind[1]})'
    ctr_terms.append('⟨['+', '.join(str(sat.code(rlit(x))) for x in ls)+f'], {k}, {kt}⟩')
assert re.search(r'def ctrs : List Ctr := \[\s*(.*?)\]\s*def tags',ss,re.S).group(1)==',\n  '.join(ctr_terms)
tags=[enc.tags[meta['source_original_clause_ids'][i-1]-1] for i in ids]
expected_tags=',\n  '.join(', '.join(sat.lean_tag(t) for t in tags[i:i+8]) for i in range(0,len(tags),8))
assert re.search(r'def tags : List Tag := \[\s*(.*?)\]\s*theorem check',ss,re.S).group(1)==expected_tags
assert len(plan['modules'])==len(plan['ports'])==202
for port in plan['ports']:
    src,dst=H/port['original'],H/port['isolated'];verify(src,port['sha256']);verify(dst,port['isolated_sha256'])
    text=dst.read_text(encoding='utf-8-sig')
    assert text.replace('import Recovered123G.','import ')==src.read_text(encoding='utf-8-sig')
    assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
stats=plan['statistics'];assert stats['simulated'] and (stats['lemmas'],stats['hints'])==(len(rows),hints)
assert plan['word_bits']==13 and plan['literal_offset']==2400 and stats['slots']==6691<8192
# Only selected saved graph keys and cycles are inspected, not all graph edges.
oldpath=R/'milestones/122-endpoint-equality/data/endpoint-graph-c4/results.json';old=read(oldpath)
oldcycle=next(x['cycle'] for x in old['profiles'] if x['profile']=='conditional_floor18')
ds=read(R/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
graphpath=R/'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
graphmeta=read(R/'milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
resultpath=H/'data/six-graph-case10/results.json';result=read(resultpath)
verify(graphpath,result['source_files_sha256'][graphpath.relative_to(R).as_posix()])
with np.load(graphpath) as graph:
    arrays={k:graph[k] for k in ['U','V','direction','history','count_code']}
    for k,v in arrays.items():assert hashlib.sha256(v.tobytes()).hexdigest()==graphmeta['arrays_sha256'][k]
    matched=[]
    for e in oldcycle:
        idx=e['edge'];di=int(arrays['direction'][idx]);q=int(arrays['history'][idx]);c=int(arrays['count_code'][idx])
        assert (di,q,c)==(e['direction'],e['history'],e['count_code']) and e['directions']==ds[di]
        word=ds[di][2:9];normal=canon(word);rev=canon(word[::-1])
        matches=[i for i,case in enumerate(cases) if case['dirs'] in [normal,rev] and case['bounds']==[[4,4]]*6]
        assert decode(c)==e['counts']==[4]*6 and c==27993
        matched.append(dict(edge=idx,direction=di,history=q,count_code=c,word=ds[di],slice=word,canon=normal,reversed_canon=rev,cases=matches,
            forward_cases=[i for i in matches if cases[i]['dirs']==normal],
            reversed_cases=[i for i in matches if cases[i]['dirs']==rev]))
assert {x['edge']:x['cases'] for x in matched}=={3049577:[10],1275804:[7,23],988624:[7,23]}
assert {x['edge']:x['forward_cases'] for x in matched}=={3049577:[10],1275804:[7],988624:[23]}
for rel,d in result['source_files_sha256'].items():verify(R/rel,d)
verify(H/'scripts/evaluate_six.py',result['script_sha256'])
profiles=[]
for prof in result['profiles']:
    cy=prof['cycle'];assert all(e['v']==cy[(i+1)%len(cy)]['u'] for i,e in enumerate(cy))
    assert Fraction(sum(e['weight'] for e in cy),len(cy))==Fraction(prof['mean'])
    assert Fraction(prof['p'],prof['d'])==Fraction(prof['mean'])
    assert Fraction(prof['range_scaled'],prof['d'])==Fraction(prof['range'])
    comparison=Fraction(1098960*prof['d']+8*prof['p']+prof['range_scaled'],4200*prof['d']+prof['p'])
    assert comparison==Fraction(prof['comparison_bound']) and comparison.numerator//comparison.denominator==prof['comparison_integer_bound']
    for e in cy:
        assert not (e['count_code']==27993 and canon(e['directions'][2:])==cases[10]['dirs'])
    profiles.append(dict(profile=prof['profile'],mean=prof['mean'],range=prof['range'],comparison=prof['comparison_bound'],integer_comparison=prof['comparison_integer_bound'],cycle_length=len(cy)))
summary=read(H/'data/six-graph/summary.json')
assert summary['case10_source_keys']==summary['case10_newly_removed']==13
present_receipts=[n for n in plan['modules'] if (H/'data'/(n+'-audit.json')).exists()]
sha(Path(__file__))
out=dict(status='PASS_CASE10_ARCHIVES_MAPPING_TRIM_AND_EXPORT_PROVENANCE',archives=archives,
    full_encoding=dict(variables=enc.nv,clauses=len(full),radius=4,window=enc.window,bounds=[[4,4]]*6),
    renamed_core=dict(input_clauses=4488,active_variables=1640,retained_input_clauses=4239),
    trimmed_proof=dict(original_steps=old_n,original_hints=old_h,steps=len(rows),hints=hints,final_empty_id=last_empty,max_literal_variable=maxvar,byte_identical_original_rows=True,exact_backward_dependency_closure=True,native_rup_replayed_here=False),
    export=dict(modules=202,slots=6691,word_bits=13,literal_offset=2400,native_simulation_recorded=True,source_ports_checked=202,semantic_raw_and_metadata_checked=True),
    graph_keys=matched,case10_graph_profiles=profiles,reported_source_hits=13,
    successful_receipts_present_not_reviewed=present_receipts,
    source_pins=pins,script_sha256=pins[Path(__file__).resolve().relative_to(R).as_posix()],
    scope='Read-only archive/CNF/renaming/retained-ID/byte-preserving proof-reduction/semantic-metadata/export provenance and selected-key arithmetic audit. No solver, Lean compiler, RUP replay or full graph scan. Native simulation is a pinned exporter record, not an independently rerun proof. Full Lean contradiction and actual-snake application remain separate obligations.')
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(dict(status=out['status'],archives=9,modules=202,steps=len(rows),hints=hints,full_clauses=len(full),keys=matched,profiles=profiles,pinned_files=len(pins),output_sha256=hashlib.sha256(args.output.read_bytes()).hexdigest() if args.output else None),indent=2))
