"""Independent ordered-table audit only; no Lean or graph rebuild."""
from pathlib import Path
import ast,collections,datetime,hashlib,json,re
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[2]
read=lambda p:json.loads((ROOT/p).read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
semantic_sha=lambda v:sha(json.dumps(v,separators=(',',':')).encode())
def canon(w):
    labels=[];out=[]
    for x in w:
        if x not in labels:labels.append(x)
        out.append(labels.index(x))
    return tuple(out)
def all_rgs(n,w=()):
    if len(w)==n:yield w
    else:
        for x in range(max(w,default=-1)+2):yield from all_rgs(n,w+(x,))
def induced_parity(w):
    for left in range(len(w)):
        parity=0
        for right in range(left,len(w)):
            parity^=1<<w[right]
            if right>left and parity.bit_count()<=1:return False
    return True
source_path='milestones/59-extended-share-window/extended/data/model.json'
history_path='milestones/67-critical-family-charge/data/full-model.json'
sm=read(source_path);hm=read(history_path)
shapes=[tuple(w) for w in sm['direction_shapes']]
extensions=[tuple(w) for w in sm['extensions']]
coverage={}
for n,actual,bell,surviving in [(8,shapes,4140,132),(9,extensions,21147,505)]:
    candidates=list(all_rgs(n));expected=[w for w in candidates if induced_parity(w)]
    assert len(candidates)==bell and len(expected)==surviving
    assert expected==actual==sorted(actual) and len(set(actual))==len(actual)
    assert all(max(w)<9 and canon(w)==w for w in actual)
    coverage[n]=dict(candidates=bell,induced=surviving,exact_order_match=True,
        ordered_semantic_sha256=semantic_sha(actual),first=actual[0],last=actual[-1],
        reversal_classes=len({min(w,canon(w[::-1])) for w in actual}))
sid={w:i for i,w in enumerate(shapes)}
source_ids=[sid[canon(w[:8])] for w in extensions]
target_ids=[sid[canon(w[1:])] for w in extensions]
assert set(source_ids)==set(range(132))==set(target_ids)
geometry=read('milestones/59-extended-share-window/data/geometry.json')['patterns']
assert [tuple(row['directions']) for row in geometry]==extensions
assert read('milestones/58-share-pressure/geometry/data/model.json')['extensions']==sm['direction_shapes']
assert read('milestones/42-six-count-state-model/data/model.json')['extensions']==sm['direction_shapes']
prefixes=[tuple(p) for p in hm['prefixes']];patterns=hm['patterns']
expected_prefixes=[()]+sorted({tuple(p['signature'][:n]) for p in patterns for n in (1,2)},key=lambda p:(len(p),p))
assert prefixes==expected_prefixes and len(set(prefixes))==75
assert collections.Counter(map(len,prefixes))=={0:1,1:31,2:43}
assert all(p[:-1] in prefixes for p in prefixes if p)
assert all(0<=d<505 for p in prefixes for d in p)
compatible=[None]+[target_ids[p[-1]] for p in prefixes[1:]]
assert compatible==hm['compatible_shapes']
assert all(target_ids[p[0]]==source_ids[p[1]] for p in prefixes if len(p)==2)
history_lean=(ROOT/'milestones/75-exact-history-bridge/history/lean/ExactHistory.lean').read_text(encoding='utf-8')
for key,expected in [('prefixes',hm['prefixes']),('signatures',[p['signature'] for p in patterns])]:
    match=re.search(r'def '+key+r' : List \(List Nat\) := (\[.*?\n\])',history_lean,re.S)
    assert match and ast.literal_eval(match.group(1))==expected
for path in ['milestones/70-proof-supported-share-model/data/model.json','milestones/70-proof-supported-share-model/data/enriched-model.json']:
    md=read(path)
    for key in ['prefixes','compatible_shapes','patterns']:assert md[key]==hm[key]
next_history=[];allowed_pairs=0;nonempty_updates=0
for q,prefix in enumerate(prefixes):
    row=[]
    for di in range(505):
        joined=prefix+(di,)
        candidates=[j for j,p in enumerate(prefixes) if p and len(p)<=len(joined) and joined[-len(p):]==p]
        if candidates:
            greatest=max(len(prefixes[j]) for j in candidates)
            maximizing=[j for j in candidates if len(prefixes[j])==greatest]
            assert len(maximizing)==1
            nxt=maximizing[0]
        else:nxt=0
        if nxt:
            nonempty_updates+=1
            assert prefixes[nxt][-1]==di and compatible[nxt]==target_ids[di]
        if not q or compatible[q]==source_ids[di]:allowed_pairs+=1
        row.append(nxt)
    next_history.append(row)
current=read('milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
mixed=read('milestones/72-four-count-proof-closure/critical-current/data/countfree16-all-except012034x20-except012310x12-model.json')
assert current['states']==mixed['states']==(132+74)*6**5==1601856
assert current['edges']==mixed['edges']==4947008
assert all(current['arrays_sha256'][k]==mixed['arrays_sha256'][k] for k in ['U','V','direction','count_code','history'])
tables=dict(direction_shapes=shapes,extensions=extensions,source_shape_ids=source_ids,target_shape_ids=target_ids,prefixes=prefixes,compatible_shapes=compatible)
(HERE/'ordered-tables.json').write_text(json.dumps(tables,indent=2)+'\n',encoding='utf-8')
paths=[
'milestones/42-six-count-state-model/scripts/model.py',
'milestones/42-six-count-state-model/data/model.json',
'milestones/58-share-pressure/scripts/apply_geometry.py',
'milestones/58-share-pressure/geometry/data/model.json',
'milestones/59-extended-share-window/scripts/extend.py',
'milestones/59-extended-share-window/scripts/verify.py',source_path,
'milestones/59-extended-share-window/data/geometry.json',
'milestones/67-critical-family-charge/scripts/build_full.py',
'milestones/67-critical-family-charge/scripts/verify_full.py',history_path,
'milestones/70-proof-supported-share-model/scripts/build.py',
'milestones/70-proof-supported-share-model/data/model.json',
'milestones/70-proof-supported-share-model/data/enriched-model.json',
'milestones/72-four-count-proof-closure/scripts/graph.py',
'milestones/72-four-count-proof-closure/critical-current/scripts/prepare.py',
'milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json',
'milestones/72-four-count-proof-closure/critical-current/data/countfree16-all-except012034x20-except012310x12-model.json',
'milestones/74-graph-interpretation-audit/lean/WindowStateShift.lean',
'milestones/74-graph-interpretation-audit/scripts/source_audit.py',
'milestones/74-graph-interpretation-audit/data/proof-audit.json',
'milestones/75-exact-history-bridge/history/lean/HistoryPrefix.lean',
'milestones/75-exact-history-bridge/history/lean/ExactHistory.lean',
'milestones/75-exact-history-bridge/history/data/proof-audit.json']
report=dict(status='PASS_ORDERED_DIRECTION_AND_HISTORY_TABLE_AUDIT',
recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),coverage=coverage,
source_map_semantic_sha256=semantic_sha(source_ids),target_map_semantic_sha256=semantic_sha(target_ids),
history=dict(prefixes=75,length_counts={'0':1,'1':31,'2':43},
compatible_rule='None at 0; target_shape_ids[prefixes[q][-1]] for q>0',
exact75_lean_prefix_and_signature_lists_match=True,
checked_update_pairs=75*505,source_compatible_pairs=allowed_pairs,nonempty_updates=nonempty_updates,
maximum_length_ties=0,every_nonempty_update_target_compatible=True,next_history_semantic_sha256=semantic_sha(next_history)),
ordered_tables_file_sha256=sha((HERE/'ordered-tables.json').read_bytes()),script_sha256=sha(Path(__file__).read_bytes()),
history_metadata_comparison=dict(previous74_source='milestones/70-proof-supported-share-model/data/enriched-model.json',previous74_hash=read('milestones/74-graph-interpretation-audit/data/interface-audit.json')['graph']['history_metadata_sha256'],current_same_source_hash=sha((ROOT/'milestones/70-proof-supported-share-model/data/enriched-model.json').read_bytes()),source67_path=history_path,source67_hash=sha((ROOT/history_path).read_bytes()),scope='The previous74 audit hashes milestone70, not milestone67. Same-file hashes agree; the different whole-file hashes of67 and70 do not establish drift. Relevant history values agree.'),
evidence=[dict(path=p,sha256=sha((ROOT/p).read_bytes())) for p in paths],
limits='Small independent Python table audit and source inspection only. No Lean run, graph-array reconstruction, full graph interpretation, exclusion/share dispatch, potential replay or new upper bound. Metadata array hashes were compared; NPZ bytes were not reloaded or rehashed.')
(HERE/'table-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:report[k] for k in ['status','coverage','history','ordered_tables_file_sha256']},indent=2))
