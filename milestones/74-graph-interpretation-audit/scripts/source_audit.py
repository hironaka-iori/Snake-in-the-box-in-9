"""Record exact current graph metadata, source interfaces and inherited receipts.
This reads metadata and sources only; it does not rebuild or kernel-check the graph.
"""
from pathlib import Path
import collections,hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
files=[
'milestones/70-proof-supported-share-model/scripts/build.py',
'milestones/72-four-count-proof-closure/scripts/graph.py',
'milestones/72-four-count-proof-closure/scripts/verify_graph.py',
'milestones/72-four-count-proof-closure/critical-current/scripts/prepare.py',
'milestones/72-four-count-proof-closure/critical-current/scripts/countfree_effect.py',
'milestones/72-four-count-proof-closure/critical-current/scripts/verify_countfree_model.py',
'milestones/59-extended-share-window/scripts/extend.py',
'milestones/67-critical-family-charge/scripts/build_full.py',
'work/spectral/stronger/WindowAutomatonDefs.lean',
'work/spectral/stronger/WindowAutomatonLemmas.lean',
'work/spectral/stronger/WindowAutomatonBridge.lean',
'work/spectral/stronger/DirectionWindowBridge.lean',
'work/final_lean/LocalWindowDirBridge.lean',
'work/spectral/stronger/AggregateWindowUnconditional.lean',
'milestones/59-extended-share-window/lean/ExtendedShareBridge.lean',
'milestones/59-extended-share-window/lean/ExtendedBudget.lean',
'milestones/61-critical-family-share/lean/FinitePotential.lean',
'milestones/67-critical-family-charge/lean/BoundaryCharge.lean',
'milestones/67-critical-family-charge/lean/ChargeBatch00.lean',
'milestones/73-countfree-share-catalogue/bridge/lean/CoreShareBudget.lean',
'milestones/73-countfree-share-catalogue/adapter/lean/ConditionalCatalogueDispatch.lean',
'milestones/72-four-count-proof-closure/critical-current/lean/CountFreeTarget.lean']
sources=[]
for rel in files:
    p=ROOT/rel;text=p.read_text(encoding='utf-8-sig')
    decls=[dict(line=i,name=m.group(2),kind=m.group(1)) for i,line in enumerate(text.splitlines(),1)
      if (m:=re.match(r'^(theorem|def|structure) ([^\s{(:]+)',line))]
    sources.append(dict(path=rel,sha256=sha(p),declarations=decls))
receipts=[]
for folder in ['59-extended-share-window','61-critical-family-share','67-critical-family-charge']:
    p=ROOT/'milestones'/folder/'data/lean-audit.json';d=read(p);checks=[]
    assert d['status']=='PASS'
    for row in d['records']:
        src=p.parents[1]/'lean'/(row['module']+'.lean')
        if src.exists() and 'source_sha256' in row:
            assert sha(src)==row['source_sha256']
            checks.append(dict(module=row['module'],source_sha256=sha(src)))
    receipts.append(dict(path=str(p.relative_to(ROOT)),sha256=sha(p),source_hash_matches=checks,scope='Historical successful receipt, current source hashes checked; no fresh compilation of these modules.'))
basepath=ROOT/'milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json';base=read(basepath)
shape_path=ROOT/'milestones/59-extended-share-window/extended/data/model.json';shape=read(shape_path)
history_path=ROOT/'milestones/70-proof-supported-share-model/data/enriched-model.json';hist=read(history_path)
assert len(shape['direction_shapes'])==132 and len(shape['extensions'])==505 and len(hist['prefixes'])==75
assert all(len(x)==8 for x in shape['direction_shapes']) and all(len(x)==9 for x in shape['extensions'])
assert hist['prefixes'][0]==[] and all(1<=len(x)<=2 for x in hist['prefixes'][1:])
assert base['states']==(132+74)*6**5==1601856 and base['edges']==4947008
tag='countfree16-all-except012034x20-except012310x12'
cur=basepath.parent
comp=read(cur/(tag+'-model.json'));verification=read(cur/(tag+'-verification.json'));analysis=read(cur/(tag+'-analysis.json'))
assert comp['states']==base['states'] and comp['edges']==base['edges']
assert all(comp['arrays_sha256'][k]==base['arrays_sha256'][k] for k in base['arrays_sha256'] if k!='weight')
assert verification['status']=='PASS_EXACT_CONDITIONAL_MODEL' and verification['arrays_sha256']==comp['arrays_sha256']
assert analysis['integer_mean']=='496' and analysis['potential_range']==600
out=dict(status='SOURCE_AND_INTERFACE_AUDIT_ONLY',contributor_commit=read(HERE/'data/contributor-sources.json')['commit'],
    graph=dict(states=base['states'],edges=base['edges'],base_shapes=132,edge_shapes=505,nonempty_history_prefixes=74,
        state_count_symbols=5,edge_count_symbols=6,block_size=6**5,
        history_prefix_lengths=dict(collections.Counter(map(len,hist['prefixes']))),
        history_pattern_modes=dict(collections.Counter(p['mode'] for p in hist['patterns'])),
        history_count_caps=sorted(set(cap for p in hist['patterns'] for cap in p['caps'].values())),
        state_formula='(132 + 74)*6^5',edge_start='r < m-8',
        source_shape='canon(d[r..r+7])',target_shape='canon(d[r+1..r+8])',
        source_counts='min(6,alpha[r+3..r+7])',target_counts='min(6,alpha[r+4..r+8])',
        edge_counts='min(6,alpha[r+3..r+8])',share_centres='r+4 through r+8',history_initial=0,
        history_update='longest listed prefix that is a suffix of prefix[q_r] ++ [directionId_r]',
        source_metadata_sha256=sha(basepath),source_arrays_sha256=base['arrays_sha256'],
        shape_metadata_sha256=sha(shape_path),history_metadata_sha256=sha(history_path),
        comparison_tag=tag,comparison_metadata_sha256=sha(cur/(tag+'-model.json')),
        comparison_arrays_sha256=comp['arrays_sha256'],comparison_verification_sha256=sha(cur/(tag+'-verification.json')),
        conditional_mean=496,conditional_potential_range=600,
        caveat='Metadata and historical Python receipts inspected; no array reconstruction, graph rebuild or full potential Lean replay performed in this audit.'),
    current_sources=sources,inherited_receipts=receipts,
    remaining_obligations=['Actual-snake numeric state coding and exact history recognition invariant.',
      'Every exclusion guard in the exact builder is covered by a proved local premise with correct count saturation.',
      'Every history-signature credit is valid for every compatible actual eleven-transition word; initialise history at zero.',
      'Every recorded edge credit is at most the five actual coreShare terms, with overlapping rules combined by maximum.',
      'Bind exact finite data to Lean definitions and kernel-check the full potential inequalities and range.',
      'Instantiate the already proved overlap, boundary and global square budget with the resulting walk.'],
    result='The direction slicing/source/target/share-suffix identities are newly checked in WindowStateShift.lean. The contributor seven-centre automaton differs in count memory and has no prefix-history/share state. No new global numerical bound is established.')
(HERE/'data/interface-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(sources),'current sources;',len(receipts),'historical receipts; graph:',base['states'],base['edges'])
