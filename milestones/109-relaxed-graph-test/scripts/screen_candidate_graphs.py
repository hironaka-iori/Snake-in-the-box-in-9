"""Measure proposed local relaxations on the unchanged graph; hypotheses only."""
from pathlib import Path
import gzip,hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import check_graph as base
np=base.np;HERE=base.HERE;ROOT=base.ROOT
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda b:hashlib.sha256(b).hexdigest()
screen=read(HERE/'data/small-core-screen.json');verified=read(HERE/'data/graph-test.json')
assert verified['status']=='NO_ADDITIONAL_ACCEPTED_KEYS_EXCLUDED'
for path,digest in verified['source_files_sha256'].items():assert sha((ROOT/path).read_bytes())==digest
dag=json.loads(gzip.decompress((ROOT/'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz').read_bytes()))
ds=base.literal((ROOT/'milestones/77-direction-state-coverage/lean/DirectionTables.lean').read_text(),'extensions')
codes=np.arange(46656,dtype=np.int64)
digits=np.stack([codes//6**j%6+1 for j in range(5,-1,-1)],axis=1)
child=np.zeros((len(dag['nodes'])+2,7),dtype=np.int64);child[1]=1;child[2:]=dag['nodes']
accepted=[]
for root in dag['roots']:
    node=np.full(46656,root,dtype=np.int64)
    for j in range(6):node=child[node,digits[:,j]]
    assert np.all((node==0)|(node==1))
    accepted.append(codes[node==1])
key_hash=hashlib.sha256()
for block,cls in dag['blocks']:key_hash.update((block*46656+accepted[cls]).astype('<i8').tobytes())
assert key_hash.hexdigest()==verified['accepted_keys_sha256']
rows=[]
for candidate in screen['candidates']:
    bounds=candidate['proposed_bounds'];width=len(bounds);word=tuple(candidate['directions'])
    assert len(word)==width+1 and all(lo<=6 and (hi<6 or hi==21) for lo,hi in bounds)
    masks={};embeddings=0
    for di,d in enumerate(ds):
        mask=np.zeros(46656,dtype=bool)
        for s in range(7-width):
            part=d[s+2:s+width+3]
            assert len(part)==width+1
            for rev in [False,True]:
                if base.canon(part[::-1] if rev else part)!=word:continue
                embeddings+=1;hit=np.ones(46656,dtype=bool)
                for i,(lo,hi) in enumerate(bounds):
                    col=s+(width-1-i if rev else i)
                    hit&=(lo<=digits[:,col])&(digits[:,col]<=hi)
                mask|=hit
        if mask.any():masks[di]=mask
    count=0;contexts=0;examples=[];digest=hashlib.sha256()
    for block,cls in dag['blocks']:
        di,qi=divmod(block,75);take=accepted[cls]
        if di not in masks:continue
        bad=take[masks[di][take]];count+=len(bad);contexts+=bool(len(bad))
        digest.update((block*46656+bad).astype('<i8').tobytes())
        for code in bad[:max(0,5-len(examples))]:
            examples.append(dict(direction=di,history=qi,count_code=int(code),directions=ds[di],symbols=digits[code].tolist()))
    rows.append(dict(root=candidate['root'],proposed_bounds=bounds,new_reference_entries=len(candidate['new_reference_indices']),
        recorded_hints=candidate['recorded_hints'],eligible_embeddings=embeddings,rejected_full_keys=count,
        affected_contexts=contexts,rejected_keys_sha256=digest.hexdigest(),examples=examples))
rows.sort(key=lambda r:(-r['rejected_full_keys'],-r['new_reference_entries'],r['recorded_hints']))
out=dict(status='HYPOTHETICAL_RELAXATION_GRAPH_SCREEN',candidates=rows,
    source_screen_sha256=sha((HERE/'data/small-core-screen.json').read_bytes()),graph_test_sha256=sha((HERE/'data/graph-test.json').read_bytes()),
    script_sha256=sha(Path(__file__).read_bytes()),
    scope='Exact graph enumeration conditional on each proposed exclusion. No candidate relaxation is proved here, no graph is changed, and no numerical upper bound is claimed.')
(HERE/'data/candidate-graph-screen.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
for row in rows[:8]:print(row['root'],'graph keys',row['rejected_full_keys'],'new reference entries',row['new_reference_entries'])
