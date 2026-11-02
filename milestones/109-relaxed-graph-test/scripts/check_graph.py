"""Test the relaxed count exclusion on all exact accepted graph keys."""
from pathlib import Path
import ast,gzip,hashlib,json,re,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
PINS={}
def raw(rel):
    data=(ROOT/rel).read_bytes();h=hashlib.sha256(data).hexdigest()
    assert rel not in PINS or PINS[rel]==h
    PINS[rel]=h
    return data
def read(rel):return json.loads(raw(rel))
def literal(source,name):
    m=re.search(r'\bdef '+re.escape(name)+r'\b[^=]*:=\s*',source);assert m
    at=m.end();at+=source[at]=='#';assert source[at]=='['
    depth=0
    for end in range(at,len(source)):
        depth+=(source[end]=='[')-(source[end]==']')
        if depth==0:return ast.literal_eval(source[at:end+1].replace('#[','['))
    raise AssertionError(name)
def canon(word):
    names={};return tuple(names.setdefault(int(x),len(names)) for x in word)
def main():
    start=time.monotonic()
    proof=read('milestones/108-smaller-reference-recovery/data/proof-summary.json')
    assert proof['status']=='PASS_RELAXED_EXCLUSION_AND_EIGHT_REFERENCE_ENTRIES'
    receipt=read('milestones/99-defined-potential-certificates/data/defined-potential-audit.json')
    assert receipt['status']=='PASS_ALL_DEFINED_GRAPH_POTENTIAL_INEQUALITIES'
    ds=literal(raw('milestones/77-direction-state-coverage/lean/DirectionTables.lean').decode('utf-8-sig'),'extensions')
    nodes=literal(raw('milestones/88-retention-diagram-certificate/lean/GraphData.lean').decode('utf-8-sig'),'retainedDiagram')
    roots=literal(raw('milestones/92-full-witness-batch/lean/BatchContextData.lean').decode('utf-8-sig'),'recordedClassRoots')
    blocks=literal(raw('milestones/92-full-witness-batch/lean/ContextAssignmentData.lean').decode('utf-8-sig'),'savedBlockClasses')
    dag=json.loads(gzip.decompress(raw('milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz')))
    assert nodes==dag['nodes'] and roots==dag['roots'] and blocks==list(map(tuple,dag['blocks']))
    assert len(ds)==505 and all(len(w)==9 for w in ds)
    assert len(nodes)==3981 and len(roots)==127 and len(blocks)==791
    for rel in ['milestones/85-reference-catalogue-union/lean/ReferenceInterface.lean',
                'milestones/88-retention-diagram-certificate/lean/BoxWitness.lean',
                'milestones/88-retention-diagram-certificate/lean/DigitReconstruction.lean',
                'milestones/92-full-witness-batch/lean/DefinedProofGraph.lean',
                'milestones/108-smaller-reference-recovery/lean/RelaxedReference108.lean']:
        raw(rel)
    graph_rel='milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
    raw(graph_rel)
    with np.load(ROOT/graph_rel) as z:
        saved={k:z[k] for k in ['direction','history','count_code']}
    assert {k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in saved.items()}==dag['source_arrays_sha256']
    saved_keys=((75*saved['direction'].astype(np.int64)+saved['history'])*46656+saved['count_code'])
    assert len(saved_keys)==4947008 and np.all(saved_keys[1:]>saved_keys[:-1])
    codes=np.arange(46656,dtype=np.int64)
    digits=np.stack([codes//6**j%6+1 for j in range(5,-1,-1)],axis=1)
    child=np.zeros((len(nodes)+2,7),dtype=np.int64);child[1]=1;child[2:]=nodes
    accepted=[]
    for root in roots:
        state=np.full(46656,root,dtype=np.int64)
        for j in range(6):state=child[state,digits[:,j]]
        assert np.all((state==0)|(state==1))
        accepted.append(codes[state==1])
    by_direction={};embeddings=[]
    for di,word in enumerate(ds):
        for s in range(2):
            part=word[s+2:s+8]
            for rev in [False,True]:
                if canon(part[::-1] if rev else part)!=(0,1,2,3,0,4):continue
                columns=[s+j for j in ([4,1,0] if rev else [0,3,4])]
                hit=(digits[:,columns[0]]<=2)&(digits[:,columns[1]]<=2)&(digits[:,columns[2]]<=3)
                e=dict(direction=di,word=word,count_offset=s,direction_offset=s+2,
                       reverse=rev,count_columns=columns,caps=[2,2,3],all_codes_hit=int(hit.sum()))
                embeddings.append(e);by_direction.setdefault(di,[]).append((e,hit))
    key_hash=hashlib.sha256();bad_hash=hashlib.sha256();total=0;bad_total=0;contexts=[];examples=[]
    for block,cls in blocks:
        di,qi=divmod(block,75);take=accepted[cls];keys=block*46656+take
        key_hash.update(keys.astype('<i8').tobytes())
        low,high=np.searchsorted(saved_keys,[block*46656,(block+1)*46656])
        assert np.array_equal(keys,saved_keys[low:high])
        forbidden=np.zeros(len(take),dtype=bool);counts=[]
        for e,hit in by_direction.get(di,[]):
            forbidden|=hit[take]
            counts.append(dict(count_offset=e['count_offset'],reverse=e['reverse'],rejected=int(hit[take].sum())))
        bad=keys[forbidden];bad_hash.update(bad.astype('<i8').tobytes())
        total+=len(take);bad_total+=len(bad)
        if by_direction.get(di):contexts.append(dict(direction=di,history=qi,diagram_class=cls,accepted=len(take),rejected=len(bad),embeddings=counts))
        for code in take[forbidden][:max(0,12-len(examples))]:
            examples.append(dict(direction=di,history=qi,count_code=int(code),word=ds[di],symbols=digits[code].tolist()))
    assert total==4947008 and key_hash.hexdigest()==receipt['accepted_full_keys_i64_sha256']
    assert all(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h for p,h in PINS.items())
    out=dict(status='NEW_ACCEPTED_KEYS_EXCLUDED' if bad_total else 'NO_ADDITIONAL_ACCEPTED_KEYS_EXCLUDED',
        previous_goal_turn='progress',seconds=time.monotonic()-start,accepted_full_keys=total,rejected_full_keys=bad_total,
        affected_profiles=['completed','conditional_floor18'],same_accepted_key_set_for_both_profiles=True,
        key_encoding='((75*direction)+history)*46656+count_code',accepted_keys_sha256=key_hash.hexdigest(),
        rejected_keys_sha256=bad_hash.hexdigest(),eligible_embeddings=embeddings,eligible_contexts=contexts,examples=examples,
        source_files_sha256=PINS,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Independent exact enumeration of every accepted defined-graph key; no new Lean theorem or numerical bound. The active graph and its certificates are unchanged.')
    (HERE/'data/graph-test.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:out[k] for k in ['status','seconds','accepted_full_keys','rejected_full_keys','examples']},indent=2))
    print('Eligible embeddings',len(embeddings),'eligible contexts',len(contexts))
if __name__=='__main__':main()
