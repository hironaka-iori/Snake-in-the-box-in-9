"""Build rejection-box data with original rule witnesses and exact saved-set checks.
No solver, Lean compilation, weights, or changes to earlier milestones.
"""
from pathlib import Path
import ast, collections, functools, gzip, hashlib, heapq, itertools, json, math, re, sys, time
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "work/solver_packages"))
import numpy as np
START = time.monotonic()
MAX_GAIN = "--max-gain" in sys.argv
TAG = "-max-gain" if MAX_GAIN else ""
PINS = {}
REPORT = {"status": "RUNNING", "scope": "Exact computational rejection-box cover. No closed Lean coverage certificate or new global bound."}
K = 6**6
FULL = (1 << K) - 1
BYTES = (K + 7)//8


def sha(raw): return hashlib.sha256(raw).hexdigest()
def filehash(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1024*1024), b''): h.update(b)
    return h.hexdigest()
def pin(p):
    PINS[p] = filehash(ROOT/p)
    return PINS[p]
def text(p):
    raw = (ROOT/p).read_bytes(); PINS[p] = sha(raw)
    return raw.decode('utf-8-sig')
def read(p): return json.loads(text(p))
def canon(w):
    labels = {}
    return tuple(labels.setdefault(x, len(labels)) for x in w)
def packed(mask): return int.from_bytes(np.packbits(mask, bitorder='little').tobytes(), 'little')
def maskhash(mask): return sha(mask.to_bytes(BYTES, 'little'))
def code_mask(codes):
    a = np.zeros(K, dtype=bool); a[codes] = True
    return packed(a)


def main():
    sm = read('milestones/59-extended-share-window/extended/data/model.json')
    md = read('milestones/67-critical-family-charge/data/full-model.json')
    refdata = read('milestones/85-reference-catalogue-union/data/reference-union.json')
    refs = refdata['rows']; assert len(refs) == 1378
    uniontext = text('milestones/85-reference-catalogue-union/lean/ReferenceUnion.lean')
    unionexpr = uniontext.split('def referenceKeys')[1].split(':=',1)[1].split('\n',1)[0]
    assert re.findall(r'keys([0-9]{2})',unionexpr) == [f'{i:02d}' for i in range(22)]
    lean_refs=[]; lean_picks=[]
    for chunk in range(22):
        name=f'{chunk:02d}'
        ct=text(f'milestones/85-reference-catalogue-union/lean/ReferenceChunk{name}.lean')
        keyliteral=ct.split(f'def keys{name}')[1].split(':=',1)[1].split('\ntheorem',1)[0].strip()
        pickliteral=ct.split(f'def picks{name}')[1].split(':=',1)[1].split(f'\ndef keys{name}',1)[0].strip()
        lean_refs.extend(ast.literal_eval(keyliteral))
        lean_picks.extend(ast.literal_eval(pickliteral.replace('false','False').replace('true','True')))
    assert lean_refs == [(r['directions'],r['symbols']) for r in refs]
    assert lean_picks == [(r['source_catalogue']==236,r['source_index']) for r in refs]
    normal = read('milestones/81-recovered-short-rule-retention/data/normalized-rules.json')
    caps = [x for x in normal if x['kind'] == 'caps']
    sums = [x for x in normal if x['kind'] == 'sum']
    short = caps + sums; assert len(caps) == 37 and len(sums) == 3
    meta = read('milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
    all_intervals = read('milestones/72-four-count-proof-closure/data/cases.json')
    intervals = [next(x for x in all_intervals if x['number'] == n) for n in meta['applied_cases']]
    assert len(intervals) == 10
    history_rules = [x for x in md['patterns'] if x['mode'] == 'exclusion']
    assert len(history_rules) == 3
    historytext=text('milestones/84-history-exclusion-retention/lean/HistoryExclusions.lean')
    ruleliteral=historytext.split('def historyRules')[1].split(':=',1)[1].split('\n',1)[0]
    assert re.findall(r'\(signature([0-9]+),([0-9]+)\)',ruleliteral)==[('0','5'),('1','3'),('2','5')]
    sigtext=text('milestones/84-history-exclusion-retention/lean/HistoryRealizations.lean')
    for i,row in enumerate(history_rules):
        sig=ast.literal_eval(sigtext.split(f'def signature{i}')[1].split(':=',1)[1].split('\n',1)[0])
        assert sig==row['signature']
        assert row['caps']=={str([5,3,5][i]):2}
    # Verify the concrete short and interval literal lists against their Lean sources.
    captext = text('milestones/81-recovered-short-rule-retention/lean/CapCatalogue.lean')
    parsedcaps = []
    for w, bs in re.findall(r'\((\[[0-9, ]+\]), \.caps (\[\([0-9, ()]+\])\)', captext.split('def capRules')[1].split('theorem cap_catalogue')[0]):
        parsedcaps.append((ast.literal_eval(w), [list(x) for x in ast.literal_eval(bs)]))
    assert parsedcaps == [(r['dirs'],r['caps']) for r in caps]
    sumtext = text('milestones/81-recovered-short-rule-retention/lean/SumCatalogue.lean')
    parsedsums = [(ast.literal_eval(w),ast.literal_eval(pos),int(c)) for w,pos,c in re.findall(r'\((\[[0-9, ]+\]), \.sum (\[[0-9, ]+\]) ([0-9]+)\)', sumtext.split('def sumRules')[1].split('theorem sum_catalogue')[0])]
    assert parsedsums == [(r['dirs'],r['positions'],r['cap']) for r in sums]
    itext = text('milestones/79-retained-edge-guards/lean/IntervalCatalogue.lean')
    literal = itext.split('def intervalKeys72')[1].split(':=',1)[1].split('\ntheorem interval_catalogue')[0].strip()
    assert [(w,[list(x) for x in bs]) for w,bs in ast.literal_eval(literal)] == [(r['dirs'],r['bounds']) for r in intervals]
    for p in ['milestones/87-retained-array-membership/lean/NumericRetention.lean', 'milestones/87-retained-array-membership/lean/RetainedPredicates.lean', 'milestones/84-history-exclusion-retention/lean/HistoryExclusions.lean', 'milestones/85-reference-catalogue-union/lean/ReferencePicks.lean', 'milestones/85-reference-catalogue-union/lean/ReferenceUnion.lean', 'milestones/87-retained-array-membership/data/NumericRetention-audit.json']:
        pin(p)
    for p, expected in refdata['inputs'].items(): assert pin(p) == expected
    graph_rel = 'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
    pin(graph_rel)
    with np.load(ROOT/graph_rel) as z:
        d,q = z['direction'],z['history']
        for k,a in [('direction',d),('history',q)]: assert sha(memoryview(a)) == meta['arrays_sha256'][k]
        blocks = 75*d+q; del d,q
        assert np.all(blocks[1:] >= blocks[:-1])
        offsets = np.r_[0,np.cumsum(np.bincount(blocks,minlength=37875))]; del blocks
        saved_codes = z['count_code']; assert sha(memoryview(saved_codes)) == meta['arrays_sha256']['count_code']
    dag_rel = 'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz'
    pin(dag_rel); dag = json.loads(gzip.decompress((ROOT/dag_rel).read_bytes()))
    assert dag['source_arrays_sha256'] == {k:meta['arrays_sha256'][k] for k in ['direction','history','count_code']}
    block_roots = dict(dag['blocks'])
    @functools.lru_cache(None)
    def decode(node, depth):
        if node == 0: return 0
        if node == 1: return (1 << 6**depth)-1
        row = dag['nodes'][node-2]; assert row[0] == depth
        result = 0
        for i,child in enumerate(row[1:]): result |= decode(child,depth-1) << (i*6**(depth-1))
        return result
    masks = [decode(root,6) for root in dag['roots']]
    assert len(masks) == 127
    codes = np.arange(K,dtype=np.int32)
    digits = np.stack([codes//6**j%6+1 for j in range(5,-1,-1)],axis=1)
    axis = {}
    for j in range(6):
        for lo in range(1,7):
            for hi in range(lo,7): axis[j,lo,hi] = packed((digits[:,j]>=lo)&(digits[:,j]<=hi))
    def box_mask(box):
        result = FULL
        for j,(lo,hi) in enumerate(box):
            if (lo,hi) != (1,6): result &= axis[j,lo,hi]
        return result
    def construct(di, witness):
        word = sm['extensions'][di]; family = witness['family']; i = witness['index']
        box = [[1,6] for _ in range(6)]
        if family == 'history':
            row = history_rules[i]; q = witness['history']; hist = tuple(md['prefixes'][q])+(di,)
            assert len(hist)>=3 and hist[-3:]==tuple(row['signature'])
            assert len(row['caps'])==1
            pos,cap = next(iter(row['caps'].items())); assert cap==2
            box[int(pos)] = [1,2]
        else:
            s,rev = witness['offset'],witness['reverse']
            if family == 'reference':
                row=refs[i]; width=len(row['symbols']); piece=word[s+2:s+width+3]
                assert s+width<=6 and canon(piece[::-1] if rev else piece)==tuple(row['directions'])
                for j,value in enumerate(row['symbols']): box[s+(width-1-j if rev else j)] = [value,value]
            elif family == 'short':
                row=short[i]; length=len(row['dirs']); piece=word[s:s+length]
                assert s+length<=9 and canon(piece[::-1] if rev else piece)==tuple(row['dirs'])
                if row['kind']=='caps':
                    tests=row['caps']
                else:
                    vals=witness['assignment']; assert len(vals)==len(row['positions']) and all(1<=v<=5 for v in vals) and sum(vals)<=row['cap']
                    tests=list(zip(row['positions'],vals))
                for j,value in tests:
                    pos=s+(length-j if rev else j)-3; assert 0<=pos<6
                    lo=1 if row['kind']=='caps' else value
                    box[pos] = [max(box[pos][0],lo),min(box[pos][1],value)]
            elif family == 'interval':
                row=intervals[i]; piece=word[s+2:s+7]
                assert 0<=s<=2 and canon(piece[::-1] if rev else piece)==tuple(row['dirs'])
                for j,(lo,hi) in enumerate(row['bounds']):
                    assert lo<=6 and (hi<6 or hi==21)
                    box[s+(3-j if rev else j)]=[max(1,lo),min(6,hi)]
            else: raise AssertionError(family)
        assert all(1<=lo<=hi<=6 for lo,hi in box)
        return tuple(map(tuple,box))
    # Group reference shapes so only direction-matching occurrences are visited.
    ref_orient = collections.defaultdict(list)
    for i,row in enumerate(refs):
        for reverse in [False,True]: ref_orient[canon(row['directions'][::-1] if reverse else row['directions'])].append((i,reverse))
    short_orient=[]
    assignments={i:[list(t) for t in itertools.product(range(1,6),repeat=len(r['positions'])) if sum(t)<=r['cap']] for i,r in enumerate(short) if r['kind']=='sum'}
    for i,row in enumerate(short):
        for reverse in [False,True]: short_orient.append((canon(row['dirs'][::-1] if reverse else row['dirs']),i,reverse))
    int_orient=[]
    for i,row in enumerate(intervals):
        for reverse in [False,True]: int_orient.append((canon(row['dirs'][::-1] if reverse else row['dirs']),i,reverse))
    def prune_boxes(boxes):
        ordered=sorted(boxes,key=lambda b:(-math.prod(hi-lo+1 for lo,hi in b),b))
        all_masks=[box_mask(b) for b in ordered]
        unpruned=functools.reduce(int.__or__,all_masks,0)
        union=0;chosen=[];chosen_masks=[]
        if MAX_GAIN:
            heap=[(-mask.bit_count(),i,0) for i,mask in enumerate(all_masks)]
            heapq.heapify(heap)
            while heap:
                negative,i,stamp=heapq.heappop(heap)
                gain=(all_masks[i]&~union).bit_count()
                if not gain:continue
                if stamp!=len(chosen):
                    heapq.heappush(heap,(-gain,i,len(chosen)));continue
                chosen.append(ordered[i]);chosen_masks.append(all_masks[i]);union|=all_masks[i]
        else:
            for box,mask in zip(ordered,all_masks):
                if mask&~union:chosen.append(box);chosen_masks.append(mask);union|=mask
        assert union==unpruned
        prefix=[0]
        for mask in chosen_masks:prefix.append(prefix[-1]|mask)
        suffix=0;final=[];final_masks=[]
        for i in range(len(chosen)-1,-1,-1):
            mask=chosen_masks[i]
            if mask&~(prefix[i]|suffix):final.append(chosen[i]);final_masks.append(mask);suffix|=mask
        final.reverse();final_masks.reverse();assert suffix==unpruned
        return unpruned,final,final_masks,len(chosen)
    global_boxes=[]; box_ids={}; directions=[]; history_mods=[]; block_records=[]
    class_boxes={};class_witnesses={};class_contexts=collections.defaultdict(list)
    totals=collections.Counter(); selected_by_family=collections.Counter(); compatible=0; incompatible=0; matched_edges=0
    shapes={tuple(w):i for i,w in enumerate(sm['direction_shapes'])}
    prefixes=[tuple(x) for x in md['prefixes']]
    for di,word in enumerate(sm['extensions']):
        unique={}; raw_count=0; raw_families=collections.Counter()
        def add(w):
            nonlocal raw_count
            box=construct(di,w); raw_count+=1;raw_families[w['family']]+=1
            unique.setdefault(box,w)
        for width in range(2,7):
            for s in range(7-width):
                for i,rev in ref_orient.get(canon(word[s+2:s+width+3]),[]):
                    row=refs[i]
                    add(dict(family='reference',index=i,source_catalogue=row['source_catalogue'],source_index=row['source_index'],offset=s,reverse=rev))
        for shape,i,rev in short_orient:
            row=short[i]; length=len(row['dirs']); positions=[x[0] for x in row['caps']] if row['kind']=='caps' else row['positions']
            for s in range(10-length):
                if canon(word[s:s+length])!=shape: continue
                if any(not 3<=s+(length-j if rev else j)<=8 for j in positions):continue
                base=dict(family='short',index=i,number=row['number'],source=row['source'],offset=s,reverse=rev)
                if row['kind']=='caps': add(base)
                else:
                    for assignment in assignments[i]: add(dict(base,assignment=assignment))
        for shape,i,rev in int_orient:
            for s in range(3):
                if canon(word[s+2:s+7])==shape: add(dict(family='interval',index=i,number=intervals[i]['number'],offset=s,reverse=rev))
        # Both variants preserve the exact union and remove every redundant final box.
        unpruned,final,final_masks,greedy_count=prune_boxes(unique)
        prefix=[0]
        for mask in final_masks:prefix.append(prefix[-1]|mask)
        suffix=0; entries=[]
        for i in range(len(final)-1,-1,-1):
            box,mask=final[i],final_masks[i];private=mask&~(prefix[i]|suffix);assert private
            private_code=(private&-private).bit_length()-1;suffix |=mask
            if box not in box_ids:box_ids[box]=len(global_boxes);global_boxes.append([list(x) for x in box])
            witness=unique[box];assert construct(di,witness)==box
            selected_by_family[witness['family']]+=1
            entries.append(dict(box=box_ids[box],witness=witness,private_code=private_code))
        entries.reverse();assert suffix==unpruned
        accepted=FULL^unpruned
        base_block=75*di;assert accepted==masks[block_roots[base_block]]
        record=dict(direction=di,dag_set=block_roots[base_block],accepted_count=accepted.bit_count(),rejection_sha256=maskhash(unpruned),raw_boxes=raw_count,unique_boxes=len(unique),after_forward_greedy=greedy_count,selected_boxes=len(entries),raw_by_family=dict(raw_families),selected=entries)
        directions.append(record)
        totals.update(raw=raw_count,unique=len(unique),forward=greedy_count,selected=len(entries))
        ps,ts=shapes[canon(word[:8])],shapes[canon(word[1:])]
        for q,prefix_word in enumerate(prefixes):
            block=75*di+q;left,right=int(offsets[block]),int(offsets[block+1])
            source_ok=q==0 or md['compatible_shapes'][q]==ps
            hist=prefix_word+(di,)
            choices=[j for j,p in enumerate(prefixes) if p and len(p)<=len(hist) and hist[-len(p):]==p]
            nq=max(choices,key=lambda j:len(prefixes[j])) if choices else 0
            target_ok=nq==0 or md['compatible_shapes'][nq]==ts
            if not source_ok:
                incompatible+=1;assert right==left and block not in block_roots
                continue
            assert target_ok
            compatible+=1;rejected=unpruned;mods=[]
            for i,row in enumerate(history_rules):
                if len(hist)>=3 and hist[-3:]==tuple(row['signature']):
                    witness=dict(family='history',index=i,history=q,signature=row['signature'])
                    box=construct(di,witness);mask=box_mask(box);newly=(mask&~rejected).bit_count();rejected|=mask
                    if box not in box_ids:box_ids[box]=len(global_boxes);global_boxes.append([list(x) for x in box])
                    mods.append(len(history_mods));history_mods.append(dict(direction=di,history=q,box=box_ids[box],witness=witness,newly_rejected=newly))
            actual=code_mask(saved_codes[left:right]);computed=FULL^rejected
            assert computed==actual==masks[block_roots[block]],(di,q)
            matched_edges+=right-left;block_records.append([block,di,block_roots[block],mods,nq])
            mi=block_roots[block]
            available=dict(unique)
            for mi_index in mods:
                mod=history_mods[mi_index]
                available[tuple(map(tuple,global_boxes[mod['box']]))]=mod['witness']
            if mi not in class_boxes:
                class_boxes[mi]=set(available)
                class_witnesses[mi]={box:dict(context=[di,q],witness=w) for box,w in available.items()}
            else:class_boxes[mi].intersection_update(available)
            class_contexts[mi].append([di,q])
        if di%100==0:print(f'direction {di}/505: selected {totals["selected"]}',flush=True)
    assert compatible==791 and incompatible==37084 and matched_edges==4947008
    assert {(x['direction'],x['history']) for x in history_mods}=={(177,43),(177,70),(180,68)}
    assert len(history_mods)==3
    main_distinct=len(global_boxes)
    class_results=[];class_complete=0;class_selected_total=0
    for mi in sorted(class_boxes):
        common=class_boxes[mi]
        union,selected,selected_masks,forward_count=prune_boxes(common)
        target=FULL^masks[mi]
        assert union&~target==0
        missing=target&~union
        entries=[]
        if not missing:
            class_complete+=1;class_selected_total+=len(selected)
            for box in selected:
                if box not in box_ids:box_ids[box]=len(global_boxes);global_boxes.append([list(x) for x in box])
                entries.append(dict(box=box_ids[box],example_source=class_witnesses[mi][box]))
        class_results.append(dict(dag_set=mi,contexts=class_contexts[mi],common_geometries=len(common),covers_rejected_set=not bool(missing),uncovered_rejected_codes=missing.bit_count(),selected=entries,selected_count=len(entries)))
    for p,before in PINS.items(): assert filehash(ROOT/p)==before,('changed input',p)
    payload=dict(format='Six-symbol rejection boxes, all bounds inclusive in 1..6; digit0 is most significant',
        box_catalogue=global_boxes,directions=directions,history_modifications=history_mods,blocks=block_records,class_intersections=class_results,
        block_fields=['block_id','base_direction','dag_set','history_modification_indices','next_history'],
        witness_offsets=dict(reference='count offset s, direction slice begins s+2',short='direction offset',interval='count offset s=0..2, direction slice begins s+2',history='no offset; sixth or fourth count digit'),
        input_sha256=PINS,script_sha256=filehash(Path(__file__)),scope=REPORT['scope'])
    raw=json.dumps(payload,separators=(',',':')).encode();compressed=gzip.compress(raw,mtime=0)
    out=HERE/f'data/box-cover-selected{TAG}.json.gz';out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(compressed)
    assert json.loads(gzip.decompress(out.read_bytes()))==payload
    REPORT.update(status='PASS_EXACT_REJECTION_BOX_COVER',base_directions=505,history_modifications=len(history_mods),compatible_blocks=compatible,incompatible_blocks=incompatible,matched_edges=matched_edges,
        raw_boxes=totals['raw'],unique_per_direction_boxes=totals['unique'],duplicates_removed=totals['raw']-totals['unique'],after_forward_union_pruning=totals['forward'],selected_box_occurrences=totals['selected'],global_distinct_selected_boxes=main_distinct,global_boxes_including_class_covers=len(global_boxes),selected_by_family=dict(selected_by_family),
        selected_min=min(r['selected_boxes'] for r in directions),selected_max=max(r['selected_boxes'] for r in directions),
        all_selected_boxes_have_original_witness=True,all_selected_boxes_have_private_code=True,all_complements_equal_saved_and_dag=True,
        history_details=history_mods,sum_assignment_counts={str(short[i]['number']):len(v) for i,v in assignments.items()},
        compressed_payload_bytes=len(compressed),uncompressed_payload_bytes=len(raw),payload_sha256=sha(compressed),payload_raw_sha256=sha(raw),
        pruning=('Lazy maximum-uncovered greedy' if MAX_GAIN else 'Descending-volume union pruning')+' followed by reverse redundancy deletion; all final boxes have private codes. No minimum-cardinality claim.',
        mask_classes=len(class_results),classes_with_full_common_geometry_cover=class_complete,class_selected_occurrences=class_selected_total,class_missing_codes=sum(x['uncovered_rejected_codes'] for x in class_results),
        input_sha256=PINS,script_sha256=filehash(Path(__file__)))


if __name__=='__main__':
    try:main()
    except BaseException as exc:
        REPORT['status']='FAIL_BOX_COVER';REPORT['error']=repr(exc);raise
    finally:
        REPORT['seconds']=time.monotonic()-START
        REPORT['script_sha256']=filehash(Path(__file__))
        REPORT['input_sha256']=PINS
        (HERE/'data').mkdir(parents=True,exist_ok=True)
        (HERE/f'data/box-cover-audit{TAG}.json').write_text(json.dumps(REPORT,indent=2)+'\n',encoding='utf-8')
        print({k:v for k,v in REPORT.items() if k not in ['input_sha256','history_details']},flush=True)
