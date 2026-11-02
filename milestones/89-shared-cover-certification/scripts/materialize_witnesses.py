"""Materialize and independently validate all context-specific common-cover witnesses.
Inputs in milestones 88 and earlier are read-only. No solver or Lean invocation.
"""
from pathlib import Path
import ast, collections, gzip, hashlib, itertools, json, re, time
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
START = time.monotonic()
PINS = {}
REPORT = {"status":"RUNNING", "scope":"Computational witness materialization and validity checks; no new Lean theorem or global bound."}


def sha(raw): return hashlib.sha256(raw).hexdigest()
def filehash(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def pin(relative):
    result=filehash(ROOT/relative);PINS[relative]=result;return result
def text(relative):
    raw=(ROOT/relative).read_bytes();PINS[relative]=sha(raw);return raw.decode('utf-8-sig')
def read(relative):return json.loads(text(relative))
def canon(word):
    seen={};return tuple(seen.setdefault(x,len(seen)) for x in word)


def main():
    audit=read('milestones/88-retention-diagram-certificate/data/box-cover-audit-max-gain.json')
    source_rel='milestones/88-retention-diagram-certificate/data/box-cover-selected-max-gain.json.gz'
    compressed=(ROOT/source_rel).read_bytes();PINS[source_rel]=sha(compressed)
    assert PINS[source_rel]==audit['payload_sha256']=='c81ab4d006d9f40e74b1b3ed1c655b11282e96db8bd8242975042414f7090e93'
    raw=gzip.decompress(compressed);assert sha(raw)==audit['payload_raw_sha256']
    source=json.loads(raw);del raw,compressed
    for relative,expected in source['input_sha256'].items():assert pin(relative)==expected
    boxes=[tuple(map(tuple,b)) for b in source['box_catalogue']]
    assert len(set(boxes))==len(boxes)==2637
    classes=[(r['dag_set'],[e['box'] for e in r['selected']]) for r in source['class_intersections']]
    assert len(classes)==127 and sum(len(g) for _,g in classes)==82659
    assert [i for i,_ in classes]==list(range(127))
    class_ids=dict(classes)
    context_rows=source['blocks']
    assert len(context_rows)==791 and len({r[0] for r in context_rows})==791
    assert {tuple(c) for r in source['class_intersections'] for c in r['contexts']}=={divmod(r[0],75) for r in context_rows}
    for r in source['class_intersections']:
        assert r['covers_rejected_set'] and r['uncovered_rejected_codes']==0
        assert all(next(x[2] for x in context_rows if x[0]==75*d+q)==r['dag_set'] for d,q in r['contexts'])
    del source['directions'],source['class_intersections']
    model=read('milestones/59-extended-share-window/extended/data/model.json')
    historydata=read('milestones/67-critical-family-charge/data/full-model.json')
    refdata=read('milestones/85-reference-catalogue-union/data/reference-union.json');refs=refdata['rows']
    normal=read('milestones/81-recovered-short-rule-retention/data/normalized-rules.json')
    caps=[r for r in normal if r['kind']=='caps'];sums=[r for r in normal if r['kind']=='sum'];short=caps+sums
    metadata=read('milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
    original_intervals=read('milestones/72-four-count-proof-closure/data/cases.json')
    intervals=[next(r for r in original_intervals if r['number']==n) for n in metadata['applied_cases']]
    histories=[r for r in historydata['patterns'] if r['mode']=='exclusion']
    assert (len(refs),len(caps),len(sums),len(intervals),len(histories))==(1378,37,3,10,3)
    # Match the exact literal catalogue order used by the Lean Witness constructors.
    uniontext=text('milestones/85-reference-catalogue-union/lean/ReferenceUnion.lean')
    assert re.findall(r'keys([0-9]{2})',uniontext.split('def referenceKeys')[1].split(':=',1)[1].split('\n',1)[0])==[f'{i:02d}' for i in range(22)]
    literals=[];picks=[]
    for i in range(22):
        name=f'{i:02d}';t=text(f'milestones/85-reference-catalogue-union/lean/ReferenceChunk{name}.lean')
        literals+=ast.literal_eval(t.split(f'def keys{name}')[1].split(':=',1)[1].split('\ntheorem',1)[0].strip())
        pl=t.split(f'def picks{name}')[1].split(':=',1)[1].split(f'\ndef keys{name}',1)[0].strip()
        picks+=ast.literal_eval(pl.replace('false','False').replace('true','True'))
    assert literals==[(r['directions'],r['symbols']) for r in refs]
    assert picks==[(r['source_catalogue']==236,r['source_index']) for r in refs]
    t=text('milestones/81-recovered-short-rule-retention/lean/CapCatalogue.lean')
    pc=[(ast.literal_eval(w),[list(x) for x in ast.literal_eval(bs)]) for w,bs in re.findall(r'\((\[[0-9, ]+\]), \.caps (\[\([0-9, ()]+\])\)',t.split('def capRules')[1].split('theorem cap_catalogue')[0])]
    assert pc==[(r['dirs'],r['caps']) for r in caps]
    t=text('milestones/81-recovered-short-rule-retention/lean/SumCatalogue.lean')
    ps=[(ast.literal_eval(w),ast.literal_eval(pos),int(c)) for w,pos,c in re.findall(r'\((\[[0-9, ]+\]), \.sum (\[[0-9, ]+\]) ([0-9]+)\)',t.split('def sumRules')[1].split('theorem sum_catalogue')[0])]
    assert ps==[(r['dirs'],r['positions'],r['cap']) for r in sums]
    t=text('milestones/79-retained-edge-guards/lean/IntervalCatalogue.lean')
    pi=ast.literal_eval(t.split('def intervalKeys72')[1].split(':=',1)[1].split('\ntheorem interval_catalogue')[0].strip())
    assert [(w,[list(x) for x in bs]) for w,bs in pi]==[(r['dirs'],r['bounds']) for r in intervals]
    t=text('milestones/84-history-exclusion-retention/lean/HistoryExclusions.lean')
    assert re.findall(r'\(signature([0-9]+),([0-9]+)\)',t.split('def historyRules')[1].split(':=',1)[1].split('\n',1)[0])==[('0','5'),('1','3'),('2','5')]
    t=text('milestones/84-history-exclusion-retention/lean/HistoryRealizations.lean')
    for i,r in enumerate(histories):
        assert ast.literal_eval(t.split(f'def signature{i}')[1].split(':=',1)[1].split('\n',1)[0])==r['signature']
        assert r['caps']=={str([5,3,5][i]):2}
    pin('milestones/88-retention-diagram-certificate/lean/BoxWitness.lean')
    pin('milestones/88-retention-diagram-certificate/lean/Boxes.lean')
    pin('milestones/88-retention-diagram-certificate/scripts/build_boxes.py')
    words=model['extensions'];prefixes=[tuple(p) for p in historydata['prefixes']]
    assert len(words)==len(set(map(tuple,words)))==505 and len(prefixes)==75
    shapes={tuple(w):i for i,w in enumerate(model['direction_shapes'])}
    by_direction=collections.defaultdict(list)
    for row in context_rows:by_direction[row[1]].append(row)
    assert set(by_direction)==set(range(505))
    geometry_id={b:i for i,b in enumerate(boxes)}
    oriented_refs=collections.defaultdict(list)
    for i,r in enumerate(refs):
        for rev in [0,1]:oriented_refs[canon(r['directions'][::-1] if rev else r['directions'])].append((i,rev,r['symbols'][::-1] if rev else r['symbols']))
    sum_assignments={i:list(itertools.product(range(1,6),repeat=len(r['positions']))) for i,r in enumerate(short) if r['kind']=='sum'}
    for i in sum_assignments:sum_assignments[i]=[a for a in sum_assignments[i] if sum(a)<=short[i]['cap']]

    def validate(q,di,b,w):
        # Direct interpretation of BoxWitness.lean validity tests, separate from
        # the oriented-rule occurrence constructor below. No raw-map lookup.
        assert len(b)==6 and q<75 and di<505 and all(1<=lo<=hi<=6 for lo,hi in b)
        family,i,s,rev=w;word=words[di]
        if family==0:
            assert i<len(refs);r=refs[i];width=len(r['symbols']);assert 2<=width and s+width<=6
            piece=word[s+2:s+width+3]
            assert canon(piece[::-1] if rev else piece)==tuple(r['directions'])
            counts=r['symbols'][::-1] if rev else r['symbols']
            assert all(b[s+j]==(v,v) for j,v in enumerate(counts))
        elif family==1:
            assert i<len(short) and s<10;r=short[i];length=len(r['dirs']);assert s+length<=9
            positions=[x[0] for x in r['caps']] if r['kind']=='caps' else r['positions']
            indices=[s+(length-j if rev else j)-3 for j in positions]
            assert all(0<=j<6 for j in indices)
            piece=word[s:s+length];assert canon(piece[::-1] if rev else piece)==tuple(r['dirs'])
            upper=[b[j][1] for j in indices]
            if r['kind']=='caps':assert all(v<=cap for v,(_,cap) in zip(upper,r['caps']))
            else:assert sum(upper)<=r['cap'] and all(v<6 for v in upper)
        elif family==2:
            assert i<len(intervals) and s<3;r=intervals[i];assert len(r['bounds'])==4
            piece=word[s+2:s+7];assert canon(piece[::-1] if rev else piece)==tuple(r['dirs'])
            for j,(lo,hi) in enumerate(r['bounds']):
                pos=s+(3-j if rev else j);assert pos<6 and lo<=b[pos][0] and b[pos][1]<=hi
        elif family==3:
            assert i<len(histories) and s==rev==0;r=histories[i];pos=[5,3,5][i]
            # extensions.idxOf the decoded valid table entry is exactly di.
            hist=prefixes[q]+(di,);assert len(hist)>=3 and hist[-3:]==tuple(r['signature']) and b[pos][1]<=2
        else:raise AssertionError(family)

    witnesses=[];witness_id={};witness_lists=[];list_id={};contexts=[]
    total_occurrences=raw_occurrences=0;by_family=collections.Counter();context_history=[]
    nonhistory_pairs=set();nonhistory_occurrences=0;nonhistory_consistency={}
    exact_groups=collections.defaultdict(list);erased_groups=collections.defaultdict(list)
    direction_groups=collections.defaultdict(set);chosen_rules=collections.Counter()
    for di in range(505):
        word=words[di];needed={g for row in by_direction[di] for g in class_ids[row[2]]}
        available={}
        def add(b,w):
            nonlocal raw_occurrences
            raw_occurrences+=1;b=tuple(map(tuple,b));g=geometry_id.get(b)
            if g in needed and (g not in available or w<available[g]):available[g]=w
        for width in range(2,7):
            for s in range(7-width):
                for i,rev,symbols in oriented_refs.get(canon(word[s+2:s+width+3]),[]):
                    b=[[1,6] for _ in range(6)]
                    for j,v in enumerate(symbols):b[s+j]=[v,v]
                    add(b,(0,i,s,rev))
        for i,r in enumerate(short):
            length=len(r['dirs']);original_positions=[x[0] for x in r['caps']] if r['kind']=='caps' else r['positions']
            for rev in [0,1]:
                shape=canon(r['dirs'][::-1] if rev else r['dirs'])
                positions=[length-j if rev else j for j in original_positions]
                for s in range(10-length):
                    if canon(word[s:s+length])!=shape:continue
                    columns=[s+j-3 for j in positions]
                    if any(j<0 or j>=6 for j in columns):continue
                    assignments=[[cap for _,cap in r['caps']]] if r['kind']=='caps' else sum_assignments[i]
                    for values in assignments:
                        b=[[1,6] for _ in range(6)]
                        for pos,v in zip(columns,values):
                            lo=1 if r['kind']=='caps' else v
                            b[pos]=[max(b[pos][0],lo),min(b[pos][1],v)]
                        add(b,(1,i,s,rev))
        for i,r in enumerate(intervals):
            for rev in [0,1]:
                shape=canon(r['dirs'][::-1] if rev else r['dirs']);bounds=r['bounds'][::-1] if rev else r['bounds']
                for s in range(3):
                    if canon(word[s+2:s+7])!=shape:continue
                    b=[[1,6] for _ in range(6)]
                    for j,(lo,hi) in enumerate(bounds):b[s+j]=[max(1,lo),min(6,hi)]
                    add(b,(2,i,s,rev))
        for row in by_direction[di]:
            block,assert_di,ci,oldmods,nq=row;q=block%75;assert assert_di==di==block//75
            ps,ts=shapes[canon(word[:8])],shapes[canon(word[1:])]
            assert q==0 or historydata['compatible_shapes'][q]==ps
            assert nq==0 or historydata['compatible_shapes'][nq]==ts
            local_history={};hist=prefixes[q]+(di,)
            for i,r in enumerate(histories):
                if len(hist)>=3 and hist[-3:]==tuple(r['signature']):
                    b=[[1,6] for _ in range(6)];b[[5,3,5][i]]=[1,2];g=geometry_id[tuple(map(tuple,b))]
                    local_history[g]=(3,i,0,0)
            aligned=[];history_positions=[]
            for position,g in enumerate(class_ids[ci]):
                w=available.get(g,local_history.get(g));assert w is not None,(di,q,ci,g)
                # Exact available geometry and independent constructor validity.
                validate(q,di,boxes[g],w)
                if w not in witness_id:witness_id[w]=len(witnesses);witnesses.append(list(w))
                wi=witness_id[w];aligned.append(wi);by_family[w[0]]+=1;total_occurrences+=1
                chosen_rules[(w[0],w[1])]+=1
                if w[0]==3:history_positions.append(position)
                else:
                    nonhistory_occurrences+=1;nonhistory_pairs.add((di,g))
                    if (di,g) in nonhistory_consistency:assert nonhistory_consistency[di,g]==wi
                    nonhistory_consistency[di,g]=wi
            key=tuple(aligned)
            if key not in list_id:list_id[key]=len(witness_lists);witness_lists.append(aligned)
            li=list_id[key];contexts.append([block,ci,li])
            exact_groups[ci,key].append(block)
            erased=tuple(-1 if witnesses[wi][0]==3 else wi for wi in aligned)
            erased_groups[ci,erased].append(block);direction_groups[di,ci].add(erased)
            if history_positions:context_history.append(dict(block=block,direction=di,history=q,class_id=ci,positions=history_positions,witness_ids=[aligned[j] for j in history_positions]))
        if di%100==0:print(f'direction {di}/505; materialized {total_occurrences} witness occurrences',flush=True)
    assert [r[0] for r in contexts]==[r[0] for r in context_rows]
    assert len(contexts)==791 and len(classes)==127
    assert all(len(v)==1 for v in direction_groups.values())
    assert {(x['direction'],x['history']) for x in context_history}=={(177,43),(177,70),(180,68)}
    # Round-trip every context to the same class order and validate every row again.
    roundtrip=0
    for block,ci,li in contexts:
        di,q=divmod(block,75);ids=witness_lists[li];assert len(ids)==len(class_ids[ci])
        for g,wi in zip(class_ids[ci],ids):validate(q,di,boxes[g],witnesses[wi]);roundtrip+=1
    assert roundtrip==total_occurrences
    changed_only_history=[]
    context_lookup={b:(ci,li) for b,ci,li in contexts}
    for (ci,erased),blocks in erased_groups.items():
        lists=sorted({context_lookup[b][1] for b in blocks})
        if len(lists)>1:changed_only_history.append(dict(class_id=ci,blocks=blocks,witness_list_ids=lists))
    for relative,expected in PINS.items():assert filehash(ROOT/relative)==expected,('input changed',relative)
    payload=dict(format='Context witnesses v1; all IDs zero-based; class geometry order inherited unchanged from milestone88',
        family_codes=['reference','short','interval','history'],witness_fields=['family_code','Lean_rule_index','offset','reverse_0_or_1'],
        history_witness_encoding='[3,ruleIndex,0,0]; ignores placeholder offset/reverse',
        box_catalogue=[[list(x) for x in b] for b in boxes],classes=[[ci,ids] for ci,ids in classes],
        class_fields=['class_id','geometry_ids_in_original_order'],witnesses=witnesses,witness_lists=witness_lists,
        contexts=contexts,context_fields=['block_id=75*direction+history','class_id','witness_list_id'],
        rule_sources=dict(reference=[[r['source_catalogue'],r['source_index']] for r in refs],short=[[r['number'],r['source']] for r in short],interval=[r['number'] for r in intervals],history=[[r['signature'],[5,3,5][i]] for i,r in enumerate(histories)]),
        history_contexts=context_history,source_payload_sha256=audit['payload_sha256'],input_sha256=PINS,
        script_sha256=filehash(Path(__file__)),scope=REPORT['scope'])
    raw=json.dumps(payload,separators=(',',':')).encode();compressed=gzip.compress(raw,mtime=0)
    out=HERE/'data/context-witnesses.json.gz';out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(compressed)
    restored=json.loads(gzip.decompress(out.read_bytes()));assert restored==payload
    REPORT.update(status='PASS_ALL_CONTEXT_WITNESSES',classes=127,contexts=791,class_box_occurrences=82659,
        materialized_witness_occurrences=total_occurrences,independent_validations=roundtrip,roundtrip_validations=roundtrip,
        raw_nonhistory_occurrences_reconstructed=raw_occurrences,unique_witness_constructors=len(witnesses),unique_aligned_witness_lists=len(witness_lists),
        stored_aligned_list_entries=sum(map(len,witness_lists)),family_occurrences={str(k):v for k,v in by_family.items()},
        nonhistory_occurrences=nonhistory_occurrences,distinct_direction_geometry_nonhistory_pairs=len(nonhistory_pairs),
        direction_only_reusable_occurrences=nonhistory_occurrences-len(nonhistory_pairs),nonhistory_witness_choice_independent_of_q=True,
        distinct_direction_class_pairs=len(direction_groups),exact_class_list_groups=len(exact_groups),history_erased_class_list_groups=len(erased_groups),
        list_groups_differing_only_in_history=changed_only_history,history_contexts=context_history,
        history_free_contexts=791-len(context_history),all_class_ids_and_box_orders_preserved=True,all_contexts_have_full_aligned_lists=True,
        payload_bytes=len(compressed),payload_raw_bytes=len(raw),payload_sha256=sha(compressed),payload_raw_sha256=sha(raw),
        script_sha256=filehash(Path(__file__)),input_sha256=PINS)


if __name__=='__main__':
    try:main()
    except BaseException as exc:
        REPORT['status']='FAIL_CONTEXT_WITNESSES';REPORT['error']=repr(exc);raise
    finally:
        REPORT['seconds']=time.monotonic()-START;REPORT['script_sha256']=filehash(Path(__file__));REPORT['input_sha256']=PINS
        (HERE/'data').mkdir(parents=True,exist_ok=True)
        (HERE/'data/context-witnesses-audit.json').write_text(json.dumps(REPORT,indent=2)+'\n',encoding='utf-8')
        print({k:v for k,v in REPORT.items() if k not in ['input_sha256','history_contexts','list_groups_differing_only_in_history']},flush=True)
