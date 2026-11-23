from pathlib import Path
from collections import Counter
from itertools import groupby
import json,hashlib
D=Path(__file__).resolve().parent;R=D.parent
rd=lambda f:[json.loads(z) for z in (D/f).read_text().splitlines()]
def physical(p):
    assert p[0]==0 and len(set(p))==len(p) and all(0<=v<512 for v in p)
    return [(x^y).bit_length()-1 for x,y in zip(p,p[1:])]
def edges(w):
    p=[0]
    for a in w:p.append(p[-1]^1<<a)
    return p
def defects(v):return [(a,b) for b,y in enumerate(v) for a in range(max(0,b-1)) if (v[a]^y).bit_count()<=1]
def ranges(segments,n):
    last=0
    for s,k in segments:
        assert s>=last and k in (3,4) and s+k<=n
        yield from ((i,1) for i in range(last,s));yield s,k;last=s+k
    yield from ((i,1) for i in range(last,n))
ctrl=rd('control191_3129.jsonl');expect=(R/'q9_gap_generations/prior191.words').read_text().split();scrambled=0
for o in ctrl:
    src=list(map(int,o['w']));orig=list(map(int,expect[o['source']]));parts=list(ranges(o['spans'],191));scrambled+=bool(defects(edges(src)))
    assert all(sorted(orig[s:s+k])==sorted(src[s:s+k]) for s,k in parts)
    grp={v:g for g,B in enumerate([*o['pairs'],[o['single']]]) for v in B}
    for field in ('path','literal_path'):
        q=o[field];word=physical(q);assert len(q)==192 and not defects(q) and all((x^y).bit_count()==1 for x,y in zip(q,q[1:]))
        for s,k in parts:
            if field=='literal_path':assert sorted(word[s:s+k])==sorted(src[s:s+k])
            else:assert sorted(grp[x] for x in word[s:s+k])==sorted(grp[x] for x in src[s:s+k])
for o in rd('any191.jsonl'):
    src=list(map(int,o['w']));dst=src.copy()
    for s,seq in sorted(o['used']):
        assert sorted(seq)==sorted(src[s:s+len(seq)]);dst[s:s+len(seq)]=seq
    p=edges(dst);assert len(p)==192 and p==o['path'] and not defects(p)
tab=Counter()
for z in rd('small.jsonl'):assert z['truth']==z['rows'].get('FOUND',0);tab.update(z['rows'])
deep=json.loads((D/'deep.json').read_text());tab.update(deep['matched'])
retry={(z['file'],z['row']):z['status'] for z in rd('retry.jsonl')};target={};anyw={};detail={}
for n in (195,196):
    C=Counter();names=[f'target{n}_{n+6129}.jsonl',f'cross{n}.jsonl']
    for f in names:
        for i,z in enumerate(rd(f)):
            assert len(z['w'])==n;list(ranges(z['spans'],n));assert 2<=len(z['spans'])<=10 and sorted([z['single'],*[v for a in z['pairs'] for v in a]])==list(range(9))
            if z['status']=='UNKNOWN':assert (f,i) in retry
            C[retry.get((f,i),z['status'])]+=1
    target[n]=C
    rs=rd(f'any{n}.jsonl');homes={}
    for z in rs:
        if z['src'] not in homes:homes[z['src']]=(R/'q9_via_q10'/z['src']).read_text().splitlines()
        raw=homes[z['src']][z['i']]
        if z['src'].endswith('.txt'):
            p=list(map(int,raw.split()[2:]));assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:]));w=''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
        else:w=raw
        assert w==z['w']
    anyw[n]=Counter(z['status'] for z in rs)
    detail[n]=dict(actual_source_defect_counts=Counter(len(defects(edges(list(map(int,z['w']))))) for z in rs))
    reduced=D/f'near{n}.jsonl'
    if reduced.exists():
        rows=rd(reduced.name)
        for z in rows:
            if 'word' not in z:continue
            p=edges(list(map(int,z['word'])));assert len(set(p))==len(p) and list(map(list,defects(p)))==z['defects'] and len(z['defects'])<=z['upper']
        detail[n]['limited_near_search']=Counter(z['status'] for z in rows)
audit=dict(original_model_sha256=hashlib.sha256((R/'q9_shuffle_blocks/search.py').read_bytes()).hexdigest(),all_small_original=tab,all_Q5_long_witnesses=deep['complete_physical_Q5']['13'],q9_controls=len(ctrl),invalid_scrambled=scrambled,original_target_after_retry=target,free_window_physical=anyw,physical_control=Counter(z['status'] for z in rd('any191.jsonl')),physical_small=json.loads((D/'check_any.json').read_text()),samples=rd('sample_replay.jsonl'),detail=detail)
print(json.dumps(audit,indent=1))
