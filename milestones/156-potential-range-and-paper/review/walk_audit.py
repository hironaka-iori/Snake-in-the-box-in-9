"""Bounded selected-row audit. No optimizer or all-edge inequality scan."""
from pathlib import Path
import sys, json, hashlib, gc, zipfile, struct, ast
from fractions import Fraction

R = Path(__file__).resolve().parents[3]
H = Path(__file__).resolve().parent
sys.path.insert(0, str(R/'milestones/155-share17-replay/scripts'))
from native_resources import snapshot
resources = snapshot()
assert not resources['errors'] and resources['free_bytes'] >= 1.5*1024**3
pins = {}
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()
def read(rel):
    p=R/rel; pins[rel]=sha(p)
    return json.loads(p.read_text(encoding='utf-8-sig'))
def canon(word):
    names={}
    return ''.join(str(names.setdefault(int(x),len(names))) for x in word)
def shape(word): return min(canon(word),canon(word[::-1]))
base='milestones/156-potential-range-and-paper/'
result=read(base+'data/share17-range496/result.json')
plan=read('work/after155-potential-plan.json')
prep=read(base+'data/preparation.json')
meta=read('milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
ds=read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
rules=read('milestones/120-nine-transition-window/data/full-rules.json')
removed_rel='milestones/144-countfree-share18/data/share18-impact/removed-indices.json'
removed=set(read(removed_rel))
assert pins[removed_rel]==result['input_pins'][removed_rel]
assert len(removed)==4947008-4661572
walk=result['deficit_walk']; cycle=plan['fourteen_cycle']['rows']
ids=sorted(set([x['source_edge'] for x in walk]+[x['edge'] for x in cycle]))
assert all(x not in removed for x in ids)
del removed
archive_rel='milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
pins[archive_rel]=sha(R/archive_rel)
assert pins[archive_rel]==result['input_pins'][archive_rel]
columns={}; array_audit={}
with zipfile.ZipFile(R/archive_rel) as z:
    for key in ['U','V','weight','direction','count_code']:
        resource=snapshot()
        assert not resource['errors'] and resource['free_bytes']>=1.5*1024**3
        with z.open(key+'.npy') as stream:
            assert stream.read(6)==b'\x93NUMPY'
            version=stream.read(2)
            headerlen=struct.unpack('<H' if version[0]==1 else '<I',stream.read(2 if version[0]==1 else 4))[0]
            header=ast.literal_eval(stream.read(headerlen).decode('latin1'))
            assert header['shape']==(4947008,) and not header['fortran_order']
            dtype=header['descr']; assert dtype[0] in ['<','|']
            width=int(dtype[2:]); assert dtype[1] in ['i','u']
            h=hashlib.sha256(); offset=0; selected={}
            for block in iter(lambda:stream.read(1048576),b''):
                h.update(block)
                for i in ids:
                    start=i*width-offset
                    if 0<=start<len(block):
                        assert start+width<=len(block)
                        selected[i]=int.from_bytes(block[start:start+width],'little',signed=dtype[1]=='i')
                offset+=len(block)
            assert offset==4947008*width and len(selected)==len(ids)
        digest=h.hexdigest()
        assert digest==meta['arrays_sha256'][key]
        columns[key]=selected
        array_audit[key]=dict(sha256=digest,dtype=dtype,length=4947008)
        gc.collect()
for rel in [base+'scripts/potential_range.py',base+'scripts/reconstruct144.py',
            'milestones/155-share17-replay/scripts/native_resources.py','work/after155-potential-plan.md']:
    pins[rel]=sha(R/rel)
    if rel in prep['script_pins']: assert pins[rel]==prep['script_pins'][rel]
assert pins['work/after155-potential-plan.json']==prep['plan_sha256']
for rel in pins:
    if rel in result['input_pins']: assert pins[rel]==result['input_pins'][rel]

def audit_row(i):
    code=columns['count_code'][i]
    counts=[code//6**j%6+1 for j in range(5,-1,-1)]
    assert sum((c-1)*6**(5-j) for j,c in enumerate(counts))==code
    d=ds[columns['direction'][i]]
    old=0; applied=[]
    for rule in rules:
        selected=d[3:9]
        if shape(selected)!=shape(rule['directions']): continue
        five=counts[1:6]
        if canon(selected)!=shape(selected): five=five[::-1]
        applicable=all(lo<=c and (21 if c==6 else c)<=hi for c,(lo,hi) in zip(five,rule['bounds']))
        if applicable:
            credit=24*max(0,rule['lower']-sum(five[j] for j in rule['positions']))
            old=max(old,credit)
            applied.append(dict(name=rule['name'],credit=credit))
    pair=24*max(0,9-counts[2]-counts[4]) if shape(d[-6:])=='012032' else 0
    six=24*max(0,25-sum(counts)) if shape(d[2:])==shape([0,1,2,3,1,0,4]) and counts[0]<6 else 0
    match=False
    for reverse in [False,True]:
        sixd=d[-6:][::-1] if reverse else d[-6:]
        five=counts[1:][::-1] if reverse else counts[1:]
        match |= canon(sixd)=='012032' and all(lo<=c<=hi for c,lo,hi in zip(five,[4,0,4,0,3],[4,4,4,5,3]))
    floor=result['floors'][shape(d[-6:])]
    baseweight=max(columns['weight'][i],120*counts[-1]+max(floor,17 if match else 0))
    shared=max(old,pair,six)
    return dict(edge=i,u=columns['U'][i],v=columns['V'][i],direction_index=columns['direction'][i],
        directions=d,count_code=code,counts=counts,suffix_shape=shape(d[-6:]),
        suffix_counts=counts[1:],source_weight=columns['weight'][i],floor=floor,
        old_bonus=old,pair_bonus=pair,six_bonus=six,shared_bonus=shared,
        applicable_count_rules=applied,share17_match=bool(match),weight=baseweight+shared,retained=True,
        occurrence_event=shape(d[-6:])=='012032' and counts[2]<6 and counts[4]<6 and counts[2]+counts[4]<=9)
rows={i:audit_row(i) for i in ids}
for saved in walk:
    row=rows[saved['source_edge']]
    for k in ['u','v','weight','share17_match']: assert row[k]==saved[k]
for saved in cycle:
    row=rows[saved['edge']]
    for k in ['u','v','directions','counts']: assert row[k]==saved[k]
    assert row['weight']==saved['conditional_weight']
w=[rows[x['source_edge']] for x in walk]
c=[rows[x['edge']] for x in cycle]
for path in [w,c+[c[0]]]:
    for a,b in zip(path,path[1:]):
        assert a['v']==b['u']
        assert canon(a['directions'][1:])==canon(b['directions'][:-1])
        assert a['counts'][1:]==b['counts'][:-1]
countword=w[0]['counts']+[x['counts'][-1] for x in w[1:]]
assert len(countword)==14
prospective=[]
for row in w:
    suffix=row['directions'][-6:]
    reverse=canon(suffix)!=shape(suffix)
    oriented=row['suffix_counts'][::-1] if reverse else row['suffix_counts']
    prospective.append(dict(edge=row['edge'],shape=row['suffix_shape'],
        canonical_suffix_counts=oriented,chronological_suffix_counts=row['suffix_counts'],
        canonical_orientation_reversed=reverse,all_five_exact=all(x<6 for x in oriented),
        stored_sum=sum(oriented),current_share_floor=row['floor'],
        larger_share_floor_first_increase=row['floor']+1,
        observed_weight_bonus=row['shared_bonus'],
        status='Recognition only; no feasibility, UNSAT, minimum-share or realizability claim'))
total=sum(x['weight'] for x in w)
assert total==3862 and 9*496-total==602
assert sum(x['weight'] for x in c)==6944==14*496
assert not any(x['share17_match'] for x in w+c)
walk_events=sum(x['occurrence_event'] for x in w)
cycle_events=sum(x['occurrence_event'] for x in c)
assert cycle_events==0 and walk_events<=9
assert Fraction(1098960+8*496+602,4200+496)==235-Fraction(30,4696)
assert 17*4200-1095098<0
out=dict(status='PASS_SELECTED_ROW_WALK_AND_CYCLE_AUDIT',resources_initial=resources,
    input_sha256=pins,array_sha256_verified=array_audit,walk=w,fourteen_cycle=c,
    chronological_count_word=countword,walk_weight=total,walk_deficit_at496=602,
    cycle_total=6944,mean_cap=496,comparison=str(235-Fraction(30,4696)),
    uniform_credit=dict(walk_occurrences=walk_events,cycle_occurrences=cycle_events,
        range_lower_bound=f'R >= 9*mu - 3862 - {walk_events}*C',
        comparison_lower_numerator=f'1095098+17*mu+{24-walk_events}*C',
        assumptions='mu>=0, C>=0, same mask and base weights, one C per exact suffix event, comparison boundary cost 24*C'),
    prospective_suffix_targets=prospective,
    bounds=dict(range='R >= 9*mu - 3862',mean='mu <= 496',
                comparison='(1098960+8*mu+R)/(4200+mu) >= (1095098+17*mu)/(4200+mu) >= 235-30/4696',
                decreasing_derivative_numerator=17*4200-1095098),
    scope=dict(selected_rows=len(ids),columns_loaded_one_at_a_time=list(array_audit),
               history_column_loaded=False,columns_streamed_in_1MiB_blocks=True,
               full_graph_reconstructed=False,all_edge_scan=False,
               optimizer_run=False,solver_run=False,new_lean_check=False,new_global_bound=False,
               changed_retained_edges_77_independently_recounted=False,
               conditional_assumptions_retained=True))
out['audit_script_sha256']=sha(Path(__file__))
(H/'walk-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],walk=w,countword=countword),indent=2))
