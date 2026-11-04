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
base='milestones/158-memory-bounded-floor-test/'
result=read(base+'data/floor17-complete/result.json')
accepted156=read('milestones/156-potential-range-and-paper/data/share17-range496/result.json')
assert result['status']=='PASS_FIXED_MEAN_TARGET_OBSTRUCTION'
assert result['floors']['012034']==17
meta=read('milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
ds=read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
rules=read('milestones/120-nine-transition-window/data/full-rules.json')
removed_rel='milestones/144-countfree-share18/data/share18-impact/removed-indices.json'
removed=set(read(removed_rel))
assert pins[removed_rel]==result['input_pins'][removed_rel]
assert len(removed)==4947008-4661572
walk=result['deficit_walk']
cycle_ids=[991858,1272641,3005579,943614,1340646,3609461,1726634,487872,3070840]
old_ids=[4001343,4684655,3607986,1742134,491026,3069298,987251,1275893,3049938]
ids=sorted(set([x['source_edge'] for x in walk]+cycle_ids+old_ids))
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
full=[rows[x['source_edge']] for x in walk]
cycle=[rows[i] for i in cycle_ids]
old=[rows[i] for i in old_ids]
for saved,row in zip(walk,full):
    for key in ['u','v','weight','share17_match']: assert saved[key]==row[key]
for name,sequence in [('full149',full),('cycle',cycle+[cycle[0]]),('old9',old)]:
    for a,b in zip(sequence,sequence[1:]):
        assert a['v']==b['u'],(name,a['edge'],b['edge'])
        assert canon(a['directions'][1:])==canon(b['directions'][:-1])
        assert a['counts'][1:]==b['counts'][:-1]
assert len(full)==149
assert sum(x['weight'] for x in full)==149*496-633
assert sum(x['weight'] for x in cycle)==4462
assert sum(x['weight'] for x in old)==3861
cycle_events=sum(x['occurrence_event'] for x in cycle)
old_events=sum(x['occurrence_event'] for x in old)
assert cycle_events==old_events==0
mu=Fraction(4462,9)
bound=Fraction(1095099+17*mu,4200+mu)
assert bound==235+Fraction(175,42262)
for rel in ['milestones/156-potential-range-and-paper/review/walk_audit.py',
            'milestones/155-share17-replay/scripts/native_resources.py',
            base+'scripts/reconstruct_mapped.py',base+'scripts/potential_range_v5.py']:
    pins[rel]=sha(R/rel)
for rel,digest in pins.items():
    if rel in result['input_pins']: assert digest==result['input_pins'][rel]
    if rel in accepted156['input_pins']: assert digest==accepted156['input_pins'][rel]
output=dict(status='PASS_SELECTED_CYCLE_OLD_WALK_AND_FULL149_AUDIT',
    resources_initial=resources,input_sha256=pins,verified_array_sha256=array_audit,
    selected_unique_rows=len(ids),cycle=cycle,old_nine_walk=old,full149_walk=full,
    cycle_total=4462,cycle_occurrences=cycle_events,cycle_share17_matches=sum(x['share17_match'] for x in cycle),
    old_walk_total=3861,old_walk_occurrences=old_events,
    full149_total=sum(x['weight'] for x in full),full149_deficit_at496=633,
    full149_occurrences=sum(x['occurrence_event'] for x in full),
    mean_cap=str(mu),comparison_lower_bound=str(bound),excess_over235=str(bound-235),
    assumptions='Same retained graph, floor17 profile, mean>=0, uniform occurrence credit C>=0, boundary cost24C',
    range_inequality='R>=9*mu-3861',comparison_inequality='comparison>235',
    all_edge_scan=False,optimizer_run=False,new_lean_check=False,new_snake_bound=False,
    audit_script_sha256=sha(Path(__file__)))
(H/'cycle-audit.json').write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
print(json.dumps({key:output[key] for key in ['status','selected_unique_rows','cycle_total','cycle_occurrences','old_walk_total','old_walk_occurrences','full149_total','full149_deficit_at496','full149_occurrences','mean_cap','comparison_lower_bound','excess_over235']}))
