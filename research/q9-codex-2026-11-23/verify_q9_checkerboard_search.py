"""Rebuild the case inventory and check full coverage, repair controls and independent results."""
import gzip,json
from collections import Counter
from pathlib import Path
from certify_q9_checkerboard import mask
from verify_q9_center_avoidance import verify
source=[list(map(int,l.split())) for l in gzip.open('q9_port_followup_public191.txt.gz','rt')]
for p in source:verify(p)
def num(A):return sum(1<<x for x in A)
cases={}
back={}
for l in open('q9_projected_checkerboard_sets.txt'):
    i,c,*A=map(int,l.split());cases[i]=(c,set(A));back[c,num(A)]=i
assert len(cases)==len(back)==1602
assert set(back)=={(c,mask(p,d,c)) for p in source for d in range(9) for c in (0,1)}
def check(p,A,c):
    verify(p)
    assert {v for v in p if (v%256).bit_count()%2==c}==A
def rows(f):return list(map(json.loads,open(f)))
def batch(tag,retries):
    name='q9_checkerboard_'+tag+('_toggles.log' if tag!='shears' else '.log')
    dones={};unknown=set()
    for l in open(name):
        token,*nums=l.split();idx,*rest=map(int,nums)
        if token=='DONE':
            assert idx not in dones
            dones[idx]=rest;continue
        assert token=='UNKNOWN'
        k=(idx,*rest);assert k not in unknown;unknown.add(k)
    assert set(dones)==set(cases)
    by_case=Counter(k[0] for k in unknown)
    for i,(tested,open_,_) in dones.items():
        assert by_case[i]==open_<=tested
        if tag=='all':assert tested==256
        if tag=='paired':assert tested==128
    outcome={}
    for f in retries:
        for r in rows(f):
            key=tuple(r[:-2]);assert key in unknown
            if key in outcome:assert outcome[key]=='UNKNOWN' or outcome[key]==r[-2]
            outcome[key]=r[-2];assert r[-1] is None
    assert unknown==outcome.keys()
    return dict(tested=sum(r[0] for r in dones.values()),native_closed=sum(r[0]-r[1] for r in dones.values()),retry=dict(Counter(outcome.values())))
def damaged(tag):
    _,c,*A=map(int,Path('q9_damaged_checkerboard_'+tag+'.txt').read_text().split());A=set(A)
    output=Path('q9_checkerboard_'+('one' if tag=='all' else 'pair')+'_repair_control.log').read_text().splitlines()
    fields=next(l for l in output if l.startswith('FOUND')).split()
    offset=3 if tag=='all' else 4
    delta=set(map(int,fields[2:offset]));p=list(map(int,fields[offset:]))
    assert len(delta)==offset-2 and len(p)==192
    check(p,A^delta,c)
for tag in ('all','paired'):damaged(tag)
p=list(map(int,Path('q9_states_control191.log').read_text().split()[3:]));check(p,cases[0][1],cases[0][0]);assert len(p)==192
overlap=set()
for r in rows('q9_checkerboard_toggles.jsonl'):
    i,d,c,v,st,w=r;assert st in ('DEGREE','UNSAT','SIZE') and w is None
    assert (c,mask(source[i],d,c)) in back
    overlap.add((back[c,mask(source[i],d,c)],v))
assert len(overlap)==16384
gen=json.loads(Path('q9_checkerboard_drat_generated.json').read_text());rep=json.loads(Path('q9_checkerboard_drat_replayed.json').read_text());assert gen==rep and rep['drat']==1602
out={'fixed':rep,'repair_control_edges':191,'SAT_overlap':len(overlap)}
for name,short in [('all','toggle'),('paired','pair'),('shears','shears')]:
    fs=sorted(Path('.').glob('q9_checkerboard_'+short+'_retry*.jsonl'));out[name]=batch(name,fs)
print(json.dumps(out,indent=2))
