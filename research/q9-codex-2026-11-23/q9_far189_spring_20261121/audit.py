from collections import Counter,defaultdict
from itertools import accumulate
from operator import xor
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;R=D.parent
def dec(w):return list(accumulate((1<<int(c) for c in w),xor,initial=0))
def key(p):
    w=[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
    def norm(o):
        m={};return ''.join(str(m.setdefault(c,len(m))) for c in o)
    return min(norm(w),norm(reversed(w)))
def test(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p)
    assert all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
def last(f):return (D/f).read_text().splitlines()[-1]
def loadwords(f):return set(f.read_text().split())
seed=(R/'q9_far_seedgrowth_20261121/new189.words').read_text().strip();test(dec(seed))
prev=R/'q9_novel189_seeds.jsonl';p=json.loads(prev.read_text().splitlines()[9])['path'];test(p);assert len(p)==190 and key(p)==seed
mixed=list(map(int,(R/'q9_detour_mixed_starters.txt').read_text().splitlines()[4903].split()))
p=mixed[1:191];test(p);assert key(p)==seed and len(p)==190
chords=[(i,j) for i,x in enumerate(mixed) for j in range(i+2,len(mixed)) if (x^mixed[j]).bit_count()==1]
assert chords==[(0,177),(176,191)]
for path,lineno in [('/private/tmp/q9_coil_nearby20.txt',138),('/private/tmp/q9_neighborhood189_nov19',2194)]:
    p=list(map(int,Path(path).read_text().splitlines()[lineno-1].split()[1:]));test(p);assert len(p)==190 and key(p)==seed
refs={i:loadwords(D/f'comparison{i}.words')|loadwords(D/'additional'/f'comparison{i}.words') for i in (189,190,191)}
classes=defaultdict(set);batches={}
for name in ['tips','novel_tips']:
    runs=[];c=defaultdict(set)
    for line in (D/(name+'.log')).read_text().splitlines():
        t=line.split()
        if not t:continue
        if t[0]=='DONE':runs.append(list(map(int,t[1:])))
        if t[0]=='PATH':
            n=int(t[1]);p=dec(t[2]);test(p);assert key(p)==t[2] and len(p)==n+1
            c[n].add(t[2]);classes[n].add(t[2])
        assert t[0]!='FOUND'
    batches[name]=dict(runs=len(runs),eligible_per_length={k:len(v) for k,v in c.items()},two_tip_roots=sum(t[3] for t in runs),nodes=sum(t[4] for t in runs),cutoffs=sum(t[5] for t in runs))
sat=[json.loads(l) for l in (D/'sat.jsonl').open()]
for d in sat[:-1]:
    if 'known190' in d:test(dec(d['known190']));classes[190].add(d['known190']);continue
    q=dec(d['w']);test(q);assert key(q)==d['w'] and len(q)==d['goal']+1
    # The output word is symmetry-normalised. Fixed masks in sat.jsonl refer to
    # the solver frame, so recompute eligibility using the checked producing code.
    classes[d['goal']].add(d['w'])
novel189=classes[189]-refs[189];assert novel189==loadwords(D/'outside189.words')
gaps={}
for n in (190,191,192):
    t=last('gaps'+str(n)+'.log').split()
    assert t[0]=='AT' and int(t[4])==0
    gaps[n]=dict(trials=int(t[1]),budget_cutoffs=int(t[2]),branch_nodes=int(t[3]),known_completions=int(t[5]))
raw=(D/'half_sat.jsonl').read_text().splitlines();half=json.loads(raw[-1]);assert half['done'] and not half['novel']
full=Path('/private/tmp/q9_all_records_20261120.zip').read_bytes()
prefixes={f.name:full.startswith(f.read_bytes()) for f in Path('/private/tmp').glob('q9_highdim*.zip')};assert all(prefixes.values())
for n in (189,190,191):
    f=D/f'checked{n}.words';f.write_text(''.join(w+'\n' for w in sorted(classes[n])))
print(json.dumps(dict(seed_previously_known=True,earlier_standalone=dict(file='q9_novel189_seeds.jsonl',line=10,field='path',vertices=len(dec(seed)),pairwise_distances=190*189//2),older_parent=dict(file='q9_detour_mixed_starters.txt',line=4904,zero_based_vertex_slice=[1,191],chords=chords),baseline_class_counts={k:len(v) for k,v in refs.items()},source_scope=json.load(open(D/'scan_scope.json')),additional_scope=json.load(open(D/'extra_scope.json')),complete_record_archive_contains_prefixes=prefixes,generated={n:dict(total=len(classes[n]),outside_reference=len(classes[n]-refs[n])) for n in (189,190,191)},sat=sat[-1],two_ended=batches,variable_gaps=gaps,parity=dict(source189=len(novel189),min_degree_half_enumeration=last('halves.log'),hamilton_layer=last('half_survivors.log'),sat=half),found192=False),indent=2))
