"""Check that the saved eleven-cycle is unaffected by the two proposed floors."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=R/'milestones/144-countfree-share18/data/share18-impact/results.json'
prior=R/'milestones/144-countfree-share18/data/graph-review.json'
assert read(prior)['status']=='PASS_BOUNDED_GRAPH_CYCLE_REVIEW'
for p,d in read(prior)['source_files_sha256'].items():
    p=Path(p);assert sha(p if p.is_absolute() else R/p)==d
profile=read(src)['profiles'][0];cycle=profile['cycle'];assert len(cycle)==11
assert all(a['v']==b['u'] for a,b in zip(cycle,cycle[1:]+cycle[:1]))
def canon(w):
    d={};a=[]
    for x in w:
        if x not in d:d[x]=len(d)
        a.append(d[x])
    return tuple(a)
shapes=[min(canon(e['directions'][-6:]),canon(e['directions'][-6:][::-1])) for e in cycle]
assert set(shapes)=={(0,1,2,0,3,2),(0,1,2,3,1,4),(0,1,2,0,3,1)}
weights=[Q(e['weight'],profile['weight_multiplier']) for e in cycle]
assert weights==[360,496,480,496,496,376,616,487,496,480,616]
assert sum(weights)==5399 and sum(bool(e['occurrence_event']) for e in cycle)==4
assert [i for i,e in enumerate(cycle) if e['occurrence_event']]==[0,2,7,9]
mu=Q(496);C=Q(57,4);spread=Q(480)
assert 11*mu==5399+4*C and 7*mu==3472 and 2*mu==512+spread
bound=(1098960+8*mu+24*C+spread)/(4200+mu)
assert bound==Q(551875,2348)==235+Q(95,2348)
j=dict(status='PASS_EXACT_TWO_SAVED_CYCLE_AUDIT',eleven_cycle_edges=[e['edge'] for e in cycle],
    eleven_cycle_base_total=5399,occurrence_events=4,unaffected_by=['012034','012301','012340'],
    necessary_condition='325F + 159G > 9074',both16_comparison_lower_bound=str(bound),gap_above_235='95/2348',
    relaxation_attaining_parameters=dict(mean='496',credit='57/4',range='480'),
    selected_continuation='Target the existing 012032 share16 together with 012301/012340 share16; retain the current012301 certificate and finish its Lean obligations.',
    scope='Fixed graph and other weights. Exact optimum only of the listed two-cycle/two-edge arithmetic relaxation, not of the full graph. No local share theorem or global bound.',
    source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [Path(__file__),src,prior,H/'data/joint-floor-analysis.json']})
p=H/'data/two-cycle-analysis.json';assert not p.exists();p.write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
