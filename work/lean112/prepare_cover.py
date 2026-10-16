"""Find translation inclusions. Lean must verify every proposed inclusion."""
import json
from service import ROOT,OUT,read,save
survey=read(OUT/'survey.json')['entries']
cores=read(OUT/'bank-cores.json')['entries']
data={}
for i,e in survey.items():
    if e['formula'] not in data:data[e['formula']]=read(ROOT/e['formula'])
regions=[data[survey[str(i)]['formula']] for i in range(262)]
sets=[frozenset(v^d['head'] for v in d['vertices']) for d in regions]
unique=list(dict.fromkeys(sets))
maximal=[r for r in unique if not any(r<t for t in unique)]
def cost(i):return cores[str(survey[str(i)].get('reused_from',i))]['derived_steps']
reps=[]
for r in maximal:
    candidates=[i for i,x in enumerate(sets) if x==r]
    rep=0 if 0 in candidates else 184 if 184 in candidates else min(candidates,key=cost)
    reps.append(rep)
mapping={}
for i,r in enumerate(sets):
    candidates=[j for j in reps if r<=sets[j]]
    rep=i if i in reps else min(candidates,key=lambda j:(j not in (0,184),cost(j),len(sets[j])))
    mapping[str(i)]=dict(representative=rep,translation=regions[i]['head']^regions[rep]['head'])
save('cover.json',dict(status='PROPOSED_NOT_CERTIFIED',representatives=reps,entries=mapping,
    scope='Each translation and region inclusion still needs a Lean proof.'))
print('Representatives:',len(reps),'derived steps:',sum(cost(i) for i in reps),flush=True)
