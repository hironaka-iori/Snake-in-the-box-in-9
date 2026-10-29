"""Enumerate all eleven-direction contexts of the full current critical family.

State keys retain original edge identities, including prefix-automaton history.
Merging by direction and count alone would discard those constraints.
"""
from pathlib import Path
import collections,itertools,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from split_share import credit
start=time.monotonic()
for d in ['data','logs','build','lean']:(HERE/d).mkdir(parents=True,exist_ok=True)
source=json.loads((ROOT/'milestones/66-full-model-and-revision/data/critical-edges.json').read_text())
assert len(source)==99
signatures=collections.defaultdict(list)
for word in model.words(11):signatures[tuple(model.canon(word[j:j+9]) for j in range(3))].append(word)
outgoing=collections.defaultdict(list)
for i,e in enumerate(source):outgoing[e['u']].append(i)
NB=[{x^(1<<d) for d in range(9)} for x in range(512)];geometry={};edges=[];rejected=[];keys=set()
for i,e in enumerate(source):
    for j in outgoing[e['v']]:
        f=source[j];assert e['counts'][1:]==f['counts'][:-1]
        for k in outgoing[f['v']]:
            g=source[k];assert f['counts'][1:]==g['counts'][:-1]
            sig=tuple(tuple(x['directions']) for x in (e,f,g));words=signatures[sig]
            if not words:rejected.append([i,j,k])
            for word in words:
                if word not in geometry:
                    W=[0]
                    for d in word:W.append(W[-1]^(1<<d))
                    D=set.union(*(NB[x] for x in W[1:-1]))-set(W);C=W[6:11]
                    geometry[word]=dict(directions=word,vertices=W,centres=C,absent=sorted(D),lower=credit(C,D))
                geo=geometry[word];lo=max(g['weight']-120*g['counts'][-1],geo['lower'])
                u=(i,j,model.canon(word[:10]));v=(j,k,model.canon(word[1:]));keys.update([u,v])
                edges.append(dict(source_edges=[i,j,k],directions=word,counts=g['counts'],
                    original_weight=g['weight'],geometric_lower=geo['lower'],share_lower=lo,
                    weight=120*g['counts'][-1]+lo,source_key=u,target_key=v))
keys=sorted(keys);sid={k:i for i,k in enumerate(keys)}
for e in edges:e['u']=sid[e.pop('source_key')];e['v']=sid[e.pop('target_key')]
data=dict(states=len(keys),edges=edges,state_keys=keys,rejected_triples=rejected,
    source_states=70,source_edges=99,unique_shapes=len(geometry),improved_edges=sum(e['weight']>e['original_weight'] for e in edges),
    seconds=time.monotonic()-start,scope='Exhaustive restricted-family context lift. Local positive geometry and finite potential still require Lean checks; no new global bound.')
(HERE/'data/family.json').write_text(json.dumps(data,indent=2)+'\n')
(HERE/'data/geometry.json').write_text(json.dumps(list(geometry.values()),indent=2)+'\n')
print({k:v for k,v in data.items() if k not in ['edges','state_keys','rejected_triples']});print('Rejected triples',len(rejected))
