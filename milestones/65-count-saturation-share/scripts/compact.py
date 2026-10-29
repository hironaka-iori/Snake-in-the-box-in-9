"""Slice count-deduction traces to the facts needed by their terminal conclusion."""
from pathlib import Path
from functools import lru_cache
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from split_share import NB,credit
base=json.loads((ROOT/'milestones/64-neighbour-choice-share/data/choices.json').read_text())['rows']
summary=json.loads((HERE/'data/summary.json').read_text());out=[];start=time.monotonic()
@lru_cache(None)
def forced_by(T,q):
    U=set(T)|{q}
    return any(len(NB[v]&U)>=3 for v in U)
selected=json.loads((HERE/'data/selected-exclusions.json').read_text())['selected']
for i in summary['improved_candidates']+selected:
    r=json.loads((HERE/f'data/cases/e{i:03d}.json').read_text());L=r['lower'] if r['lower'] is not None else 0;packets=[]
    for br,origin in zip(r['branches'],base[i]['branches']):
        assert br['choices']==origin['choices'];a,b=br['choices'];initial=set(r['vertices'])|{v for v in [a,b] if v is not None}
        known=(set(r['A'])-({a} if a is not None else set()))|(set(r['B'])-({b} if b is not None else set()))
        steps=[]
        for t in br['trace']:
            if t['rule'] in ['crowded','saturated']:steps.append(dict(kind='degree',add=t['absent'][:]))
            elif t['rule']=='count_upper':steps.append(dict(kind='select',condition=t['constraint'],add=t['selected'][:]))
            else:raise AssertionError(t['rule'])
        if br['status']=='CLOSED':
            D=set(br['absent'])
            for q in sorted(D,reverse=True):
                D.remove(q)
                if credit(r['centres'],D)<L:D.add(q)
            ending=dict(kind='share',mask=sum(1<<v for v in D),absent=sorted(D))
        else:
            kind,k=br['reason'];assert kind in ['degree','count_upper']
            ending=dict(kind='degree') if kind=='degree' else dict(kind='upper',condition=k)
        F=set(origin['forced'])
        def valid():
            T=set(initial);D=set(F)|known
            for t in steps:
                Q=set(t['add'])
                if t['kind']=='degree':
                    if not all(forced_by(tuple(sorted(T)),q) for q in Q):return False
                    D|=Q
                else:
                    c=r['constraints'][t['condition']];K=set(c['corners'])
                    if not all(c['hi']<len(K&(D|{q})) for q in Q):return False
                    T|=Q
            if ending['kind']=='share':return set(ending['absent'])<=D
            if ending['kind']=='degree':return any(len(NB[v]&T)>=3 for v in T)
            c=r['constraints'][ending['condition']];return c['hi']<len(set(c['corners'])&D)
        assert valid()
        for t in reversed(steps):
            for q in t['add'][:]:
                t['add'].remove(q)
                if not valid():t['add'].append(q)
            t['add'].sort()
        for q in sorted(F,reverse=True):
            F.remove(q)
            if not valid():F.add(q)
        assert valid() and all(forced_by(tuple(sorted(initial)),q) for q in F)
        steps=[t for t in steps if t['add']]
        packets.append(dict(choices=br['choices'],forced=sorted(F),steps=steps,ending=ending))
    out.append(dict(edge=i,lower=L,mode='exclusion' if r['lower'] is None else 'share',certificates=packets))
    print(i,'branches',len(packets),'initial facts',sum(len(p['forced']) for p in packets),'steps',sum(len(p['steps']) for p in packets),flush=True)
payload=dict(rows=out,seconds=time.monotonic()-start,scope='Reduced proposed proof traces. Every finite certificate and its geometric interpretation still require Lean replay.')
(HERE/'data/compact-certificates.json').write_text(json.dumps(payload,indent=2)+'\n');print('Seconds',payload['seconds'])
