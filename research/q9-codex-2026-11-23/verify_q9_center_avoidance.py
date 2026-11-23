"""Recompute center coverage and verify every retained new witness independently."""
import gzip,json
from collections import Counter
from pathlib import Path

def verify(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p)
    assert all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))

def code(t):
    def norm(word):
        table={};return bytes(table.setdefault(c,len(table)) for c in word)
    return min(norm(t),norm(t[::-1]))

def forms(p,k):
    t=[a^b for a,b in zip(p,p[1:])]
    return [code(t[i:i+k]) for i in range(len(p)-k)]

def summary():
    k=142;sets=[];whole=set()
    for f in ['q9_centers_1042_inputs.txt.gz','q9_free_bridge_join_inputs.txt.gz']:
        fam=set()
        for l in gzip.open(f,'rt'):
            p=list(map(int,l.split()));verify(p)
            if f.startswith('q9_centers_1042'):
                assert len(p)==191
                whole.add(forms(p,190)[0])
            fam.update(forms(p,k))
        sets.append(fam)
    assert len(whole)==1042
    ln=Path('q9_capacity142_192.log').read_text().split()
    assert ln[:3]==['NO_JOIN','cores',str(len(sets[0]))]
    prev=json.loads(Path('q9_free_bridge_join_results.json').read_text())
    assert any(r['status']=='NO_JOIN' and r['args']==[142,192,1] and r['cores']==len(sets[1]) for r in prev['sliding_center']['runs'])
    bank=set.union(*sets)
    old={forms(r[2],r[1])[0] for r in map(json.loads,open('q9_center_avoiding_seeds.jsonl')) if r[0]=='SEED'}
    prior={}
    out=[]
    solved={}
    for f in ['q9_avoiding_sat_results.jsonl','q9_avoiding_sat_remaining.jsonl']:
        for s,key,n,w in map(json.loads,open(f)):
            assert (key,n) not in solved
            solved[key,n]=s
            if s=='FOUND':
                verify(w);assert n==len(w)-1 and bank.isdisjoint(forms(w,k))
                assert int(key,16)&~sum(1<<v for v in w)==0
                shape=forms(w,n)[0];prior[shape]=n
                if shape not in old and shape not in {a for a,_,_ in out}:out.append((shape,n,w))
    assert sum(n==192 for _,n in solved)==4000
    c=Path('q9_capacity_center_positive.log').read_text().split();assert c[0]=='FOUND'
    w=list(map(int,c[1:]));verify(w);assert len(w)==192
    return {'distinct_190_input_paths':len(whole),'center_length':k,'classes_by_bank':[len(v) for v in sets],
            'additional_exclusions':len(sets[0]-sets[1]),'combined_exclusions':len(bank),
            'positive_control_edges':len(w)-1,'target192_results':dict(Counter(s for (_,n),s in solved.items() if n==192)),
            'distinct_mixed_witnesses':dict(Counter(prior.values())),'distinct_beyond_two_previous_seeds':len(out),
            'new_witnesses':[{'edges':n,'vertices':p} for _,n,p in out]}
if __name__=='__main__':print(json.dumps(summary(),separators=(',',':')))
