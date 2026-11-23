"""Build the orientation-complete 93--98 edge Q8 arm bank used for the lift audit."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

BASE=Path(__file__).resolve().parent

def norm(word):
    labels={}
    return ''.join(str(labels.setdefault(d,len(labels))) for d in word)

def vertices(word):
    q=[0]
    for d in word:
        assert 0<=d<8
        q.append(q[-1]^(1<<d))
    return q

def checked(p,dim):
    assert all(0<=v<1<<dim for v in p) and len(p)==len(set(p))
    assert all(((u^p[j]).bit_count()==1)==(j==i+1) for i,u in enumerate(p) for j in range(i+1,len(p)))
    return tuple((a^b).bit_length()-1 for a,b in zip(p,p[1:]))

def run():
    seen=set();summary=[]
    files=('q8_combined_exchange_arms.txt','q8_exchange_second_rooted_arms.txt','q8_bitterman_plus_reference_arms.txt','q8_via_seven_for_single_cross.txt','q8_bitterman_97.json','q8_long_alternative_donors.jsonl','q9_highdim_full_excerpts.txt')
    for name in files:
        f=BASE/name;records=[];kinds=Counter()
        if name.endswith('.json'):
            for r in json.loads(f.read_text())['rows']:
                w=checked(r['vertices'],8);assert len(w)==97;records.append(w);kinds['historical_rows']+=1
        elif name.endswith('.jsonl'):
            for line in f.read_text().splitlines():
                r=json.loads(line)
                if 'done' in r:
                    kinds['completed_search_rows']+=1;records.append(tuple(bytes.fromhex(r['done'])))
                elif 'vertices' in r:
                    kinds['explicit_paths']+=1;records.append(checked(r['vertices'],8))
                else:raise ValueError(r.keys())
        elif 'highdim' in name:
            for line in f.read_text().splitlines():
                fields=line.split();dim=int(fields[0]);word=fields[1]
                if dim==8 and len(word)>=93:
                    records.append(tuple(ord(c)-ord('a') for c in word));kinds['dimension_8_rows']+=1
        else:
            records=[tuple(map(int,w)) for w in f.read_text().split()]
            kinds['lines']=len(records)
        fresh=set()
        for w in set(records):
            checked(vertices(w),8)
            for n in range(93,min(98,len(w))+1):
                for i in range(len(w)-n+1):
                    sub=w[i:i+n];fresh.update((norm(sub),norm(sub[::-1])))
        summary.append(dict(input=name,sha256=hashlib.sha256(f.read_bytes()).hexdigest(),records=kinds,source_edges=Counter(map(len,records)),rooted_subwords=len(fresh),new_rooted_subwords=len(fresh-seen)))
        seen|=fresh
    for w in seen:assert norm(w[::-1]) in seen
    body=''.join(w+'\n' for w in sorted(seen,key=lambda x:(len(x),x)))
    return body,dict(sources=summary,
        rooted=Counter(map(len,seen)),
        unoriented=Counter(map(len,{min(w,norm(w[::-1])) for w in seen})),
        bank_sha256=hashlib.sha256(body.encode()).hexdigest())

if __name__=='__main__':
    out,info=run();(BASE/'q8_single_cross_complete_arms.txt').write_text(out)
    (BASE/'q8_single_cross_complete_bank.json').write_text(json.dumps(info,indent=2)+'\n')
    print(json.dumps({k:v for k,v in info.items() if k!='sources'}))
