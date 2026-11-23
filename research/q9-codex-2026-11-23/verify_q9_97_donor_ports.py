"""Reconstruct the 97-edge donor bank, enumerate facet branches, and check their integer certificates."""
from itertools import combinations
from collections import Counter
from pathlib import Path
import gzip,json
from verify_q9_intact98_all_crossings import integer_bound,check,parity
def normalize(s):
    axes=list(dict.fromkeys(s))
    return ''.join(str(axes.index(x)) for x in s)
def donors():
    bank=set()
    rows=Path('q8_single_cross_complete_arms.txt').read_text().split()
    rows+= [s.split('\t')[-1] for s in Path('q8_mother_search_20261120/mothers.tsv').read_text().splitlines()[1:]]
    for word in rows:
        for j in range(len(word)-96):
            sub=word[j:j+97]
            bank.add(min(normalize(sub),normalize(sub[::-1])))
    return bank
def path(word):
    p=[0]
    for d in word:
        check(d in '01234567','invalid direction');p.append(p[-1]^(1<<int(d)))
    check(len(p)==len(set(p))==98,'invalid donor vertices')
    check(all(((v^w).bit_count()==1)==(j==i+1) for i,v in enumerate(p) for j,w in enumerate(p) if i<j),'donor chord')
    return p
def all_branches(word):
    p=path(word);base=set(p)
    possible={x for x in range(256) if x not in base and all((x^v).bit_count()!=1 for v in p[1:-1])}
    expected={};max_low=0
    for n in range(len(possible)+1):
        for added in combinations(sorted(possible),n):
            lower=base|set(added)
            adj={v:{v^(1<<d) for d in range(8)}&lower for v in lower}
            if max(map(len,adj.values()))>2:continue
            unseen=set(lower);components=[]
            while unseen:
                stack=[unseen.pop()]
                for x in stack:
                    fresh=adj[x]&unseen;unseen-=fresh;stack.extend(fresh)
                components.append(set(stack))
            if any(sum(len(adj[x]) for x in c)!=2*(len(c)-1) for c in components):continue
            max_low=max(max_low,len(lower)-1)
            required={v for v in lower if not adj[v]}
            optional=sorted(v for v in lower if len(adj[v])==1)
            for mask in range(1<<len(optional)):
                selected=required|{v for i,v in enumerate(optional) if mask>>i&1}
                if not all(selected&c for c in components):continue
                low_ends={v for v in lower if len(adj[v])+int(v in selected)==1}
                if len(low_ends)>2:continue
                remaining=2-len(low_ends)
                for hi_even in range(remaining+1):
                    hi=(hi_even,remaining-hi_even)
                    full=tuple(hi[i]+sum(parity(v)==i for v in low_ends) for i in (0,1))
                    imbalance=sum(1-2*parity(v) for v in lower)-(full[0]-full[1])//2
                    key=(word,added,tuple(sorted(selected)),full)
                    expected[key]=(lower,selected,hi,imbalance)
    return expected,max_low
def key_of(r):
    return r['word'],tuple(r['added']),tuple(r['ports']),tuple(r['full'])
def check_dual(r,geometry):
    low,ports,hi,delta=geometry
    check(tuple(r['ends'])==hi and r['delta']==delta,'branch endpoint totals disagree')
    numerator=integer_bound(r['cert'],low,ports,hi,delta)
    check(numerator==r['numerator'],'group maxima disagree')
    b=len(low)-1+numerator//r['cert']['scale'];b-=(b%2!=(r['full']==[1,1]))
    check(b==r['bound'],'integer bound disagree')
    return b
def main():
    allkeys={};maximum_low=0;words=donors()
    for w in sorted(words):
        table,b=all_branches(w);allkeys.update(table);maximum_low=max(b,maximum_low)
    base=list(map(json.loads,gzip.open('q9_97_donor_port_duals.jsonl.gz','rt')))
    exact=list(map(json.loads,open('q9_97_exact_port_branches.jsonl')))
    check(len(base)==len(set(map(key_of,base)))==len(allkeys) and set(map(key_of,base))==set(allkeys),'incomplete facet branch list')
    check(sorted(r[0] for r in exact)==list(range(len(base))),'incomplete result indices')
    counts=Counter();unresolved=set()
    for idx,status,n,witness in exact:
        r=base[idx];k=key_of(r);b=check_dual(r,allkeys[k]);target=192+(k[-1]==(1,1))
        check(r.get('empty') is None,'unverified empty branch')
        if status=='DUAL':check(b<target and not n and witness is None,'reported DUAL is not certified')
        else:unresolved.add(idx)
        counts[status]+=1
    stronger=list(map(json.loads,gzip.open('q9_97_stronger_port_duals.jsonl.gz','rt')))
    for i,r in stronger:
        k=key_of(r);check(k==key_of(base[i]),'stronger certificate donor or geometry mismatch')
        if check_dual(r,allkeys[k])<192+(k[-1]==(1,1)):unresolved.discard(i)
    print(json.dumps(dict(donor_count=len(words),branch_count=len(allkeys),max_lower_only_relaxation=maximum_low,
        source_status=counts,stronger_records=len(stronger),remaining_after_integer_duals=sorted(unresolved),
        goal=192),indent=2))
if __name__=='__main__':main()
