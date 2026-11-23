"""Validate lower configurations, unrestricted upper certificates and constructive witnesses from disk."""
import json,random
from collections import Counter
from itertools import combinations,accumulate
from operator import xor
from pathlib import Path
from q9_classify_record_donor_windows import canonical
from verify_q9_intact98_all_crossings import integer_bound
D=Path("q9_catalogue_four_cross")
def main():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    K={canonical(w):i for i,w in enumerate(bank)};assert len(K)==753
    stored={(i,j,tuple(e),tuple(f)) for i,j,e,f in json.loads((D/"lower.json").read_text())}
    catalog=[json.loads(l) for l in (D/"cases.jsonl").read_text().splitlines()]
    expected=set();four=set()
    for i,w in enumerate(bank):
        p=list(accumulate([1<<int(z) for z in w],xor,initial=0));inside=set(p)
        assert len(p)==len(inside) and all(((x^y).bit_count()==1)==(k==j+1) for k,x in enumerate(p) for j,y in enumerate(p[:k]))
        ns={x:{x^1<<d for d in range(8)} for x in range(256)}
        E=[x for x in range(256) if x not in inside and all((x^v).bit_count()!=1 for v in p[1:-1])]
        for t in range(len(E)+1):
            for e in combinations(E,t):
                F=inside|set(e);adj={x:F&ns[x] for x in F}
                if any(len(z)>2 for z in adj.values()):continue
                singles=tuple(sorted(x for x in F if not adj[x]))
                if len(singles)>2:continue
                rem=F-set(singles)
                ends=[x for x in rem if len(adj[x])==1]
                if not ends:continue
                assert len(ends)==2
                q=[ends[0]];rem.remove(q[0])
                while adj[q[-1]]&rem:
                    x,=adj[q[-1]]&rem;q.append(x);rem.remove(x)
                assert not rem and inside<=set(q)
                word="".join(str((v^x).bit_length()-1) for v,x in zip(q,q[1:]))
                expected.add((i,K[canonical(word)],e,singles))
                if set(e)==set(singles) and len(e)==2:four.add((i,e))
    assert expected==stored and len(catalog)==len(four)==1000
    assert {(r["index"],tuple(r["ends"])) for r in catalog}==four
    rows=[[],[]];miss=[[],[]];cert_count=[0,0];exact_paths=[]
    for j,r in enumerate(catalog):
        i=r["index"];p=list(accumulate([1<<int(z) for z in bank[i]],xor,initial=0));u,v=r["ends"]
        parity=(u^v).bit_count()%2
        assert j==r["case"] and parity==r["parity"] and bank[i]==r["word"]
        file=D/("odd_certs" if parity else "certs")/f"c{j}.json"
        if not file.exists():miss[parity].append(j);continue
        save=json.loads(file.read_text());L=set(p)|{u,v};ports={p[0],p[-1],u,v}
        delta=sum((-1)**x.bit_count() for x in L)-(((-1)**u.bit_count()+(-1)**v.bit_count())//2)
        if "empty_table" in save:
            zero=dict(end_weights=[0,0],balance_weight=0,weights=[],scale=1,axes=save["axes"])
            try:integer_bound(zero,L,ports,[0,0],delta)
            except ValueError as exc:assert str(exc) in ("infeasible affine face","no possible state for required upper vertex")
            else:raise AssertionError("empty-table claim failed")
            cert_count[parity]+=1;continue
        c=save["cert"];score=integer_bound(c,L,ports,[0,0],delta)+len(L)*c["scale"]
        assert score==save["total_scaled"]
        if not parity:
            assert set(save["lower_vertices"])==L and set(save["ports"])==ports and save["upper_delta"]==delta
        edges=score//c["scale"]-1
        if edges%2!=parity:edges-=1
        rows[parity].append((edges,j))
        cert_count[parity]+=1
    for line in (D/"beam.log").read_text().splitlines():
        j,tries,steps,e,*p=map(int,line.split());r=catalog[j]
        if not p:continue
        assert len(p)==len(set(p))==e+1 and set((p[0],p[-1]))==set(r["ends"])
        assert {x for x in p if x<256}==set(accumulate([1<<int(z) for z in r["word"]],xor,initial=0))|set(r["ends"])
        assert all(0<=x<512 for x in p) and all(((v^u).bit_count()==1)==(k==h+1) for k,v in enumerate(p) for h,u in enumerate(p[:k]))
        exact_paths.append((e,j))
    print(json.dumps(dict(lower_checked=len(expected),four_cross_cases=len(catalog),checked_certificates=cert_count,
                         missing_by_endpoint_parity=list(map(len,miss)),upper_edges_histogram=[dict(sorted(Counter(e for e,j in rs).items())) for rs in rows],
                         beam_witnesses=len(exact_paths),best_constructed_even=max(exact_paths))))
if __name__=="__main__":main()
