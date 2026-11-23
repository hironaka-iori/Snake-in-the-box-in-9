"""Classify all multi-visit lower layers on the 94-edge catalogue with both endpoints above it."""
from pathlib import Path
import json,random
from collections import Counter
from itertools import combinations
from q9_lower_bend import N,canonical,word_path,build,integer_bound
D=Path("q9_upper_endpoint_94")
def main():
    D.mkdir(exist_ok=True)
    inputs=Path("q8_catalogue_96_98.words").read_text().split()+Path("q8_single_cross_complete_arms.txt").read_text().split()
    catalog={};counts={}
    for size in [95,94]:
        bank=sorted({canonical(w[j:j+size]) for w in inputs for j in range(len(w)-size+1)})
        counts[size]=len(bank)
        for w in bank:
            a=word_path(w);F=set(a)
            spare={x for x in range(256) if x not in F and not N[x]&F}
            bends=[(u,c,v) for c in spare for u,v in combinations(sorted(N[c]&spare),2)]
            for bend in bends:
                core=F|set(bend);sat=set(a[1:-1])|{bend[1]}
                avail=sorted(v for v in set(range(256))-core if not N[v]&sat)
                for m in range(1<<len(avail)):
                    low=core|{x for j,x in enumerate(avail) if m>>j&1}
                    if any(len(N[v]&low)>2 for v in low):continue
                    components=[];rem=set(low)
                    while rem:
                        seq=[rem.pop()]
                        for x in seq:
                            more=N[x]&rem;seq.extend(more);rem-=more
                        components.append(seq)
                    if len(components)<2:continue
                    if any(len(g)<3 or sum(len(N[x]&low)==1 for x in g)!=2 for g in components):continue
                    ports=sorted(x for x in low if len(N[x]&low)==1)
                    catalog[w,tuple(sorted(low-F))]=ports
    assert counts=={94:2939,95:1494} and len(catalog)==15
    axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
    earlier=Path("q9_lower_bend/prices")
    indexed={}
    for f in earlier.glob("b*_m*.json"):
        r=json.loads(f.read_text())
        if len(r["word"])==94:
            indexed[r["word"],tuple(r["lower_vertices"]),tuple(r["upper_endpoint_counts"])]=f
    cases=[]
    for j,((w,extras),ports) in enumerate(sorted(catalog.items())):
        a=word_path(w);L=set(a)|set(extras)
        assert len(ports)==4
        for ends in ([2,0],[0,2],[1,1]):
            delta=sum(1-2*(x.bit_count()%2) for x in L)-(ends[0]-ends[1])//2
            key=(w,tuple(sorted(L)),tuple(ends))
            if key in indexed:
                file=indexed[key];saved=json.loads(file.read_text())
            else:
                file=D/f"case{j}_even{ends[0]}.json"
                if file.exists():saved=json.loads(file.read_text())
                else:
                    base,scale,tables,c=build(a,ports,L,ends,delta,axes[:12])
                    saved=dict(cert=c,total_scaled=base+len(L)*scale+sum(t[0][2] for _,t in tables))
                    file.write_text(json.dumps(saved,separators=(",",":")))
            c=saved["cert"];num=integer_bound(c,L,set(ports),ends,delta)+len(L)*c["scale"]
            assert num==saved["total_scaled"]
            upper=num//c["scale"]-1; upper-=(upper-(ends[0]%2))%2
            cases.append(dict(word=w,extra=extras,ports=ports,ends=ends,certificate=str(file),upper_edges=upper))
    print(json.dumps(dict(source_counts=counts,geometries=len(catalog),cells=cases),indent=2))
if __name__=="__main__":main()
