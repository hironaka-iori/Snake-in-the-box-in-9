import json,random,sys
from itertools import combinations
from pathlib import Path
from prepare import D,R
sys.path.insert(0,str(R))
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
from q9_rigid_ports_tree import export
import subprocess
cs=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()))
A=list(combinations(range(8),3));random.Random(403215).shuffle(A)
for i in range(int(sys.argv[1]),int(sys.argv[2])):
    c=cs[i];p=c['lo'];b=c['edge'];L=set(p+b)
    for y in b:
        z=next(v for v in b if v!=y)
        for selected in ((p[0],),(p[-1],),(p[0],p[-1])):
            lo_ends=[z]+[v for v in (p[0],p[-1]) if v not in selected]
            majority=z.bit_count()%2
            if any(v.bit_count()%2!=majority for v in lo_ends):continue
            ports=set(selected)|{y};ends=[int(k==majority)*(2-len(lo_ends)) for k in (0,1)]
            delta=sum(1-2*(v.bit_count()%2) for v in L)-(1-2*majority)
            label=f"c{i}_p{'-'.join(map(str,sorted(ports)))}";tag=D/'bounds'/label;tag.parent.mkdir(exist_ok=True)
            directions=int(sys.argv[3]) if len(sys.argv)>3 else 10
            args=build(p,ports,L,ends,delta,A[:directions])
            if args is None:print(json.dumps(dict(case=i,ports=sorted(ports),empty=True)),flush=True);continue
            base,scale,ts,dual=args
            val=base+sum(o[0][2] for _,o in ts);assert val==integer_bound(dual,L,ports,ends,delta)
            rec=dict(word=c['w'],lower_vertices=sorted(L),ports=sorted(ports),majority=majority,upper_endpoint_counts=ends,upper_delta=delta,cert=dual,total_scaled=val+scale*len(L))
            tag.with_suffix('.json').write_text(json.dumps(rec,separators=(',',':')))
            res=dict(case=i,ports=sorted(ports),total_scaled=rec['total_scaled'],scale=scale)
            if rec['total_scaled']>=193*scale:
                export(rec,tag.with_suffix('.tables'))
                res['tree']=subprocess.check_output([R/'q9_facet_priced_tree_20261121/tree',tag,tag.with_suffix('.tree'),'193','180000'],text=True).strip()
                res['replay']=subprocess.check_output([R/'q9_facet_priced_tree_20261121/replay',tag.with_suffix('.tables'),tag.with_suffix('.tree'),'193'],text=True).strip()
            print(json.dumps(res),flush=True)
