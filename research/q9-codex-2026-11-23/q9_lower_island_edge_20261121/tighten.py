from pathlib import Path
import json,random,re,subprocess,sys
from itertools import combinations
from collections import defaultdict
from prepare import D,R
sys.path.insert(0,str(R))
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
from q9_rigid_ports_tree import export
A=list(combinations(range(8),3));random.Random(403215).shuffle(A)
cases=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()))
rows=defaultdict(list)
for f in ('bounds94a.log','bounds94b.log'):
    for s in (D/f).read_text().splitlines():
        if s.endswith('}'):r=json.loads(s);rows[r['case']].append(r)
dest=D/'tight';dest.mkdir(exist_ok=True)
limit_lo=int(sys.argv[1]) if len(sys.argv)>1 else 1
limit_hi=int(sys.argv[2]) if len(sys.argv)>2 else 1
residue=int(sys.argv[3]) if len(sys.argv)>3 else 0
modulus=int(sys.argv[4]) if len(sys.argv)>4 else 1
for i,rs in sorted(rows.items()):
    pending=[r for r in rs if r['total_scaled']>=1930000 and ' open 0 ' not in r['replay']]
    if len(rs)!=4 or not limit_lo<=len(pending)<=limit_hi or i%modulus!=residue:continue
    for orig in pending:
        P=set(orig['ports']);name='c'+str(i)+'_p'+'-'.join(map(str,sorted(P)))
        f=dest/(name+'.result');tag=dest/name
        if f.exists():continue
        c=cases[i];p=c['lo'];base=json.loads((D/'bounds'/(name+'.json')).read_text())
        L=set(base['lower_vertices']);ends=base['upper_endpoint_counts'];delta=base['upper_delta']
        const,scale,t,pr=build(p,P,L,ends,delta,A[:10]);v=const+sum(tz[0][2] for _,tz in t)+len(L)*scale
        assert integer_bound(pr,L,P,ends,delta)+len(L)*scale==v
        base['cert']=pr;base['total_scaled']=v;tag.with_suffix('.json').write_text(json.dumps(base,separators=(',',':')))
        log=dict(case=i,ports=sorted(P),total_scaled=v,scale=scale)
        if v>=193*scale:
            export(base,tag.with_suffix('.tables'))
            log['tree']=subprocess.check_output([R/'q9_facet_priced_tree_20261121/tree',tag,tag.with_suffix('.tree'),'193','180000'],text=True).strip()
            log['replay']=subprocess.check_output([R/'q9_facet_priced_tree_20261121/replay',tag.with_suffix('.tables'),tag.with_suffix('.tree'),'193'],text=True).strip()
        f.write_text(json.dumps(log)+'\n');print(json.dumps(log),flush=True)
