from pathlib import Path
from itertools import combinations
import os,random,json,sys,subprocess
from banks import D,path
sys.path.insert(0,str(D.parent))
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
from q9_rigid_ports_tree import export
axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
words=(D/'donors.words').read_text().split()
for i in map(int,sys.argv[1:]):
    for c in map(int,os.getenv("COLS","0,1").split(",")):
        p=path(words[i]); low=set(p);ports={p[0],p[-1]};ends=[1,1] if c==-1 else [2*int(k==c) for k in (0,1)];delta=sum(1-2*(v.bit_count()%2) for v in low)-(ends[0]-ends[1])//2
        base,scale,opts,cert=build(p,ports,low,ends,delta,axes[:int(os.environ.get('AXES','6'))]);v=base+sum(t[0][2] for _,t in opts)
        assert integer_bound(cert,low,ports,ends,delta)==v
        tag=D/f"{os.environ.get('TAG','price')}_{i}_{c}";rec=dict(word=words[i],lower_vertices=sorted(low),ports=sorted(ports),upper_endpoint_counts=ends,upper_delta=delta,majority=c,total_scaled=v+len(low)*scale,cert=cert)
        tag.with_suffix('.json').write_text(json.dumps(rec,separators=(',',':')));report=dict(id=i,c=c,scale=scale,bound=rec['total_scaled'])
        if c!=-1 and report['bound']>=193*scale:
            export(rec,tag.with_suffix('.tables'));exe=D.parent/'q9_facet_priced_tree_20261121'
            report['tree']=subprocess.check_output([str(exe/'tree'),str(tag),str(tag.with_suffix('.tree')),'193','80000'],text=True).strip();report['checked']=subprocess.check_output([str(exe/'replay'),str(tag.with_suffix('.tables')),str(tag.with_suffix('.tree')),'193'],text=True).strip()
        print(json.dumps(report),flush=True)
