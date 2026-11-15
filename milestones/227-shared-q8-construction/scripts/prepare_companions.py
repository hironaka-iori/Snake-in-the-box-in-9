"""Enumerate the complete small upper-face portions of each second path."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,j):p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
def adjacent(u,v):return (u^v).bit_count()==1
def induced(p):return len(p)==len(set(p)) and all(adjacent(u,p[j])==(j==i+1) for i,u in enumerate(p) for j in range(i+1,len(p)))
def upper_paths(domain,start,other,ports):
    out=[];stack=[[start]];nodes=0
    while stack:
        p=stack.pop();nodes+=1
        if p[-1]-256 in ports:out.append(p)
        for v in sorted(domain-set(p)-{other},reverse=True):
            if adjacent(p[-1],v) and not any(adjacent(z,v) for z in p[:-1]):stack.append(p+[v])
    return out,nodes
source=H/'data/regions44.json';planpath=H/'data/shared-q8-plan.json'
raw=json.loads(source.read_bytes());plan=json.loads(planpath.read_bytes())
assert sha(source)==plan['source_sha256']
seed=raw['seed'];first=set(plan['first_lower_domain']);records=[];configs=[]
for row in plan['context_rows']:
    assert row==raw['contexts'][row['id']]
    part=row['parts'][1];u,v=part['anchors']
    allowed={z for z in part['allowed'] if z!=480 and not adjacent(z,480)}
    upper={z for z in allowed if z>=256};lower={z for z in allowed if z<256}
    ports={z for z in lower if z+256 in upper}
    left,lc=upper_paths(upper,u,v,ports);right,rc=upper_paths(upper,v,u,ports)
    rowconfigs=[]
    for a in left:
        for br in right:
            if any(x==y or adjacent(x,y) for x in a for y in br):continue
            b=list(reversed(br));s=a[-1]-256;t=b[0]-256
            assert s!=t
            tops=set(a+b);projections={z-256 for z in tops}
            domain=lower-(projections-{s,t})
            length=44-2-(len(a)-1)-(len(b)-1)
            firstdomain=first-projections
            if length<1 or not {s,t}<=domain or not {18,224}<=firstdomain:continue
            cfg=dict(id=len(configs),context=row['id'],upper_prefix=a,upper_suffix=b,lower_anchors=[s,t],lower_edges=length,lower_domain=sorted(domain),first_domain=sorted(firstdomain),upper_projections=sorted(projections),intervals=row['intervals'])
            assert induced(a) and induced(b) and len(a)+length+1+len(b)==45
            configs.append(cfg);rowconfigs.append(cfg['id'])
    records.append(dict(context=row['id'],upper_domain=sorted(upper),lower_vertices=len(lower),ports=sorted(ports),prefix_count=len(left),suffix_count=len(right),prefix_nodes=lc,suffix_nodes=rc,configurations=rowconfigs))
out=dict(status='COMPLETE_UPPER_ENUMERATION',pins={str(source):sha(source),str(planpath):sha(planpath),str(Path(__file__)):sha(__file__)},first_lower_edges=43,first_lower_anchors=[18,224],first_upper_suffix=[480],contexts=records,configurations=configs,scope='Complete induced upper prefix/suffix pairs for the seven selected two-crossing second paths, after compatibility with fixed first vertex480. Native finite enumeration; no Lean traversal certificate. Each configuration still requires two compatible lower paths and a full assembled witness audit.')
save(H/'data/companions.json',out)
print(json.dumps(dict(configurations=len(configs),contexts=records),indent=2))
