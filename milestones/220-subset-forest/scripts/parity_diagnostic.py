"""Find exact product-consistency violations on the saved short cycles."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
reports=[]
for root in [0,78]:
    mp=H/'data'/f'forest-{root}'/'model.json';m=json.loads(mp.read_bytes());names={n:i for i,n in enumerate(m['variables'])}
    E={tuple(e) for e in m['edges']};cycles=[]
    for C in m['cycles']:
        start=min(C);path=[start];old=None;cur=start
        while True:
            choices=sorted(v for v in C if tuple(sorted([cur,v])) in E and v!=old)
            nxt=choices[0]
            if nxt==start:break
            assert nxt not in path;path.append(nxt);old,cur=cur,nxt
        assert len(path)==len(C);cycles.append(path)
    for kind in ['primal','target94']:
        p=H/'data'/f'rational-{root}'/(kind+'-certificate.json');c=json.loads(p.read_bytes());z=[Q(*q) for q in c['values']]
        violations=[];total=0
        for C in cycles:
            cycle_edges=[tuple(sorted([u,v])) for u,v in zip(C,C[1:]+C[:1])]
            d=[z[names[f'x{u}']]+z[names[f'x{v}']]-2*z[names[f'y{u}_{v}']] for u,v in cycle_edges]
            assert all(0<=a<=1 for a in d)
            for mask in range(1<<len(C)):
                if mask.bit_count()%2!=1:continue
                total+=1;lhs=sum((a if mask>>i&1 else -a for i,a in enumerate(d)),Q());rhs=mask.bit_count()-1
                if lhs>rhs:
                    violations.append({'cycle':C,'edges':cycle_edges,'odd_edge_indices':[i for i in range(len(C)) if mask>>i&1],
                        'disagreements':[[a.numerator,a.denominator] for a in d],'lhs':[lhs.numerator,lhs.denominator],
                        'rhs':rhs,'violation':[(lhs-rhs).numerator,(lhs-rhs).denominator]})
        violations.sort(key=lambda x:Q(*x['violation']),reverse=True)
        reports.append({'root':root,'point':kind,'model_sha256':sha(mp),'primal_sha256':sha(p),'cycles_checked':len(cycles),
            'odd_subsets_checked':total,'violations_found':len(violations),'largest_witnesses':violations[:10]})
        print(root,kind,'VIOLATIONS',len(violations),'MAX',violations[0]['violation'] if violations else None)
out=H/'data/parity-diagnostic.json';assert not out.exists()
out.write_text(json.dumps({'source_sha256':sha(__file__),'reports':reports,
    'scope':'Exact violations on saved4/6-cycles only. The valid inequalities are classical cut-polytope cycle inequalities applied to selection disagreement; no new LP solve or global bound.'},indent=2)+'\n',encoding='utf-8')
