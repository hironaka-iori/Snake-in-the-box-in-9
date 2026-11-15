"""Combine a certified rational point with an actual one-edge path."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rat(q):return [q.numerator,q.denominator]
for root in [0,78]:
    model_path=H/'data'/f'forest-{root}'/'model.json'
    p=H/'data'/f'rational-{root}'/'primal-certificate.json'
    m=json.loads(model_path.read_bytes()); cert=json.loads(p.read_bytes())
    values=[Q(*v) for v in cert['values']]
    other=min(v if u==root else u for u,v in m['edges'] if root in [u,v])
    names={n:i for i,n in enumerate(m['variables'])}; short=[Q() for n in names]
    for name in [f'x{root}',f'x{other}',f'e{other}',f'y{min(root,other)}_{max(root,other)}']:
        short[names[name]]=Q(1)
    lam=Q(92)/(Q(*cert['objective'])-2)
    assert 0<lam<1
    target=[lam*a+(1-lam)*b for a,b in zip(values,short)]
    for vector in [short,target]:
        assert all(0<=q<=1 for q in vector)
        for row in m['rows']:
            lhs=sum((a*vector[i] for i,a in row['terms']),Q())
            assert lhs==row['rhs'] if row['sense']=='eq' else lhs<=row['rhs'],row['name']
    assert sum(target[:len(m['vertices'])])==94
    out=p.with_name('target94-certificate.json'); assert not out.exists()
    out.write_text(json.dumps({'model_sha256':sha(model_path),'primal_sha256':sha(p),
        'source_sha256':sha(Path(__file__)),'short_path':[root,other],
        'mixing_weight':rat(lam),'short_values':[rat(v) for v in short],
        'values':[rat(v) for v in target],'objective':[94,1],
        'all_cycle_argument':'The certified original point and this one-edge path each satisfy every cycle occupancy inequality. Their convex combination does too.'},indent=2)+'\n',encoding='utf-8')
    print(root,'EXACT_TARGET94',rat(lam),sha(out))
