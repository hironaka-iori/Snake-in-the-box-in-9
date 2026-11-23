import gzip,json,re,sys,subprocess,tempfile
from pathlib import Path
from itertools import combinations
from collections import Counter,defaultdict
d=Path(__file__).resolve().parent;r=d.parent
sys.path.insert(0,str(r))
from verify_q9_intact98_all_crossings import integer_bound
cs=list(map(json.loads,(d/'cases.jsonl').read_text().splitlines()))
def check_tree(path,row):
    if '--trees' not in sys.argv:return
    source=path.with_suffix('.tree');tables=path.with_suffix('.tables')
    with tempfile.TemporaryDirectory() as folder:
        if not source.exists():
            saved=source.with_suffix('.tree.gz');source=Path(folder)/'tree';source.write_bytes(gzip.decompress(saved.read_bytes()))
        result=subprocess.check_output([r/'q9_facet_priced_tree_20261121/replay',tables,source,'193'],text=True).strip()
        assert row['replay']==result
sets={'two_longest':('certs.log',),'four_controls':('controls_bounds.log',),'all_94':('bounds94a.log','bounds94b.log')}
summary={}
for name,files in sets.items():
    expected={}; branches={};rbound=Counter();upper={}
    price={}; original={}
    ids=[0,1] if name=='two_longest' else list(range(1249,1253)) if name=='four_controls' else list(range(2,63))
    for i in ids:
        z=cs[i];L=set(z['lo']+z['edge'])
        deg={x:sum(x^1<<k in L for k in range(8)) for x in L}
        terminals={x for x,q in deg.items() if q==1}
        for k in (2,3):
            for P in combinations(sorted(terminals),k):
                P=frozenset(P)
                if len(P&set(z['edge']))!=1:continue
                ends=terminals-P;col={x.bit_count()%2 for x in ends}
                if len(col)!=1:continue
                m=next(iter(col));eps=[int(c==m)*(2-len(ends)) for c in range(2)]
                delta=sum((-1)**v.bit_count() for v in L)-(-1)**m
                expected[i,P]=(m,eps,delta,L)
    for file in files:
        for line in (d/file).read_text().splitlines():
            row=json.loads(line);i=row['case'];P=frozenset(row['ports']);m,eps,delta,L=expected[i,P]
            if row.get('empty'):raise AssertionError('empty table needs independent replay')
            path=d/'bounds'/('c'+str(i)+'_p'+'-'.join(map(str,sorted(P)))+'.json')
            rec=json.loads(path.read_text())
            assert rec['word']==cs[i]['w'] and set(rec['lower_vertices'])==L and set(rec['ports'])==P
            assert (rec['majority'],rec['upper_endpoint_counts'],rec['upper_delta'])==(m,eps,delta)
            v=integer_bound(rec['cert'],L,P,eps,delta)+len(L)*rec['cert']['scale']
            assert v==rec['total_scaled']==row['total_scaled']
            root_closed=v<193*row['scale']
            if root_closed:status='root'
            else:
                assert 'replay' in row
                check_tree(path,row);result=row['replay'];assert result.startswith('VERIFIED ')
                opens=int(re.search(r'open (\d+)',result).group(1));found=int(re.search(r'witnesses (\d+)',result).group(1))
                assert not found;status='open' if opens else 'tree'
            assert (i,P) not in branches;branches[i,P]=status;rbound[status]+=1
            price[i,P]=v;original[i,P]=status
    assert set(branches)==set(expected),(name,len(branches),len(expected))
    refinements=0
    if name=='all_94':
        for f in sorted((d/'tight').glob('*.result')):
            row=json.loads(f.read_text());i=row['case'];P=frozenset(row['ports']);m,eps,delta,L=expected[i,P]
            assert original[i,P]=='open'
            rec=json.loads(f.with_suffix('.json').read_text())
            assert rec['word']==cs[i]['w'] and set(rec['lower_vertices'])==L and set(rec['ports'])==P
            assert (rec['majority'],rec['upper_endpoint_counts'],rec['upper_delta'])==(m,eps,delta)
            val=integer_bound(rec['cert'],L,P,eps,delta)+len(L)*rec['cert']['scale']
            assert val==row['total_scaled']==rec['total_scaled'] and row['scale']==10000
            price[i,P]=min(price[i,P],val)
            if val<1930000:branches[i,P]='root'
            else:
                check_tree(f,row);assert 'witnesses 0' in row['replay'] and row['replay'].startswith('VERIFIED ')
                if ' open 0 ' in row['replay']:branches[i,P]='tree'
            refinements+=1
    upper={i:max(v for (j,_),v in price.items() if j==i) for i in ids}
    closed=sorted(i for i in ids if all(branches[j,k]!='open' for j,k in expected if j==i))
    summary[name]=dict(cases=len(ids),cells=len(expected),initial_status=rbound,refinements=refinements,status=Counter(branches.values()),closed_cases=closed,open_cases=sorted(set(ids)-set(closed)),maximum_root_numerators=upper,scale=10000)
(d/'bounds_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
