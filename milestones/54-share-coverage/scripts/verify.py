"""Reconstruct full transition eligibility and audit potentials, controls, and Lean accounting."""
from pathlib import Path
from fractions import Fraction
import collections, gzip, hashlib, itertools, json, re, sys

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/52-share-on-235/scripts'))
from geometry_helpers import forest,shares
np=model.np

def read(path): return json.loads((HERE/path).read_text())
def sha(data): return hashlib.sha256(data).hexdigest()

for row in read('data/provenance.json')['files']:
    data=(HERE/'data/upstream'/row['archive']).read_bytes()
    assert sha(data if row['path'].endswith('.gz') else gzip.decompress(data))==row['sha256']

results=[]
for name,keyfile in [('base235','keys_235.json'),('all-known','all-keys.json'),
                     ('proposed-share','all-keys.json'),('proposed-joint','combined-keys.json'),
                     ('bidirectional','all-keys.json'),('proposed-bidirectional','combined-keys.json')]:
    meta=read(f'{name}/data/model.json'); keys=read('data/'+keyfile)['keys']
    with np.load(HERE/name/'build/graph.npz') as z: a={k:z[k] for k in z.files}
    for field,digest in meta['arrays_sha256'].items(): assert sha(a[field].tobytes())==digest
    tables={}
    for ds,bounds in keys:
        cs=[lo for lo,hi in bounds]
        assert all((lo==hi and 1<=lo<=5) or (lo==6 and hi==21) for lo,hi in bounds)
        for word,counts in [(ds,cs),(ds[::-1],cs[::-1])]:
            table=tables.setdefault(model.canon(word),np.zeros(6**len(cs),dtype=bool))
            table[int(model.code(np.array([counts]))[0])]=True
    sid={tuple(ds):i for i,ds in enumerate(meta['direction_shapes'])}
    full=np.array(list(itertools.product(range(1,7),repeat=6)),dtype=np.int16)
    for di,ds in enumerate(meta['extensions']):
        keep=np.ones(6**6,dtype=bool)
        for width in range(2,7):
            table=tables.get(model.canon(ds[-width-1:]))
            if table is not None: keep &= ~table[model.code(full[:,-width:])]
        indices=np.flatnonzero(a['direction']==di); codes=np.flatnonzero(keep)
        assert np.array_equal(a['count_code'][indices],codes)
        assert np.array_equal(a['U'][indices],sid[model.canon(ds[:7])]*6**5+codes//6)
        assert np.array_equal(a['V'][indices],sid[model.canon(ds[1:])]*6**5+codes%6**5)
        assert np.array_equal(a['count'][indices],full[codes,-1])
        lower=np.zeros(len(codes),dtype=np.int16)
        for rule in meta['share_rules']:
            if model.canon(ds[-6:])==tuple(rule['directions']):
                lower=np.maximum(lower,np.where(np.all(full[codes,-5:]==rule['counts'],axis=1),rule['lower'],0))
        assert np.array_equal(a['share_lower'][indices],lower)
    for mode in ['count','share']:
        analysis=read(f'{name}/data/analysis-{mode}.json'); assert analysis['status']=='EXACT_FINITE_MODEL'
        W=120*a['count'].astype(np.int64)+(a['share_lower'] if mode=='share' else 0)
        mean=Fraction(analysis['integer_weight_mean']); p,q=mean.numerator,mean.denominator
        encoded=gzip.decompress((HERE/name/f'data/potential-{mode}.i64.gz').read_bytes())
        assert sha(encoded)==analysis['potential_sha256']
        pi=np.frombuffer(encoded,dtype='<i8')
        assert len(pi)==meta['states'] and int(pi.max()-pi.min())==analysis['potential_range']
        assert np.all(p+pi[a['V']]<=q*W+pi[a['U']])
        cycle=analysis['cycle']
        for j,row in enumerate(cycle):
            ds,cs=row['directions'],row['counts'];di=meta['extensions'].index(ds)
            code=int(model.code(np.array([cs]))[0])
            matches=np.flatnonzero((a['direction']==di)&(a['count_code']==code))
            assert len(matches)==1; e=matches[0]
            assert row['state']==a['U'][e] and row['next_state']==a['V'][e]==cycle[(j+1)%len(cycle)]['state']
            assert row['weight']==W[e]
            assert row['share_lower']==(a['share_lower'][e] if mode=='share' else 0)
        assert Fraction(sum(r['weight'] for r in cycle),len(cycle))==mean
        bound=Fraction(1099800*q+7*p+analysis['potential_range'],p+4200*q)
        assert str(bound)==analysis['conditional_edge_bound']
        results.append(dict(model=name,mode=mode,mean=str(mean/120),cycle_length=len(cycle),
            edges=len(W),potential_range=analysis['potential_range'],conditional_bound=str(bound)))

controls=[];screen_status=collections.Counter()
windows=read('data/windows.json')
for i,row in enumerate(windows):
    control=read(f'data/controls/w{i:02d}.json');screen=read(f'data/screen/w{i:02d}.json')
    screen_status[screen['status']]+=1
    if control['status']=='SAT':
        W=[0]
        for d in row['directions']: W.append(W[-1]^(1<<d))
        S=set(control['selected']);alpha=forest(S,W);share=shares(S,W[1:-1])
        assert alpha==control['census']['alpha'] and share==control['census']['share']
        assert all((a>=6 if c==6 else a==c) for a,c in zip(alpha,row['counts']))
        controls.append(dict(row=i,share=sum(share),sha256=sha((HERE/f'data/controls/w{i:02d}.json').read_bytes())))
        if screen['status'] in ['FEASIBLE','OPTIMAL']:
            S=set(screen['selected']);alpha=forest(S,W);share=shares(S,W[1:-1])
            assert all((6<=a<=21 if c==6 else a==c) for a,c in zip(alpha,row['counts']))
            assert sum(share)<=screen['cap']
    else:
        assert screen['status']=='SKIPPED'

record=read('logs/build-record.json');build=Path(record['build'])
assert (HERE/'build/latest.txt').read_text().strip()==str(build)
assert len(record['records'])==2
for row in record['records']:
    assert row['exit_code']==0 and row['source_sha256']==sha((HERE/'lean'/(row['module']+'.lean')).read_bytes())
    assert (build/(row['module']+'.olean')).exists()
audits=[]
for module,count in [('FiveWindowBudget',5),('ReverseShareRule',3)]:
    log=(HERE/f'logs/{module}.log').read_text()
    assert not any(s in log for s in ['error:','sorryAx','Lean.ofReduceBool'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    assert len(rows)==count
    for name,axioms in rows: assert {x.strip() for x in axioms.split(',')}<={'propext','Classical.choice','Quot.sound'}
    audits.extend(name for name,axs in rows)
out=dict(status='PASS',models=results,lean_modules=2,lean_audits=8,audited_theorems=audits,positive_controls=controls,
    screen_status=dict(screen_status),scope='Full numerical graph reconstruction, potentials and cycles checked; local controls checked independently; five-window and conditional arithmetic checked in Lean. No complete all-key replay or global bound improvement.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='positive_controls'})
