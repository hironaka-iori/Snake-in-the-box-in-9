"""One exact integer potential test for the fixed H15/C1 profile."""
from pathlib import Path
from fractions import Fraction
import datetime, gzip, hashlib, importlib.util, json, subprocess, time

H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/97-geometric-credit-integration/floor-sensitivity'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
target=H/'data/new-potential.json';assert not target.exists()
start=time.monotonic();deadline=start+120
resources=json.loads(subprocess.check_output(['powershell.exe','-NoProfile','-Command',
    '$o=Get-CimInstance Win32_OperatingSystem; @{free_bytes=([long]$o.FreePhysicalMemory*1024)} | ConvertTo-Json -Compress'],text=True))
assert resources['free_bytes']>=3*1024**3
spec=importlib.util.spec_from_file_location('old_inputs149',P/'test.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old);np=old.np
meta,a,shapes,entering,w,cycle,paths,pins=old.setup()
expected=read(H/'data/saved-potential-test.json')
for s,k in [('012034',18),('012032',15)]:
    chosen=shapes==old.SHAPES.index(s);w[chosen]=np.maximum(a['weight'][chosen],entering[chosen]+k)
code=a['count_code'];x=code//6**3%6+1;y=code//6%6+1
event=(shapes==1)&(x<6)&(y<6)&(x+y<=9);w+=event
assert hashlib.sha256(w.tobytes()).hexdigest()==expected['candidate_weight_sha256']
u,v,n=a['U'],a['V'],meta['states'];assert sum(int(w[e]) for e in cycle)==1488
dist=np.zeros(n,dtype=np.int64);parents=[]
out=dict(status='UNRESOLVED_ITERATION_LIMIT',mean=496,credit=1,
    occurrence_allowance_assumed=24,edges=len(u),states=n,
    fixed_floors=expected['fixed_floors'],weight_sha256=expected['candidate_weight_sha256'],
    source_test_sha256=sha(H/'data/saved-potential-test.json'),script_sha256=sha(Path(__file__)),
    resource_preflight=resources,iteration_limit=227,time_budget_seconds=120,
    source_files_sha256=pins,cycle_ids=cycle,
    scope='Exact finite graph under the listed local floors, reference and occurrence premises; no actual-snake or global234 conclusion.')
for iteration in range(1,228):
    if time.monotonic()>deadline:
        out['status']='UNRESOLVED_TIME_LIMIT';break
    candidate=dist[u]+w-496;nxt=dist.copy();np.minimum.at(nxt,v,candidate)
    if np.array_equal(nxt,dist):
        pi=dist-dist.min();spread=int(pi.max());assert np.all(496+pi[v]<=w+pi[u])
        raw=pi.astype('<i8').tobytes();archive=H/'data/floor15-credit1-potential.i64.gz'
        assert not archive.exists();archive.write_bytes(gzip.compress(raw,mtime=0))
        bound=Fraction(1098960+8*496+24+spread,4696)
        out.update(status='PASS_CONDITIONAL234_POTENTIAL' if spread<608 else 'PASS_POTENTIAL_WITHOUT234',
            potential_range=spread,comparison=str(bound),strict_margin=608-spread,
            potential_file=archive.name,potential_raw_sha256=hashlib.sha256(raw).hexdigest(),
            potential_archive_sha256=sha(archive),all_edge_inequalities_checked=True)
        break
    eligible=np.flatnonzero((candidate==nxt[v])&(nxt[v]<dist[v]))
    pred=np.full(n,-1,dtype=np.int32);np.maximum.at(pred,v[eligible],eligible)
    assert np.all(pred[nxt<dist]>=0);parents.append(pred);dist=nxt
    deficit=-int(dist.min())
    if deficit>=608:
        end=int(np.argmin(dist));edges=[]
        for layer in reversed(parents):
            e=int(layer[end])
            if e>=0:edges.append(e);end=int(u[e])
        edges.reverse();old.valid_walk(edges,a)
        total=sum(int(w[e]) for e in edges)
        assert len(edges)<=iteration<=227 and len(edges)*496-total==deficit
        ceiling=(227-len(edges))*496+total-24
        assert ceiling<=111960
        out.update(status='PASS_FIXED_CREDIT_ALL_SLOPE_RANGE_OBSTRUCTION',
            length=len(edges),weight=total,deficit=deficit,criterion_ceiling=ceiling,
            walk=[dict(row,event=bool(event[row['edge']]),
                  weaker_weight_without_credit=int(w[row['edge']])-int(event[row['edge']]))
                  for row in old.rows(edges,a,shapes,w)])
        break
out.update(iterations=iteration,seconds=time.monotonic()-start,
    timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat())
assert all(sha(R/p)==d for p,d in pins.items())
target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['walk','source_files_sha256']}),flush=True)
