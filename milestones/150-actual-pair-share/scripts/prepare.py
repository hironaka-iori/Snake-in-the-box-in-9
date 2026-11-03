"""Prepare two local share queries with an explicit actual-count pair condition."""
from pathlib import Path
import datetime,gzip,hashlib,itertools,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d in ['data','audit','work','scripts']:(H/d).mkdir(exist_ok=True)
assert not (H/'data/preparation.json').exists()
sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
import tagged_share,gen_lean_sat,wincert
from tagged_share import TaggedShare
old=R/'milestones/72-four-count-proof-closure/critical-current'
meta=read(old/'data/pysat1-cap15-certificate.json')
archived=gzip.decompress((old/'certificates/pysat1-cap15.cnf.gz').read_bytes())
assert hashlib.sha256(archived).hexdigest()==meta['cnf_sha256']
base=TaggedShare([0,1,2,0,3,2],[(0,21)]*5,15)
old_clauses=[[int(v) for v in line.split()[:-1]] for line in archived.decode('ascii').splitlines() if line and line[0] not in 'pc']
assert old_clauses==base.clauses and not meta['cycle_cuts']
sources=[Path(__file__),Path(tagged_share.__file__),Path(gen_lean_sat.__file__),Path(wincert.__file__),
    old/'data/pysat1-cap15-certificate.json',old/'certificates/pysat1-cap15.cnf.gz',
    R/'milestones/149-share-credit-tradeoff/audit/next-local-target.md']
pins={p.relative_to(R).as_posix():sha(p) for p in sources}
for p in sources:
    if p.suffix=='.py':(H/'audit'/('input-source-'+p.name+'.txt')).write_bytes(p.read_bytes())
prepared=[]
for label,cap,pair_minimum in [('universal15',14,None),('highpair16',15,10)]:
    start=time.monotonic();e=TaggedShare([0,1,2,0,3,2],[(0,21)]*5,cap)
    original_clauses=len(e.clauses);pair_corners=[];pair_counter=None
    if pair_minimum is not None:
        for ci in [2,4]:
            center=e.window[ci]
            used={(center^e.window[ci-1]).bit_length()-1,(center^e.window[ci+1]).bit_length()-1}
            corners=[center^(1<<a)^(1<<b) for a,b in itertools.combinations(range(9),2) if a not in used and b not in used]
            assert len(corners)==21 and len(set(corners))==21
            pair_corners.append(corners)
        missing=[-e.var[v] for row in pair_corners for v in row]
        assert len(missing)==42
        pair_counter,out=e.totalizer(missing,('actualPair',[2,4]),up=False,down=True,limit=10)
        e.add([out[10]],('actualPairLo',pair_counter,10))
    folder=H/'work'/label;folder.mkdir(exist_ok=False)
    cnf=folder/'input.cnf'
    cnf.write_bytes((f'p cnf {e.nv} {len(e.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.clauses)).encode('ascii'))
    meanings=folder/'meanings.json.gz'
    with meanings.open('wb') as f:
        f.write(gzip.compress(json.dumps(dict(meaning=e.meaning,smeaning=e.smeaning,ctrs=e.ctrs,tots=e.tots,tags=e.tags)).encode(),mtime=0))
    row=dict(label=label,status='PREPARED_UNSOLVED_LOCAL_QUERY',directions=[0,1,2,0,3,2],window=e.window,
        bounds=[[0,21]]*5,resolution=12,radius=4,endpoint_budget=2,share_cap=cap,
        target_share=cap+1,actual_pair_positions=[2,4] if pair_minimum else None,actual_pair_minimum=pair_minimum,
        pair_corners=pair_corners,pair_corner_occurrences=sum(map(len,pair_corners)),
        distinct_pair_corners=len(set(v for row in pair_corners for v in row)),pair_counter=pair_counter,
        variables=e.nv,clauses=len(e.clauses),base_clauses=original_clauses,
        extra_clauses=len(e.clauses)-original_clauses,extra_cycle_cuts=[],
        cnf_sha256=sha(cnf),meanings_sha256=sha(meanings),source_files_sha256=pins,
        historical_cap15_clauses_reproduced=True,seconds=time.monotonic()-start,
        scope='Local necessary-condition query only. The high-pair counter counts all42 missing-corner occurrences with multiplicity. No clipped counts or additional endpoint-location hypotheses. Solver, independent certificate replay and Lean interpretation remain separate.')
    (folder/'encoding.json').write_text(json.dumps(row,indent=2)+'\n',encoding='utf-8')
    prepared.append(row)
out=dict(status='PREPARED_TWO_LOCAL_SHARE_QUERIES',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    queries=prepared,source_files_sha256=pins,
    hypothesis='Every012032 window has share>=15, and actual alpha2+alpha4>=10 implies share>=16. Both unproved here.')
(H/'data/preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status=out['status'],queries=[{k:q[k] for k in ['label','share_cap','actual_pair_minimum','variables','clauses','extra_clauses','distinct_pair_corners']} for q in prepared])))
