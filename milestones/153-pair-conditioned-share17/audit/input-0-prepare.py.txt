"""Test share17 under the explicit actual second-plus-fourth count floor10."""
from pathlib import Path
import datetime,gzip,hashlib,itertools,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d in ['data','audit','work','scripts']:(H/d).mkdir(exist_ok=True)
assert not (H/'data/preparation.json').exists()
sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
import tagged_share,gen_lean_sat,wincert
e=tagged_share.TaggedShare([0,1,2,0,3,2],[(0,21)]*5,16,M=12)
base_count=len(e.clauses);base_variables=e.nv
base_bytes=(f'p cnf {e.nv} {base_count}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.clauses)).encode('ascii')
prior=R/'milestones/152-countfree-share16-completion/strengthening/work/universal17/encoding.json'
assert hashlib.sha256(base_bytes).hexdigest()==read(prior)['cnf_sha256']
corners=[]
for ci in [2,4]:
    center=e.window[ci]
    used={(center^e.window[ci-1]).bit_length()-1,(center^e.window[ci+1]).bit_length()-1}
    row=[center^(1<<a)^(1<<b) for a,b in itertools.combinations(range(9),2) if a not in used and b not in used]
    assert len(row)==len(set(row))==21
    corners.append(row)
missing=[-e.var[v] for row in corners for v in row]
assert len(missing)==42 and len(set(v for row in corners for v in row))==37
counter,out=e.totalizer(missing,('actualPair',[2,4]),up=False,down=True,limit=10)
e.add([out[10]],('actualPairLo',counter,10))
folder=H/'work/highpair17';folder.mkdir(exist_ok=False)
cnf=folder/'input.cnf'
cnf.write_bytes((f'p cnf {e.nv} {len(e.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.clauses)).encode('ascii'))
meanings=folder/'meanings.json.gz'
meanings.write_bytes(gzip.compress(json.dumps(dict(meaning=e.meaning,smeaning=e.smeaning,ctrs=e.ctrs,
    tots=e.tots,tags=e.tags,ball=e.ball,var=e.var)).encode(),mtime=0))
sources=[Path(__file__),Path(tagged_share.__file__),Path(gen_lean_sat.__file__),Path(wincert.__file__),prior,
         R/'milestones/150-actual-pair-share/scripts/prepare.py']
pins={p.relative_to(R).as_posix():sha(p) for p in sources}
for i,p in enumerate(sources):(H/'audit'/f'input-{i}-{p.name}.txt').write_bytes(p.read_bytes())
enc=dict(label='highpair17',status='PREPARED_UNSOLVED_CONDITIONAL_QUERY',directions=[0,1,2,0,3,2],window=e.window,
    bounds=[[0,21]]*5,resolution=12,radius=4,endpoint_budget=2,share_cap=16,target_share=17,
    actual_pair_positions=[2,4],actual_pair_minimum=10,pair_corners=corners,
    pair_corner_occurrences=42,distinct_pair_corners=37,pair_counter=counter,
    variables=e.nv,clauses=len(e.clauses),base_clauses=base_count,base_variables=base_variables,
    extra_clauses=len(e.clauses)-base_count,extra_variables=e.nv-base_variables,extra_cycle_cuts=[],
    cnf_sha256=sha(cnf),meanings_sha256=sha(meanings),base_cnf_sha256=hashlib.sha256(base_bytes).hexdigest(),
    source_files_sha256=pins,
    scope='Conditional target. Actual pair floor10 is additional; complete snakes with smaller sums exist. All42 missing-corner occurrences, including multiplicities, are counted. No global-bound consequence is asserted.')
(folder/'encoding.json').write_text(json.dumps(enc,indent=2)+'\n',encoding='utf-8')
old=R/'milestones/150-actual-pair-share/scripts/native_queries.py';s=old.read_text(encoding='utf-8')
assert s.count("['highpair16','universal15']")==2
s=s.replace("['highpair16','universal15']","['highpair17']")
s=s.replace('memory_limit_bytes=2*1024**3','memory_limit_bytes=1024**3')
s=s.replace('two explicit local share queries','one conditional local share query')
s=s.replace('Two bounded local certificate experiments','One bounded conditional certificate experiment')
s=s.replace('continuing147','continuing151').replace('existing147','existing151')
driver=H/'scripts/native_queries.py';assert not driver.exists();driver.write_text(s,encoding='utf-8',newline='\n')
record=dict(status='PREPARED_CONDITIONAL_SHARE17_TEST',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    encoding=enc,source_driver_sha256=sha(old),driver_sha256=sha(driver),solver_seconds=90,replay_seconds=90,
    hypothesis='Every actual012032 window with alpha2+alpha4>=10 has five-centre share>=17.',
    motivation='The existing endpoint theorem controls the number of smaller-pair windows. This query targets an improved share contribution away from them.',
    universal_share17=False,new_global_upper_bound=False)
(H/'data/preparation.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:enc[k] for k in ['label','variables','clauses','base_clauses','extra_clauses','extra_variables','target_share','actual_pair_minimum']}))
