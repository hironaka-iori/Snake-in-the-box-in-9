"""Test the next012032 share floor without altering the active share16 proof."""
from pathlib import Path
import gzip,hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1];S=H/'strengthening'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ['scripts','data','work','audit']:(S/name).mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
import tagged_share,gen_lean_sat,wincert
e=tagged_share.TaggedShare([0,1,2,0,3,2],[(0,21)]*5,16,M=12)
folder=S/'work/universal17';folder.mkdir(exist_ok=False)
cnf=folder/'input.cnf';cnf.write_bytes((f'p cnf {e.nv} {len(e.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.clauses)).encode('ascii'))
meanings=folder/'meanings.json.gz'
meanings.write_bytes(gzip.compress(json.dumps(dict(meaning=e.meaning,smeaning=e.smeaning,ctrs=e.ctrs,tots=e.tots,tags=e.tags,ball=e.ball,var=e.var)).encode(),mtime=0))
sources=[Path(__file__),Path(tagged_share.__file__),Path(gen_lean_sat.__file__),Path(wincert.__file__)]
pins={p.relative_to(R).as_posix():sha(p) for p in sources}
for p in sources:(S/'audit'/('input-source-'+p.name+'.txt')).write_bytes(p.read_bytes())
encoding=dict(label='universal17',status='PREPARED_UNSOLVED_LOCAL_QUERY',directions=[0,1,2,0,3,2],window=e.window,
    bounds=[[0,21]]*5,resolution=12,radius=4,endpoint_budget=2,share_cap=16,target_share=17,
    variables=e.nv,clauses=len(e.clauses),base_clauses=len(e.clauses),extra_clauses=0,extra_cycle_cuts=[],
    cnf_sha256=sha(cnf),meanings_sha256=sha(meanings),source_files_sha256=pins,
    scope='Next integer floor, with no added count condition. A numerical certificate is not yet an actual-snake theorem; timeout is unresolved.')
(folder/'encoding.json').write_text(json.dumps(encoding,indent=2)+'\n',encoding='utf-8')
old=R/'milestones/150-actual-pair-share/scripts/native_queries.py';s=old.read_text(encoding='utf-8')
s=s.replace("H=Path(__file__).resolve().parents[1];R=H.parents[1]","H=Path(__file__).resolve().parents[1];R=H.parents[2]")
s=s.replace("['highpair16','universal15']","['universal17']")
s=s.replace('memory_limit_bytes=2*1024**3','memory_limit_bytes=1024**3')
s=s.replace("folder,'solver',90,raw","folder,'solver',60,raw")
s=s.replace("folder,'replay',90","folder,'replay',60")
s=s.replace('two explicit local share queries','one stronger local share query').replace('Two bounded local certificate experiments','One bounded local certificate experiment')
s=s.replace('continuing147','continuing151').replace('existing147','existing151')
driver=S/'scripts/native_queries.py';assert not driver.exists();driver.write_text(s,encoding='utf-8',newline='\n')
record=dict(status='PREPARED_SHARE17_HYPOTHESIS_TEST',encoding=encoding,
    source_driver_sha256=sha(old),driver_sha256=sha(driver),solver_seconds=60,replay_seconds=60,
    hypothesis='Every fitting012032 window has five-centre share at least17. Unproved; the existing share16 full replay continues unchanged.',
    prior_review='The historical cap23,47,71 attempts were UNKNOWN after approximately6 seconds. They do not settle cap16 or establish sharpness of16.')
(S/'data/preparation.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:encoding[k] for k in ['status','share_cap','target_share','variables','clauses']}))
