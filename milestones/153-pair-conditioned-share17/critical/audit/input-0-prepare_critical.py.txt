"""Test one exact low-pair context that actually occurs on the saved eleven-cycle."""
from pathlib import Path
import gzip,hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1];S=H/'critical'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
for d in ['scripts','data','work','audit']:(S/d).mkdir(parents=True,exist_ok=True)
review=R/'milestones/149-share-credit-tradeoff/audit/graph-review.json'
j=read(review); row=next(x for x in j['eleven_cycle']['rows'] if x['edge']==2222339)
assert row['shape']=='012032' and row['counts']==[5,4,4,4,5,3]
assert row['counts'][2]+row['counts'][4]==9 and max(row['counts'])<6
counts=row['counts'][1:];assert counts==[4,4,4,5,3]
sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
import tagged_share,gen_lean_sat,wincert
e=tagged_share.TaggedShare([0,1,2,0,3,2],[(c,c) for c in counts],16,M=12)
folder=S/'work/critical17';folder.mkdir(exist_ok=False)
cnf=folder/'input.cnf'
cnf.write_bytes((f'p cnf {e.nv} {len(e.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.clauses)).encode('ascii'))
meanings=folder/'meanings.json.gz'
meanings.write_bytes(gzip.compress(json.dumps(dict(meaning=e.meaning,smeaning=e.smeaning,ctrs=e.ctrs,
    tots=e.tots,tags=e.tags,ball=e.ball,var=e.var)).encode(),mtime=0))
sources=[Path(__file__),Path(tagged_share.__file__),Path(gen_lean_sat.__file__),Path(wincert.__file__),review]
pins={p.relative_to(R).as_posix():sha(p) for p in sources}
for i,p in enumerate(sources):(S/'audit'/f'input-{i}-{p.name}.txt').write_bytes(p.read_bytes())
enc=dict(label='critical17',status='PREPARED_UNSOLVED_CRITICAL_CONTEXT_QUERY',directions=[0,1,2,0,3,2],window=e.window,
    bounds=[[c,c] for c in counts],resolution=12,radius=4,endpoint_budget=2,share_cap=16,target_share=17,
    actual_pair_minimum=None,actual_pair_value=9,source_cycle_edge=2222339,
    variables=e.nv,clauses=len(e.clauses),base_clauses=len(e.clauses),extra_clauses=0,extra_cycle_cuts=[],
    cnf_sha256=sha(cnf),meanings_sha256=sha(meanings),source_files_sha256=pins,
    scope='Only the exact five-count context4,4,4,5,3 is tested. No universal or high-pair share claim; no actual snake theorem before complete interpretation and replay.')
(folder/'encoding.json').write_text(json.dumps(enc,indent=2)+'\n',encoding='utf-8')
old=H/'scripts/native_queries.py';s=old.read_text(encoding='utf-8')
s=s.replace("H=Path(__file__).resolve().parents[1];R=H.parents[1]","H=Path(__file__).resolve().parents[1];R=H.parents[2]")
assert s.count("['highpair17']")==2;s=s.replace("['highpair17']","['critical17']")
s=s.replace('one conditional local share query','one exact critical-context share query')
s=s.replace('One bounded conditional certificate experiment','One bounded exact critical-context certificate experiment')
driver=S/'scripts/native_queries.py';assert not driver.exists();driver.write_text(s,encoding='utf-8',newline='\n')
record=dict(status='PREPARED_CRITICAL_CONTEXT_SHARE17_TEST',encoding=enc,
    source_driver_sha256=sha(old),driver_sha256=sha(driver),solver_seconds=90,replay_seconds=90,
    hypothesis='An actual012032 window with five counts4,4,4,5,3 has share>=17.',
    motivation='The high-pair restriction misses every012032 occurrence on the critical eleven-cycle. This exact context occurs on that cycle.',
    universal_share17=False,new_global_upper_bound=False)
(S/'data/preparation.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:enc[k] for k in ['label','bounds','variables','clauses','target_share','actual_pair_value']}))
