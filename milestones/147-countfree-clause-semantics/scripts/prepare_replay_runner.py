"""Adapt the audited bounded runner to the separately pinned15-bit pilot."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def one(s,a,b):assert s.count(a)==1,(a,s.count(a));return s.replace(a,b)
checker=H/'scripts/check_module.py';s=checker.read_text(encoding='utf-8')
s=one(s,"H=Path(__file__).resolve().parents[1];R=H.parents[1]","P=Path(__file__).resolve().parents[1];H=P/'replay';R=P.parents[1]")
s=one(s,"planpath=H/'data/semantic-plan.json'","planpath=H/'data/pilot-source-plan.json'")
s=one(s,"env['LEAN_PATH']=str(build)","env['LEAN_PATH']=str(build)+';'+str(P/'build')")
s=one(s,"rp=H/'data'/(name+'-audit.json');q=read(rp)","rp=H/'data'/(name+'-audit.json')\n    if not rp.exists():rp=P/'data'/(name+'-audit.json')\n    q=read(rp)")
s=one(s,"assert p.is_relative_to(build.resolve()) or p.is_relative_to((B.parent/'lib/lean').resolve()),p", "assert p.is_relative_to(build.resolve()) or p.is_relative_to((P/'build').resolve()) or p.is_relative_to((B.parent/'lib/lean').resolve()),p")
s=one(s,"generic=a.module in plan['framework_modules']","generic=a.module in ['LratCheck147Replay','LratFast147Replay','InputTree147Replay','ReplayTools147']")
s=one(s,"log=str(log),paths=[str(build)]","log=str(log),paths=[str(build),str(P/'build')]")
out=H/'scripts/check_replay.py';assert not out.exists();out.write_text(s,encoding='utf-8',newline='\n')
driver=H/'scripts/run_semantics.py';s=driver.read_text(encoding='utf-8')
s=one(s,"H=Path(__file__).resolve().parents[1];R=H.parents[1]","P=Path(__file__).resolve().parents[1];H=P/'replay';R=P.parents[1]")
s=one(s,"planpath=H/'data/semantic-plan.json'","planpath=H/'data/pilot-source-plan.json'")
s=one(s,"plan['status']=='PREPARED_MINIMAL_IMPORTS_WITH_UNCHANGED_MATHEMATICAL_INPUT'","plan['status']=='SOURCE_PREPARED_UNCHECKED'")
s=s.replace("H/'scripts/check_module.py'","P/'scripts/check_replay.py'")
s=s.replace('semantic-batch','replay-batch').replace('semantic-progress','replay-progress').replace('semantic-launch','replay-launch')
s=one(s,"lock=H/'data/replay-batch.lock';stamp=str(time.time_ns())","(H/'logs').mkdir(parents=True,exist_ok=True)\nlock=H/'data/replay-batch.lock';stamp=str(time.time_ns())")
s=s.replace('PASS_BOUNDED_SEMANTIC_PREFIX','PASS_BOUNDED_REPLAY_PILOT_PREFIX')
s=s.replace('PASS_COMPLETE_GENERIC_AND_CONCRETE_CLAUSE_CHECKS','PASS_COMPLETE_REPLAY_PILOT')
s=s.replace('Fresh generic models and exact concrete clause checks. Full contradiction and actual-snake theorem remain separate.', '15-bit checker, full initial-tree bridge and bounded prefix/checkpoint. The full contradiction and actual-snake theorem remain separate.')
runner=H/'scripts/run_replay.py';assert not runner.exists();runner.write_text(s,encoding='utf-8',newline='\n')
q=dict(status='PREPARED_BOUNDED_REPLAY_RUNNER',
    files_sha256={p.relative_to(H).as_posix():sha(p) for p in [Path(__file__),checker,driver,out,runner,H/'replay/data/pilot-source-plan.json']},
    parent_build_path=str(H/'build'),replay_build_path=str(H/'replay/build'),
    limits='Zero other Lean processes at launch;3GiB own-process limit,768MiB free-memory floor; one compiler at a time.')
(H/'data/replay-runner-plan.json').write_text(json.dumps(q,indent=2)+'\n',encoding='utf-8',newline='\n')
print(q['status'])
