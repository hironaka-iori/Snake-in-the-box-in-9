"""Compiler-free safety controls for planning, hash reuse and axiom audit."""
from pathlib import Path
import contextlib,io,json,sys,tempfile,os,copy
import build_replay as D
H=Path(__file__).resolve().parent;checks=0
realrun,realpopen=D.subprocess.run,D.subprocess.Popen
D.subprocess.run=lambda *a,**k:(_ for _ in ()).throw(AssertionError('plan invoked compiler'))
D.subprocess.Popen=D.subprocess.run
saved=sys.argv
try:
 sys.argv=['build_replay.py','--plan','--max-modules','1']
 with contextlib.redirect_stdout(io.StringIO()) as out:assert D.main()==0
 plan=json.loads(out.getvalue());assert plan['build']==1 and plan['deferred']==75;checks+=1
finally:D.subprocess.run,D.subprocess.Popen=realrun,realpopen;sys.argv=saved
oldroot=D.ROOT
with tempfile.TemporaryDirectory(prefix='driver_test_',dir=H) as temporary:
 root=Path(temporary).resolve();assert root.is_relative_to(H.resolve())
 D.ROOT=root;prefix=root/'tool';(prefix/'lib/lean').mkdir(parents=True);(prefix/'lib/lean/Std.olean').write_bytes(b'std-old')
 names=['A','B',D.AUDIT]
 for name,text in [('A','import Std\n'),('B','import A\n'),(D.AUDIT,'import B\n')]:
  D.module_path(name,'.lean').write_text(text);D.module_path(name,'.olean').write_bytes(b'valid-'+name.encode())
 identity={'version':'Lean (version 4.19.0)','executable_sha256':'recorded-hash','prefix':str(prefix)}
 state={'toolchain':identity.copy(),'completed':{}}
 for name in names:
  state['completed'][name]={'source_sha256':D.sha(D.module_path(name,'.lean')),'olean_sha256':D.sha(D.module_path(name,'.olean')),'dependency_olean_sha256':D.dependency_hashes(D.module_path(name,'.lean'),names,identity),'audit':{'final_theorem_audited':name==D.AUDIT}}
 assert all(r['action']=='REUSE' for r in D.make_plan(names,state,identity,True,None));checks+=1
 changed=dict(identity,executable_sha256='different');assert all(r['action']=='BUILD' for r in D.make_plan(names,state,changed,True,None));checks+=1
 p=D.module_path('A','.olean');st=p.stat();p.write_bytes(b'bad-A');os.utime(p,ns=(st.st_atime_ns,st.st_mtime_ns))
 assert all(r['action']=='BUILD' for r in D.make_plan(names,state,identity,True,None));checks+=1
 p.write_bytes(b'valid-A');std=prefix/'lib/lean/Std.olean';std.write_bytes(b'std-new')
 assert all(r['action']=='BUILD' for r in D.make_plan(names,state,identity,True,None));checks+=1
 std.write_bytes(b'std-old');state['completed'][D.AUDIT]['audit']={};rows=D.make_plan(names,state,identity,True,None)
 assert [r['action'] for r in rows]==['REUSE','REUSE','BUILD'];checks+=1
D.ROOT=oldroot
valid=f"'{D.THEOREM}' depends on axioms: [propext, Classical.choice, Quot.sound]"
assert D.log_audit(valid,True)['passed'];checks+=1
for text in [valid+'\nerror: bad',valid+'\nsorryAx',valid.replace('Quot.sound','unproved_axiom'),'no audit present']:
 try:D.log_audit(text,True)
 except ValueError:checks+=1
 else:raise AssertionError(text)
for v,ok in [('Lean (version 4.19.0, x86_64, Release)',True),('Lean (version 4.19.0)',True),('Lean version 4.19.0',True),('Lean (version 4.19.0-rc1)',False),('Lean (version 4.19.01)',False),('Lean (version 4.20.0)',False)]:
 assert D.pinned_version(v)==ok;checks+=1
result={'compiler_free_controls_passed':checks,'plan_compiler_invocations':0,'hash_dependency_and_toolchain_reuse_tested':True,'final_axiom_audit_negatives_rejected':True}
(H/'build_driver_tests.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
