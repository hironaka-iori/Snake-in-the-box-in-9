"""Ordinary sequential Lean4.19 replay builder with a compiler-free plan mode.
Never downloads tools or changes application-control policy. Full replay is unrun here.
"""
from pathlib import Path
import argparse,json,os,subprocess,time,hashlib,sys,re
H=Path(__file__).resolve().parent;ROOT=H/'lrat_replay';AUDIT='PeerLratFinalAudit';THEOREM='Snake9.LocalWindow.PointwiseScore22.unsat';ALLOWED={'propext','Classical.choice','Quot.sound'}
def pinned_version(version):return bool(re.search(r'\bversion 4\.19\.0(?=,|\)|\s*$)',version))

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,d):p.write_text(json.dumps(d,indent=2),encoding='utf-8')
def imports(path):return re.findall(r'^import (\S+)',path.read_text(encoding='utf-8'),re.M)
def module_path(name,suffix):return ROOT.joinpath(*name.split('.')).with_suffix(suffix)
def dependency_hashes(source,order,toolchain):
 result={};prefix=toolchain.get('prefix')
 for name in imports(source):
  p=module_path(name,'.olean') if name in order else Path(prefix)/'lib/lean'/Path(*name.split('.')).with_suffix('.olean') if prefix else None
  result[name]=sha(p) if p is not None and p.exists() else None
 return result

def log_audit(text,require_final=False):
 if 'sorryAx' in text or "declaration uses 'sorry'" in text or re.search(r'(^|\n).*\berror:',text,re.I):raise ValueError('compiler log contains error/sorry')
 found=[]
 for match in re.finditer(r'depends on axioms:\s*\[([^\]]*)\]',text):
  axioms={x.strip() for x in match.group(1).split(',') if x.strip()}
  if not axioms<=ALLOWED:raise ValueError('unapproved axioms: '+str(axioms-ALLOWED))
  found.append(sorted(axioms))
 if require_final:
  lines=[line for line in text.splitlines() if THEOREM in line]
  if not any(('depends on axioms:' in line or 'does not depend on any axioms' in line) for line in lines):raise ValueError('missing final theorem axiom audit')
 return {'passed':True,'axiom_lists':found,'final_theorem_audited':require_final}

def make_plan(order,state,toolchain,reuse,limit):
 identity=bool(toolchain.get('version')) and all(toolchain.get(k)==state.get('toolchain',{}).get(k) for k in ('version','executable_sha256'))
 rows=[];building=set();count=0
 for name in order:
  src=module_path(name,'.lean');olean=module_path(name,'.olean');record=state.get('completed',{}).get(name,{});deps=dependency_hashes(src,order,toolchain)
  reasons=[]
  if not reuse:reasons.append('reuse not requested')
  if not identity:reasons.append('no matching recorded compiler hash/version')
  if record.get('source_sha256')!=sha(src):reasons.append('source not recorded or changed')
  if not olean.exists() or record.get('olean_sha256')!=sha(olean):reasons.append('olean missing or changed')
  if any(v is None for v in deps.values()) or record.get('dependency_olean_sha256')!=deps:reasons.append('import olean hashes missing or changed')
  if any(im in building for im in imports(src)):reasons.append('dependency scheduled to rebuild')
  if name==AUDIT and not record.get('audit',{}).get('final_theorem_audited'):reasons.append('final audit not recorded')
  action='REUSE'
  if reasons:
   action='BUILD' if limit is None or count<limit else 'DEFER_LIMIT';count+=1;building.add(name)
  rows.append({'module':name,'action':action,'reasons':reasons})
 return rows

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--lean',help='real ordinary Lean4.19 executable');ap.add_argument('--max-modules',type=int);ap.add_argument('--reuse',action='store_true');ap.add_argument('--plan',action='store_true',help='no subprocess/compiler invocation');ap.add_argument('--plan-output',type=Path);a=ap.parse_args()
 manifest=json.loads((H/'full_replay_manifest.json').read_text(encoding='utf-8'));order=manifest['build_order'];statefile=H/'native_build_progress.json'
 previous=json.loads(statefile.read_text(encoding='utf-8')) if statefile.exists() else {'completed':{}}
 if a.max_modules is not None and a.max_modules<0:raise ValueError('nonnegative module limit required')
 if a.plan:
  toolchain=dict(previous.get('toolchain',{}));selected=a.lean or toolchain.get('executable_path')
  if selected:
   p=Path(selected)
   current=sha(p) if p.is_file() else None
   if current!=toolchain.get('executable_sha256'):toolchain={'executable_path':selected,'executable_sha256':current,'version':None}
  rows=make_plan(order,previous,toolchain,a.reuse,a.max_modules);result={'mode':'PLAN_ONLY_NO_COMPILER_INVOCATION','toolchain_identity_from_receipt':toolchain,'modules':rows,'build':sum(x['action']=='BUILD' for x in rows),'reuse':sum(x['action']=='REUSE' for x in rows),'deferred':sum(x['action']=='DEFER_LIMIT' for x in rows)}
  if a.plan_output:write(a.plan_output,result)
  print(json.dumps(result,indent=2));return 0
 if not a.lean:raise ValueError('--lean required unless --plan')
 state=previous if a.reuse else {'completed':{}}
 try:
  executable=Path(a.lean).resolve(strict=True);version=subprocess.run([str(executable),'--version'],capture_output=True,text=True,check=True).stdout.strip()
  if not pinned_version(version):raise ValueError('exact Lean4.19.0 required')
  prefix=subprocess.run([str(executable),'--print-prefix'],capture_output=True,text=True,check=True).stdout.strip()
 except (OSError,ValueError,subprocess.CalledProcessError) as exc:
  state.update(status='TOOLCHAIN_UNAVAILABLE',error=str(exc));write(statefile,state);print(json.dumps(state));return 2
 toolchain={'executable_path':str(executable),'executable_sha256':sha(executable),'version':version,'prefix':prefix}
 rows=make_plan(order,state,toolchain,a.reuse,a.max_modules);state['toolchain']=toolchain;env=os.environ.copy();env['LEAN_PATH']=str(ROOT)+(os.pathsep+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
 logdir=H/'native_logs';logdir.mkdir(exist_ok=True)
 for row in rows:
  name=row['module']
  if row['action']=='REUSE':continue
  if row['action']=='DEFER_LIMIT':state['status']='LIMIT_REACHED';write(statefile,state);return 0
  source=module_path(name,'.lean');olean=module_path(name,'.olean');start=time.perf_counter();log=logdir/(name.replace('.','_')+'.log');deps=dependency_hashes(source,order,toolchain)
  if any(v is None for v in deps.values()):raise ValueError('missing compiled dependency: '+name)
  with log.open('w',encoding='utf-8') as output:
   process=subprocess.Popen([str(executable),'-o',str(olean),str(source)],cwd=ROOT,env=env,stdout=output,stderr=subprocess.STDOUT)
   state.update(status='RUNNING',current_module=name,pid=process.pid,log=str(log));write(statefile,state);code=process.wait()
  try:
   if code!=0:raise ValueError('compiler returned '+str(code))
   audit=log_audit(log.read_text(encoding='utf-8',errors='replace'),require_final=name==AUDIT)
  except ValueError as exc:state.update(status='BUILD_OR_AUDIT_FAILED',error=str(exc));write(statefile,state);print(json.dumps(state));return 1
  state['completed'][name]={'source_sha256':sha(source),'olean_sha256':sha(olean),'dependency_olean_sha256':deps,'audit':audit,'seconds':time.perf_counter()-start};write(statefile,state)
  print(json.dumps({'module':name,'seconds':state['completed'][name]['seconds'],'status':'LEAN_COMPILED_LOG_AUDITED'}),flush=True)
 final=state.get('completed',{}).get(AUDIT,{}).get('audit',{}).get('final_theorem_audited',False)
 state['status']='ALL_COMPILED_AUDIT_PASSED' if final else 'FINAL_AUDIT_MISSING';state['final_theorem']=THEOREM;write(statefile,state);return 0 if final else 1
if __name__=='__main__':sys.exit(main())
