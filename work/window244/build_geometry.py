"""Resumable kernel checks of concrete descriptor tables and clause instances."""
import argparse,ast,ctypes,hashlib,json,os,pathlib,re,subprocess,sys,time,msvcrt
from generate_bridge import emit
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=ROOT/'outputs/window244';CACHE=OUT/'cache';LOG=OUT/'logs'
LEAN=ROOT.parent/'Snake in the Box/work/research_20261015/proof/dependencies/lean-4.19.0-windows/bin/lean.exe'
LAKE=LEAN.with_name('lake.exe')
MATHLIB=LEAN.parents[2]/'mathlib4'
FOUNDATION=ROOT.parent/'Snake in the Box/work/spectral/.verification/strengthened-n0xmejea'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
tree=ast.parse((ROOT/'work/window244/check_certificates.py').read_text())
nodes=[n for n in tree.body if isinstance(n,(ast.ClassDef,ast.FunctionDef)) and n.name in {'MemoryCounters','bounded_run'}]
exec(compile(ast.Module(body=nodes,type_ignores=[]),'<resource-monitor>','exec'))
memory_info=ctypes.WinDLL('psapi').GetProcessMemoryInfo
memory_info.argtypes=[ctypes.c_void_p,ctypes.POINTER(MemoryCounters),ctypes.c_ulong]
memory_info.restype=ctypes.c_int
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[CACHE,FOUNDATION,FOUNDATION/'core/.lake/build/lib/lean']))
env['LEAN_PATH']=subprocess.check_output([str(LAKE),'-d',str(MATHLIB),'env',sys.executable,'-c',"import os;print(os.environ['LEAN_PATH'])"],env=env,text=True).strip()
parser=argparse.ArgumentParser();parser.add_argument('--shape',choices=['repeated','distinct'],default='repeated');args=parser.parse_args()
guard=(OUT/(args.shape+'-geometry.lock')).open('a+b');guard.write(b'0');guard.flush();guard.seek(0);msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
manifest=OUT/(args.shape+'-geometry-build.json')
state=json.loads(manifest.read_text()) if manifest.exists() else dict(modules={})
state.update(status='RUNNING',pid=os.getpid(),scope='standardized geometry only; no Boolean refutation or arbitrary normalization')
def save():
    tmp=manifest.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2)+'\n');tmp.replace(manifest)
prefix='W223'+args.shape.title();folder=ROOT/'work/window244/generated'
modules=emit(args.shape)
# The distinct proof's structural input types may be needed before its RUP run.
if not (CACHE/(prefix+'Constraints.olean')).exists():
    modules=[p.stem for p in sorted(folder.glob(prefix+'Types*.lean'))]+[prefix+'Constraints']+modules
for name in modules:
    src=folder/(name+'.lean');obj=CACHE/(name+'.olean');log=LOG/(name+'.log')
    text=src.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide|bv_decide)\b|^\s*axiom\s',text,re.M)
    imports={n:sha(CACHE/(n+'.olean')) for n in re.findall(r'^import (\w+)\s*$',text,re.M)}
    identity=dict(source_sha256=sha(src),imports=imports,lean_sha256=sha(LEAN))
    prior=state['modules'].get(name,{})
    if prior.get('identity')==identity and prior.get('exit_code')==0 and obj.exists() and prior.get('olean_sha256')==sha(obj):continue
    state['active']=name;save();start=time.monotonic()
    with log.open('w',encoding='utf-8') as f:
        code,peak,exceeded=bounded_run([str(LEAN),'-j','1','--root='+str(folder),'-o',str(obj),str(src)],f)
    output=log.read_text(encoding='utf-8')
    audits={n:[a.strip() for a in raw.split(',') if a.strip()] for n,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output)}
    result=dict(identity=identity,exit_code=code,seconds=time.monotonic()-start,peak_private_bytes=peak,memory_exceeded=exceeded,log_sha256=sha(log),axioms=audits)
    if not code:result['olean_sha256']=sha(obj)
    state['modules'][name]=result;save();print(name,code,round(result['seconds'],2),flush=True)
    if code or any(set(a)-{'propext','Classical.choice','Quot.sound'} for a in audits.values()):
        state.update(status='FAILED',error=output[-4000:]);save();raise SystemExit(1)
state.update(status='PASSED_STANDARDIZED_GEOMETRY_ONLY',active=None);save()
