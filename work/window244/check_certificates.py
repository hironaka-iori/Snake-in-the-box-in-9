"""Resumable source compilation; certificate-only success is not geometry."""
import argparse,ctypes,hashlib,json,msvcrt,os,pathlib,re,subprocess,time
from export_certificate import emit
ROOT=pathlib.Path(__file__).resolve().parents[2]
HERE=ROOT/'work/window244';OUT=ROOT/'outputs/window244';CACHE=OUT/'cache';LOG=OUT/'logs'
CACHE.mkdir(exist_ok=True);LOG.mkdir(exist_ok=True)
LEAN=ROOT.parent/'Snake in the Box/work/research_20261015/proof/dependencies/lean-4.19.0-windows/bin/lean.exe'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

class MemoryCounters(ctypes.Structure):
    _fields_=[('cb',ctypes.c_ulong),('PageFaultCount',ctypes.c_ulong)]+[(n,ctypes.c_size_t) for n in ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage','PrivateUsage']]
memory_info=ctypes.WinDLL('psapi').GetProcessMemoryInfo
memory_info.argtypes=[ctypes.c_void_p,ctypes.POINTER(MemoryCounters),ctypes.c_ulong]
memory_info.restype=ctypes.c_int

def bounded_run(command,log):
    # Lean 4.19's Windows -M flag refers to an unregistered max_memory option.
    # Monitor private committed bytes externally; retain observed peak in manifest.
    peak=0;exceeded=False
    with subprocess.Popen(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT) as proc:
        while proc.poll() is None:
            info=MemoryCounters();info.cb=ctypes.sizeof(info)
            if memory_info(int(proc._handle),ctypes.byref(info),info.cb):
                peak=max(peak,info.PrivateUsage,info.PeakPagefileUsage)
                if peak>1800*1024**2:
                    exceeded=True;proc.kill();break
            time.sleep(.2)
        code=proc.wait()
    if exceeded:log.write('\nExternal private-memory budget exceeded (1800 MiB).\n')
    return code,peak,exceeded
def save(p,data):
    tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(p)
parser=argparse.ArgumentParser();parser.add_argument('--shape',choices=['all','repeated','distinct'],default='all');args=parser.parse_args()
def lock(name):
    f=(OUT/name).open('a+b');f.write(b'0');f.flush();f.seek(0);msvcrt.locking(f.fileno(),msvcrt.LK_NBLCK,1);return f
guard=lock('certificate.lock')
if args.shape!='all':
    shape_guard=lock('certificate-'+args.shape+'.lock')
    guard.seek(0);msvcrt.locking(guard.fileno(),msvcrt.LK_UNLCK,1);guard.close()
else:shape_guards=[lock('certificate-'+s+'.lock') for s in ['repeated','distinct']]
manifest=OUT/('certificate-build.json' if args.shape=='all' else 'certificate-'+args.shape+'-build.json')
seed=manifest if manifest.exists() else OUT/'certificate-build.json'
state=json.loads(seed.read_text()) if seed.exists() else dict(modules={})
state.update(status='RUNNING',pid=os.getpid(),scope='Boolean certificates only; geometric bridge still required')
state.pop('error',None)
env=os.environ.copy();env['LEAN_PATH']=str(CACHE)
modules=[ROOT/'work/lean112/LocalRup.lean',ROOT/'work/lean112/TreeRup.lean']
shapes=['repeated','distinct'] if args.shape=='all' else [args.shape]
for shape in shapes:modules += [HERE/'generated'/(n+'.lean') for n in emit(shape)]
state['module_order']=[s.stem for s in modules]
state['modules']={n:r for n,r in state['modules'].items() if n in state['module_order']}
save(manifest,state)
for source in modules:
    name=source.stem;target=CACHE/(name+'.olean');log=LOG/(name+'.log')
    text=source.read_text(encoding='utf-8');assert not re.search(r'\b(sorry|admit|native_decide|bv_decide)\b|^\s*axiom\s',text,re.M),name
    deps={n:sha(CACHE/(n+'.olean')) for n in re.findall(r'^import (\w+)\s*$',text,re.M) if n!='Std'}
    identity=dict(source_sha256=sha(source),imports=deps,lean_sha256=sha(LEAN))
    old=state['modules'].get(name,{})
    if old.get('identity')==identity and old.get('exit_code')==0 and target.exists() and old.get('olean_sha256')==sha(target):continue
    state['active']=name;save(manifest,state);start=time.monotonic()
    with log.open('w',encoding='utf-8') as f:
        code,peak,exceeded=bounded_run([str(LEAN),'-j','1','--root='+str(source.parent),'-o',str(target),str(source)],f)
    r=dict(identity=identity,source=source.relative_to(ROOT).as_posix(),exit_code=code,seconds=time.monotonic()-start,memory_limit_mib=1800,peak_private_bytes=peak,memory_exceeded=exceeded,log_sha256=sha(log))
    if code==0:r['olean_sha256']=sha(target)
    state['modules'][name]=r;save(manifest,state)
    print(name,code,round(r['seconds'],2),flush=True)
    if code:
        state.update(status='FAILED',error=log.read_text()[-3000:]);save(manifest,state);raise SystemExit(code)
for name in ['W223'+s.title() for s in shapes]:
    text=(LOG/(name+'.log')).read_text()
    line=next(x for x in text.splitlines() if f"'{name}.constraints_unsat' depends on axioms:" in x)
    ax=set(filter(None,re.search(r'\[(.*)\]',line)[1].split(', ')))
    assert ax<={'propext','Classical.choice','Quot.sound'},line
state.update(status='PASSED_BOOLEAN_ONLY',active=None);save(manifest,state)
if args.shape!='all':
    reports=[OUT/('certificate-'+s+'-build.json') for s in ['repeated','distinct']]
    if all(p.exists() for p in reports):
        parts=[json.loads(p.read_text()) for p in reports]
        if all(p['status']=='PASSED_BOOLEAN_ONLY' for p in parts):
            merged=dict(status='PASSED_BOOLEAN_ONLY',scope='Both Boolean certificates only; geometry and normalization audits are separate',modules={},module_order=[])
            for part in parts:
                for n,r in part['modules'].items():
                    if n in merged['modules']:assert merged['modules'][n]['olean_sha256']==r['olean_sha256']
                    merged['modules'][n]=r
                merged['module_order']+= [n for n in part['module_order'] if n not in merged['module_order']]
            save(OUT/'certificate-build.json',merged)
