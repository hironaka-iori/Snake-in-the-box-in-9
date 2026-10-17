"""Check the largest hint trace in each core in isolation, before full replay."""
import ast,hashlib,json,os,pathlib,subprocess,time,ctypes
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=ROOT/'outputs/window244';CACHE=OUT/'cache';LOG=OUT/'logs'
LEAN=ROOT.parent/'Snake in the Box/work/research_20261015/proof/dependencies/lean-4.19.0-windows/bin/lean.exe'
env=os.environ.copy();env['LEAN_PATH']=str(CACHE)
# Reuse only the monitor definitions, never execute the driver at import time.
tree=ast.parse((ROOT/'work/window244/check_certificates.py').read_text())
names={'MemoryCounters','bounded_run'}
nodes=[n for n in tree.body if isinstance(n,(ast.ClassDef,ast.FunctionDef)) and n.name in names]
exec(compile(ast.Module(body=nodes,type_ignores=[]),'<resource-monitor>','exec'))
memory_info=ctypes.WinDLL('psapi').GetProcessMemoryInfo
memory_info.argtypes=[ctypes.c_void_p,ctypes.POINTER(MemoryCounters),ctypes.c_ulong]
memory_info.restype=ctypes.c_int
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def literals(c):return '['+', '.join(f'({abs(v)}, {str(v>0).lower()})' for v in c)+']'
records={}
for shape in ['repeated','distinct']:
    inp=ROOT/f'milestones/07-window-223/data/window_223_{shape}_compact_core.json'
    data=json.loads(inp.read_text());ident,target,hints=max(data['proof'],key=lambda r:len(r[2]))
    db={i:c for i,c in enumerate(data['clauses'],1)};db.update({i:c for i,c,h in data['proof']})
    name='Probe'+shape.title();src=OUT/(name+'.lean');log=LOG/(name+'.log')
    text='import TreeRup\nopen Snake9.LocalRup\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
    text+='def hints : List (List Lit) := ['+',\n'.join(literals(db[h]) for h in hints)+']\n'
    text+='def target : List Lit := '+literals(target)+'\n'
    text+='theorem checked : Snake9.TreeRup.check hints (Std.TreeSet.ofList target) = true := by decide\n#print axioms checked\n'
    src.write_text(text,encoding='utf-8');start=time.monotonic()
    with log.open('w',encoding='utf-8') as f:
        code,peak,exceeded=bounded_run([str(LEAN),'-j','1','--root='+str(OUT),'-o',str(CACHE/(name+'.olean')),str(src)],f)
    records[shape]=dict(step=ident,hints=len(hints),exit_code=code,peak_private_bytes=peak,memory_exceeded=exceeded,seconds=time.monotonic()-start,core_sha256=sha(inp),source_sha256=sha(src),log_sha256=sha(log),scope='single RUP check only; not full certificate or geometry')
    (OUT/'large-step-probe.json').write_text(json.dumps(records,indent=2)+'\n')
    print(shape,records[shape],flush=True)
    if code:break
