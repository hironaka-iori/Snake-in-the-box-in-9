"""One bounded Lean check with hash-matched milestone75 support."""
from pathlib import Path
import ctypes,hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
SUPPORT=ROOT/'milestones/75-exact-history-bridge/history'
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
MATHLIB=BIN.parent.parent/'mathlib'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for folder in ['build','data','logs']:(HERE/folder).mkdir(exist_ok=True)
receipt=SUPPORT/'data/proof-audit.json';audit=json.loads(receipt.read_text())
assert audit['status']=='PASS_EXACT_HISTORY'
support=[]
for rec in audit['records']:
    module=rec['module'];src=SUPPORT/'lean'/(module+'.lean');obj=SUPPORT/'build'/(module+'.olean')
    assert sha(src)==rec['source_sha256'] and sha(obj)==rec['olean_sha256']
    support.append(dict(module=module,source=str(src),source_sha256=sha(src),olean=str(obj),olean_sha256=sha(obj)))
class Memory(ctypes.Structure):
    _fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong)]+[(x,ctypes.c_ulonglong) for x in ['total_phys','avail_phys','total_page','avail_page','total_virtual','avail_virtual','avail_extended']]
mem=Memory();mem.length=ctypes.sizeof(mem);assert ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(mem))
# Keep physical-memory headroom. The host rejected the -M1024 option before
# source compilation, so no compiler memory cap is asserted for this run.
assert mem.avail_phys>=1536*1024**2, 'Less than 1536 MiB available; defer this bounded check.'
module='NumericHistory';src=HERE/'lean'/(module+'.lean');obj=HERE/'build'/(module+'.olean');log=HERE/'logs'/(module+'.log')
source=src.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b',source)
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=str(HERE/'build')+';'+str(SUPPORT/'build')
command=[str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)]
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    result=subprocess.run(command,cwd=MATHLIB,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=90)
record=dict(exit_code=result.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),memory_limit_mib=None,available_bytes_before=mem.avail_phys,command=command,support_receipt_sha256=sha(receipt),support=support)
if result.returncode:
    (HERE/'data/failed-check.json').write_text(json.dumps(record,indent=2)+'\n');print(log.read_text());raise SystemExit(result.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log.read_text(),re.S)
clean=re.findall(r"'([^']+)' does not depend on any axioms",log.read_text())
assert len(rows)+len(clean)==source.count('#print axioms')
theorems=[dict(theorem=n,axioms=[]) for n in clean]
for n,axs in rows:
    names=re.findall(r'[A-Za-z][\w.]*',axs);assert set(names)<={'propext','Classical.choice','Quot.sound'}
    theorems.append(dict(theorem=n,axioms=names))
record.update(status='PASS_NUMERIC_HISTORY_AND_SIGNATURE_EQUIVALENCE',olean_sha256=sha(obj),theorems=theorems,lean_version=subprocess.check_output([str(BIN/'lean.exe'),'--version'],text=True).strip(),script_sha256=sha(Path(__file__)),limits='Uses hash-matched existing75 objects and installed mathlib; does not rebuild their complete dependency closure. No direction-table interpretation, finite graph, credit dispatch or global bound.')
(HERE/'data/proof-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],round(record['seconds'],3),'seconds;',len(theorems),'theorem audits.')
