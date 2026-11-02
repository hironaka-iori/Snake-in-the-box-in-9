"""Fresh small Lean check of the manuscript's conditional arithmetic."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
MATHLIB=BIN.parent.parent/'mathlib'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d in ['build','logs','data']:(HERE/d).mkdir(exist_ok=True)
source=HERE/'lean/PaperArithmetic.lean';obj=HERE/'build/PaperArithmetic.olean';log=HERE/'logs/PaperArithmetic.log'
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH']
env.pop('LEAN_PATH',None)
start=time.monotonic()
with log.open('w',encoding='utf-8') as f:
    proc=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(obj),str(source)],cwd=MATHLIB,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=120)
elapsed=time.monotonic()-start
text=log.read_text(encoding='utf-8')
if proc.returncode:print(text);raise SystemExit(proc.returncode)
assert not any(x in text for x in ['error:','sorryAx'])
assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text())
rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
assert len(rows)==6,rows
audits=[]
for name,axs in rows:
    axioms=re.findall(r'[A-Za-z][\w.]*',axs)
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
    audits.append(dict(theorem=name,axioms=axioms))
receipt=dict(status='PASS_PAPER_CONDITIONAL_ARITHMETIC',exit_code=0,seconds=elapsed,
 source_sha256=sha(source),olean_sha256=sha(obj),log_sha256=sha(log),theorem_audits=audits,
 lean_version=subprocess.check_output([str(BIN/'lean.exe'),'--version'],text=True).strip(),
 mathlib_root=str(MATHLIB),mathlib_manifest_sha256=sha(MATHLIB/'lake-manifest.json'),
 scope='Six new conditional arithmetic checks with installed mathlib objects. No local refutation, finite graph replay or complete snake-to-graph theorem is asserted.')
(HERE/'data/arithmetic-audit.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(receipt['status'],elapsed,'seconds;',len(audits),'axiom audits')
