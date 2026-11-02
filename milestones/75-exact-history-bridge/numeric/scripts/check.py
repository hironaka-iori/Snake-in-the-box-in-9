"""Check the numeric state coding using the pinned Lean/mathlib runtime."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
for folder in ['build','data','logs']:(HERE/folder).mkdir(parents=True,exist_ok=True)
source=HERE/'lean/CountStateCode.lean';dest=HERE/'build/CountStateCode.olean';log=HERE/'logs/CountStateCode.log'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH']
t=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    run=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(dest.with_suffix('.fresh.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=120)
record=dict(exit_code=run.returncode,seconds=time.monotonic()-t,source_sha256=sha(source))
(HERE/'logs/build-record.json').write_text(json.dumps(record,indent=2)+'\n')
if run.returncode:print(log.read_text());raise SystemExit(run.returncode)
os.replace(dest.with_suffix('.fresh.olean'),dest)
text=log.read_text();assert 'sorryAx' not in text and 'error:' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text())
rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
rows += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(rows)==9
checks=[]
for name,values in rows:
    axioms=re.findall(r'[A-Za-z][\w.]*',values);assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
    checks.append(dict(theorem=name,axioms=axioms))
record.update(status='PASS_NUMERIC_STATE_CODE',olean_sha256=sha(dest),log_sha256=sha(log),theorem_audits=checks,
    scope='Exact base-six prefix/suffix/entering-count identities, state index bounds and unsaturated guards. Actual-snake membership, compatible history shape, exclusion coverage and potential replay remain separate. Existing pinned mathlib objects were reused.')
(HERE/'data/proof-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],record['seconds'],'seconds;',len(checks),'axiom audits')
