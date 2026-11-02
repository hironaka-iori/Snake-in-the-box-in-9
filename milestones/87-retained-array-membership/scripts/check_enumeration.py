"""Check exact enumeration/index lemmas; concrete array equality stays explicit."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time,sys
HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f in ['data','build','logs']:(HERE/f).mkdir(exist_ok=True)
module='RetainedEnumeration'
src=HERE/'lean'/(module+'.lean');obj=HERE/'build'/(module+'.olean');log=HERE/'logs'/(module+'.log')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env.pop('LEAN_PATH',None)
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    run=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],
        cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=180)
if run.returncode:print(log.read_text());raise SystemExit(run.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==src.read_text().count('#print axioms')==11
rows=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    rows.append(dict(theorem=name,axioms=values))
result=dict(status='PASS_RETAINED_ENUMERATION',module=module,exit_code=0,seconds=time.monotonic()-start,
    source_sha256=sha(src),object_sha256=sha(obj),log_sha256=sha(log),theorem_audits=rows,
    mathlib_manifest_sha256=sha(BIN.parent.parent/'mathlib/lake-manifest.json'),lean_binary_sha256=sha(BIN/'lean.exe'),
    scope='Exact enumeration and full-key index lemmas. Concrete keep acceptance, saved array equality, and any catalogue refutation premises are separate; existing mathlib reused.')
receipt='enumeration-audit.json'
(HERE/'data'/receipt).write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],len(rows),'audits',round(result['seconds'],3),'seconds')
