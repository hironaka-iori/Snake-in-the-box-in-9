"""Check the rational obstruction arithmetic in Lean 4.19.0."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time,uuid
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=HERE/'lean/ConditionalTarget.lean';obj=HERE/'build/ConditionalTarget.olean';log=HERE/'logs/ConditionalTarget.log'
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env.pop('LEAN_PATH',None)
start=time.monotonic()
fresh=HERE/'build'/('ConditionalTarget-'+uuid.uuid4().hex+'.olean')
with log.open('w',encoding='utf-8') as out:
    run=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(fresh),str(src)],
        cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=180)
if run.returncode:print(log.read_text());raise SystemExit(run.returncode)
os.replace(fresh,obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==3
rows=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    rows.append(dict(theorem=name,axioms=values))
result=dict(status='PASS_SINGLE_TARGET_CONDITIONAL_ARITHMETIC',exit_code=0,seconds=time.monotonic()-start,
    source_sha256=sha(src),object_sha256=sha(obj),log_sha256=sha(log),theorem_audits=rows,
    comparison_audit_sha256=sha(HERE/'data/comparison-audit.json'),
    mathlib_manifest_sha256=sha(BIN.parent.parent/'mathlib/lake-manifest.json'),
    lean_binary_sha256=sha(BIN/'lean.exe'),
    scope='Conditional budget arithmetic only. Single local target and full graph interpretation remain premises; existing mathlib reused.')
(HERE/'data/lean-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],'3 audits',round(result['seconds'],3),'seconds')
