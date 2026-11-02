"""Check executable bounded retention and its actual-snake specialization."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as stream:
        for b in iter(lambda:stream.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
receipt=HERE/'data/RetainedPredicates-audit.json';support=json.loads(receipt.read_text())
assert support['status']=='PASS_ACTUAL_RETENTION_PREDICATES'
for sub,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
    assert sha(HERE/sub/('RetainedPredicates'+suffix))==support[key]
assert sha(HERE/'data/RetainedPredicates-support.json')==support['combined_support_sha256']
module='NumericRetention';paths=support['paths']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=300)
row=dict(module=module,exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,
    retained_predicates_receipt_sha256=sha(receipt),combined_support_sha256=support['combined_support_sha256'])
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(row,indent=2)+'\n')
if p.returncode:print(log.read_text()[-18000:]);raise SystemExit(p.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==src.read_text().count('#print axioms')
checked=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    checked.append(dict(theorem=name,axioms=values))
row.update(status='PASS_EXECUTABLE_NUMERIC_RETENTION',olean_sha256=sha(obj),theorem_audits=checked,
    scope='Explicit executable bounded predicates for the four exclusion families, history compatibility and ranges, proved true on every fitting actual snake step under the two reference-catalogue premises. Saved-array coverage/equality, edge weights and potential remain separate. Existing hash-matched support reused.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(row,indent=2)+'\n')
print(module,'PASS',round(row['seconds'],3),'seconds;',len(checked),'audits',flush=True)
