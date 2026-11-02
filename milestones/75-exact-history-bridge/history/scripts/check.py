"""Check the two small history modules; never rebuild imported libraries."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
MATHLIB=BIN.parent.parent/'mathlib'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
provenance=json.loads((HERE/'data/source-provenance.json').read_text())
for row in provenance['sources']:assert sha(Path(row['path']))==row['sha256']
assert sha(HERE/'lean/ExactHistory.lean')==provenance['source_sha256']
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=str(HERE/'build')
modules=sys.argv[1:] or ['HistoryPrefix','ExactHistory']
records=[]
for module in modules:
    assert module in ['HistoryPrefix','ExactHistory']
    source=HERE/'lean'/(module+'.lean');dest=HERE/'build'/(module+'.olean');log=HERE/'logs'/(module+'.log')
    assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text())
    start=time.monotonic()
    with log.open('w',encoding='utf-8') as out:
        run=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','16384','-R',str(HERE/'lean'),'-o',str(dest.with_suffix('.fresh.olean')),str(source)],cwd=MATHLIB,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=90)
    record=dict(module=module,exit_code=run.returncode,seconds=time.monotonic()-start,source_sha256=sha(source),log_sha256=sha(log))
    if run.returncode:
        (HERE/'logs'/(module+'-failed.json')).write_text(json.dumps(record,indent=2)+'\n');print(log.read_text());raise SystemExit(run.returncode)
    os.replace(dest.with_suffix('.fresh.olean'),dest)
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log.read_text(),re.S)
    # Lean prints axiom-free declarations separately.
    clean=re.findall(r"'([^']+)' does not depend on any axioms",log.read_text())
    assert len(rows)+len(clean)==source.read_text().count('#print axioms')
    audits=[dict(theorem=n,axioms=[]) for n in clean]
    for name,axs in rows:
        axioms=re.findall(r'[A-Za-z][\w.]*',axs);assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
        audits.append(dict(theorem=name,axioms=axioms))
    record.update(olean_sha256=sha(dest),theorems=audits);records.append(record)
    (HERE/'data'/(module+'-audit.json')).write_text(json.dumps(record,indent=2)+'\n')
    print(module,'PASS',round(record['seconds'],3),'seconds;',len(audits),'theorems.',flush=True)
if len(modules)==2:
    imports=[]
    for module in ['Infix','Induction','Nodup']:
        s=MATHLIB/'Mathlib/Data/List'/(module+'.lean');o=MATHLIB/'.lake/build/lib/lean/Mathlib/Data/List'/(module+'.olean')
        imports.append(dict(module='Mathlib.Data.List.'+module,source_sha256=sha(s),olean_sha256=sha(o)))
    audit=dict(status='PASS_EXACT_HISTORY',lean_version=subprocess.check_output([str(BIN/'lean.exe'),'--version'],text=True).strip(),records=records,direct_mathlib_imports=imports,provenance_sha256=sha(HERE/'data/source-provenance.json'),scope='Small list and dictionary proofs. No graph-edge membership, direction-ID coverage, coordinate realization, local credit dispatch, finite potential replay or numerical bound.')
    (HERE/'data/proof-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
