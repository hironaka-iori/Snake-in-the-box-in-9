"""Measure the strengthened proof before spending time on replay or Lean export."""
from pathlib import Path
import hashlib,importlib.util,json,shutil,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
solver=json.loads((HERE/'data/pooled-cuts-solver.json').read_text())
assert solver['status']=='UNSAT_LRAT_UNCHECKED'
raw=Path(solver['scratch'])/'full.raw.lrat'
assert sha(raw)==solver['raw_sha256']==sha(HERE/solver['raw'])
generator=ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
sp=importlib.util.spec_from_file_location('trim114pool',generator);g=importlib.util.module_from_spec(sp);sp.loader.exec_module(g)
trim=raw.with_name('full.trim.lrat');assert not trim.exists();start=time.monotonic()
nl,nh,ids=g.trim_lrat(str(raw),str(trim),solver['clauses'])
target=(HERE/solver['raw']).with_name('full.trim.lrat');assert not target.exists();shutil.copyfile(trim,target)
assert sha(trim)==sha(target)
baseline=json.loads((HERE/'data/012310-total18-certificate.json').read_text())
out=dict(status='TRIMMED_POOLED_PROOF_NOT_REPLAYED',lemmas=nl,hints=nh,core_ids=ids,core_clauses=len(ids),
    baseline_lemmas=baseline['lemmas'],baseline_hints=baseline['hints'],fewer_hints=nh<baseline['hints'],
    seconds=time.monotonic()-start,trim=target.relative_to(HERE).as_posix(),trim_sha256=sha(target),
    solver_record_sha256=sha(HERE/'data/pooled-cuts-solver.json'),generator_sha256=sha(generator),script_sha256=sha(Path(__file__)),
    scope='Dependency trimming only. This alternative strengthened certificate has not been independently replayed or checked in Lean.')
record=HERE/'data/pooled-trim.json';assert not record.exists();record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('POOLED_TRIM',len(ids),nl,nh,'fewer_hints',out['fewer_hints'],round(out['seconds'],3),flush=True)
