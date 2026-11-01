"""Reconstruct each verified native formula and pin all proof/checker evidence."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
import gen_lean_sat as gen
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();read=lambda p:json.loads(p.read_text())
rows=[]
def canon(ds):
 d={};return [d.setdefault(x,len(d)) for x in ds]
shapes=read(HERE/'data/all-six-direction-shapes.json')['up_to_reversal']
for f in sorted((HERE/'data').glob('*-certificate.json')):
 meta=read(f)
 if meta['status']!='NATIVE_DRAT_VERIFIED' or 'shape_index' not in meta:continue
 assert min(canon(meta['directions']),canon(meta['directions'][::-1]))==shapes[meta['shape_index']]
 tag=f.name.removesuffix('-certificate.json');prefix=HERE/'build'/tag
 e=TaggedShare(meta['directions'],meta['bounds'],meta['cap'])
 cuts=meta.get('cycle_cuts',[])
 for c in cuts:
  assert gen.is_cycle_set(c);e.add([-e.var[v] for v in c],('old',('cut',)))
 cnf=prefix.with_suffix('.cnf');core=prefix.with_suffix('.core.cnf');drat=prefix.with_suffix('.drat')
 assert sha(cnf)==meta['cnf_sha256'] and sha(core)==meta['core_sha256'] and sha(drat)==meta['drat_sha256']
 parse=lambda p:[list(map(int,l.split()[:-1])) for l in p.read_text().splitlines() if l and l[0] not in 'pc']
 assert e.clauses==parse(cnf)
 lookup={tuple(sorted(c)):t for c,t in zip(e.clauses,e.tags)}
 core_clauses=parse(core);tags=[lookup[tuple(sorted(c))] for c in core_clauses]
 active=len({abs(x) for c in core_clauses for x in c})
 assert sum(t[0]=='shareCap' for t in tags)==1
 log=HERE/f'logs/{tag}-verify.log';assert 's VERIFIED' in log.read_text()
 rows.append(dict(certificate=f.name,shape_index=meta['shape_index'],directions=meta['directions'],share_lower=meta['cap']+1,cycle_cuts=len(cuts),used_cycle_cuts=sum(t[0]=='old' and t[1][0]=='cut' for t in tags),core_clauses=len(tags),active_core_variables=active,minimum_literal_offset=1<<active.bit_length(),cnf_sha256=sha(cnf),core_sha256=sha(core),drat_sha256=sha(drat),verifier_log_sha256=sha(log)))
covered=sorted({r['shape_index'] for r in rows if r['share_lower']>=16})
out=dict(status='PASS_NATIVE_FORMULA_AUDIT',certificates=rows,share16_covered_shapes=covered,share16_pending_shapes=sorted(set(range(9))-set(covered)),encoder_sources={str(Path(x).relative_to(ROOT)):sha(Path(x)) for x in [sys.modules['tagged_share'].__file__,sys.modules['gen_lean_sat'].__file__]},drat_checker_sha256=sha(ROOT/'work/share-wheels/drat-trim.exe'),scope='Reconstructed Boolean formulas and independent DRAT evidence. Geometric meanings, reversal/coordinate normalization and Lean replay remain required. No new unconditional bound.')
(HERE/'data/native-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],'certificates',len(rows),'share16 covered',covered,'pending',out['share16_pending_shapes'])
