"""Append the proved pair counter to the exact reduced input from round 127."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sys.dont_write_bytecode=True
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding
for name in ['data','work','logs','audit','archives']: (H/name).mkdir(exist_ok=True)
prior=R/'milestones/127-direct-cardinality'
task=read(prior/'data/next-pair-task.json')
for name,digest in task['source_pins'].items():assert sha(R/name)==digest,name
case=read(R/'milestones/125-critical-six-count/data/probes/0120324-total22-positive.json')
enc=TaggedEncoding(case['window'],case['bounds'],radius=9)
corners=read(prior/'data/direct-clauses.json')['corner_lists']
enc.atmost(sorted(-enc.var[v] for cs in corners for v in cs),22,('unproved_sum',))
for cut in case['cycle_cuts']:enc.add([-enc.var[v] for v in cut],('cut',))
def cnf(n,clauses):
 return (f'p cnf {n} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)).encode()
assert cnf(enc.nv,enc.clauses)==(prior/'work/original.cnf').read_bytes()
vertices=corners[1]+corners[3]
assert vertices==task['pair_vertices'] and len(vertices)==42 and len(set(vertices))==37
lits=[enc.var[v] for v in vertices];assert lits==task['selected_literal_occurrences']
old_nv=enc.nv;old_nc=len(enc.clauses);ci=len(enc.ctrs)
enc.atmost(lits,34,('proved_pair_lower',))
pair=enc.clauses[old_nc:];tags=enc.tags[old_nc:]
assert old_nv==7277 and len(pair)==2863 and enc.nv-old_nv==1428
lines=(prior/'work/reduced.cnf').read_text().splitlines()
assert lines[0]=='p cnf 7277 101666'
base=[[int(x) for x in line.split()[:-1]] for line in lines[1:]]
assert len(base)==101666
allclauses=base+pair
dest=H/'work/pair.cnf';assert not dest.exists()
dest.write_bytes(cnf(enc.nv,allclauses))
details=dict(counter_index=ci,literals=lits,upper=34,vertices=vertices,tags=tags,
 clauses=pair,registers={str(v):meaning for v,meaning in enc.meaning.items() if v>old_nv})
detail_path=H/'data/pair-counter.json';assert not detail_path.exists()
detail_path.write_text(json.dumps(details,indent=2)+'\n',encoding='utf-8')
out=dict(status='PREPARED_PAIR_COUNTER_ACTUAL_SEMANTICS_PENDING',pattern='0120324',sum_cap=22,
 pair_positions=[2,4],pair_absent_lower=8,pair_selected_upper=34,pair_occurrences=42,
 pair_distinct_vertices=37,multiplicity_histogram=dict(Counter(Counter(vertices).values())),
 base_clauses=len(base),new_counter_clauses=len(pair),clauses=len(allclauses),
 declared_variables=enc.nv,occurring_variables=len({abs(x) for c in allclauses for x in c}),
 new_variables=1428,first_new_variable=old_nv+1,counter_index=ci,
 source_pins={**task['source_pins'], 'milestones/127-direct-cardinality/data/next-pair-task.json':sha(prior/'data/next-pair-task.json'),
 'milestones/10-window-aggregate/scripts/gen_lean_sat.py':sha(R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py'),
 'milestones/125-critical-six-count/data/probes/0120324-total22-positive.json':sha(R/'milestones/125-critical-six-count/data/probes/0120324-total22-positive.json')},
 script_sha256=sha(Path(__file__)),cnf_sha256=sha(dest),counter_sha256=sha(detail_path),
 scope='The added 2863 clauses require the proved geometric pair bound and counter semantics. They are not asserted to be RUP consequences of the original input. An UNSAT result still requires a complete checked certificate and actual-snake transfer.')
record=H/'data/preparation.json';assert not record.exists()
record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='source_pins'},indent=2))
