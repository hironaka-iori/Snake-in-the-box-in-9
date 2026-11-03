"""Restrict the saved paired input to the fourth-count-three branch."""
from pathlib import Path
from collections import Counter
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sys.dont_write_bytecode=True
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding
for name in ['data','work','logs','audit','archives']:(H/name).mkdir(exist_ok=True)
prior=R/'milestones/128-coupled-pair';task=read(prior/'data/next-case-task.json')
for name,d in task['source_pins'].items():assert sha(R/name)==d,name
old=R/'milestones/127-direct-cardinality'
case=read(R/'milestones/125-critical-six-count/data/probes/0120324-total22-positive.json')
enc=TaggedEncoding(case['window'],case['bounds'],radius=9)
corners=read(old/'data/direct-clauses.json')['corner_lists']
enc.atmost(sorted(-enc.var[v] for cs in corners for v in cs),22,('unproved_sum',))
for cut in case['cycle_cuts']:enc.add([-enc.var[v] for v in cut],('cut',))
def cnf(n,cs):return (f'p cnf {n} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()
assert cnf(enc.nv,enc.clauses)==(old/'work/original.cnf').read_bytes()
start=len(enc.clauses)
enc.atmost([enc.var[v] for v in corners[1]+corners[3]],34,('proved_pair_lower',))
reduced=[[int(x) for x in line.split()[:-1]] for line in (old/'work/reduced.cnf').read_text().splitlines()[1:]]
base=reduced+enc.clauses[start:]
assert cnf(enc.nv,base)==(prior/'work/pair.cnf').read_bytes()
assert enc.nv==8705 and len(enc.ctrs)==9 and len(base)==104529
families=[];new_start=len(enc.clauses);variable_start=enc.nv
for name,literals,k,kind,positions in [
 ('first_lower_three',[enc.var[v] for v in corners[0]],18,('lo',0),[1]),
 ('second_lower_five',[enc.var[v] for v in corners[1]],16,('lo',1),[2]),
 ('fourth_upper_three',[-enc.var[v] for v in corners[3]],3,('hi',3),[4]),
 ('other_three_upper_eleven',sorted(-enc.var[v] for i in [2,4,5] for v in corners[i]),11,('proved_other_three',),[3,5,6])]:
 ci=len(enc.ctrs);nc=len(enc.clauses);nv=enc.nv
 enc.atmost(literals,k,kind)
 vertices=[abs(x)-1 for x in literals]
 families.append(dict(name=name,counter_index=ci,positions=positions,literals=literals,upper=k,
  kind=kind,clauses=enc.clauses[nc:],tags=enc.tags[nc:],first_new_variable=nv+1,last_new_variable=enc.nv,
  occurrences=len(literals),distinct_vertices=len(set(vertices)),multiplicity_histogram=dict(Counter(Counter(vertices).values()))))
extra=enc.clauses[new_start:];allclauses=base+extra
assert len(extra)==3014 and enc.nv-variable_start==1470
assert len(allclauses)==107543 and enc.nv==10175
detail=dict(families=families,corner_lists=corners,registers={str(v):m for v,m in enc.meaning.items() if v>variable_start})
dp=H/'data/branch-counters.json';target=H/'work/three.cnf'
assert not dp.exists() and not target.exists()
dp.write_text(json.dumps(detail,indent=2)+'\n',encoding='utf-8');target.write_bytes(cnf(enc.nv,allclauses))
out=dict(status='PREPARED_FOURTH_THREE_BRANCH_LEAN_SPLIT_PENDING',pattern='0120324',total_cap=22,
 branch='fourth_count_equals_three',necessary_intervals=task['branches'][0]['necessary_intervals'],
 other_positions=[3,5,6],other_sum_upper=11,pair_sum_lower=8,
 base_clauses=len(base),new_clauses=len(extra),clauses=len(allclauses),declared_variables=enc.nv,
 occurring_variables=len({abs(x) for c in allclauses for x in c}),new_variables=1470,first_new_variable=8706,
 counters=[{k:v for k,v in x.items() if k not in ['clauses','tags','literals']} for x in families],
 source_pins={**task['source_pins'],
  'milestones/128-coupled-pair/data/next-case-task.json':sha(prior/'data/next-case-task.json'),
  'milestones/128-coupled-pair/data/verification.json':sha(prior/'data/verification.json'),
  'milestones/127-direct-cardinality/data/direct-clauses.json':sha(old/'data/direct-clauses.json'),
  'milestones/10-window-aggregate/scripts/gen_lean_sat.py':sha(R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py')},
 script_sha256=sha(Path(__file__)),cnf_sha256=sha(target),counter_sha256=sha(dp),
 scope='Restricted equality branch only. Retains all previous input and the total22 and paired constraints. A complete native result needs proof replay and actual-snake transfer. The fourth-count-at-least-four branch remains separate and unresolved.')
p=H/'data/preparation.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['source_pins','counters']},indent=2))
