"""Test the complementary fourth-count-at-least-four case with valid premises."""
from pathlib import Path
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sys.dont_write_bytecode=True
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding
for n in ['data','work','logs','audit','lean','archives']:(H/n).mkdir(exist_ok=True)
old=R/'milestones/127-direct-cardinality';paired=R/'milestones/128-coupled-pair'
task=read(paired/'data/next-case-task.json')
for p,d in task['source_pins'].items():assert sha(R/p)==d,p
casefile=R/'milestones/125-critical-six-count/data/probes/0120324-total22-positive.json'
case=read(casefile);corners=read(old/'data/direct-clauses.json')['corner_lists']
enc=TaggedEncoding(case['window'],case['bounds'],radius=9)
enc.atmost(sorted(-enc.var[v] for cs in corners for v in cs),22,('unproved_sum',))
for cut in case['cycle_cuts']:enc.add([-enc.var[v] for v in cut],('cut',))
def cnf(n,cs):return (f'p cnf {n} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()
assert cnf(enc.nv,enc.clauses)==(old/'work/original.cnf').read_bytes()
start=len(enc.clauses)
enc.atmost([enc.var[v] for v in corners[1]+corners[3]],34,('proved_pair_lower',))
reduced=[[int(x) for x in s.split()[:-1]] for s in (old/'work/reduced.cnf').read_text().splitlines()[1:]]
base=reduced+enc.clauses[start:]
assert cnf(enc.nv,base)==(paired/'work/pair.cnf').read_bytes()
assert enc.nv==8705 and len(enc.ctrs)==9 and len(base)==104529
before=len(enc.clauses);first=enc.nv+1;ci=len(enc.ctrs)
literals=[enc.var[v] for v in corners[3]]
enc.atmost(literals,17,('lo',3))
extra=enc.clauses[before:];allclauses=base+extra
detail=dict(counter_index=ci,position=4,absent_lower=4,selected_upper=17,literals=literals,
 clauses=extra,tags=enc.tags[before:],registers={str(v):x for v,x in enc.meaning.items() if v>=first},
 corner_lists=corners,first_new_variable=first,last_new_variable=enc.nv)
dp=H/'data/large-counter.json';target=H/'work/large.cnf'
assert not dp.exists() and not target.exists()
dp.write_text(json.dumps(detail,indent=2)+'\n',encoding='utf-8');target.write_bytes(cnf(enc.nv,allclauses))
split=R/'milestones/129-fourth-count-three/lean/ActualSplit129.lean'
receipt=R/'milestones/129-fourth-count-three/logs/actual-split-1793689366716282000/record.json'
rec=read(receipt);assert rec['status']=='PASS' and rec['exit_code']==0
assert sha(split)==rec['source_sha256']
out=dict(status='PREPARED_COMPLEMENTARY_BRANCH_ACTUAL_BOUNDS_CHECKED',pattern='0120324',total_cap=22,
 branch='fourth_count_at_least_four',necessary_intervals=[[1,21],[2,21],[1,21],[4,21],[1,21],[1,21]],
 pair_sum_lower=8,base_clauses=len(base),new_clauses=len(extra),clauses=len(allclauses),
 declared_variables=enc.nv,occurring_variables=len({abs(x) for c in allclauses for x in c}),
 first_new_variable=first,new_variables=enc.nv-first+1,counter_index=ci,
 source_pins={**task['source_pins'],split.relative_to(R).as_posix():sha(split),
 receipt.relative_to(R).as_posix():sha(receipt),casefile.relative_to(R).as_posix():sha(casefile),
 'milestones/128-coupled-pair/data/verification.json':sha(paired/'data/verification.json'),
 'milestones/128-coupled-pair/work/pair.cnf':sha(paired/'work/pair.cnf'),
 'milestones/127-direct-cardinality/data/direct-clauses.json':sha(old/'data/direct-clauses.json'),
 'milestones/10-window-aggregate/scripts/gen_lean_sat.py':sha(R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py')},
 script_sha256=sha(Path(__file__)),cnf_sha256=sha(target),counter_sha256=sha(dp),
 scope='Complementary branch only. No equality-case first>=3, second>=5 or triple<=11 constraint is used. Actual interpretation of the concrete added counter and any returned native certificate remain separate checks.')
(H/'data/preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='source_pins'},indent=2))
