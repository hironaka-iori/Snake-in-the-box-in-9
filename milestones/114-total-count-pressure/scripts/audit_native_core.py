"""Reconstruct and inspect saved CNF/core/proof evidence without solving.

No proof checker/compiler is invoked. Partial LRAT is inspected for structure
and an empty-clause conclusion, not replayed. --output creates a new file only.
"""
from pathlib import Path
from collections import Counter, defaultdict, deque
from itertools import combinations
import argparse, hashlib, json, re, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
pins = {}
def pin(path):
    path = Path(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    try: key = path.relative_to(ROOT).as_posix()
    except ValueError: key = str(path)
    assert key not in pins or pins[key] == digest
    pins[key] = digest
    return digest
def read(path):
    pin(path)
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))
def formula(path):
    pin(path)
    rows=[]; variables=count=None
    for line in path.read_text().splitlines():
        if line.startswith('p '):
            _,kind,variables,count=line.split(); assert kind=='cnf'
        elif line and not line.startswith('c'):
            row=list(map(int,line.split())); assert row[-1]==0 and 0 not in row[:-1]
            rows.append(row[:-1])
    assert len(rows)==int(count)
    assert all(0<abs(x)<=int(variables) for c in rows for x in c)
    return int(variables),rows
def inspect_lrat(path):
    pin(path)
    additions=deletions=empty=unterminated=0
    last_id=None
    with path.open('rb') as f:
        for raw in f:
            row=raw.split()
            if not row: continue
            last_id=int(row[0])
            if len(row)>1 and row[1]==b'd':
                deletions+=1
            else:
                additions+=1
                if len(row)>1 and row[1]==b'0': empty+=1
            if not raw.endswith(b'\n') or not row or row[-1]!=b'0':
                unterminated+=1
    return dict(bytes=path.stat().st_size,additions=additions,deletions=deletions,
        empty_clause_additions=empty,unterminated_records=unterminated,last_id=last_id,
        proof_replayed=False)

gen=ROOT/'milestones/10-window-aggregate/scripts'
pin(gen/'gen_lean_sat.py'); pin(gen/'wincert.py')
sys.path.insert(0,str(gen))
# Importing these modules constructs no solver or compiler. Only the two
# independent encoding classes and their clause-building methods are used.
from gen_lean_sat import TaggedEncoding
from wincert import Encoding
probe=read(HERE/'data/probes/012310-total18.json')
assert probe['status']=='UNSAT_UNCERTIFIED'
assert probe['directions']==[0,1,2,3,1,0]
assert probe['bounds']==[[0,21]]*5 and probe['positions']==[0,1,2,3,4] and probe['cap']==18
window=[0]
for d in probe['directions']: window.append(window[-1]^(1<<d))
assert window==[0,1,3,7,15,13,12]
bounds=list(map(tuple,probe['bounds']))
tagged=TaggedEncoding(window,bounds,radius=4)
plain=Encoding(window,bounds,radius=4)
assert tagged.clauses==plain.clauses and tagged.nv==plain.nv
base_clauses=len(plain.clauses)
corners=[]
for i in range(1,6):
    used={probe['directions'][i-1],probe['directions'][i]}
    row=[window[i]^(1<<a)^(1<<b) for a,b in combinations(range(9),2) if a not in used and b not in used]
    assert len(row)==len(set(row))==21 and set(row)<=plain.B
    corners.append(row)
vertices=[v for row in corners for v in row]
literals=sorted(-plain.var[v] for v in vertices)
assert len(literals)==105 and len(set(literals))==84
plain.atmost(literals,18,'independent_total_sum')
tagged.atmost(literals,18,('unproved_sum',))
assert plain.clauses==tagged.clauses and plain.nv==tagged.nv
assert len(plain.clauses)==probe['clauses'] and plain.nv==probe['variables']
cuts=[]
assert len(probe['cycle_cuts'])==8
for cut in probe['cycle_cuts']:
    vertices_set=set(cut)
    assert len(vertices_set)==len(cut)>2 and vertices_set<=plain.B
    adj={v:[w for w in vertices_set if (v^w).bit_count()==1] for v in vertices_set}
    assert all(len(ns)==2 for ns in adj.values())
    reached={cut[0]}; todo=[cut[0]]
    while todo:
        for w in adj[todo.pop()]:
            if w not in reached: reached.add(w); todo.append(w)
    assert reached==vertices_set
    plain.add_cycle_cut(cut)
    cuts.append(dict(vertices=cut,length=len(cut),connected=True,induced_degree=2))
full=HERE/'work/012310-total18/full.cnf'
nv,clauses=formula(full)
assert (nv,clauses)==(plain.nv,plain.clauses)
rebuilt=(f'p cnf {nv} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in plain.clauses)).encode()
assert rebuilt==full.read_bytes()

first=read(HERE/'data/012310-total18-solver.json')
native=read(HERE/'data/012310-total18-cadical153.json')
conversion=read(HERE/'data/drat-conversion-bootstrap.json')
assert first['status']=='TIMEOUT' and native['status']=='UNSAT_DRAT_UNCHECKED'
assert conversion['status']=='TIMEOUT_OR_FAILED'
assert all(d['cnf_sha256']==pin(full) for d in [first,native,conversion])
for path,digest in native['source_files_sha256'].items(): assert pin(path)==digest
assert pin(Path(conversion['source']))==conversion['source_sha256']
assert pin(HERE/'build-native/drat-trim.exe')==conversion['checker_sha256']
for control in conversion['controls']:
    folder=HERE/'work/drat-conversion-bootstrap'
    name=control['name']
    assert pin(folder/(name+'.log'))==control['log_sha256']
    _,cs=formula(folder/(name+'.cnf'))
    pin(folder/(name+'.drat'))
    satisfiable=any(all(any(bool(mask&(1<<(abs(lit)-1)))==(lit>0) for lit in clause) for clause in cs) for mask in range(4))
    assert satisfiable==(name=='invalid')
    assert control['verified']==control['expected']==(name=='valid')
    if name=='truncated': assert (folder/(name+'.drat')).stat().st_size==0
for artifact in conversion['artifacts']:
    path=HERE/artifact['path']
    assert pin(path)==artifact['sha256'] and path.stat().st_size==artifact['bytes']
drat=HERE/native['proof']
assert pin(drat)==native['proof_sha256'] and drat.stat().st_size==native['proof_bytes']
drat_lines=drat_empty=0; last=None
with drat.open() as f:
    for line in f:
        drat_lines+=1; last=line.strip()
        if last=='0': drat_empty+=1
assert drat_lines==native['proof_lines'] and last=='0' and drat_empty>=1

_,extracted=formula(HERE/'work/drat-conversion-bootstrap/core.cnf')
record=read(HERE/'data/extracted-core-solver.json')
available=defaultdict(deque)
for i,c in enumerate(clauses,1): available[tuple(sorted(c))].append(i)
ids=[]
for c in extracted:
    assert available[tuple(sorted(c))]
    ids.append(available[tuple(sorted(c))].popleft())
assert len(ids)==len(set(ids))==5431 and ids==record['input_ids']
assert record['variables']==nv and record['clauses']==len(ids)
assert record['full_cnf_sha256']==pin(full)
core=HERE/'work/extracted-core/core.cnf'
assert formula(core)==(nv,[clauses[i-1] for i in ids])
assert record['core_cnf_sha256']==pin(core)
reordered=sum(c!=clauses[i-1] for c,i in zip(extracted,ids))
assert reordered>0
assert pin(HERE/'scripts/certify_core_permuted.py')==record['script_sha256']
pin(HERE/'scripts/certify_extracted_core.py')
partial=[]
for name,path,expected in [
    ('full_direct',Path(first['command'][-1]),first),
    ('conversion',HERE/'work/drat-conversion-bootstrap/full.lrat',None),
    ('extracted_core',HERE/'work/extracted-core/core.raw.lrat',record)]:
    if expected and expected['status']=='RUNNING':
        partial.append(dict(name=name,status='RUNNING_NOT_INSPECTED')); continue
    if expected:
        assert pin(path)==expected['raw_sha256'] and path.stat().st_size==expected['raw_bytes']
    info=inspect_lrat(path)
    assert info['empty_clause_additions']==0
    partial.append(dict(name=name,status='PARTIAL_NO_EMPTY_CLAUSE',**info))

theorems=[]
for name,objdir,status in [('Comparison114','build','PASS_COMPARISON_ARITHMETIC'),
                           ('TotalGeometry114','build-total-geometry','PASS_TOTAL_GEOMETRY')]:
    r=read(HERE/'data'/(name+'-audit.json'))
    assert r['status']==status and r['exit_code']==0 and not r['timeout']
    for path,digest in [(HERE/'lean'/(name+'.lean'),r['source_sha256']),
                        (HERE/objdir/(name+'.olean'),r['olean_sha256']),
                        (HERE/r['log'],r['log_sha256']),
                        (HERE/r['source_snapshot'],r['source_sha256'])]:
        assert pin(path)==digest
    assert all(set(row['axioms'])<={'propext','Classical.choice','Quot.sound'} for row in r['theorem_audits'])
    source=(HERE/'lean'/(name+'.lean')).read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide)\b',source)
    if name=='TotalGeometry114': assert '(hlocal : ∀ S E : Nat → Bool,' in source and 'apply hlocal _ _ ax' in source
    theorems.append(dict(module=name,seconds=r['seconds'],audits=r['theorem_audits'],explicit_local_premise=name=='TotalGeometry114'))

out=dict(status='PASS_CNF_CORE_IDENTITY_AND_BOUNDED_SCOPE_REVIEW',window=window,variables=nv,clauses=len(clauses),
    clauses_before_sum=base_clauses,sum_counter_clause_count=probe['clauses']-base_clauses,
    literal_occurrences=len(literals),distinct_literals=len(set(literals)),multiplicity_histogram=dict(Counter(Counter(literals).values())),
    corners_by_centre=corners,cycle_cuts=cuts,core_clause_count=len(ids),core_input_ids=ids,
    reordered_extracted_clauses=reordered,original_order_restored=True,
    direct_status=first['status'],drat_status=native['status'],drat_lines=drat_lines,drat_empty_clauses=drat_empty,drat_checked=False,
    conversion_status=conversion['status'],extracted_core_status=record['status'],partial_lrat=partial,theorem_receipts=theorems,
    source_pins=pins,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    scope='Exact CNF reconstruction and core identity, connected induced cycle validation, proof structure only, and existing theorem scope/receipt checks. No native proof replay, solver or compiler. No complete checked contradiction or new snake bound.')
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);args=parser.parse_args()
text=json.dumps(out,indent=2)+'\n'
if args.output:
    with args.output.open('x',encoding='utf-8') as f:f.write(text)
    print(json.dumps(dict(status=out['status'],clauses=len(clauses),core=len(ids),reordered=reordered,
        partial_lrat=partial,output=str(args.output),sha256=hashlib.sha256(args.output.read_bytes()).hexdigest()),indent=2))
else:print(text,end='')
