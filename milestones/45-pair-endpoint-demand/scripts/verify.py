"""Independent clause provenance, geometry, build, and axiom audit."""
from pathlib import Path
import gzip,hashlib,itertools,json,re,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads((HERE/p).read_text())
def raw(name):
    p=HERE/'certificates'/name
    return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def cnf(name):return [list(map(int,l.split()))[:-1] for l in raw(name).decode().splitlines() if l and not l.startswith(('c','p'))]
meta=read('data/endpoint451.json');ds=meta['dirs'];W=window(ds)
e=TaggedEncoding(W,[(0,21)]*7,radius=4)
lits=[-e.var[W[j]^(1<<a)^(1<<b)] for j in [2,6] for a,b in itertools.combinations(range(9),2) if a not in (ds[j-1],ds[j]) and b not in (ds[j-1],ds[j])]
e.atmost(lits,7,('ends',))
endvars={v:k for k,(kind,v,*_) in e.meaning.items() if kind=='e'}
for v in range(512):
    if (v^W[2]).bit_count()<=2:e.add([-endvars[v]],('avoid',v))
assert e.clauses==cnf('endpoint451.full.cnf')
rename={int(k):v for k,v in meta['original_to_new'].items()}
core=[[(-1 if v<0 else 1)*rename[abs(v)] for v in e.clauses[j-1]] for j in meta['source_original_clause_ids']]
assert core==cnf('endpoint451.cnf') and len(core)==1065
assert meta['ordinary_clauses']==1046 and meta['cycle_cuts']==[]
assert all((v^W[2]).bit_count()==2 for v in meta['endpoint_vertices'])
assert core[1046:]==[[-rename[endvars[v]]] for v in meta['endpoint_vertices']]
free=set(range(9))-{1,2}
expected={3^(1<<a)^(1<<b) for a,b in itertools.combinations(sorted(free),2) if (a,b) not in [(0,4),(3,4)]}
assert set(meta['endpoint_vertices'])==expected and len(expected)==19
assert 's VERIFIED' in (HERE/'logs/endpoint451-drat-check.txt').read_text()
assert read('logs/endpoint451-export.txt')['hints']==23414
audits=[]
for name,number in [('EndpointUnits',1),('LocalWindowSat-EndpointPair451',1),('EndpointPair',5),('EndpointDistance',4),('WitnessEndpointSharp',5)]:
    log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
    assert not any(x in log for x in ['sorryAx','error:','Lean.ofReduceBool'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    assert len(rows)==number,(name,rows)
    for theorem,axioms in rows:
        assert set(x.strip() for x in axioms.split(',')) <= {'propext','Classical.choice','Quot.sound'}
        audits.append(theorem)
build=Path((HERE/'build/latest.txt').read_text().strip());sources={}
for p in (HERE/'lean').rglob('*.lean'):
    relative=p.relative_to(HERE/'lean');o=build/relative.with_suffix('.olean')
    assert o.exists() and o.stat().st_mtime>=p.stat().st_mtime,relative
    sources[relative.as_posix()]=sha(p.read_bytes())
records=read('logs/build-record.json')['records']+[read('logs/witness-build-record.json')]
for r in records:assert r['exit_code']==0 and sources[r['module']+'.lean']==r['source_sha256']
checks=[]
for p in sorted((HERE/'data').glob('*.json')):
    r=json.loads(p.read_text())
    if not isinstance(r,dict) or r.get('status')!='SAT' or 'selected' not in r:continue
    S=set(r['selected']);degree={v:sum((v^(1<<i)) in S for i in range(9)) for v in S}
    assert all(d<=2 for d in degree.values())
    e2=TaggedEncoding(W,[(0,21)]*7,radius=r['ball_radius'])
    interior={v for v in S if all(v^(1<<i) in e2.ball for i in range(9))}
    assert all(degree[v]>=1 for v in interior)
    ends={v for v in interior if degree[v]==1};assert len(ends)<=2 and not ends.intersection(r['avoid_vertices'])
    # Every component must be a path, including a possible isolated boundary vertex.
    unseen=set(S)
    while unseen:
        stack=[unseen.pop()];component=[]
        while stack:
            v=stack.pop();component.append(v)
            for i in range(9):
                u=v^(1<<i)
                if u in unseen:unseen.remove(u);stack.append(u)
        assert sum(degree[v] for v in component)==2*(len(component)-1)
    alpha=[]
    for c in W[1:-1]:
        alpha.append(sum(all(v not in S for v in [c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b)]) for a,b in itertools.combinations(range(9),2)))
    assert alpha==r['census']['alpha'] and alpha[1]+alpha[5]<=r['joint_cap']
    vs=r['vertex_sequence']
    if vs:
        assert set(vs)==S and len(vs)==len(S)
        assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(len(vs)) for j in range(i+1,len(vs)))
    checks.append(dict(file=p.name,sha256=sha(p.read_bytes()),complete_path_edges=len(vs)-1 if vs else None))
for r in read('data/archives.json'):
    assert sha(raw(r['file']))==r['sha256']
    assert sha((HERE/'certificates'/(r['file']+'.gz')).read_bytes())==r['archive_sha256']
out=dict(status='PASS',lean_audits=len(audits),audited_theorems=audits,proof_clauses=1065,ordinary_clauses=1046,endpoint_units=19,proof_hints=23414,
    sources_sha256=sources,geometry_checks=checks,sharp_witness_edges=148,pair_counts=[5,3],endpoint_distances=[4,4],
    scope='Endpoint distance-two implication and sharp endpoint-free bound eight checked in Lean; no improved global snake bound.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['audited_theorems','sources_sha256','geometry_checks']},indent=2))
