"""Audit saved six-sum probe formulas and cuts without SAT or Lean execution.
Default prints summary; --output creates a fresh JSON file exclusively.
"""
from pathlib import Path
from collections import Counter
from itertools import combinations
import argparse, hashlib, json, sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages')]
from gen_lean_sat import TaggedEncoding
from wincert import Encoding
pins={}
def sha(p):
    p=Path(p);d=hashlib.sha256(p.read_bytes()).hexdigest();pins[p.resolve().relative_to(R).as_posix()]=d;return d
def read(p):
    sha(p);return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def verify(p,d):assert sha(p)==d,str(p)
def cnf_digest(n,cs):
    raw=(f'p cnf {n} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs)).encode()
    return hashlib.sha256(raw).hexdigest()
def counter(lits,k,nv):
    # Independent transcription of the sequential counter, retaining repetitions.
    s=[]
    for _ in lits:
        s.append(list(range(nv+1,nv+k+1)));nv+=k
    cs=[[-lits[0],s[0][0]]]+[[-s[0][j]] for j in range(1,k)]
    for i in range(1,len(lits)):
        cs += [[-lits[i],s[i][0]],[-s[i-1][0],s[i][0]]]
        for j in range(1,k):
            cs += [[-lits[i],-s[i-1][j-1],s[i][j]],[-s[i-1][j],s[i][j]]]
        cs.append([-lits[i],-s[i-1][k-1]])
    return nv,cs
def inspect_cut(cut):
    assert cut and len(cut)==len(set(cut)) and all(isinstance(v,int) and 0<=v<512 for v in cut)
    S=set(cut);degrees=[sum((v^(1<<j)) in S for j in range(9)) for v in cut]
    assert min(degrees)>=2
    unseen=set(S);components=[]
    while unseen:
        todo=[next(iter(unseen))];component=[]
        while todo:
            v=todo.pop()
            if v not in unseen:continue
            unseen.remove(v);component.append(v)
            todo += [v^(1<<j) for j in range(9) if (v^(1<<j)) in unseen]
        components.append(len(component))
    return dict(vertices=len(cut),min_internal_degree=min(degrees),max_internal_degree=max(degrees),components=components,
        vertices_sha256=hashlib.sha256(json.dumps(cut,separators=(',',':')).encode()).hexdigest())
rows=[];allcuts=[]
for stem,script in [('0123042-total24-full','probe_six_sum.py'),('0123042-total25-full','probe_six_sum.py'),('0123042-total25-resume','probe_six_sum_resume.py')]:
    path=H/'data/probes'/(stem+'.json');p=read(path)
    verify(H/'scripts'/script,p['script_sha256'])
    for rel,d in p['source_files_sha256'].items():verify(R/rel,d)
    case_paths=[R/rel for rel in p['source_files_sha256'] if rel.startswith(H.relative_to(R).as_posix()+'/data/')]
    assert len(case_paths)==1
    case=next(c for c in read(case_paths[0]) if c['name']==stem)
    assert all(p[k]==v for k,v in case.items())
    assert p['directions']==[0,1,2,3,0,4,2] and p['bounds']==[[0,21]]*6
    assert p['positions']==list(range(6)) and p['radius']==9 and p['cap'] in [24,25]
    word=[0]
    for d in p['directions']:word.append(word[-1]^(1<<d))
    assert word==[0,1,3,7,15,14,30,26]
    tagged=TaggedEncoding(word,[(0,21)]*6,radius=9)
    plain=Encoding(word,[(0,21)]*6,radius=9)
    assert tagged.ball==plain.ball==list(range(512)) and tagged.ends==plain.ends==2
    assert tagged.nv==plain.nv and tagged.clauses==plain.clauses
    base_clauses=len(tagged.clauses);base_variables=tagged.nv
    assert all(tagged.meaning[tagged.var[v]]==('p',v) for v in range(512))
    corner_rows=[]
    for i in range(1,7):
        a=(word[i]^word[i-1]).bit_length()-1;b=(word[i]^word[i+1]).bit_length()-1
        assert a!=b
        corners=[word[i]^(1<<x)^(1<<y) for x,y in combinations(range(9),2) if x not in [a,b] and y not in [a,b]]
        assert len(corners)==len(set(corners))==21
        corner_rows.append(corners)
    occurrences=[v for cs in corner_rows for v in cs]
    counts=Counter(occurrences)
    lits=sorted(-tagged.var[v] for v in occurrences)
    assert len(lits)==p['literal_occurrences']==126 and len(set(lits))==p['distinct_literals']==106
    before=list(tagged.clauses)
    manual_nv,manual_counter=counter(lits,p['cap'],tagged.nv)
    tagged.atmost(lits,p['cap'],('unproved_sum',))
    assert tagged.nv==manual_nv==p['variables'] and tagged.clauses==before+manual_counter
    assert tagged.ctrs[-1]==(lits,p['cap'],('unproved_sum',))
    initial=[]
    if 'cut_source' in p:
        source=R/p['cut_source'];verify(source,p['cut_source_sha256']);prior=read(source)
        assert prior['status']=='UNKNOWN'
        for key in ['directions','bounds','positions','cap','radius']:
            assert prior[key]==p[key]
        initial=prior['cycle_cuts']
        assert p['initial_cycle_cuts']==len(initial)==13 and p['cycle_cuts'][:len(initial)]==initial
    initial_clauses=[[-tagged.var[v] for v in cut] for cut in initial]
    assert len(tagged.clauses)+len(initial_clauses)==p['clauses']
    cuts=[inspect_cut(cut) for cut in p['cycle_cuts']]
    allcuts.extend(tuple(sorted(c)) for c in p['cycle_cuts'])
    full=tagged.clauses+[[-tagged.var[v] for v in cut] for cut in p['cycle_cuts']]
    assert p['selected'] is None
    census=p['census'];assert census and len(census['alpha'])==6
    assert all(0<=a<=21 for a in census['alpha']) and sum(census['alpha'])<=p['cap']
    assert sum(census['share'])==census['total_share']
    assert census['cycles'] and p['cycle_cuts'][-len(census['cycles']):]==census['cycles']
    for c in census['cycles']:inspect_cut(c)
    assert isinstance(p['calls'],int) and p['calls']>0 and p['conflict_budget_per_call']==1000
    assert p['build_seconds']>=0 and p['solver_seconds']>0 and p['nominal_seconds']>0
    expected='UNKNOWN' if stem=='0123042-total25-full' else 'UNSAT_UNCERTIFIED'
    assert p['status']==expected
    if expected=='UNKNOWN':assert p['solver_seconds']>=p['nominal_seconds']
    rows.append(dict(probe=path.relative_to(R).as_posix(),probe_sha256=sha(path),status=p['status'],cap=p['cap'],candidate_lower=p['cap']+1,
        window=word,bounds=p['bounds'],positions=p['positions'],full_cube_vertices=512,
        base_variables=base_variables,base_clauses=base_clauses,variables=tagged.nv,sum_counter_clauses=len(manual_counter),
        literal_occurrences=126,distinct_literals=106,multiplicity_histogram=dict(sorted(Counter(counts.values()).items())),
        repeated_vertices={str(v):n for v,n in sorted(counts.items()) if n>1},
        recorded_clauses=p['clauses'],initial_cuts=len(initial),new_cuts=len(cuts)-len(initial),total_cuts=len(cuts),cuts=cuts,
        reconstructed_starting_cnf_sha256=cnf_digest(tagged.nv,tagged.clauses+initial_clauses),
        reconstructed_final_cnf_clauses=len(full),reconstructed_final_cnf_sha256=cnf_digest(tagged.nv,full),
        last_census_alpha=census['alpha'],last_census_total=sum(census['alpha']),last_census_cycle_count=len(census['cycles']),
        selected_path=None,census_scope='Last cyclic model summary, not a selected path; full selected model was not saved so alpha/share values cannot be independently recomputed.',
        build_seconds=p['build_seconds'],solver_seconds=p['solver_seconds'],nominal_seconds=p['nominal_seconds'],calls=p['calls']))
sha(Path(__file__))
out=dict(status='PASS_SIX_SUM_PROBE_ENCODING_CUTS_AND_PROVENANCE',probes=rows,cut_records=sum(r['total_cuts'] for r in rows),unique_cut_vertex_sets=len(set(allcuts)),
    source_pins=pins,script_sha256=pins[Path(__file__).resolve().relative_to(R).as_posix()],
    scope='Pinned-source and case audit; full-cube base formula plus independently rebuilt multiplicity-preserving sequential sum counter; every saved cut checked as a nonempty finite subgraph of minimum internal degree at least2. Resume preserves13previous cuts. Native status/time are recorded provenance, not independently rerun. No CNF archive was supplied for these probes, so reconstructed formula hashes describe the deterministic pinned-source reconstruction. No solver, Lean compiler, certificate replay or new local theorem.')
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(dict(status=out['status'],cut_records=out['cut_records'],unique_cuts=out['unique_cut_vertex_sets'],rows=[{k:r[k] for k in ['status','cap','variables','recorded_clauses','reconstructed_final_cnf_clauses','total_cuts','multiplicity_histogram']} for r in rows],output_sha256=hashlib.sha256(args.output.read_bytes()).hexdigest() if args.output else None,script_sha256=out['script_sha256']),indent=2))
