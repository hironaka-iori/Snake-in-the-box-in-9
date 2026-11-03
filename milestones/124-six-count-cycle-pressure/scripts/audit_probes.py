"""Audit saved six-sum probe formulas and cuts without SAT or Lean execution.
Default prints summary; --output creates a fresh JSON file exclusively.
"""
from pathlib import Path
from collections import Counter
from itertools import combinations
import argparse, hashlib, json, sys, subprocess, datetime
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

def canonical(word):
    seen=[];out=[]
    for value in word:
        if value not in seen:seen.append(value)
        out.append(seen.index(value))
    return tuple(out)

def actual_counts(selected,centres):
    return [sum(all(z not in selected for z in (v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)))
        for a,b in combinations(range(9),2)) for v in centres]

def verify_selected(p,word,ball):
    if p['selected'] is None:return None
    S=set(p['selected']);assert len(S)==len(p['selected']) and S<=set(ball) and set(word)<=S
    adj={v:[v^(1<<j) for j in range(9) if (v^(1<<j)) in S] for v in S}
    counts=actual_counts(S,word[1:-1]);assert counts==p['census']['alpha'] and sum(counts)<=p['cap']
    if p['radius']!=9:
        assert p['status']=='SAT_LOCAL_CONFIGURATION'
        return dict(status='LOCAL_SELECTED_COUNTS_CHECKED_NOT_A_SNAKE_COUNTEREXAMPLE',vertices=len(S),counts=counts)
    assert p['status']=='SAT_FULL_PATH_CANDIDATE'
    endpoints=sorted(v for v in S if len(adj[v])==1)
    assert len(endpoints)==2 and all(len(ns) in [1,2] for ns in adj.values())
    order=[];previous=None;v=endpoints[0]
    while True:
        assert v not in order;order.append(v)
        choices=[u for u in adj[v] if u!=previous]
        if not choices:break
        assert len(choices)==1;previous,v=v,choices[0]
    assert set(order)==S and order[-1]==endpoints[1]
    pairs=0
    for i,v in enumerate(order):
        for j in range(i+1,len(order)):
            assert ((v^order[j]).bit_count()==1)==(j==i+1);pairs+=1
    positions=[i for i in range(len(order)-7) if order[i:i+8]==word or order[i:i+8]==word[::-1]]
    assert len(positions)==1
    return dict(status='ACTUAL_INDUCED_PATH_COUNTEREXAMPLE',edges=len(order)-1,order=order,
        counts=counts,total=sum(counts),pair_checks=pairs,window_start=positions[0])

ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
resume_cases=read(H/'data/universal-resume.json');assert len(resume_cases)==5
expected=[H/'data/probes'/(case['name']+'.json') for case in resume_cases]
assert all(p.exists() for p in expected),'All five requested resume records must exist before freezing this audit'
command="@(Get-CimInstance Win32_Process | Where-Object {$_.Name -eq 'python.exe'} | Select-Object ProcessId,CommandLine) | ConvertTo-Json -Compress"
raw=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes=json.loads(raw) if raw else [];processes=processes if isinstance(processes,list) else [processes]
live=[p for p in processes if '124-six-count-cycle-pressure' in (p.get('CommandLine') or '') and 'probe_resume.py' in (p.get('CommandLine') or '') and 'data/universal-resume.json' in (p.get('CommandLine') or '')]
assert not live,('Requested resume driver is still active',live)
process_observation=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),matching_live_drivers=live,
    method='Win32_Process python.exe command lines checked for milestone124 probe_resume.py and data/universal-resume.json')
coverage=read(H/'data/coverage-audit.json');assert coverage['status']=='PASS_ENUMERATION_AND_HISTORICAL_COVERAGE_AUDIT'
assert coverage['reversal_classes']==21
for rel,d in coverage['verified_file_hashes'].items():verify(R/rel,d)
verify(H/'scripts/audit_coverage.py',coverage['script_sha256'])
reps={tuple(x['directions']):x for x in coverage['representatives']}
paths=sorted((H/'data/probes').glob('*.json'))
assert len(paths)==28,('Expected two targets, three radius controls, eighteen new universal probes and five resumes',len(paths))
prior=R/'milestones/123-six-count-recovery/data/probes/0123042-total25-resume.json'
paths.append(prior)
rows=[];allcuts=[]
for path in paths:
    p=read(path);probe_home=path.parents[2]
    script='probe_six_sum_resume.py' if probe_home.name.startswith('123-') else 'probe_resume.py' if 'cut_source' in p else 'probe_radius.py' if p['radius']<9 else 'probe_six_sum.py'
    verify(probe_home/'scripts'/script,p['script_sha256'])
    for rel,d in p['source_files_sha256'].items():verify(R/rel,d)
    case_paths=[R/rel for rel in p['source_files_sha256'] if rel.startswith(probe_home.relative_to(R).as_posix()+'/data/')]
    assert len(case_paths)==1
    case=next(c for c in read(case_paths[0]) if c['name']==p['name'])
    assert all(p[k]==v for k,v in case.items() if k!='status')
    for field,digest in [('source','source_sha256'),('source_target_file','source_target_sha256')]:
        if field in case:verify(R/case[field],case[digest])
    if 'case_table_sha256' in case:verify(R/'milestones/32-seven-count-four-screen/data/cases.json',case['case_table_sha256'])
    assert len(p['directions'])==7 and p['bounds']==[[0,21]]*6
    assert p['positions']==list(range(6)) and p['radius'] in [3,4,9] and p['cap'] in [24,25]
    shape=min(canonical(p['directions']),canonical(p['directions'][::-1]));assert shape in reps
    word=[0]
    for d in p['directions']:word.append(word[-1]^(1<<d))
    assert len(set(word))==8 and all(((word[i]^word[j]).bit_count()==1)==(j==i+1) for i in range(8) for j in range(i+1,8))
    tagged=TaggedEncoding(word,[(0,21)]*6,radius=p['radius'])
    plain=Encoding(word,[(0,21)]*6,radius=p['radius'])
    assert tagged.ball==plain.ball and tagged.ends==plain.ends==2
    assert tagged.nv==plain.nv and tagged.clauses==plain.clauses
    if p['radius']==9:assert tagged.ball==list(range(512))
    base_clauses=len(tagged.clauses);base_variables=tagged.nv
    assert all(tagged.meaning[tagged.var[v]]==('p',v) for v in tagged.ball)
    corner_rows=[]
    for i in range(1,7):
        a=(word[i]^word[i-1]).bit_length()-1;b=(word[i]^word[i+1]).bit_length()-1
        assert a!=b
        corners=[word[i]^(1<<x)^(1<<y) for x,y in combinations(range(9),2) if x not in [a,b] and y not in [a,b]]
        assert len(corners)==len(set(corners))==21 and set(corners)<=set(tagged.ball)
        corner_rows.append(corners)
    occurrences=[v for cs in corner_rows for v in cs];counts=Counter(occurrences)
    lits=sorted(-tagged.var[v] for v in occurrences)
    assert len(lits)==p['literal_occurrences']==126 and len(set(lits))==p['distinct_literals']
    before=list(tagged.clauses);manual_nv,manual_counter=counter(lits,p['cap'],tagged.nv)
    tagged.atmost(lits,p['cap'],('unproved_sum',))
    assert tagged.nv==manual_nv==p['variables'] and tagged.clauses==before+manual_counter
    assert tagged.ctrs[-1]==(lits,p['cap'],('unproved_sum',))
    initial=[]
    if 'cut_source' in p:
        source=R/p['cut_source'];verify(source,p['cut_source_sha256']);earlier=read(source)
        assert earlier['status']=='UNKNOWN'
        for key in ['directions','bounds','positions','cap','radius']:assert earlier[key]==p[key]
        initial=earlier['cycle_cuts']
        assert p['initial_cycle_cuts']==len(initial) and p['cycle_cuts'][:len(initial)]==initial
    initial_clauses=[[-tagged.var[v] for v in cut] for cut in initial]
    assert len(tagged.clauses)+len(initial_clauses)==p['clauses']
    assert all(set(cut)<=set(tagged.ball) for cut in p['cycle_cuts'])
    cuts=[inspect_cut(cut) for cut in p['cycle_cuts']]
    allcuts.extend(tuple(sorted(c)) for c in p['cycle_cuts'])
    full=tagged.clauses+[[-tagged.var[v] for v in cut] for cut in p['cycle_cuts']]
    assert p['status'] in ['UNSAT_UNCERTIFIED','UNKNOWN','SAT_FULL_PATH_CANDIDATE','SAT_LOCAL_CONFIGURATION']
    selected=verify_selected(p,word,tagged.ball)
    if p['status'] in ['UNKNOWN','UNSAT_UNCERTIFIED']:assert selected is None
    census=p['census']
    if census is not None:
        assert len(census['alpha'])==6 and all(0<=a<=21 for a in census['alpha']) and sum(census['alpha'])<=p['cap']
        assert sum(census['share'])==census['total_share']
        if selected is None:
            assert census['cycles'] and p['cycle_cuts'][-len(census['cycles']):]==census['cycles']
            for c in census['cycles']:inspect_cut(c)
    else:assert len(cuts)==len(initial)
    assert isinstance(p['calls'],int) and p['calls']>0 and p['conflict_budget_per_call']==1000
    assert p['build_seconds']>=0 and p['solver_seconds']>0 and p['nominal_seconds']>0
    if p['status']=='UNKNOWN':assert p['solver_seconds']>=p['nominal_seconds']
    rows.append(dict(probe=path.relative_to(R).as_posix(),probe_sha256=sha(path),status=p['status'],cap=p['cap'],candidate_lower=p['cap']+1,
        representative=list(shape),word=''.join(map(str,shape)),radius=p['radius'],window=word,bounds=p['bounds'],positions=p['positions'],
        local_vertices=len(tagged.ball),base_variables=base_variables,base_clauses=base_clauses,variables=tagged.nv,sum_counter_clauses=len(manual_counter),
        literal_occurrences=126,distinct_literals=len(set(lits)),multiplicity_histogram=dict(sorted(Counter(counts.values()).items())),
        repeated_vertices={str(v):n for v,n in sorted(counts.items()) if n>1},recorded_clauses=p['clauses'],
        initial_cuts=len(initial),new_cuts=len(cuts)-len(initial),total_cuts=len(cuts),cuts=cuts,
        reconstructed_starting_cnf_sha256=cnf_digest(tagged.nv,tagged.clauses+initial_clauses),
        reconstructed_final_cnf_clauses=len(full),reconstructed_final_cnf_sha256=cnf_digest(tagged.nv,full),
        last_census_alpha=None if census is None else census['alpha'],last_census_total=None if census is None else sum(census['alpha']),
        last_census_cycle_count=None if census is None else len(census['cycles']),selected_path=selected,
        census_scope='Selected models independently checked when saved. Otherwise any census is only the last discarded cyclic-model summary; its alpha/share values cannot be recomputed without the full selected set.',
        build_seconds=p['build_seconds'],solver_seconds=p['solver_seconds'],nominal_seconds=p['nominal_seconds'],calls=p['calls']))

def coverage_table(include_resumes):
    table=[]
    for shape,case in sorted(reps.items()):
        candidates=[r for r in rows if tuple(r['representative'])==shape and r['radius']==9 and
            (include_resumes or '/123-' in r['probe'] or 'universal-total24-resume' not in r['probe'])]
        assert candidates,shape
        negatives=[r for r in candidates if r['status']=='UNSAT_UNCERTIFIED']
        if negatives:
            best=max(negatives,key=lambda r:(r['candidate_lower'],-r['total_cuts'],-r['solver_seconds']))
            state='NATIVE_NEGATIVE'
        else:
            best=max(candidates,key=lambda r:('resume' in r['probe'],r['nominal_seconds'],r['total_cuts']))
            state='ACTUAL_COUNTEREXAMPLE' if best['selected_path'] else 'UNKNOWN'
        table.append(dict(word=case['word'],directions=list(shape),case_indices=case['case_indices'],status=state,
            native_candidate_lower=best['candidate_lower'] if negatives else None,selected_probe=best['probe'],
            selected_probe_sha256=best['probe_sha256'],selected_probe_status=best['status'],selected_probe_total_cuts=best['total_cuts'],
            available_probes=[r['probe'] for r in candidates]))
    return table
initial_table=coverage_table(False);table=coverage_table(True)
assert Counter(r['status'] for r in initial_table)=={'NATIVE_NEGATIVE':16,'UNKNOWN':5}
sha(Path(__file__))
out=dict(status='PASS_SIX_COUNT_PROBES_AND_NATIVE_COVERAGE_AUDIT',probes=rows,probe_records=len(rows),current_probe_records=len(paths)-1,
    prior_probe=prior.relative_to(R).as_posix(),process_observation=process_observation,
    cut_records=sum(r['total_cuts'] for r in rows),unique_cut_vertex_sets=len(set(allcuts)),
    initial_coverage=initial_table,initial_coverage_counts=dict(Counter(r['status'] for r in initial_table)),
    current_coverage=table,current_coverage_counts=dict(Counter(r['status'] for r in table)),
    universal_floor25_proved=False,universal_floor26_proved=False,
    source_pins=pins,script_sha256=pins[Path(__file__).resolve().relative_to(R).as_posix()],
    scope='All saved milestone124 count-sum probes plus the explicit prior123 floor26 probe. Pinned formulas reconstructed with126 count-literal occurrences, independent sequential counters and every cycle cut. Five resume records exist and their matching driver is absent. Native statuses and times are provenance rather than independently repeated outcomes. Separate contradiction certificates and their Lean semantics/transfers are outside this audit; no universal floor or new global bound is proved.')
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(dict(status=out['status'],probes=len(rows),cut_records=out['cut_records'],unique_cuts=out['unique_cut_vertex_sets'],
    initial_coverage=out['initial_coverage_counts'],current_coverage=out['current_coverage_counts'],
    unknown=[r['word'] for r in table if r['status']=='UNKNOWN'],
    counterexamples=[r['probe'] for r in rows if r['selected_path']],
    output_sha256=hashlib.sha256(args.output.read_bytes()).hexdigest() if args.output else None,script_sha256=out['script_sha256']),indent=2))
