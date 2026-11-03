"""Read-only audit of the positive-bound search; no solver or compiler."""
from pathlib import Path
from itertools import combinations, permutations
from collections import Counter
import argparse, gzip, hashlib, json, re, sys

HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.dont_write_bytecode=True
sys.path[:0]=[str(ROOT/'milestones/10-window-aggregate/scripts'),str(ROOT/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding
from wincert import window_from_dirs

pins={};cache={}
def sha(path):
    path=Path(path).resolve();stat=path.stat();key=(str(path),stat.st_size,stat.st_mtime_ns)
    if key not in cache:
        h=hashlib.sha256()
        with path.open('rb') as stream:
            for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
        cache[key]=h.hexdigest()
    try:display=path.relative_to(ROOT).as_posix()
    except ValueError:display=str(path)
    if display in pins:assert pins[display]==cache[key],('Input changed',display)
    pins[display]=cache[key];return cache[key]
def read(path):sha(path);return json.loads(Path(path).read_text(encoding='utf-8-sig'))
def verify(path,digest):assert sha(path)==digest,str(path)
def cnf(path):
    sha(path);nv=nc=None;rows=[]
    with Path(path).open() as stream:
        for line in stream:
            if line.startswith('p '):
                _,kind,nv,nc=line.split();assert kind=='cnf';nv,nc=int(nv),int(nc)
            elif line.strip() and not line.startswith('c'):
                row=list(map(int,line.split()));assert row[-1]==0 and 0 not in row[:-1];rows.append(row[:-1])
    assert len(rows)==nc and all(0<abs(x)<=nv for c in rows for x in c)
    return nv,rows
def components(vertices):
    remaining=set(vertices);out=[]
    while remaining:
        todo=[min(remaining)];part=set()
        while todo:
            v=todo.pop()
            if v not in remaining:continue
            remaining.remove(v);part.add(v)
            todo.extend(v^(1<<a) for a in range(9) if v^(1<<a) in remaining)
        out.append(sorted(part))
    return out
def valid_cycle(vertices):
    s=set(vertices)
    assert len(s)==len(vertices)>2 and all(0<=v<512 for v in s)
    assert all(sum((v^(1<<a)) in s for a in range(9))==2 for v in s)
    assert len(components(s))==1
def permute(v,perm):
    result=v&31
    for source,target in enumerate(perm,5):
        if v&(1<<source):result|=1<<target
    return result
def proof_rows(path):
    with Path(path).open('rb') as stream:
        for line in stream:
            tokens=line.split()
            if len(tokens)>1 and tokens[1]==b'd':continue
            row=list(map(int,tokens));z=row.index(0,1)
            assert row[-1]==0 and all(h>0 for h in row[z+1:-1])
            yield row[0],row[1:z],row[z+1:-1],hashlib.sha256(line).hexdigest()

def audit_one(name):
    record_path=HERE/'data'/(name+'-solver.json');record=read(record_path)
    assert record['status']!='RUNNING',('Pending native run',name)
    assert record['status'] in ['TIMEOUT','FAILED','NATIVE_SAT','NATIVE_UNSAT_LEAN_PENDING']
    case_path=HERE/'data/probes'/(name+'.json')
    if not case_path.exists():raise SystemExit('Pending terminal probe publication: '+name)
    case=read(case_path);verify(case_path,record['probe_sha256'])
    verify(HERE/'scripts/search_bounded.py',case['script_sha256']);assert case['script_sha256']==record['script_sha256']
    assert case['solver_record']==record_path.relative_to(ROOT).as_posix()
    assert case['source_files_sha256']==record['source_files_sha256']
    for path,digest in case['source_files_sha256'].items():verify(ROOT/path,digest)
    prior_path=ROOT/'milestones/124-six-count-cycle-pressure/data/probes/0120324-universal-total24-resume.json'
    prior=read(prior_path)
    assert prior['status']=='UNKNOWN' and len(prior['cycle_cuts'])==8
    for path,digest in prior['source_files_sha256'].items():verify(ROOT/path,digest)
    assert case['directions']==prior['directions']==[0,1,2,0,3,2,4]
    assert case['window']==window_from_dirs(case['directions'])==[0,1,3,7,6,14,10,26]
    assert case['bounds']==[[1,21],[2,21],[1,21],[3,21],[1,21],[1,21]] and case['positions']==list(range(6)) and case['radius']==9
    assert case['cap']==22
    seeds=case['seed_cuts'];assert seeds[:8]==prior['cycle_cuts']
    extra_models=[]
    for path in case['source_files_sha256']:
        if path.startswith('milestones/125-critical-six-count/data/probes/'):
            extra=read(ROOT/path);assert extra['status']=='NATIVE_CYCLIC_MODEL'
            extra_models.append(extra)
    assert len(extra_models)<=1
    assert seeds[8:]==[c for m in extra_models for c in m['census']['cycles']]
    orbit=set();provenance={}
    for index,seed in enumerate(seeds):
        valid_cycle(seed)
        for perm in permutations(range(5,9)):
            images=[permute(v,perm) for v in range(512)]
            assert len(set(images))==512 and all(images[v]==v for v in case['window'])
            assert all((images[v]^images[v^(1<<a)]).bit_count()==1 for v in range(512) for a in range(9))
            image=tuple(sorted(images[v] for v in seed));valid_cycle(image);orbit.add(image)
            provenance.setdefault(image,(index,list(perm)))
    assert case['cycle_cuts']==record['cycle_cuts']==[list(c) for c in sorted(orbit)]
    assert len(case['cut_provenance'])==len(orbit)
    for row in case['cut_provenance']:
        key=tuple(row['vertices']);assert key in orbit
        assert (row['seed'],row['permutation'])==provenance[key]
    assert len({tuple(x['vertices']) for x in case['cut_provenance']})==len(orbit)

    enc=TaggedEncoding(case['window'],[tuple(b) for b in case['bounds']],radius=9)
    assert set(enc.ball)==set(range(512))
    corner_lists=[]
    for i in range(1,7):
        centre=enc.window[i];incident={centre^enc.window[i-1],centre^enc.window[i+1]}
        assert len(incident)==2
        corners=[centre^(1<<a)^(1<<b) for a,b in combinations(range(9),2)
                 if (1<<a) not in incident and (1<<b) not in incident]
        assert len(corners)==len(set(corners))==21;corner_lists.append(corners)
    counts=Counter(v for cs in corner_lists for v in cs)
    lits=sorted(-enc.var[v] for cs in corner_lists for v in cs)
    assert len(lits)==case['literal_occurrences']==126 and len(set(lits))==case['distinct_literals']==100
    enc.atmost(lits,case['cap'],('unproved_sum',))
    before_cuts=len(enc.clauses)
    for cut in sorted(orbit):enc.add([-enc.var[v] for v in cut],('cut',))
    work=HERE/'work'/name;nv,full=cnf(work/'full.cnf')
    assert full==enc.clauses and nv==enc.nv==case['variables'] and len(full)==case['clauses']
    assert len(full)==before_cuts+len(orbit)
    verify(work/'full.cnf',record['cnf_sha256'])
    raw=work/'full.raw.lrat';verify(raw,record['raw_sha256']);assert raw.stat().st_size==record['raw_bytes']
    stdout=HERE/'logs'/(name+'-solver.stdout.txt');stderr=HERE/'logs'/(name+'-solver.stderr.txt')
    verify(stdout,record['stdout_sha256']);verify(stderr,record['stderr_sha256'])
    verify(record['command'][0],record['solver_sha256'])
    assert record['command'][1:]==['-q','--lrat','--no-binary','--seed=1',str(work/'full.cnf'),str(raw)]
    text=stdout.read_text(encoding='utf-8',errors='replace');model=None;proof=None
    if record['status']=='NATIVE_SAT':
        assert record['exit_code']==10 and 's SATISFIABLE' in text
        vals=[int(x) for line in text.splitlines() if line.startswith('v ') for x in line.split()[1:] if x!='0']
        assert len(vals)==len(set(map(abs,vals)))==nv and set(map(abs,vals))==set(range(1,nv+1))
        assigned=set(vals);assert all(any(x in assigned for x in c) for c in full)
        selected={v for v in range(512) if enc.var[v] in assigned}
        assert sorted(selected)==case['selected'] and set(case['window'])<=selected
        degree={v:sum((v^(1<<a)) in selected for a in range(9)) for v in selected}
        assert all(d in [1,2] for d in degree.values())
        endpoints=sorted(v for v,d in degree.items() if d==1);assert len(endpoints)<=2
        pieces=components(selected);cycles=[c for c in pieces if all(degree[v]==2 for v in c)]
        for cut in orbit:assert not set(cut)<=selected
        assert {tuple(c) for c in cycles}=={tuple(sorted(c)) for c in case['census']['cycles']}
        alpha=[sum(all(v not in selected for v in (c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b)))
                   for a,b in combinations(range(9),2)) for c in case['window'][1:-1]]
        free_alpha=[sum(v not in selected for v in cs) for cs in corner_lists]
        assert alpha==free_alpha==case['census']['alpha'] and sum(alpha)<=case['cap']
        assert all(lo<=a<=hi for a,(lo,hi) in zip(alpha,case['bounds'],strict=True))
        path=None
        if cycles:
            assert case['status']=='NATIVE_CYCLIC_MODEL'
        else:
            assert case['status']=='SAT_FULL_PATH_CANDIDATE' and len(pieces)==1 and len(endpoints)==2
            path=[endpoints[0]];previous=None
            while len(path)<len(selected):
                options=[path[-1]^(1<<a) for a in range(9) if path[-1]^(1<<a) in selected and path[-1]^(1<<a)!=previous]
                assert len(options)==1 and options[0] not in path
                previous=path[-1];path.append(options[0])
            assert path[-1]==endpoints[1]
            assert any(path[i:i+8] in [case['window'],case['window'][::-1]] for i in range(len(path)-7))
        model=dict(status=case['status'],all_clauses_verified=True,selected_vertices=len(selected),component_sizes=[len(c) for c in pieces],endpoints=endpoints,cycles=cycles,alpha=alpha,total_alpha=sum(alpha),induced_path=path,edge_length=len(path)-1 if path else None)
    elif record['status']=='NATIVE_UNSAT_LEAN_PENDING':
        assert record['exit_code']==20 and 's UNSATISFIABLE' in text
        certpath=HERE/'data'/(name+'-certificate.json')
        if not certpath.exists():raise SystemExit('Pending certificate trimming/publication: '+name)
        cert=read(certpath)
        assert cert['cycle_cuts']==case['cycle_cuts'] and cert['sum_cap']==case['cap']
        assert cert['variables']==nv and cert['clauses']==len(full)
        verify(certpath,sha(certpath));verify(work/'full.trim.lrat',cert['lrat_sha256']);verify(work/'core.cnf',cert['core_sha256'])
        verify(case_path,cert['probe_sha256']);verify(record_path,cert['solver_record_sha256'])
        assert cert['script_sha256']==case['script_sha256'] and cert['source_files_sha256']==case['source_files_sha256']
        verify(ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py',cert['trimming_generator_sha256'])
        ids=cert['core_ids'];assert ids==sorted(set(ids)) and len(ids)==cert['core_clauses']
        assert cnf(work/'core.cnf')==(nv,[full[i-1] for i in ids])
        proof=dict(status=cert['status'],core_inputs=len(ids),deductions=cert['lemmas'],hints=cert['hints'],rup_replayed_here=False,cycle_cut_input_ids=[i for i in ids if i>before_cuts])
        if cert['hints']<=2_000_000:
            assert cert['status']=='NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING'
            db={i:full[i-1] for i in ids};used=set();deps={};last=len(full);hints=0;trim_hashes={}
            for cid,cl,hs,digest in proof_rows(work/'full.trim.lrat'):
                assert cid>last and all(0<h<cid and h in db for h in hs)
                assignment={};conflict=False
                for lit in cl:
                    variable=abs(lit);value=lit<0
                    if variable in assignment and assignment[variable]!=value:conflict=True
                    assignment[variable]=value
                for h in hs:
                    if h<=len(full):used.add(h)
                    if conflict:continue
                    c=db[h]
                    if any(abs(x) in assignment and assignment[abs(x)]==(x>0) for x in c):continue
                    remaining={x for x in c if abs(x) not in assignment};assert len(remaining)<=1
                    if not remaining:conflict=True
                    else:
                        lit=next(iter(remaining));assignment[abs(lit)]=lit>0
                assert conflict
                db[cid]=cl;deps[cid]=hs;trim_hashes[cid]=digest;last=cid;hints+=len(hs)
            assert db[last]==[] and len(deps)==cert['lemmas'] and hints==cert['hints'] and sorted(used)==ids
            closure=set();todo=[last]
            while todo:
                cid=todo.pop()
                if cid<=len(full) or cid in closure:continue
                closure.add(cid);todo.extend(deps[cid])
            assert closure==set(deps)
            found=set()
            for cid,_,_,digest in proof_rows(raw):
                if cid in trim_hashes:assert trim_hashes[cid]==digest;found.add(cid)
            assert found==set(trim_hashes)
            proof.update(rup_replayed_here=True,final_empty_id=last,exact_backward_closure=True,trim_rows_identical_to_raw=True)
        else:
            assert cert['status']=='TRIMMED_OVER_HINT_LIMIT_NOT_REPLAYED'
            proof['limitation']='More than two million hints: no RUP replay performed by this auditor.'
    else:
        assert case['status']==record['status'] and case['selected'] is None and case['census'] is None
    return dict(name=name,cap=case['cap'],bounds=case['bounds'],solver_status=record['status'],probe_status=case['status'],exit_code=record['exit_code'],seconds=record['seconds'],variables=nv,clauses=len(full),clauses_before_added_cuts=before_cuts,seed_cycles=len(seeds),distinct_orbit_cuts=len(orbit),orbit_permutations=24,all_cut_cycles_verified=True,all_permutations_fix_window=True,literal_occurrences=len(lits),distinct_literals=len(set(lits)),multiplicity_histogram=dict(sorted(Counter(counts.values()).items())),full_formula_rebuilt=True,raw_lrat_bytes=raw.stat().st_size,raw_proof_complete=record['status']=='NATIVE_UNSAT_LEAN_PENDING',stdout_prints_unsat='s UNSATISFIABLE' in text,stdout_prints_sat='s SATISFIABLE' in text,model=model,proof=proof)

parser=argparse.ArgumentParser();parser.add_argument('names',nargs='*');parser.add_argument('--output',type=Path);args=parser.parse_args()
names=args.names or ['0120324-total22-positive']
assert names and len(names)==len(set(names))
results=[audit_one(name) for name in names]
provenance_path=HERE/'data/bounded-search-provenance.json';provenance=read(provenance_path)
verify(HERE/provenance['source'],provenance['source_sha256'])
verify(HERE/provenance['new_script'],provenance['new_sha256'])
assert provenance['bounds']==[[1,21],[2,21],[1,21],[3,21],[1,21],[1,21]]
original=(HERE/provenance['source']).read_text(encoding='utf-8')
changed=original.replace("default='orbit'", "default='positive'").replace('args.cap in [22,23,24]','args.cap == 22').replace("enc=TaggedEncoding(window_from_dirs(dirs),[(0,21)]*6,radius=9)","bounds=[(1,21),(2,21),(1,21),(3,21),(1,21),(1,21)]\nenc=TaggedEncoding(window_from_dirs(dirs),bounds,radius=9)").replace('window=enc.window,bounds=[[0,21]]*6','window=enc.window,bounds=[list(b) for b in bounds]')
assert changed==(HERE/provenance['new_script']).read_text(encoding='utf-8')
bridge=dict(status='NOT_REVIEWED_OR_PENDING',scope='Search lower bounds are explicit. A separate ActualBounds125 receipt review is required to establish applicability to actual cap22 counterexamples.')
receipt_path=HERE/'data/ActualBounds125-audit.json'
if receipt_path.exists():
    receipt=read(receipt_path)
    assert receipt['module']=='ActualBounds125' and receipt['status']=='PASS_REFERENCE_RECOVERY_MODULE'
    assert receipt['exit_code']==0 and receipt['timeout'] is False
    source=HERE/'lean/ActualBounds125.lean';obj=HERE/'build-isolated/ActualBounds125.olean'
    log=HERE/receipt['log'];snapshot=HERE/receipt['source_snapshot']
    for path,digest in [(source,receipt['source_sha256']),(obj,receipt['olean_sha256']),
                        (log,receipt['log_sha256']),(snapshot,receipt['source_sha256']),
                        (snapshot.parent/'checker.py.txt',receipt['checker_sha256'])]:verify(path,digest)
    for path,digest in receipt['dependencies'].items():
        q=Path(path);verify(q if q.is_absolute() else ROOT/q,digest)
    text=source.read_text(encoding='utf-8');output=log.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
    assert 'error:' not in output and 'sorryAx' not in output
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)
    rows += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",output)]
    audits=[dict(theorem=name,axioms=re.findall(r'[A-Za-z][\w.]*',axs)) for name,axs in rows]
    assert audits==receipt['theorem_audits'] and len(audits)==text.count('#print axioms')==5
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in audits)
    imports=[]
    for name in re.findall(r'^import ([\w.]+)$',text,re.M):
        rel=name.replace('.','/')+'.olean'
        found=next((Path(path)/rel for path in receipt['paths'] if (Path(path)/rel).exists()),None)
        assert found is not None
        verify(found,receipt['dependencies'][found.relative_to(ROOT).as_posix()])
        imports.append(dict(module=name,object=found.relative_to(ROOT).as_posix(),sha256=sha(found)))
    assert '(hr : r+7 ≤ m)' in text and '(htotal : (∑ j ∈ range 6, coreAlpha p (r+j+1)) ≤ 22)' in text
    assert '[(1,21),(2,21),(1,21),(3,21),(1,21),(1,21)]' in text
    assert 'ActualPair121.actual_pair_minima' in text and 'ActualSum112.actual_outer_sum' in text and 'CycleWindow4906.refuted' in text
    bridge=dict(status='PASS_ACTUAL_CAP22_BOUNDS_RECEIPT',receipt=receipt_path.relative_to(ROOT).as_posix(),receipt_sha256=sha(receipt_path),source_sha256=receipt['source_sha256'],object_sha256=receipt['olean_sha256'],log=log.relative_to(ROOT).as_posix(),log_sha256=receipt['log_sha256'],theorem_audits=audits,imports=imports,
        scope='For an actual snake with forward canonical window0120324 and six-count total<=22, the six explicit intervals are proved. This validates their use in this bounded search; it does not exclude such a window or prove total>=23.')
else:
    failed=[]
    for path in sorted((HERE/'logs').glob('ActualBounds125-*-record.json')):
        attempt=read(path)
        if attempt['exit_code']==0 and not attempt['timeout']:continue
        log=HERE/attempt['log'];snapshot=HERE/attempt['source_snapshot']
        verify(log,attempt['log_sha256']);verify(snapshot,attempt['source_sha256'])
        verify(snapshot.parent/'checker.py.txt',attempt['checker_sha256'])
        failed.append(dict(record=path.relative_to(ROOT).as_posix(),record_sha256=sha(path),exit_code=attempt['exit_code'],timeout=attempt['timeout'],log=log.relative_to(ROOT).as_posix(),log_sha256=attempt['log_sha256'],source_snapshot=snapshot.relative_to(ROOT).as_posix(),source_sha256=attempt['source_sha256']))
    if failed:
        bridge.update(status='PENDING_AFTER_FAILED_SOURCE_CHECK',failed_attempts=failed,
            scope='At audit time no successful ActualBounds125 receipt exists. Failed source-check evidence is preserved. The formula includes explicit lower bounds; this audit does not yet certify their applicability to actual snakes.')
script_sha=sha(Path(__file__))
for path,digest in list(pins.items()):verify(ROOT/path if not Path(path).is_absolute() else path,digest)
out=dict(status='PASS_BOUNDED_SEARCH_FORMULA_AND_AVAILABLE_EVIDENCE',attempts=results,producer_diff_verified=True,bounded_search_provenance=provenance,actual_bound_bridge=bridge,source_files_sha256=pins,script_sha256=script_sha,
    cut_soundness='Each listed set induces a connected cycle in Q9. An induced path cannot contain every vertex of such a set, so each exclusion is necessary for actual snakes. Unused-coordinate permutations are bijective cube automorphisms fixing the specified window; all images were checked.',
    scope='Independent saved formula/orbit/multiplicity audit and terminal evidence review. Returned SAT assignments are checked against every clause and their actual induced components. Complete trimmed proofs are replayed only up to two million hints. Timeout or failure supplies no impossibility claim; cyclic models are not snakes. Explicit coordinate-wise lower bounds are added to this formula; their actual-snake applicability is separate from the native result. No solver or Lean compiler invocation, and no new Lean-certified total floor.')
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as stream:json.dump(out,stream,indent=2);stream.write('\n')
print(json.dumps(dict(status=out['status'],attempts=results,pinned_files=len(pins),output_sha256=hashlib.sha256(args.output.read_bytes()).hexdigest() if args.output else None),indent=2))
