"""Read-only reconstruction and independent RUP audit; writes only its audit receipt."""
from pathlib import Path
from collections import Counter, defaultdict
import datetime, gzip, hashlib, itertools, json, sys, time, types

sys.dont_write_bytecode = True
H = Path(__file__).resolve().parents[1]
R = H.parents[1]
W = H / 'work/certificate-alternative'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text(encoding='utf-8-sig'))
normal = lambda x: json.loads(json.dumps(x))
pins = {}

def pin(p, expected=None):
    p = Path(p)
    value = sha(p)
    if expected is not None:
        assert value == expected, (str(p), value, expected)
    pins[p.as_posix()] = value
    return value

def dimacs(nv, clauses):
    return (f'p cnf {nv} {len(clauses)}\n' + ''.join(' '.join(map(str,c))+' 0\n' for c in clauses)).encode('ascii')

def main():
    start = time.monotonic()
    enc = read(H/'work/short/encoding.json')
    native = read(H/'data/native-alternative.json')
    assert 'finished_utc' in native, 'Native job is not terminal; do not audit a moving certificate'
    passed = native['status'] == 'PASS_COMPLETE_NATIVE_RUP_REPLAY'
    assert native['solver_runs'] == 1
    assert native['replay_hint_limit'] == 12000000
    if passed: assert native['worker_exit'] == native['conversion_exit'] == 0
    assert enc['directions'] == [0,1,2,0,3,4] and enc['bounds'] == [[0,21]]*5
    assert (enc['share_cap'],enc['resolution'],enc['radius']) == (17,12,4)
    assert enc['target_share'] == 18
    assert enc['extra_cycle_cuts'] == []
    if 'core_premises' in native: assert native['core_premises']['extra_cycle_cuts'] == []
    assert (H/'data/preparation.json').read_bytes() == (H/'work/short/encoding.json').read_bytes()
    for rel, expected in enc['source_files_sha256'].items():
        p = R/rel
        pin(p,expected)
        if p.suffix == '.py':
            pin(H/'audit'/('input-source-'+p.name+'.txt'),expected)
    for rel,expected in native['source_files_sha256'].items():
        pin(R/rel,expected)
    for name,expected in native['preserved_files_sha256'].items():
        pin(W/name,expected)
    for p,digest in native.get('worker_result',{}).get('solver_files_sha256',{}).items(): pin(p,digest)
    worker = read(W/'worker.json')
    assert worker == native['worker_result'] and worker['cnf_sha256'] == enc['cnf_sha256']
    assert worker['extra_cycle_cuts'] == [] and worker['cnf_unchanged']
    if passed: assert b's VERIFIED' in (W/'conversion-stdout.txt').read_bytes()
    if passed: assert worker['status'] == 'UNSAT_DRAT_UNCHECKED'
    if passed: assert not (W/'worker-stderr.txt').read_bytes() and not (W/'conversion-stderr.txt').read_bytes()
    pin(H/'work/short/base.cnf',enc['cnf_sha256'])
    pin(H/'work/short/meanings.json.gz',enc['meanings_sha256'])
    old = read(H/'data/old-share20-observation.json')
    pin(old['source'],old['source_sha256'])
    pin(H/old['snapshot'],old['source_sha256'])
    pin(H/'audit/native-input-review.md','43c12f8df6b2b93a9098b280d8b9f8804a2a8dcc2ca2b999f1f59afdc6755b50')
    pin(H/'data/native-input-review.json','9df50fce179ba51ddeddac84b753bc60f53351c3f90fb04e28cd705b2a81574a')
    pin(H/'audit/review-native.py','244fcfb7724944a8eda58ede14d951bc9daae571291e5d5c8f56a5a903cd1a80')
    first = read(H/'data/native-base.json')
    assert first['status'] == 'TIMEOUT'
    for name,digest in first['preserved_files_sha256'].items():
        pin(H/'work/certificate-base'/name,digest)
    old13 = R/'milestones/143-countfree-share13'
    pin(old13/'audit/native-input-review.md','917eb1b775f92cab65ef1ca20009c2506e488a81fd5ff6ab783f90e438b0e718')
    pin(old13/'data/native-input-review.json','a67af5a06408cb30fdbb8388e76f5e101b64d51659868c4c1a2ab04d29861b09')
    pin(old13/'audit/range-review.md','9535e7be9bd7a483d40bc9c31d652c37eadcd0af2e5a2ccae4fcddccd77ae73c')
    pin(old13/'data/range-review.json','1af86f7251792394922896ed341c882b8970421b2bd790dc4f44e97d6757fc65')
    oldnative = read(old13/'data/native-base.json')
    for name,digest in oldnative['preserved_files_sha256'].items():
        pin(old13/'work/certificate-base'/name,digest)

    # Block solver construction even if an imported module were to attempt it.
    def forbidden(*args, **kwargs):
        raise AssertionError('Solver invocation is forbidden in this audit')
    pysat = types.ModuleType('pysat')
    solvers = types.ModuleType('pysat.solvers')
    solvers.Cadical153 = forbidden
    pysat.solvers = solvers
    sys.modules.update({'pysat':pysat,'pysat.solvers':solvers})
    sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
    from tagged_share import TaggedShare
    from gen_lean_sat import TaggedEncoding
    from wincert import Encoding
    e = TaggedShare([0,1,2,0,3,4],[(0,21)]*5,17,M=12)
    assert (e.nv,len(e.clauses)) == (11924,96091)
    assert dimacs(e.nv,e.clauses) == (W/'input.cnf').read_bytes() == (H/'work/short/base.cnf').read_bytes()
    saved = json.loads(gzip.decompress((H/'work/short/meanings.json.gz').read_bytes()))
    assert saved == normal(dict(meaning=e.meaning,smeaning=e.smeaning,ctrs=e.ctrs,tots=e.tots,tags=e.tags))
    base = TaggedEncoding(e.window,[(0,21)]*5,radius=4,ends=2)
    other = Encoding(e.window,[(0,21)]*5,radius=4,ends=2)
    assert base.clauses == other.clauses == e.clauses[:len(base.clauses)]
    assert len(base.ctrs) == 1 and base.ctrs[0][1:] == (2,('ends',))
    assert e.ball == [v for v in range(512) if min((v^c).bit_count() for c in e.window[1:-1]) <= 4]
    assert set(e.meaning)|set(e.smeaning) == set(range(1,e.nv+1))
    assert not (set(e.meaning)&set(e.smeaning))
    assert all(0 < abs(x) <= e.nv for c in e.clauses for x in c)

    bytag = defaultdict(list)
    for c,t in zip(e.clauses,e.tags):
        bytag[t].append(c)
    # Independently rebuild each totalizer using saved register meanings.
    registers = {m:v for v,m in e.smeaning.items() if m[0]=='t'}
    roots = {}
    for ti,(lits,kind) in enumerate(e.tots):
        up = kind[0] != 'nb'
        down = kind[0] == 'nb'
        limit = 18 if kind[0]=='cap' else len(lits)
        upclauses,downclauses = [],[]
        def tree(lo,hi):
            if hi-lo == 1:
                return [None,lits[lo]]
            mid = (lo+hi)//2
            left,right = tree(lo,mid),tree(mid,hi)
            out = [None]+[registers[('t',ti,lo,hi,j)] for j in range(1,min(hi-lo,limit)+1)]
            for a in range(len(left)):
                for b in range(len(right)):
                    if up and 0<a+b<len(out):
                        upclauses.append([out[a+b]]+([-left[a]] if a else [])+([-right[b]] if b else []))
                    if down and a+b+1<len(out):
                        downclauses.append([-out[a+b+1]]+([left[a+1]] if a+1<len(left) else [])+([right[b+1]] if b+1<len(right) else []))
            return out
        roots[ti] = tree(0,len(lits))
        assert upclauses == bytag[('totUp',ti)]
        assert downclauses == bytag[('totDown',ti)]
    assert len(e.tots) == 71
    caplits,capkind = e.tots[-1]
    assert capkind[0] == 'cap' and len(caplits) == 630 and len(set(caplits)) == 630
    expectedempty = []
    incidences = []
    for ci,c in enumerate(e.window[1:-1],1):
        used = {(c^e.window[ci-1]).bit_length()-1,(c^e.window[ci+1]).bit_length()-1}
        assert len(used) == 2
        for k in range(9):
            if k in used:
                continue
            q = c^(1<<k)
            j = len(incidences)
            incidences.append((ci,c,k,q))
            es,ekind = e.tots[2*j]
            ns,nkind = e.tots[2*j+1]
            assert ekind == ('emp',q) and nkind == ('nb',q)
            squares = [(a,b) for a,b in itertools.combinations(range(9),2) if k not in (a,b)]
            assert len(es) == len(squares) == 28
            for var,(a,b) in zip(es,squares):
                assert e.smeaning[var] == ('sq',q,a,b)
                vertices = [q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)]
                assert all(v in e.var for v in vertices)
                expectedempty.append([e.var[v] for v in vertices]+[var])
            assert ns == [e.var[q^(1<<a)] for a in range(9)]
            expectedshare = []
            for t,var in enumerate(caplits[18*j:18*j+18],1):
                assert e.smeaning[var] == ('u',q,t)
                for degree in range(1,10):
                    need = (t*degree+11)//12
                    expectedshare.append([var,-roots[2*j][need]]+([roots[2*j+1][degree+1]] if degree<9 else []))
            assert expectedshare == bytag[('shareCl',2*j,2*j+1)]
    assert expectedempty == bytag[('emptyE',)]
    assert bytag[('shareCap',70)] == [[-roots[70][18]]]
    assert len(incidences) == 35

    conversion_structure = dict(independent_rup_replay=False)
    if 'conversion_exit' in native and native['conversion_exit'] == 0:
        command = native['conversion_command']
        assert command[1:3] == [str(W/'input.cnf'),str(W/'raw.drat')]
        assert command[3:] == ['-U','-L',str(W/'raw.lrat'),'-c',str(W/'drat-core.cnf'),'-t','120']
        assert b's VERIFIED' in (W/'conversion-stdout.txt').read_bytes()
        corelines = (W/'drat-core.cnf').read_text(encoding='ascii').splitlines()
        header = corelines[0].split()
        assert header[:2] == ['p','cnf'] and int(header[2]) == e.nv
        converterclauses = []
        for line in corelines[1:]:
            if not line or line.startswith('c'): continue
            vals = list(map(int,line.split()))
            assert vals[-1] == 0
            converterclauses.append(vals[:-1])
        assert len(converterclauses) == int(header[3])
        fullmultiset = Counter(tuple(sorted(c)) for c in e.clauses)
        coremultiset = Counter(tuple(sorted(c)) for c in converterclauses)
        assert not (coremultiset-fullmultiset)
        conversion_structure.update(converter_exit_zero=True,converter_verified_marker=True,rup_only_command=True,converter_core_clauses=len(converterclauses),converter_core_is_original_input_submultiset=True)
        if (W/'core-ids.json').exists():
            selected = read(W/'core-ids.json')
            assert selected == sorted(set(selected)) and all(1<=i<=len(e.clauses) for i in selected)
            assert dimacs(e.nv,[e.clauses[i-1] for i in selected]) == (W/'core.cnf').read_bytes()
            selectedmultiset = Counter(tuple(sorted(e.clauses[i-1])) for i in selected)
            assert not (selectedmultiset-coremultiset)
            conversion_structure.update(trimmed_original_core_clauses=len(selected),trimmed_core_original_ids_checked=True,trimmed_core_is_converter_core_submultiset=True)

    if not passed:
        for p,digest in list(pins.items()):
            assert sha(p) == digest, ('Source changed during review',p)
        pin(Path(__file__))
        pin(H/'data/native-alternative.json')
        family = lambda t: 'old/'+t[1][0] if t[0]=='old' else t[0]
        receipt = dict(status='PASS_ALTERNATIVE_INPUT_REVIEW_NO_COMPLETED_NATIVE_REPLAY',
            native_status=native['status'],conversion_structure=conversion_structure,worker_status=worker['status'],
            recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
            variables=e.nv,clauses=len(e.clauses),base_clauses=len(base.clauses),ball_vertices=len(e.ball),
            full_tag_counts=dict(sorted(Counter(map(family,e.tags)).items())),added_cycle_cuts=0,
            share=dict(cap=17,target=18,resolution=12,incidences=35,cap_literals=630,totalizers=71),
            input_reconstruction_passed=True,independent_untagged_base_matched=True,
            meanings_tags_totalizers_share_geometry_checked=True,independent_replay_performed=False,
            no_solver_lean_or_graph_invocation=True,
            limitations=['No finite contradiction or actual-snake conclusion certified by this audit',
                'Replay was not attempted because the producer status was not PASS_COMPLETE_NATIVE_RUP_REPLAY',
                'Any native partial trace remains historical evidence only'],sources_sha256=pins)
        target=H/'data/alternative-review.json'
        assert not target.exists(), 'Preserve previous review'
        target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
        print(json.dumps({k:v for k,v in receipt.items() if k!='sources_sha256'},indent=2))
        return

    rawstats = Counter()
    with (W/'raw.lrat').open('rb') as stream:
        for line in stream:
            parts = line.split()
            assert parts and parts[-1] == b'0'
            if parts[1] == b'd':
                assert int(parts[0]) >= len(e.clauses) and all(int(x)>0 for x in parts[2:-1])
                rawstats.update(deletion_lines=1,deleted_ids=len(parts)-3)
            else:
                z = parts.index(b'0',1)
                assert int(parts[0])>len(e.clauses)
                assert all(int(x)>0 for x in parts[z+1:-1]), 'RAT or nonpositive hint in raw LRAT'
                rawstats.update(deduction_lines=1,hints=len(parts)-z-2)
    conversion_structure['raw_lrat_structure'] = dict(rawstats)
    conversion_structure['deletion_policy'] = 'Trimmed proof contains no deletion commands; retained clauses are sound persistent consequences. Original core identities and every positive-hint step are checked independently.'
    ids = read(W/'core-ids.json')
    assert ids == sorted(set(ids)) and len(ids) == native['core_clauses']
    assert all(1<=i<=len(e.clauses) for i in ids)
    assert dimacs(e.nv,[e.clauses[i-1] for i in ids]) == (W/'core.cnf').read_bytes()
    triples = [(i,e.clauses[i-1],e.tags[i-1]) for i in ids]
    # Separate replay implementation: collect literals known true, then scan each hint.
    database = {i:e.clauses[i-1] for i in ids}
    used = set()
    stats = Counter()
    previous = len(e.clauses)
    proof_ids = set()
    with (W/'trimmed.lrat').open('rb') as trimmed, (W/'raw.lrat').open('rb') as raw:
        rawline = raw.readline()
        for line in trimmed:
            while rawline and rawline != line:
                rawline = raw.readline()
            assert rawline == line, 'Trimmed deduction is not an unchanged ordered raw deduction'
            rawline = raw.readline()
            row = list(map(int,line.split()))
            z = row.index(0,1)
            cid,clause,hints = row[0],row[1:z],row[z+1:-1]
            assert row[-1] == 0 and cid>previous and all(0<abs(x)<=e.nv for x in clause)
            assert all(0<h<cid and h in database for h in hints)
            previous = cid
            proof_ids.add(cid)
            truth = {-x for x in clause}
            conflict = any(-x in truth for x in truth)
            for hint in hints:
                if hint<=len(e.clauses):
                    used.add(hint)
                if conflict:
                    continue
                hc = database[hint]
                assert not any(x in truth for x in hc), (cid,hint,'satisfied hint')
                unresolved = {x for x in hc if -x not in truth}
                assert len(unresolved)<=1, (cid,hint,'nonunit hint')
                if unresolved:
                    truth.update(unresolved)
                else:
                    conflict = True
            assert conflict, cid
            database[cid] = clause
            stats.update(deductions=1,hints=len(hints),derived_literal_occurrences=len(clause))
            stats['maximum_step_hints'] = max(stats['maximum_step_hints'],len(hints))
    assert not database[previous] and used == set(ids)
    assert (stats['deductions'],stats['hints']) == (native['lemmas'],native['hints'])
    assert stats['hints'] <= native['replay_hint_limit']
    conversion_structure['independent_rup_replay'] = True
    family = lambda t: 'old/'+t[1][0] if t[0]=='old' else t[0]
    cutlens = Counter(len(c) for c,t in zip(e.clauses,e.tags) if t==('old',('cut',)))
    assert set(cutlens) == {4,6}
    pin(old['source'],old['source_sha256'])
    for p,digest in list(pins.items()):
        assert sha(p) == digest, ('Source changed during review',p)
    pin(Path(__file__))
    pin(H/'data/native-alternative.json')
    pin(H/'data/old-share20-observation.json')
    receipt = dict(status='PASS_INDEPENDENT_ALTERNATIVE_CORE_AND_RUP_REVIEW',
        recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-start,native_status=native['status'],conversion_structure=conversion_structure,
        variables=e.nv,clauses=len(e.clauses),base_clauses=len(base.clauses),ball_vertices=len(e.ball),
        core_clauses=len(ids),core_id_min=min(ids),core_id_max=max(ids),core_triples_sha256=hashlib.sha256(json.dumps(triples,separators=(',',':')).encode()).hexdigest(),
        full_tag_counts=dict(sorted(Counter(map(family,e.tags)).items())),core_tag_counts=dict(sorted(Counter(family(e.tags[i-1]) for i in ids).items())),
        ordinary_cycle_clause_counts=dict(cutlens),added_cycle_cuts=0,endpoint_budget=2,alpha_bounds=[[0,21]]*5,
        share=dict(centres=5,incidences=35,distinct_neighbor_vertices=len(set(x[3] for x in incidences)),empty_square_variables=980,cap_literals=630,totalizers=71,resolution=12,cap=17,target=18,duplicate_semantic_incidence_meanings_preserved=True),
        replay=dict(stats,final_empty_clause=True,original_clause_ids_preserved=True,literal_multiplicity_preserved=True,trimmed_lines_are_unchanged_ordered_raw_lines=True),
        checks=['All saved native/source/executable pins matched','Exact reconstructed CNF byte equality','Independent untagged base encoding matched','Complete meanings and tags matched','All totalizer clause families reconstructed from register meanings','All share thresholds, neighborhood geometry and cap independently reconstructed','Every original core clause and tag checked','Independent complete positive-hint RUP replay','Old7302 completion record and selected143 evidence unchanged before and after'],
        no_solver_lean_or_graph_invocation=True,
        semantic_obligations=['Kernel replay of the complete core contradiction','Actual induced-path assignment satisfies degree, endpoint and ordinary four/six-cycle clauses','Integer share interpretation and cap saturation with repeated incidences preserved','Coordinate relabelling and reversed-path transport when applying reverse orientation'],
        limitations=['Finite Boolean contradiction only; no actual-snake share theorem claimed','No parity, total-length, far-endpoint, fixed-alpha or extra cycle-cut assumptions','Old7302 completion record and selected143 evidence checked; no entire-directory before/after claim','This audit does not assess partial Lean receipts'],
        sources_sha256=pins)
    target = H/'data/alternative-review.json'
    assert not target.exists(), 'Preserve previous review'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in receipt.items() if k!='sources_sha256'},indent=2))

if __name__ == '__main__':
    main()
