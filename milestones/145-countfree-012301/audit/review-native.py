"""Read-only provenance and input audit. No proof replay, conversion, or solver."""
from pathlib import Path
from collections import Counter, defaultdict
import datetime, gzip, hashlib, itertools, json, re, sys, time, types

sys.dont_write_bytecode = True
H = Path(__file__).resolve().parents[1]
R = H.parents[1]
OLD = R/'milestones/72-four-count-proof-closure/critical-current'
CAT = R/'milestones/73-countfree-share-catalogue'
pins = {}

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''): h.update(b)
    return h.hexdigest()

def pin(p, expected=None):
    p = Path(p); value = sha(p)
    if expected is not None: assert value == expected, str(p)
    pins[p.as_posix()] = value
    return value

def read(p):
    return json.loads(Path(p).read_text(encoding='utf-8-sig'))

def parse(raw):
    lines = raw.decode('ascii').splitlines()
    header = next(x.split() for x in lines if x.startswith('p '))
    clauses = [list(map(int,x.split())) for x in lines if x and x[0] not in 'pc']
    assert all(x[-1] == 0 for x in clauses)
    clauses = [x[:-1] for x in clauses]
    assert int(header[3]) == len(clauses)
    return int(header[2]), clauses

def main():
    started = time.monotonic()
    metadata_path = OLD/'data/pysat3-cap15-certificate.json'
    meta = read(metadata_path)
    assert meta['status'] == 'NATIVE_DRAT_VERIFIED'
    assert meta['directions'] == [0,1,2,3,0,1]
    assert meta['shape_index'] == 3 and meta['bounds'] == [[0,21]]*5 and meta['cap'] == 15
    assert len(meta['cycle_cuts']) == 16
    assert meta['cycle_cuts'] == read(OLD/'data/cap15-cyclic-control.json')['cycles']
    assert not (CAT/'cases/case7303').exists()
    portfolio = read(OLD/'data/portfolio.json')['selected'][3]
    assert portfolio['certificate'] == metadata_path.name and portfolio['required_share'] == 16
    assert portfolio['drat_bytes'] == 106351672
    checkpoint = next(x for x in read(CAT/'data/checkpoint.json')['cases'] if x['case_number'] == 7303)
    assert checkpoint['status'] == 'NATIVE_CERTIFICATE_ONLY'
    for p in [metadata_path, OLD/'data/portfolio.json', OLD/'data/archive.json',
              OLD/'data/native-audit.json', OLD/'data/cap15-cyclic-control.json',
              OLD/'data/all-six-direction-shapes.json', OLD/'scripts/certify_pysat16.py',
              OLD/'scripts/audit_native.py', OLD/'scripts/archive_evidence.py',
              OLD/'scripts/select_portfolio.py', OLD/'scripts/prepare_lean.py',
              CAT/'scripts/bootstrap_case.py', CAT/'data/checkpoint.json',
              CAT/'data/required-shares.json',
              CAT/'adapter/lean/ConditionalCatalogueDispatch.lean', Path(__file__)]: pin(p)
    archives = {x['path']:x for x in read(OLD/'data/archive.json')['native']}
    files = {}
    raw_small = {}
    for ext,key in [('cnf','cnf_sha256'),('core.cnf','core_sha256'),('drat','drat_sha256')]:
        name = 'pysat3-cap15.'+ext
        compressed = OLD/'certificates'/(name+'.gz')
        original = OLD/'build'/name
        a = archives['certificates/'+name+'.gz']
        pin(compressed,a['sha256']); pin(original,meta[key])
        digest = hashlib.sha256(); size = 0; tail = b''
        with gzip.open(compressed,'rb') as f:
            for b in iter(lambda:f.read(1048576),b''):
                digest.update(b); size += len(b); tail = (tail+b)[-128:]
        assert digest.hexdigest() == meta[key] == a['raw_sha256'] and size == a['raw_bytes']
        files[ext] = dict(original=original.as_posix(),archive=compressed.as_posix(),
            raw_bytes=size,compressed_bytes=compressed.stat().st_size,raw_sha256=digest.hexdigest(),
            archive_sha256=pins[compressed.as_posix()],final_text=tail.decode('ascii') if ext=='drat' else None)
        if ext!='drat': raw_small[ext] = original.read_bytes()
    # Stub any solver construction before importing encoding-only modules.
    def forbidden(*args,**kwargs): raise AssertionError('Solver construction forbidden')
    pysat = types.ModuleType('pysat'); solvers = types.ModuleType('pysat.solvers')
    solvers.Cadical153 = forbidden; pysat.solvers = solvers
    sys.modules.update({'pysat':pysat,'pysat.solvers':solvers})
    sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
    from tagged_share import TaggedShare
    from gen_lean_sat import TaggedEncoding
    from wincert import Encoding
    for name in ['tagged_share','gen_lean_sat','wincert']: pin(sys.modules[name].__file__)
    e = TaggedShare(meta['directions'],[(0,21)]*5,15,M=12)
    assert e.M == 12 and e.cap == 15 and e.window == [0,1,3,7,15,14,12]
    base = TaggedEncoding(e.window,[(0,21)]*5,radius=4,ends=2)
    independent = Encoding(e.window,[(0,21)]*5,radius=4,ends=2)
    assert base.clauses == independent.clauses == e.clauses[:len(base.clauses)]
    assert len(base.ctrs) == 1 and base.ctrs[0][1:] == (2,('ends',))
    assert e.ball == [v for v in range(512) if min((v^c).bit_count() for c in e.window[1:-1]) <= 4]
    assert set(e.meaning)|set(e.smeaning) == set(range(1,e.nv+1))
    assert not set(e.meaning)&set(e.smeaning)
    before_cuts = len(e.clauses)
    cycle_checks = []
    for cyc in meta['cycle_cuts']:
        assert len(cyc) == len(set(cyc)) == 8 and all(v in e.var for v in cyc)
        adj = {v:[w for w in cyc if (v^w).bit_count()==1] for v in cyc}
        assert all(len(ns)==2 for ns in adj.values())
        seen = set(); todo = [cyc[0]]
        while todo:
            v = todo.pop()
            if v not in seen: seen.add(v); todo.extend(adj[v])
        assert seen == set(cyc)
        e.add([-e.var[v] for v in cyc],('old',('cut',)))
        cycle_checks.append(dict(vertices=cyc,clause_id=len(e.clauses),connected=True,degrees=[2]*8))
    nv, full = parse(raw_small['cnf'])
    assert (nv,len(full)) == (11378,92656) and e.nv == nv and full == e.clauses
    generated = (f'p cnf {nv} {len(full)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in full)).encode()
    assert raw_small['cnf'].replace(b'\r\n',b'\n') == generated
    # Independently reconstruct every share totalizer and share implication.
    bytag = defaultdict(list)
    for c,t in zip(e.clauses,e.tags): bytag[t].append(c)
    registers = {m:v for v,m in e.smeaning.items() if m[0]=='t'}
    roots = {}
    for ti,(lits,kind) in enumerate(e.tots):
        up = kind[0]!='nb'; down = kind[0]=='nb'; limit = 16 if kind[0]=='cap' else len(lits)
        ups,downs = [],[]
        def tree(lo,hi):
            if hi-lo==1: return [None,lits[lo]]
            mid=(lo+hi)//2; left,right=tree(lo,mid),tree(mid,hi)
            out=[None]+[registers[('t',ti,lo,hi,j)] for j in range(1,min(hi-lo,limit)+1)]
            for a in range(len(left)):
                for b in range(len(right)):
                    if up and 0<a+b<len(out): ups.append([out[a+b]]+([-left[a]] if a else [])+([-right[b]] if b else []))
                    if down and a+b+1<len(out): downs.append([-out[a+b+1]]+([left[a+1]] if a+1<len(left) else [])+([right[b+1]] if b+1<len(right) else []))
            return out
        roots[ti]=tree(0,len(lits))
        assert ups==bytag[('totUp',ti)] and downs==bytag[('totDown',ti)]
    caplits,capkind=e.tots[-1]
    assert len(e.tots)==71 and capkind[0]=='cap' and len(caplits)==len(set(caplits))==560
    incidences=[]; empties=[]
    for ci,c in enumerate(e.window[1:-1],1):
        used={(c^e.window[ci-1]).bit_length()-1,(c^e.window[ci+1]).bit_length()-1}
        for k in range(9):
            if k in used: continue
            q=c^(1<<k); j=len(incidences); incidences.append((ci,c,k,q))
            es,ek=e.tots[2*j]; ns,nk=e.tots[2*j+1]
            assert ek==('emp',q) and nk==('nb',q)
            pairs=[(a,b) for a,b in itertools.combinations(range(9),2) if k not in (a,b)]
            assert len(es)==len(pairs)==28
            for var,(a,b) in zip(es,pairs):
                assert e.smeaning[var]==('sq',q,a,b)
                vs=[q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)]
                assert all(v in e.var for v in vs)
                empties.append([e.var[v] for v in vs]+[var])
            assert ns==[e.var[q^(1<<a)] for a in range(9)]
            implications=[]
            for t,var in enumerate(caplits[16*j:16*j+16],1):
                assert e.smeaning[var]==('u',q,t)
                for degree in range(1,10):
                    need=(t*degree+11)//12
                    implications.append([var,-roots[2*j][need]]+([roots[2*j+1][degree+1]] if degree<9 else []))
            assert implications==bytag[('shareCl',2*j,2*j+1)]
    assert len(incidences)==35 and empties==bytag[('emptyE',)]
    assert bytag[('shareCap',70)]==[[-roots[70][16]]]
    _, core = parse(raw_small['core.cnf'])
    lookup=defaultdict(list)
    for i,c in enumerate(full,1): lookup[tuple(sorted(c))].append(i)
    core_ids=[]; core_tags=[]; ambiguous=[]
    for c in core:
        candidates=lookup[tuple(sorted(c))]
        assert candidates and len({e.tags[i-1] for i in candidates})==1
        core_ids.append(candidates[0]);core_tags.append(e.tags[candidates[0]-1])
        if len(candidates)>1: ambiguous.append(candidates)
    assert Counter(tuple(sorted(c)) for c in core) <= Counter(tuple(sorted(c)) for c in full)
    assert len(core)==12977 and Counter(t[0] for t in core_tags)==meta['core_clause_tags']
    used_added=[x for x in cycle_checks if x['clause_id'] in core_ids]
    log=OLD/'logs/pysat3-cap15-verify.log';pin(log)
    text=log.read_text(); assert 's VERIFIED' in text and '0 RAT lemmas' in text
    assert '31017505 resolution steps' in text and '285541 of 554437 lemmas' in text
    historical=next(x for x in read(OLD/'data/native-audit.json')['certificates'] if x['certificate']==metadata_path.name)
    assert historical['core_clauses']==len(core) and historical['verifier_log_sha256']==pins[log.as_posix()]
    pin(R/'work/share-wheels/drat-trim.exe',read(OLD/'data/native-audit.json')['drat_checker_sha256'])
    for name,digest in read(OLD/'data/native-audit.json')['encoder_sources'].items():pin(R/name,digest)
    for p,digest in pins.items(): assert sha(p)==digest,('Changed during audit',p)
    semantics=dict(meaning=e.meaning,smeaning=e.smeaning,ctrs=e.ctrs,tots=e.tots,tags=e.tags)
    receipt=dict(status='PASS_INPUT_CORE_AND_ARCHIVE_RECONSTRUCTION_NO_NEW_PROOF_REPLAY',
        recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-started,
        native_status_recorded=meta['status'],parameters=dict(directions=meta['directions'],bounds=meta['bounds'],
            cap=15,target_share=16,resolution=12,radius=4,endpoint_budget=2,window=e.window),
        variables=nv,clauses=len(full),base_clauses=len(base.clauses),ball_vertices=len(e.ball),
        before_added_cycles=before_cuts,added_cycles=cycle_checks,used_added_cycles=used_added,
        core_clauses=len(core),core_original_clause_ids=core_ids,duplicate_clause_identity_candidates=ambiguous,
        core_family_counts=dict(Counter(t[0] for t in core_tags)),
        core_detailed_family_counts=dict(Counter(t[0]+'/'+t[1][0] if t[0]=='old' else t[0] for t in core_tags)),
        active_core_variables=len({abs(x) for c in core for x in c}),
        reconstructed_meanings_sha256=hashlib.sha256(json.dumps(semantics,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        source_files_sha256=pins,certificate_files=files,
        historical_verifier=dict(core_lemmas=285541,input_lemmas=554437,resolution_steps=31017505,rat_lemmas=0,seconds=24.485),
        independently_checked=['Full original clauses and ordered literals','Independent untagged base encoding',
            'Every totalizer and share implication','Every extra eight-cycle is connected and degree two',
            'Core submultiset and exact original clause identities/tags','All original and gzip content hashes'],
        not_performed=['DRAT or LRAT replay','DRAT-to-LRAT conversion','Solver invocation','Lean compilation','Graph evaluation'],
        limitations=['No matching LRAT found; no bounded native RUP replay performed',
            'Historical 31,017,505 resolution steps are not a measured LRAT hint count',
            'Actual-snake semantics, coordinate relabelling and reversal remain separate Lean obligations'])
    dest=H/'data/native-review.json';assert not dest.exists();dest.write_text(json.dumps(receipt,indent=2)+'\n')
    located=dict(status='LOCATED_EXACT_NATIVE_DRAT_INPUT_LRAT_UNAVAILABLE',
        metadata_path=metadata_path.as_posix(),metadata_sha256=pins[metadata_path.as_posix()],
        certificate_files=files,parameters=receipt['parameters'],added_eight_cycle_cuts=16,
        case7303_folder_exists=False,matching_lrat_found=False,
        search_scope='Filename search under milestones for pysat3, share7303, 7303, and 012301; authoritative72/73 metadata and generation scripts inspected',
        historical_verifier=receipt['historical_verifier'],review_path=dest.as_posix(),review_sha256=sha(dest),
        conclusion='Existing DRAT evidence and input provenance verified; no fresh proof replay or actual-snake theorem claimed')
    loc=H/'data/native-locate.json';assert not loc.exists();loc.write_text(json.dumps(located,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['source_files_sha256','core_original_clause_ids','added_cycles','used_added_cycles','certificate_files']},indent=2))
    print('used_added_cycles',len(used_added),'files', {x:sha(H/x) for x in ['audit/review-native.py','data/native-review.json','data/native-locate.json']})

if __name__=='__main__':main()
