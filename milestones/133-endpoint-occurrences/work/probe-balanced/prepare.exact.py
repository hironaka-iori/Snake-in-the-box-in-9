"""Prepare one odd-length balanced-pair query with no fixed or forbidden endpoints."""
from pathlib import Path
from itertools import combinations
import ast, hashlib, importlib.util, json, sys

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
W = H/'work/probe-balanced'
sys.dont_write_bytecode = True
sys.path[:0] = [str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages'),str(R/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding
from wincert import Encoding
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def save(path,value):
    with path.open('x',encoding='utf-8') as out:
        json.dump(value,out,indent=2)
        out.write('\n')

def derive_probe():
    source = R/'milestones/132-odd-pair-endpoint/scripts/probe.py'
    text = source.read_text(encoding='utf-8')
    changes = [
        ('Bounded native falsification only. Run parent mode; preserve every added cut.',
         'One bounded balanced-pair test. No endpoint is fixed or forbidden; retain every validated cut.'),
        ('132-odd-pair-endpoint','133-endpoint-occurrences'),
        ('SNAKE132_PARENT_PID','SNAKE133_BALANCED_PARENT_PID'),
        ("H/'work/base.cnf'","H/'work/probe-balanced/base.cnf'"),
        ("H/'data/preparation.json'","H/'work/probe-balanced/preparation.json'"),
        ("H/'data/encoding.json'","H/'work/probe-balanced/encoding.json'"),
        ("metadata['forbidden_common_sphere']","metadata['common_sphere']"),
        ('assert flags.isdisjoint(common)',
         "model_pair = [sum(v not in selected for v in corners) for corners in metadata['corner_lists']]\n            assert min(model_pair) >= 4 and sum(model_pair) <= 9"),
        ('components=components,cycles=cycles))','components=components,cycles=cycles,pair_counts=model_pair))'),
        ('assert all(not((end^3).bit_count() == (end^6).bit_count() == 2) for end in flags)',
         "assert counts[1]['alpha'] >= 4 and counts[3]['alpha'] >= 4\n            assert [counts[1]['alpha'],counts[3]['alpha']] == model_pair"),
        ('ACTUAL_ODD_PATH_COUNTEREXAMPLE_CHECKED','ACTUAL_ODD_BALANCED_PAIR_PATH_CHECKED'),
        ('pair_sum=pair,common_sphere=common,unordered_pairs_checked=pairs_checked,',
         'pair_sum=pair,balanced_pair=model_pair,common_sphere=common,unordered_pairs_checked=pairs_checked,'),
        ('Independently checked native counterexample candidate, with complete vertices for separate review. No Lean check is claimed.',
         'Independently checked actual odd induced path with both counted centres at least4 and pair sum at most9. No Lean witness check or global-bound claim.'),
        ("ap.add_argument('--label',default='initial')","ap.add_argument('--label',default='balanced',choices=['balanced'])"),
        ("lock = H/'work/probe.lock'","lock = folder/'probe.lock'"),
        ('folder.mkdir(exist_ok=False)',"folder.mkdir(exist_ok=True)\n    assert {p.name for p in folder.iterdir()} == {'base.cnf','encoding.json','preparation.json'}, 'Preserve this single probe; no automatic restart'"),
        ("H/'scripts/prepare.py'","H/'scripts/prepare_balanced.py'"),
        ("if p.is_file() and p.name!='run-status.json'","if p.is_file() and p.name not in ['run-status.json','probe.lock']"),
        (r"'probe\\.py'",r"'probe(?:_external|_balanced)?\\.py'")]
    for old,new in changes:
        assert old in text, 'Source changed: '+old
        text = text.replace(old,new)
    assert 'flags.isdisjoint' not in text and 'forbidden_common_sphere' not in text
    assert 'r == 0' not in text
    ast.parse(text)
    target = H/'scripts/probe_balanced.py'
    with target.open('x',encoding='utf-8',newline='\n') as out:
        out.write(text)
    return source,target

def main():
    assert not W.exists()
    source,target = derive_probe()
    W.mkdir()
    window,bounds = [0,1,3,7,6,14,10],[[0,21] for _ in range(5)]
    enc = TaggedEncoding(window,bounds,radius=9)
    plain = Encoding(window,[tuple(b) for b in bounds],radius=9)
    assert enc.clauses == plain.clauses and enc.nv == plain.nv
    assert enc.ball == list(range(512)) and enc.ends == 2
    assert all(enc.var[v] == v+1 and enc.meaning[513+v] == ('e',v) for v in range(512))
    base_clauses,base_variables = len(enc.clauses),enc.nv
    corners = []
    for k in [2,4]:
        used = {(window[k]^window[k-1]).bit_length()-1,(window[k]^window[k+1]).bit_length()-1}
        cs = [window[k]^(1<<a)^(1<<b) for a,b in combinations(range(9),2) if a not in used and b not in used]
        assert len(cs) == len(set(cs)) == 21
        corners.append(cs)
    literals = [-enc.var[v] for cs in corners for v in cs]
    assert len(literals) == 42 and len(set(literals)) == 37
    enc.atmost(literals,9,('pair_counterexample_cap',))
    pair_end = len(enc.clauses)
    lower_counters = []
    for position,cs in zip([2,4],corners):
        first = len(enc.clauses)
        selected = [enc.var[v] for v in cs]
        counter = len(enc.ctrs)
        enc.atmost(selected,17,('lo',position-1))
        lower_counters.append(dict(position=position,absent_lower=4,selected_upper=17,
            literals=selected,counter_index=counter,clause_interval_zero_based=[first,len(enc.clauses)]))
    even = [513+v for v in range(512) if v.bit_count()%2 == 0]
    odd = [513+v for v in range(512) if v.bit_count()%2 == 1]
    assert len(even) == len(odd) == 256
    enc.add(even,('one_even_endpoint',))
    enc.add(odd,('one_odd_endpoint',))
    assert len(enc.ctrs) == 4 and enc.ctrs[1][0] == literals and enc.ctrs[1][1] == 9
    assert enc.clauses[-2:] == [even,odd]
    assert enc.nv == 3140 and len(enc.clauses) == 97972
    raw = (f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode('ascii')
    (W/'base.cnf').write_bytes(raw)
    paths = [Path(__file__),target,source,R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',
             R/'milestones/10-window-aggregate/scripts/wincert.py']
    for module in ['pysat.solvers','pysolvers']:
        spec = importlib.util.find_spec(module)
        assert spec and spec.origin
        paths.append(Path(spec.origin))
    pins = {path.relative_to(R).as_posix():sha(path) for path in paths}
    metadata = dict(window=window,directions=[0,1,2,0,3,2],bounds=bounds,radius=9,centres=[3,6],
        corner_lists=corners,pair_literals=literals,pair_cap=9,occurrence_count=42,unique_literal_count=37,
        pair_counter_index=1,pair_clause_interval_zero_based=[base_clauses,pair_end],lower_counters=lower_counters,
        base_variables=base_variables,base_clauses=base_clauses,variables=enc.nv,clauses=len(enc.clauses),
        even_endpoint_clause=even,odd_endpoint_clause=odd,required_endpoint_vertices=[],forbidden_endpoint_vertices=[],
        common_sphere=[v for v in range(512) if (v^3).bit_count() == (v^6).bit_count() == 2],
        variable_meaning=enc.meaning,counters=enc.ctrs,cnf_sha256=sha(W/'base.cnf'),source_files_sha256=pins,
        additional_cycle_cuts=[],scope='Full existing base with five unrestricted bounds, pair cap9, two explicit selected-corner caps17 imposing alpha2>=4 and alpha4>=4, and two parity-positive endpoint clauses. No endpoint fixed or forbidden, and no inherited experimental cuts.')
    save(W/'encoding.json',metadata)
    ast.parse(Path(__file__).read_text(encoding='utf-8'))
    preparation = dict(status='PREPARED_SINGLE_BALANCED_QUERY_NOT_RUN',cnf=(W/'base.cnf').relative_to(R).as_posix(),
        cnf_sha256=sha(W/'base.cnf'),encoding_sha256=sha(W/'encoding.json'),source_files_sha256=pins,
        variables=enc.nv,clauses=len(enc.clauses),pair_occurrences=42,pair_unique_literals=37,
        lower_counts=[4,4],fixed_or_forbidden_endpoints=False,plain_and_tagged_base_equal=True,syntax_checked=True,
        nominal_solver_seconds=45,hard_parent_timeout_seconds=90,conflicts_per_call=1000,minimum_free_bytes=1610612736,
        solver_started=False,lean_started=False,
        tested_hypothesis='For odd length and a fitting012032 window, alpha2>=4 and alpha4>=4 imply alpha2+alpha4>=10.',
        scope='One bounded native falsification query only. SAT requires independent path/count checks. Native UNSAT is uncertified; UNKNOWN or timeout gives no exclusion. No global bound.')
    save(W/'preparation.json',preparation)
    print(json.dumps({k:v for k,v in preparation.items() if k!='source_files_sha256'},indent=2))

if __name__ == '__main__': main()
