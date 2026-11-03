"""Prepare and derive one endpoint0 sharpness probe from the saved132 driver."""
from pathlib import Path
from itertools import combinations
import ast, hashlib, importlib.util, json, sys

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
sys.dont_write_bytecode = True
sys.path[:0] = [str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages'),str(R/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding
from wincert import Encoding
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def write_json(path,value):
    with path.open('x',encoding='utf-8') as out:
        json.dump(value,out,indent=2)
        out.write('\n')

def derive_probe():
    source = R/'milestones/132-odd-pair-endpoint/scripts/probe.py'
    text = source.read_text(encoding='utf-8')
    replacements = [
        ('Bounded native falsification only. Run parent mode; preserve every added cut.',
         'One bounded endpoint0 sharpness test. Preserve every model and validated cycle cut.'),
        ('132-odd-pair-endpoint','133-endpoint-occurrences'),
        ('SNAKE132_PARENT_PID','SNAKE133_PARENT_PID'),
        ("H/'work/base.cnf'","H/'work/probe-endpoint0/base.cnf'"),
        ("metadata['forbidden_common_sphere']","metadata['common_sphere']"),
        ('assert flags.isdisjoint(common)','assert 0 in flags and assignment[513]'),
        ("assert all(not((end^3).bit_count() == (end^6).bit_count() == 2) for end in flags)",
         'assert path[0] == 0 and r == 0 and 0 in flags'),
        ('ACTUAL_ODD_PATH_COUNTEREXAMPLE_CHECKED','ACTUAL_ODD_ENDPOINT0_PATH_CHECKED'),
        ("pair_sum=pair,common_sphere=common,unordered_pairs_checked=pairs_checked,",
         'pair_sum=pair,sharpness_attained=(pair == 9),common_sphere=common,unordered_pairs_checked=pairs_checked,'),
        ('Independently checked native counterexample candidate, with complete vertices for separate review. No Lean check is claimed.',
         'Independently checked odd induced path starting at window0. Pair sum is computed directly; equality9 attains the known odd-length lower bound. No Lean witness check or global bound is claimed.'),
        ("ap.add_argument('--label',default='initial')","ap.add_argument('--label',default='endpoint0',choices=['endpoint0'])"),
        ("lock = H/'work/probe.lock'","lock = folder/'probe.lock'"),
        ('folder.mkdir(exist_ok=False)',"folder.mkdir(exist_ok=True)\n    assert {p.name for p in folder.iterdir()} == {'base.cnf'}, 'Preserve the first probe; no automatic restart'"),
        ('Native bounded falsification. UNSAT is uncertified. UNKNOWN or timeout gives no exclusion.',
         'One bounded sharpness test. Native UNSAT is uncertified. UNKNOWN or timeout gives no exclusion.')]
    for old,new in replacements:
        assert old in text, 'Source pattern changed: '+old
        text = text.replace(old,new)
    assert 'forbidden_common_sphere' not in text
    assert 'COUNTEREXAMPLE' not in text
    ast.parse(text)
    target = H/'scripts/probe.py'
    with target.open('x',encoding='utf-8',newline='\n') as out:
        out.write(text)
    return source

def main():
    (H/'data').mkdir(exist_ok=True)
    folder = H/'work/probe-endpoint0'
    folder.mkdir(parents=True,exist_ok=False)
    targets = [folder/'base.cnf',H/'data/encoding.json',H/'data/preparation.json']
    assert not any(path.exists() for path in targets)
    source = derive_probe()
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
    even = [513+v for v in range(512) if v.bit_count()%2 == 0]
    odd = [513+v for v in range(512) if v.bit_count()%2 == 1]
    assert len(even) == len(odd) == 256
    enc.add(even,('one_even_endpoint',))
    enc.add(odd,('one_odd_endpoint',))
    enc.add([513],('endpoint_at_window_zero',))
    assert len(enc.ctrs) == 2 and enc.ctrs[1][0] == literals and enc.ctrs[1][1] == 9
    assert len(enc.clauses) == pair_end+3 == 96539 and enc.nv == 2426
    raw = (f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode('ascii')
    with targets[0].open('xb') as out: out.write(raw)
    common = [v for v in range(512) if (v^3).bit_count() == (v^6).bit_count() == 2]
    paths = [Path(__file__),H/'scripts/probe.py',source,R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',
             R/'milestones/10-window-aggregate/scripts/wincert.py']
    for module in ['pysat.solvers','pysolvers']:
        spec = importlib.util.find_spec(module)
        assert spec and spec.origin
        paths.append(Path(spec.origin))
    pins = {path.relative_to(R).as_posix():sha(path) for path in paths}
    metadata = dict(window=window,directions=[0,1,2,0,3,2],bounds=bounds,radius=9,centres=[3,6],
        corner_lists=corners,pair_literals=literals,pair_cap=9,occurrence_count=42,unique_literal_count=37,
        pair_counter_index=1,pair_clause_interval_zero_based=[base_clauses,pair_end],
        base_variables=base_variables,base_clauses=base_clauses,variables=enc.nv,clauses=len(enc.clauses),
        even_endpoint_clause=even,odd_endpoint_clause=odd,required_endpoint_vertex=0,required_endpoint_unit=[513],
        common_sphere=common,forbidden_endpoint_vertices=[],variable_meaning=enc.meaning,counters=enc.ctrs,
        cnf_sha256=sha(targets[0]),source_files_sha256=pins,additional_cycle_cuts=[],
        scope='Full existing base, pair cap9, two parity-positive clauses, and endpoint0 TRUE. No common-sphere endpoint exclusion, no inherited experimental cut and no other candidate condition.')
    write_json(targets[1],metadata)
    ast.parse(Path(__file__).read_text(encoding='utf-8'))
    preparation = dict(status='PREPARED_ONE_SHARPNESS_PROBE_NOT_RUN',cnf=targets[0].relative_to(R).as_posix(),
        cnf_sha256=sha(targets[0]),encoding_sha256=sha(targets[1]),source_files_sha256=pins,
        variables=enc.nv,clauses=len(enc.clauses),pair_occurrences=42,pair_unique_literals=37,
        required_endpoint_vertex=0,full_cube=True,plain_and_tagged_base_equal=True,syntax_checked=True,
        nominal_solver_seconds=45,hard_parent_timeout_seconds=90,conflicts_per_call=1000,minimum_free_bytes=1610612736,
        solver_started=False,lean_started=False,derived_probe_source=source.relative_to(R).as_posix(),
        purpose='Seek an actual odd induced path beginning with012032 whose two counted centres have pair sum9.',
        scope='One bounded sharpness test. A SAT witness requires full independent path and count checks; native UNSAT is uncertified; UNKNOWN or timeout gives no exclusion. No global bound.')
    write_json(targets[2],preparation)
    print(json.dumps({k:v for k,v in preparation.items() if k!='source_files_sha256'},indent=2))

if __name__ == '__main__': main()
