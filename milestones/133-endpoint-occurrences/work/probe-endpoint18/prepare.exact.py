"""Prepare one endpoint18 query without changing the frozen endpoint0 experiment."""
from pathlib import Path
import ast, copy, hashlib, json

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
W = H/'work/probe-endpoint18'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
def write_json(path,value):
    with path.open('x',encoding='utf-8') as out:
        json.dump(value,out,indent=2)
        out.write('\n')

def main():
    assert not W.exists()
    source = H/'scripts/probe.py'
    text = source.read_text(encoding='utf-8')
    changes = [
        ('endpoint0','endpoint18'),
        ('ACTUAL_ODD_ENDPOINT0_PATH_CHECKED','ACTUAL_ODD_ENDPOINT18_PATH_CHECKED'),
        ("H/'data/preparation.json'","H/'work/probe-endpoint18/preparation.json'"),
        ("H/'data/encoding.json'","H/'work/probe-endpoint18/encoding.json'"),
        ('assert 0 in flags and assignment[513]','assert 18 in flags and assignment[531]'),
        ('assert path[0] == 0 and r == 0 and 0 in flags','assert 18 in flags and {path[0],path[-1]} == flags'),
        ('Independently checked odd induced path starting at window0.',
         'Independently checked odd induced path containing the fixed012032 window and having endpoint18.'),
        ("H/'scripts/prepare.py'","H/'scripts/prepare_external.py'"),
        ('SNAKE133_PARENT_PID','SNAKE133_EXTERNAL_PARENT_PID'),
        ("== {'base.cnf'}, 'Preserve the first probe; no automatic restart'",
         "== {'base.cnf','encoding.json','preparation.json'}, 'Preserve this single probe; no automatic restart'"),
        ("if p.is_file() and p.name!='run-status.json'",
         "if p.is_file() and p.name not in ['run-status.json','probe.lock']"),
        (r"'probe\\.py'",r"'probe(?:_external)?\\.py'")]
    for old,new in changes:
        assert old in text, 'Frozen source changed: '+old
        text = text.replace(old,new)
    assert 'r == 0' not in text and 'assert path[0] == 0' not in text
    ast.parse(text)
    target = H/'scripts/probe_external.py'
    with target.open('x',encoding='utf-8',newline='\n') as out:
        out.write(text)
    initial_preparation = read(H/'data/preparation.json')
    initial_encoding = read(H/'data/encoding.json')
    initial_cnf = H/'work/probe-endpoint0/base.cnf'
    assert sha(initial_cnf) == initial_preparation['cnf_sha256'] == initial_encoding['cnf_sha256']
    assert sha(H/'data/encoding.json') == initial_preparation['encoding_sha256']
    for rel,digest in initial_preparation['source_files_sha256'].items():
        assert sha(R/rel) == digest, rel
    rows = initial_cnf.read_text(encoding='ascii').splitlines()
    assert rows[0] == 'p cnf 2426 96539' and rows[-1] == '513 0'
    assert len(initial_encoding['pair_literals']) == 42 and len(set(initial_encoding['pair_literals'])) == 37
    assert initial_encoding['bounds'] == [[0,21]]*5 and initial_encoding['forbidden_endpoint_vertices'] == []
    rows[-1] = '531 0'
    W.mkdir()
    (W/'base.cnf').write_text('\n'.join(rows)+'\n',encoding='ascii',newline='\n')
    assert (W/'base.cnf').read_bytes().rsplit(b'\n',2)[-2] == b'531 0'
    pins = dict(initial_preparation['source_files_sha256'])
    for path in [Path(__file__),target,H/'data/preparation.json',H/'data/encoding.json',initial_cnf]:
        pins[path.relative_to(R).as_posix()] = sha(path)
    metadata = copy.deepcopy(initial_encoding)
    metadata.update(required_endpoint_vertex=18,required_endpoint_unit=[531],cnf_sha256=sha(W/'base.cnf'),
        source_files_sha256=pins,source_input=initial_cnf.relative_to(R).as_posix(),
        source_input_sha256=sha(initial_cnf),changed_original_clause_id=96539,
        changed_original_clause=[513],changed_clause=[531],
        scope='Same full base, pair cap9 and two parity-positive clauses as endpoint0; only its final endpoint unit changes to endpoint18 TRUE. Window position is unrestricted. No common-sphere exclusions or prior experimental cuts.')
    write_json(W/'encoding.json',metadata)
    ast.parse(Path(__file__).read_text(encoding='utf-8'))
    preparation = dict(status='PREPARED_SINGLE_EXTERNAL_ENDPOINT_QUERY_NOT_RUN',
        cnf=(W/'base.cnf').relative_to(R).as_posix(),cnf_sha256=sha(W/'base.cnf'),
        encoding_sha256=sha(W/'encoding.json'),source_files_sha256=pins,
        variables=2426,clauses=96539,pair_occurrences=42,pair_unique_literals=37,required_endpoint_vertex=18,
        exactly_one_input_clause_changed=True,changed_original_clause_id=96539,syntax_checked=True,
        nominal_solver_seconds=45,hard_parent_timeout_seconds=90,conflicts_per_call=1000,minimum_free_bytes=1610612736,
        solver_started=False,lean_started=False,initial_experiment_unchanged=True,
        scope='One bounded external-endpoint sharpness query. A path must be independently checked. Native UNSAT is uncertified and UNKNOWN gives no exclusion. No global bound.')
    write_json(W/'preparation.json',preparation)
    print(json.dumps({k:v for k,v in preparation.items() if k!='source_files_sha256'},indent=2))

if __name__ == '__main__': main()
