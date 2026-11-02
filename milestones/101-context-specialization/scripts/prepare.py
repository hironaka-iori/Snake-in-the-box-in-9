"""Pin the successful milestone100 environment without copying its objects."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
OLD = ROOT / 'milestones/100-prefix-potential-checker'
for directory in ['data', 'build', 'logs', 'lean', 'audit']:
    (HERE / directory).mkdir(parents=True, exist_ok=True)
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
env = read(OLD / 'data/environment.json')
env['paths'] = [str(HERE / 'build'), *env['paths']]
for p in [OLD / 'data/environment.json', OLD / 'data/checkpoint.json', OLD / 'data/proof-summary.json']:
    env['receipts'][p.relative_to(ROOT).as_posix()] = sha(p)
for p in sorted((OLD / 'data').glob('*-audit.json')):
    r = read(p)
    if r.get('status') != 'PASS_PREFIX_POTENTIAL_MODULE':
        continue
    name = r['module']
    src = OLD / 'lean' / f'{name}.lean'
    obj = OLD / 'build' / f'{name}.olean'
    assert sha(src) == r['source_sha256'] and sha(obj) == r['olean_sha256']
    assert sha(OLD / r['log']) == r['log_sha256']
    env['receipts'][p.relative_to(ROOT).as_posix()] = sha(p)
    env['sources'][src.relative_to(ROOT).as_posix()] = sha(src)
    env['objects'][obj.relative_to(ROOT).as_posix()] = sha(obj)
env['status'] = 'PINNED_REUSED_MILESTONE100_ENVIRONMENT'
(HERE / 'data/environment.json').write_text(json.dumps(env, indent=2) + '\n')
(HERE / '.gitattributes').write_text('* -text\n')
checker = (OLD / 'scripts/check.py').read_text().replace(
    'PASS_PREFIX_POTENTIAL_MODULE', 'PASS_CONTEXT_SPECIALIZATION_MODULE')
(HERE / 'scripts/check.py').write_text(checker)
print('PINNED', len(env['receipts']), 'receipts;', len(env['sources']), 'source hashes')
