"""Check a complete regrowth certificate, with bounded concurrency and durable logs.

Unlike a shell pipeline, every failed build produces a nonzero exit status.
The successful aggregate theorem and its transitive axiom audit are mandatory.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / 'work/final_lean'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tag', help='e.g. 144v2')
    ap.add_argument('--workers', type=int, default=2)
    ap.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    args = ap.parse_args()
    if not re.fullmatch(r'\d+(?:v2)?', args.tag) or args.workers < 1:
        ap.error('invalid tag or worker count')
    aggregate = f'DfsBankCert{args.tag}'
    source = LEAN / f'{aggregate}.lean'
    targets = re.findall(r'^import (DfsBankCert\w+)$', source.read_text(), re.M)
    if not targets:
        raise RuntimeError('Aggregate has no certificate dependencies')
    folder = ROOT / 'outputs' / f'dfs-lean-{args.tag}'
    folder.mkdir(parents=True, exist_ok=True)
    files = list(LEAN.glob('*.lean')) + [LEAN / 'lakefile.toml', LEAN / 'lean-toolchain']
    manifest = {'tag': args.tag, 'status': 'RUNNING', 'workers': args.workers,
                'sources_sha256': {f.name: hashlib.sha256(f.read_bytes()).hexdigest() for f in files},
                'completed': {}, 'aggregate': None}
    manifest_path = folder / 'manifest.json'

    def save():
        temporary = manifest_path.with_suffix('.tmp')
        temporary.write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
        temporary.replace(manifest_path)

    def build(module):
        start = time.monotonic()
        log = folder / f'{module}.log'
        with log.open('w', encoding='utf-8') as out:
            r = subprocess.run([args.lake, 'build', module], cwd=LEAN,
                               stdout=out, stderr=subprocess.STDOUT)
        return {'returncode': r.returncode, 'seconds': round(time.monotonic()-start, 3),
                'log': str(log.relative_to(ROOT))}

    save()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(build, target): target for target in targets}
        for future in as_completed(futures):
            target = futures[future]
            try:
                result = future.result()
            except Exception as exc:
                result = {'returncode': -1, 'error': str(exc)}
            manifest['completed'][target] = result
            save()
            print(f"{len(manifest['completed'])}/{len(targets)} {target}: {result['returncode']}", flush=True)
    if any(r['returncode'] for r in manifest['completed'].values()):
        manifest['status'] = 'FAILED'
        save()
        return 1
    manifest['aggregate'] = build(aggregate)
    if manifest['aggregate']['returncode']:
        manifest['status'] = 'FAILED'
        save()
        return 1
    # Run a fresh import audit even if Lake replayed a cached aggregate build.
    audit = LEAN / f'{aggregate}Audit.lean'
    audit.write_text(f'import {aggregate}\n#print axioms Snake9.Dfs.bank_no192_keep{args.tag}\n', encoding='utf-8')
    r = subprocess.run([args.lake, 'env', 'lean', str(audit)], cwd=LEAN,
                       capture_output=True, text=True)
    (folder / 'axioms.log').write_text(r.stdout + r.stderr, encoding='utf-8')
    audits = re.findall(r'depends on axioms: \[([^]]*)\]', r.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    good = r.returncode == 0 and len(audits) == 1 and set(audits[0].split(', ')) <= allowed
    # Detect source changes during a long check rather than claiming an ambiguous build.
    unchanged = all(hashlib.sha256((LEAN/name).read_bytes()).hexdigest() == digest
                    for name, digest in manifest['sources_sha256'].items())
    manifest.update(status='PASSED' if good and unchanged else 'FAILED',
                    axioms=audits, sources_unchanged=unchanged)
    save()
    print(json.dumps({k: manifest[k] for k in ('status', 'axioms', 'sources_unchanged')}), flush=True)
    return 0 if manifest['status'] == 'PASSED' else 1


if __name__ == '__main__':
    sys.exit(main())
