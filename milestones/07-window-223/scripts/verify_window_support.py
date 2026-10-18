"""Check the geometric support modules against a completed pinned dependency build.

The upstream source-only build is reused. This runner rebuilds all five listed
support modules, records their hashes, and rejects nonstandard theorem axioms.
It does not assert that the complete geometric-to-CNF interpretation is finished.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mathlib', type=Path, required=True)
    parser.add_argument('--dependency-build', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[3]
    milestone = root / 'milestones/07-window-223'
    output_parent = milestone / 'lean/generated/geometry'
    output_parent.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='support-', dir=output_parent))
    dependency = args.dependency_build.resolve()
    upstream_path = dependency / 'manifest.json'
    upstream = json.loads(upstream_path.read_text(encoding='utf-8'))
    assert upstream['status'] == 'success', 'Upstream verification did not pass'
    for rel, sha in upstream['source_sha256'].items():
        if rel.endswith('.lean'):
            assert digest(root / rel) == sha, f'Changed dependency source: {rel}'
    mathlib = args.mathlib.resolve()
    pin = subprocess.check_output(['git', '-c', f'safe.directory={mathlib.as_posix()}',
        '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
    assert pin == upstream['mathlib_commit'], 'Different mathlib revision'
    lean, lake = shutil.which('lean'), shutil.which('lake')
    assert lean and lake, 'Put Lean 4.19.0 on PATH'
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.19.0' in version
    sources = [root / 'work/spectral/CycleExclusion.lean'] + [
        milestone / 'lean' / (name + '.lean') for name in
        ['WindowCornerData', 'WindowGeometry', 'WindowCycles', 'WindowSingletons']]
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [
        output, dependency / 'core/.lake/build/lib/lean', dependency]))
    record = {'status': 'running', 'started_utc': datetime.now(timezone.utc).isoformat(),
        'lean_version': version, 'mathlib_commit': pin, 'build_directory': str(output),
        'upstream_manifest_sha256': digest(upstream_path),
        'scope': 'Five rebuilt support modules; reused checked upstream dependencies. '
                 'No complete window exclusion or new global upper bound.', 'steps': []}
    manifest = milestone / 'data/geometry-support-manifest.json'
    def save():
        manifest.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    save()
    try:
        for source in sources:
            print('Checking ' + source.stem, flush=True)
            before = digest(source)
            command = [lake, 'env', 'lean', '--root=' + str(source.parent),
                '-o', str(output / (source.stem + '.olean')), str(source)]
            result = subprocess.run(command, cwd=mathlib, env=env,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding='utf-8', errors='replace')
            log = milestone / 'logs' / (source.stem + '-support-build.log')
            log.write_text(result.stdout, encoding='utf-8')
            assert digest(source) == before, 'Source changed during checking'
            record['steps'].append({'source': source.relative_to(root).as_posix(),
                'source_sha256': before, 'exit_code': result.returncode,
                'log': log.relative_to(root).as_posix()})
            save()
            assert result.returncode == 0, result.stdout
            assert 'sorryAx' not in result.stdout and "declaration uses 'sorry'" not in result.stdout
            audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout)
            empty = re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)
            assert len(audits) + len(empty) == source.read_text(encoding='utf-8').count('#print axioms ')
            parsed = {name: [a.strip() for a in axioms.split(',') if a.strip()]
                      for name, axioms in audits}
            parsed.update({name: [] for name in empty})
            assert all(set(ax) <= {'propext', 'Classical.choice', 'Quot.sound'}
                       for ax in parsed.values())
            record['steps'][-1]['axiom_audits'] = parsed
            record['steps'][-1]['olean_sha256'] = digest(output / (source.stem + '.olean'))
            save()
        record.update(status='success', completed_utc=datetime.now(timezone.utc).isoformat())
    except BaseException as error:
        record.update(status='failed', error=str(error))
        raise
    finally:
        save()
    print('All five support modules passed.', flush=True)


if __name__ == '__main__':
    main()
