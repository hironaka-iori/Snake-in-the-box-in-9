"""Read-only hashes, provenance, lossless archive and independent-check linkage audit."""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
def sha(data): return hashlib.sha256(data).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def portable(p): return Path(p.replace('\\','/'))

def main():
    manifest=read(HERE/'evidence-manifest.json')
    for f in manifest['files']:
        p=HERE/portable(f['path'])
        assert p.stat().st_size==f['bytes'] and sha(p.read_bytes())==f['sha256'],p
    models=read(HERE/'model-archives.json')['files']
    for f in models:
        data=(HERE/portable(f['archive'])).read_bytes()
        assert sha(data)==f['archive_sha256']
        decoded=gzip.decompress(data)
        assert len(decoded)==f['original_bytes'] and sha(decoded)==f['original_sha256']
    count=0
    for p in (HERE/'runs').rglob('P*.json'):
        if '.input.' in p.name or '.failure.' in p.name: continue
        obj=read(p); result=obj['result']
        assert sha(p.with_name(p.stem+'.input.json').read_bytes())==obj['input_sha256']
        assert sha(p.with_suffix('.log').read_bytes())==result['log_sha256']
        model=gzip.decompress(p.with_name(p.stem+'.model.txt.gz').read_bytes())
        assert sha(model)==result['model_sha256']
        code=subprocess.check_output(['git','show',obj['run_git']+':milestones/23-saturated-pairs/scripts/pairs.py'],cwd=ROOT)
        assert sha(code)==obj['code_sha256'],p
        count+=1
    independent=[]
    for p in (HERE/'checks').glob('independent-*.json'):
        obj=read(p)
        code=subprocess.check_output(['git','show',obj['git']+':milestones/23-saturated-pairs/scripts/check_independent.py'],cwd=ROOT)
        assert sha(code)==obj['code_sha256']
        for c in obj['checks']:
            assert c['status']=='PASS'
            assert sha((ROOT/portable(c['file'])).read_bytes())==c['sha256']
            independent.append(c)
    assert count==43 and len(models)==43 and len(independent)==15
    old=ROOT/'milestones/22-empty-square-tradeoff'
    for f in read(old/'evidence-manifest.json')['files']:
        assert sha((old/portable(f['path'])).read_bytes())==f['sha256']
    print(json.dumps(dict(status='PASS',manifest_files=len(manifest['files']),solver_cases=count,
        losslessly_archived_models=len(models),linked_independent_checks=len(independent),
        first_round_preserved=True,evidence='File and provenance audit; not a Lean proof'),indent=2))

if __name__=='__main__': main()
