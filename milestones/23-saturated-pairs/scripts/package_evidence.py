"""Freeze source provenance and manifest without changing milestone 22."""
import hashlib
import json
from pathlib import Path
import subprocess
import pairs

HERE=pairs.HERE; ROOT=pairs.ROOT

def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
def rel(p): return p.relative_to(HERE).as_posix()

def main():
    assert not (HERE/'evidence-manifest.json').exists(), 'Do not overwrite a frozen manifest.'
    old=ROOT/'milestones/22-empty-square-tradeoff'
    manifest=json.loads((old/'evidence-manifest.json').read_text(encoding='utf-8'))
    for f in manifest['files']:
        p=old/f['path'].replace('\\','/')
        assert pairs.sha(p)==f['sha256'],p
    pairs.write(HERE/'checks/first-round-integrity.json',dict(status='PASS',files=len(manifest['files']),
        source_manifest_sha256=pairs.sha(old/'evidence-manifest.json'),checked=pairs.now(),
        scope='Hash verification only; no old experiment or Lean rebuild rerun'))
    source_refs={
        'origin/main':['README.md','COLLABORATION.md','RESEARCH_LEDGER.md',
            'work/final_lean/Snake9.lean','work/spectral/SquareIncidence.lean',
            'work/spectral/stronger/WindowAutomaton5Sequence.lean',
            'work/spectral/stronger/UpperBound238.lean','outputs/upper-bound-238-audit-linux.log'],
        'origin/research/unconditional-241':['milestones/11-local-ceiling/s0_corner_charge.md',
            'milestones/11-local-ceiling/s0_radius4/README.md',
            'milestones/10-window-aggregate/local-task-236-replays.md'],
        pairs.BASE:['milestones/22-empty-square-tradeoff/README.zh-CN.md',
            'milestones/22-empty-square-tradeoff/lean/TradeoffChecks.lean',
            'milestones/22-empty-square-tradeoff/logs/definitions-attempt2/manifest.json']}
    sources=[]
    for ref,files in source_refs.items():
        commit=git('rev-parse',ref).decode().strip()
        for path in files:
            sources.append(dict(commit=commit,path=path,git_blob_sha256=hashlib.sha256(git('show',f'{commit}:{path}')).hexdigest()))
    pairs.write(HERE/'provenance.json',dict(base_first_round=pairs.BASE,
        packaged_from=git('rev-parse','HEAD').decode().strip(),date=pairs.now(),
        branch_heads=git('for-each-ref','--format=%(refname:short) %(objectname)','refs/remotes/origin').decode().splitlines(),
        sources=sources,scope='Only milestone 23 added; no other branch, worktree, historical proof or evidence modified.'))
    files=[]
    for p in sorted(HERE.rglob('*')):
        if not p.is_file() or 'runtime' in p.parts or '__pycache__' in p.parts: continue
        if p.name in ('status.json','RUNNING.lock','evidence-manifest.json'): continue
        if p.suffix=='.tmp': continue
        files.append(dict(path=rel(p),bytes=p.stat().st_size,sha256=pairs.sha(p)))
    pairs.write(HERE/'evidence-manifest.json',dict(status='PACKAGED',created=pairs.now(),
        git_before_package_commit=git('rev-parse','HEAD').decode().strip(),files=files))
    print('first-round unchanged',len(manifest['files']),'new package files',len(files))

if __name__=='__main__': main()
