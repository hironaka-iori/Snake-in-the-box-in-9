"""Refresh a manifest without modifying any historical experiment receipt."""
import hashlib,json,pathlib,subprocess
from datetime import datetime,timezone
P=pathlib.Path(__file__).resolve().parents[1]; R=P.parents[1]
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
main=git('rev-parse','origin/main').decode().strip()
up=git('rev-parse','origin/research/unconditional-241').decode().strip()
sources=[]
for rev,files in [(main,['README.md','COLLABORATION.md','RESEARCH_LEDGER.md',
 'work/final_lean/Snake9.lean','work/final_lean/LocalWindowModel.lean','work/spectral/SquareIncidence.lean',
 'work/spectral/stronger/WindowAutomaton5Data.lean','work/spectral/stronger/WindowAutomaton5Sequence.lean',
 'work/spectral/stronger/AggregateWindowConditional.lean','work/spectral/stronger/UpperBound238.lean',
 'outputs/upper-bound-238-audit-linux.log','outputs/upper-bound-238-replay-linux.log',
 'outputs/aggregate-238-chain-175-linux.log','milestones/11-local-ceiling/README.md']),
 (up,['COLLABORATION.md','milestones/11-local-ceiling/s0_corner_charge.md',
      'milestones/11-local-ceiling/s0_radius4/README.md'])]:
    for f in files:sources.append({'commit':rev,'path':f,'git_blob_sha256':sha(git('show',rev+':'+f))})
checks=[]
for f in sorted((P/'runs').glob('20261020-*/*.json')):
    data=json.loads(f.read_text(encoding='utf-8'))
    if 'result' not in data:continue
    inputfile=f.with_name(f.stem+'.input.json')
    assert sha(inputfile.read_bytes())==data['input_sha256']
    script='milestones/22-empty-square-tradeoff/scripts/research.py'
    historical=git('show',data['run_git']+':'+script)
    assert sha(historical)==data['code_sha256'],f
    checks.append({'case':f.stem,'git_code_hash_matches':True,'input_hash_matches':True})
provenance={'base_main':main,'read_only_research_branch':up,'refreshed_utc':datetime.now(timezone.utc).isoformat(),
            'branch_heads':git('for-each-ref','--format=%(refname:short) %(objectname)','refs/remotes/origin').decode().splitlines(),
            'inspected_sources':sources,'historical_run_provenance':checks,
            'scope':'Only milestone 22 added. No modification to historical proofs, other worktrees, main, or paper authors.'}
(P/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
files=[]
for f in sorted(P.rglob('*')):
    if not f.is_file():continue
    rel=f.relative_to(P)
    if any(x in rel.parts for x in ['.build','dashboard-runtime','__pycache__']):continue
    if f.name in ['evidence-manifest.json','RUNNING.lock','status.json']:continue
    files.append({'path':str(rel).replace('\\','/'),'bytes':f.stat().st_size,'sha256':sha(f.read_bytes())})
manifest={'status':'PASS','git_before_package_commit':git('rev-parse','HEAD').decode().strip(),
          'files':files,'historical_receipts_checked':len(checks),
          'scope':'Hashes of source, human proof, raw experiments and retained successful/failed logs; not a mathematical completeness certificate.'}
(P/'evidence-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS',len(files),'files,',len(checks),'historical code/input hashes')
