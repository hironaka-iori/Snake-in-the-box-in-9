"""Audit the small proofs and freeze only completed rows of the live replay."""
from pathlib import Path
import datetime,hashlib,json,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7305'
read=lambda p:json.loads(p.read_text())
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
for folder in ['data','upstream','replay-snapshot/logs']:(HERE/folder).mkdir(parents=True,exist_ok=True)
audits=[]
for sub,module in [('lookup','GraphShareLookup'),('numeric','CountStateCode')]:
    out=HERE/sub;a=read(out/'data/proof-audit.json');assert a['exit_code']==0 and a['status'].startswith('PASS_')
    assert sha(out/'lean'/(module+'.lean'))==a['source_sha256']
    assert sha(out/'build'/(module+'.olean'))==a['olean_sha256']
    assert sha(out/'logs'/(module+'.log'))==a['log_sha256']
    audits+=a['theorem_audits']
h=read(HERE/'history/data/proof-audit.json');assert h['status']=='PASS_EXACT_HISTORY'
assert sha(HERE/'history/data/source-provenance.json')==h['provenance_sha256']
for row in read(HERE/'history/data/source-provenance.json')['sources']:assert sha(Path(row['path']))==row['sha256']
for r in h['records']:
    assert r['exit_code']==0
    assert sha(HERE/'history/lean'/(r['module']+'.lean'))==r['source_sha256']
    assert sha(HERE/'history/build'/(r['module']+'.olean'))==r['olean_sha256']
    assert sha(HERE/'history/logs'/(r['module']+'.log'))==r['log_sha256']
    audits+=r['theorems']
assert len(audits)==39
for r in audits:assert set(r['axioms'])<={'propext','Classical.choice','Quot.sound'}
for p in HERE.rglob('*.lean'):
    if 'build' not in p.relative_to(HERE).parts:
        assert not re.search(r'\b(sorry|admit|native_decide)\b',p.read_text())

# Read the whole JSON atomically enough to tolerate the driver's brief rewrite.
record_path=CASE/'logs/completion-record.json'
for attempt in range(5):
    try:
        raw=record_path.read_bytes();record=json.loads(raw);break
    except json.JSONDecodeError:
        if attempt==4:raise
        time.sleep(.1)
rows=[]
for row in record['records']:
    if row['exit_code']!=0:continue
    name=row['module'];src=CASE/'lean'/(name+'.lean');obj=Path(record['build'])/(name+'.olean')
    log=CASE/'logs'/(name.replace('/','-')+'.log')
    assert sha(src)==row['source_sha256']
    for dep,digest in row.get('dependencies',{}).items():assert sha(CASE/'lean'/(dep+'.lean'))==digest
    assert obj.exists() and log.exists()
    txt=log.read_text();assert 'error:' not in txt and 'sorryAx' not in txt
    target=HERE/'replay-snapshot/logs'/log.name;shutil.copyfile(log,target)
    rows.append(dict(row,object_sha256=sha(obj),log_sha256=sha(target),snapshot_log=target.relative_to(HERE).as_posix()))
selection=read(CASE/'data/lrat-slice-selection.json')
assert sha(CASE/'certificates/share7305.lrat')==selection['selected_lrat_sha256']
snapshot=dict(status='PARTIAL_REPLAY_COMPLETED_MODULES_ONLY',observed_record_sha256=hashlib.sha256(raw).hexdigest(),
              selected_lrat_sha256=selection['selected_lrat_sha256'],records=rows,
              completed_check_modules=sum('/Check' in r['module'] for r in rows),
              completed_data_modules=sum('/Data' in r['module'] for r in rows),
              scope='Frozen successful rows and matching source/object/log hashes from the live completion record. The final refutation and local share theorem remain pending.')
(HERE/'replay-snapshot/record.json').write_text(json.dumps(snapshot,indent=2)+'\n')

branch='origin/research/unconditional-241'
rev=subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',branch],cwd=ROOT,text=True).strip()
assert rev=='1e0ebb95954cc70f9edf59268b5a36df3f616422','Review changed contributor branch before repinning'
pinned=[]
for rel,name in [('handoff/README.md','contributor-handoff.md'),('handoff/PROMPT.md','contributor-continuation.md')]:
    dest=HERE/'upstream'/name;dest.write_bytes(subprocess.check_output(['git','-c','core.commitGraph=false','show',rev+':'+rel],cwd=ROOT))
    pinned.append(dict(source=rel,snapshot=dest.relative_to(HERE).as_posix(),sha256=sha(dest)))
repo=dict(branch=branch,commit=rev,files=pinned,
          finding='Documentation-only update since cd0c90fd;235 remains contributor-checked and234 production certificates/table shards remain unfinished. No branch merge or stronger bound inferred.')
(HERE/'data/repository-check.json').write_text(json.dumps(repo,indent=2)+'\n')
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7305*' } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
raw=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
live=json.loads(raw) if raw else [];live=live if isinstance(live,list) else [live]
paper=ROOT/'paper/snake9_research.tex';mirror=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(mirror)=='d422a0b3dea2c2e81cb2d63294c14ff37b2237447faf5fca193ee2664951d341'
out=dict(status='CHECKED_HISTORY_LOOKUP_AND_NUMERIC_COMPONENTS_GLOBAL_PROOF_PENDING',
         recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),new_theorem_audits=audits,
         unconditional_edge_interval=[191,235],conditional_target=234,
         completed_stronger_share_cases=[7300,7304,7306],case7305_final_theorem=False,
         replay_snapshot_sha256=sha(HERE/'replay-snapshot/record.json'),
         replay_completed_modules=len(rows),replay_check_modules=snapshot['completed_check_modules'],
         observed_processes=live,tool_session_id=41012,
         process_scope='These PIDs and tool handle were live or inspected only at recorded_at. Revalidate before continuing; never restart after an observation timeout alone.',
         paper=dict(revision=66,next_rewrite=76,sha256=sha(paper),changed=False),
         remaining=['Actual direction IDs and compatible history-state coding',
                    'Exact exclusion and all compatible eleven-direction variant coverage',
                    'All local credit dispatch and full potential replay',
                    'Six stronger local catalogue target proofs',
                    'Exact optimum and construction beyond191 unresolved'])
(HERE/'data/checkpoint.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(audits),'new declarations;',len(rows),'saved replay modules;',
      snapshot['completed_check_modules'],'large checks;',len(live),'matching processes')
