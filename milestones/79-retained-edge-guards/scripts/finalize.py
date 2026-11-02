"""Freeze successful guard interfaces and an honest case7305 observation."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for name in ['CanonicalExclusions','CountWindows','BaseSix','ReferenceRetention','IntervalGuards','IntervalCatalogue']:
    path=HERE/'data'/f'{name}-audit.json';r=json.loads(path.read_text())
    assert r['status']=='PASS_LEAN_MODULE'
    for sub,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(HERE/sub/(name+suffix))==r[key]
    for dep,digest in r['dependencies'].items():assert sha(HERE/'data'/f'{dep}-audit.json')==digest
    if name=='IntervalCatalogue':assert sha(HERE/'data/interval-support.json')==r['interval_support_sha256']
    rows.append(dict(module=name,receipt=path.relative_to(HERE).as_posix(),sha256=sha(path),audits=len(r['theorem_audits'])))
comparison=json.loads((HERE/'data/filter-comparison.json').read_text())
assert comparison['status']=='PASS_EXHAUSTIVE_COUNT_AND_INTERVAL_CONVENTIONS'
for path,digest in comparison['inputs'].items():assert sha(ROOT/path)==digest
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd'
result=dict(status='PASS_ENCODED_GUARDS_AND_TEN_INTERVAL_RETENTION',receipts=rows,
    printed_theorem_audits=sum(r['audits'] for r in rows),filter_comparison_sha256=sha(HERE/'data/filter-comparison.json'),
    interval_support_sha256=sha(HERE/'data/interval-support.json'),paper_sha256=sha(paper),
    limitations=['Existing hash-matched objects reused; full inherited dependency closure not rebuilt.',
        'Reference Refuted premises remain explicit; concrete 1378-key union uninstantiated.',
        'Recovered short rules, history exclusions, array membership, credit validity and full potential remain.',
        'No new global upper bound or case7305 local share theorem is claimed by this milestone.'])
(HERE/'data/proof-summary.json').write_text(json.dumps(result,indent=2)+'\n')
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7305'
sources={f.relative_to(CASE/'lean').with_suffix('').as_posix():f for f in (CASE/'lean').rglob('*.lean')}
successful={};record_hashes={}
for kind in ['semantic','composition','completion']:
    source=CASE/'logs'/f'{kind}-record.json'
    for attempt in range(5):
        try:raw=source.read_bytes();saved=json.loads(raw);break
        except json.JSONDecodeError:
            if attempt==4:raise
            time.sleep(.1)
    target=HERE/'data'/f'replay-{kind}-record.json';target.write_bytes(raw);record_hashes[kind]=sha(target)
    for row in saved['records']:
        name=row['module']
        if row['exit_code']!=0 or sha(sources[name])!=row['source_sha256']:continue
        if any(sha(sources[n])!=h for n,h in row.get('dependencies',{}).items()):continue
        obj=Path(saved['build'])/(name+'.olean');log=CASE/'logs'/(name.replace('/','-')+'.log')
        if obj.is_file():
            text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
            successful[name]=dict(module=name,source_sha256=sha(sources[name]),object_sha256=sha(obj),log_sha256=sha(log))
pending=sorted(set(sources)-successful.keys())
(HERE/'data/replay-evidence.json').write_text(json.dumps(dict(status='PARTIAL_SUCCESSFUL_MODULE_OBSERVATION',
    modules=list(successful.values()),source_modules=len(sources),pending_modules=pending,
    scope='Historical source/object observation. Final local theorem requires completion and audit.'),indent=2)+'\n')
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7305*' } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
text=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes=json.loads(text) if text else []
if isinstance(processes,dict):processes=[processes]
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip()
    for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
checkpoint=dict(status=result['status'],recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),git_refs=refs,
    unconditional_edge_interval=[191,235],conditional_target=234,paper_revision=76,paper_sha256=sha(paper),
    printed_theorem_audits=result['printed_theorem_audits'],replay_successful_modules=len(successful),
    replay_total_sources=len(sources),replay_pending_modules=pending,replay_record_hashes=record_hashes,
    observed_processes=processes,tool_session_id=72392,case7305_final_theorem=False,
    process_scope='Historical observation; inspect actual processes before restarting. One completion driver only.')
(HERE/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
print(result['status'],result['printed_theorem_audits'],'audits;',len(successful),'of',len(sources),'replay modules;',len(processes),'processes')
