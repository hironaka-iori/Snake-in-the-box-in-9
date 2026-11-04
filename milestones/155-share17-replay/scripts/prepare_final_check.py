"""Prepare one actual-snake composition check and continuation; never run Lean."""
from pathlib import Path
import ast, datetime, hashlib, importlib.util, json, re

H=Path(__file__).resolve().parents[1];R=H.parents[1]
S=R/'milestones/154-share17-broader-semantics'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(path,content):
    raw=content.encode('utf-8') if isinstance(content,str) else content
    path.parent.mkdir(parents=True,exist_ok=True)
    if path.exists():assert path.read_bytes()==raw,path
    else:path.write_bytes(raw)
def once(text,old,new):
    assert text.count(old)==1,(old,text.count(old));return text.replace(old,new)

target=read(H/'data/final-target.json');source=H/'lean/ShareComplete155.lean'
assert sha(source)==target['source_sha256']=='3652fbffbd7977553308f05a744d3a0c88c3fe0ec1d2206291691e0726fe160b'
assert not target['extra_unsat_premise_in_target'] and target['count_conditions_retained']
text=source.read_text(encoding='utf-8');signature=text[text.index('theorem share17'):text.index(':=')]
assert not re.search(r'\b(Unsat|hunsat|href|sorry|admit|native_decide|axiom)\b',signature)
assert 'coreAlpha p (r+2) ≤ 4' in signature and 'coreAlpha p (r+4) ≤ 5' in signature
assert 'coreAlpha p (r+2) ≤ 5' in signature and 'coreAlpha p (r+4) ≤ 4' in signature
assert 'Snake9.CriticalShare154.share17_of_core_unsat Snake9.ReplayFull153.unsat p r hr hcase' in text
sem=read(S/'data/semantics-completion.json');semantic_plan=read(S/'data/semantic-plan-v2.json')
assert sem['status']=='PASS_BROADER_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE17'
assert sem['checked_modules']==98 and sem['axiom_reports']==100
assert sem['plan_sha256']==sha(S/'data/semantic-plan-v2.json')
assert target['adapter_sha256']==sha(S/'lean/CriticalShareAdapter154.lean')
for row in sem['receipts']:assert sha(R/row['receipt'])==row['sha256']
full_plan=read(H/'data/full-source-plan.json');assert full_plan['module_count']==137
assert full_plan['module_order'][-1]=='ReplayUnsat153'
assert sha(H/'lean/ReplayUnsat153.lean')==next(row['sha256'] for row in full_plan['artifacts'] if row['module']=='ReplayUnsat153')

checker=(S/'scripts/check_module_v2.py').read_text(encoding='utf-8')
checker=once(checker,"H=Path(__file__).resolve().parents[1];R=H.parents[1];Q=R/'milestones/147-countfree-clause-semantics'",
    "H=Path(__file__).resolve().parents[1];R=H.parents[1];Q=R/'milestones/147-countfree-clause-semantics';S=R/'milestones/154-share17-broader-semantics'")
checker=checker.replace('data/semantic-plan-v2.json','data/final-composition-plan.json')
checker=once(checker,"assert a.module in expected and sha(src)==expected[a.module]",
    "assert a.module=='ShareComplete155' and a.module in expected and sha(src)==expected[a.module]\n"
    "assert plan['status']=='PREPARED_COUNT_CONDITIONED_ACTUAL_SNAKE_COMPOSITION'\n"
    "for p,d in plan['script_pins'].items():assert sha(R/p)==d,p\n"
    "for p,d in plan['input_pins'].items():assert sha(R/p)==d,p\n"
    "fullpath=H/'data/full-replay-completion.json'\n"
    "if not fullpath.exists():\n"
    "    print(json.dumps(dict(status='WAITING_FOR_AUDITED_FULL_REPLAY')));raise SystemExit(2)\n"
    "full=read(fullpath);assert full['status']=='PASS_COMPLETE_SHARED_SHARE17_CORE_CONTRADICTION'\n"
    "assert (full['checked_modules'],full['axiom_reports'],full['initial_core_clauses'],full['deductions'],full['references'])==(137,407,11869,30305,1754767)\n"
    "assert full['final_theorem']=='Snake9.ReplayFull153.unsat' and full['final_CNF']=='Snake9.LocalWindow.ShareWindow153.cnf'\n"
    "for row in full['receipts']:assert sha(H/row['receipt'])==row['sha256']\n"
    "for p,d in full['source_files_sha256'].items():assert sha(R/p)==d,p\n"
    "sempath=S/'data/semantics-completion.json';sem=read(sempath)\n"
    "assert sem['status']=='PASS_BROADER_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE17' and sem['checked_modules']==98\n"
    "for row in sem['receipts']:assert sha(R/row['receipt'])==row['sha256']")
checker=checker.replace("plan['recovery_v2']['resource_helper_sha256']","plan['resource_helper_sha256']")
checker=checker.replace("[build,R/'milestones/148-actual-snake-share-transfer/build',Q/'build']",
    "[build,S/'build',R/'milestones/148-actual-snake-share-transfer/build',Q/'build']")
checker=checker.replace("[build,R/'milestones/148-actual-snake-share-transfer/build',Q/'build',B.parent/'lib/lean']",
    "[build,S/'build',R/'milestones/148-actual-snake-share-transfer/build',Q/'build',B.parent/'lib/lean']")
checker=once(checker,"deps={str(planpath):sha(planpath),str(B/'lean.exe'):sha(B/'lean.exe'),str(helper):sha(helper)}",
    "deps={str(planpath):sha(planpath),str(B/'lean.exe'):sha(B/'lean.exe'),str(helper):sha(helper),str(fullpath):sha(fullpath),str(sempath):sha(sempath)}\n"
    "for group in [plan['script_pins'],plan['input_pins'],full['source_files_sha256']]:\n"
    "    for p,d in group.items():deps[str(R/p)]=d\n"
    "for row in full['receipts']:deps[str(H/row['receipt'])]=row['sha256']\n"
    "for row in sem['receipts']:deps[str(R/row['receipt'])]=row['sha256']")
checker=once(checker,"    rp=H/'data'/(name+'-audit.json')",
    "    rp=H/'data'/(name+'-audit.json')\n"
    "    if not rp.exists():rp=S/'data'/(name+'-audit.json')")
checker=once(checker,"    assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']",
    "    assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']\n"
    "    assert sha(q['log'])==q['log_sha256']\n"
    "    qfolder=Path(q['log']).parent\n"
    "    assert sha(qfolder/'source.lean.txt')==q['source_sha256']\n"
    "    assert sha(qfolder/'checker.py.txt')==q['checker_sha256']\n"
    "    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])\n"
    "    item=plan['direct_import_receipts'][name]\n"
    "    assert rp.resolve()==(R/item['receipt']).resolve()\n"
    "    assert Path(q['source']).resolve()==(R/item['source']).resolve() and q['source_sha256']==item['source_sha256']\n"
    "    assert Path(q['object']).resolve() in {Path(x).resolve() for x in direct}\n"
    "    deps[q['log']]=q['log_sha256']\n"
    "    deps[str(qfolder/'source.lean.txt')]=q['source_sha256']\n"
    "    deps[str(qfolder/'checker.py.txt')]=q['checker_sha256']")
checker=checker.replace("paths=[str(build),str(Q/'build')]+list(map(str,external))",
    "paths=[str(build),str(S/'build'),str(R/'milestones/148-actual-snake-share-transfer/build'),str(Q/'build')]+list(map(str,external))")
checker=checker.replace('The shared153 core and broader154 clause interpretation and conditional transfer are freshly checked; the single153 core contradiction remains separate.',
    'The completed shared153 core contradiction and broader154 conditional actual-snake transfer are composed in this single check. The stated count conditions remain; no global bound is claimed.')
assert 'Get-CimInstance' not in checker
put(H/'scripts/check_final.py',checker)

progress=read(H/'data/full-replay-progress.json')
assert progress['status']=='RUNNING' and progress['total_modules']==137
assert progress['driver_sha256']==sha(H/'scripts/run_full_replay.py')
assert progress['checker_sha256']==sha(H/'scripts/check_full_replay.py')
spec=importlib.util.spec_from_file_location('final_identity155',H/'scripts/continue_after_full.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
handle=module.kernel.OpenProcess(0x1000|0x00100000,False,progress['pid']);assert handle
try:driver=module.identity(handle)
finally:module.kernel.CloseHandle(handle)
assert driver['exit_code']==259
created=datetime.datetime.fromtimestamp(driver['creation_filetime']/10000000-11644473600,datetime.timezone.utc)
started=datetime.datetime.fromisoformat(progress['started_at'])
assert abs((started-created).total_seconds())<5
driver.update(pid=progress['pid'],started_at=progress['started_at'],driver_sha256=progress['driver_sha256'],
    checker_sha256=progress['checker_sha256'],plan_sha256=progress['plan_sha256'],
    observed_checked_modules=len(progress['checked_modules']),creation_utc=created.isoformat(),verified_live_at_preparation=True)
imports={}
for name,folder in [('CriticalShareAdapter154',S),('ReplayUnsat153',H)]:
    path=folder/'lean'/(name+'.lean')
    imports[name]=dict(receipt=(folder/'data'/(name+'-audit.json')).relative_to(R).as_posix(),
        source=path.relative_to(R).as_posix(),source_sha256=sha(path))
scripts=[Path(__file__),H/'scripts/check_final.py',H/'scripts/audit_actual.py',H/'scripts/continue_after_full.py',
    H/'scripts/finish_full_replay.py',H/'scripts/native_resources.py']
for path in scripts:ast.parse(path.read_text(encoding='utf-8'),filename=str(path))
inputs=[source,H/'data/final-target.json',S/'lean/CriticalShareAdapter154.lean',H/'lean/ReplayUnsat153.lean',
    S/'data/semantics-completion.json',S/'data/semantic-plan-v2.json',S/'data/source-plan.json',S/'data/semantic-progress-v2.json',
    S/'scripts/finish_semantics_v2.py',S/'scripts/check_module_v2.py',
    H/'data/full-source-plan.json',H/'data/full-execution-preparation.json',H/'scripts/run_full_replay.py',H/'scripts/check_full_replay.py']
plan=dict(status='PREPARED_COUNT_CONDITIONED_ACTUAL_SNAKE_COMPOSITION',Lean_started=False,
    module_order=['ShareComplete155'],framework_modules=['ShareComplete155'],
    artifacts=[dict(module='ShareComplete155',path='lean/ShareComplete155.lean',sha256=sha(source),bytes=source.stat().st_size)],
    expected_signature=' '.join(signature.split()),expected_theorem='Snake9.CriticalShare155.share17',
    directions=[0,1,2,0,3,2],bounds=[[4,4],[0,4],[4,4],[0,5],[3,3]],
    reverse_bounds=[[3,3],[0,5],[4,4],[0,4],[4,4]],count_conditions_retained=True,
    extra_unsat_premise=False,new_global_upper_bound=False,
    inherited_modules={},external_library_search_paths=semantic_plan['external_library_search_paths'],
    external_pins=semantic_plan['external_pins'],resource_helper_sha256=sha(H/'scripts/native_resources.py'),
    direct_import_receipts=imports,full_driver=driver,
    script_pins={p.relative_to(R).as_posix():sha(p) for p in scripts},
    input_pins={p.relative_to(R).as_posix():sha(p) for p in inputs},
    scope='Prepared final composition only. Continue only after the same full driver completes and its137-module evidence passes the full auditor. The98-module count-conditioned semantics is already accepted. No compiler was launched by preparation.')
put(H/'data/final-composition-plan.json',json.dumps(plan,indent=2)+'\n')
print(json.dumps(dict(status=plan['status'],Lean_started=False,source_sha256=sha(source),
    plan_sha256=sha(H/'data/final-composition-plan.json'),verified_live_full_driver=driver,
    count_conditions_retained=True,extra_unsat_premise=False,new_global_upper_bound=False)))
