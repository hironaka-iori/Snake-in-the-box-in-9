"""Verify saved146 evidence and stage only exact manifest bytes."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p);key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:
        d=hashlib.sha256()
        with p.open('rb') as f:
            for b in iter(lambda:f.read(1048576),b''):d.update(b)
        cache[key]=d.hexdigest()
    return cache[key]
def pins(j,key='source_files_sha256'):
    for p,d in j.get(key,{}).items():
        p=Path(p);assert sha(p if p.is_absolute() else R/p)==d,p
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json'
if not manifest.exists():
    assert len(sys.argv)==1
    assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='8e16400c85ecb96faafd6a82dd50710f15869420'
    bridge=read(H/'data/bridge-completion.json')
    assert bridge['status']=='PASS_ORIGINAL_CNF_TO_INITIAL_TREE_AND_CHECKED_PREFIX';pins(bridge)
    assert (bridge['checked_modules'],bridge['axiom_reports'],bridge['raw_chunks'],bridge['existing_prefix_deductions'],bridge['existing_prefix_references'])==(3,4,104,1055,6006)
    assert bridge['original_constructor_body_preserved'] and bridge['initial_tree_truth_bridge_complete']
    assert not any(bridge[k] for k in ['full_share18_replay_complete','actual_share18_theorem_complete','actual_share16_theorem_complete'])
    print('Verified the saved initial-tree and prefix receipt.',flush=True)
    plan=read(H/'data/semantic-plan.json');pins(plan)
    assert plan['status']=='PREPARED_EXACT_012301_CORE_INTERPRETATION_LEAN_PENDING'
    assert len(plan['module_order'])==len(plan['artifacts'])==105
    assert (plan['full_input_clauses'],plan['core_clauses'],plan['retained_cycle_cuts'])==(92656,12977,6)
    for x in plan['artifacts']:assert sha(H/x['path'])==x['sha256']
    progress=read(H/'data/semantic-progress.json')
    assert progress['status']!='RUNNING' and progress['active'] is None
    assert not (H/'data/semantic-batch.lock').exists()
    print('Checking the exact namespace copies and module dependencies.',flush=True)
    overlay=read(H/'data/semantic-import-overlay.json')
    assert overlay['status']=='PASS_HASH_AUDITED_NAMESPACE_OVERLAY'
    assert len(overlay['objects'])==overlay['object_count']
    assert len({x['relative_path'] for x in overlay['objects']})==overlay['object_count']
    assert sum(x['bytes'] for x in overlay['objects'])==overlay['total_bytes']
    for x in overlay['objects']:
        source=Path(x['source']);dest=Path(x['destination'])
        assert source==Path(overlay['ordered_source_paths'][x['source_priority']])/x['relative_path']
        assert dest==H/'build-independent'/x['relative_path']
        assert not any((Path(p)/x['relative_path']).exists() for p in overlay['ordered_source_paths'][:x['source_priority']])
        assert source.stat().st_size==dest.stat().st_size==x['bytes']
        assert sha(source)==sha(dest)==x['sha256']
    known={'RawChunksAssoc146','AssemblyAssoc146','PrefixAssoc146'}|set(plan['module_order'])
    modules=[];reports=0
    for receipt in sorted((H/'data').glob('*-audit.json')):
        j=read(receipt)
        if 'source' not in j:continue
        name=receipt.name.removesuffix('-audit.json');assert name in known,name
        assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
        assert sha(j['source'])==j['source_sha256'] and sha(j['object'])==j['olean_sha256']
        assert sha(j['log'])==j['log_sha256']
        folder=Path(j['log']).parent
        assert sha(folder/'source.lean.txt')==j['source_sha256']
        assert sha(folder/'checker.py.txt')==j['checker_sha256']
        pins(j,'dependencies')
        assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])
        assert len(j['axioms'])==Path(j['source']).read_text().count('#print axioms')
        reports+=len(j['axioms']);modules.append(name)
    for x in progress['checked_modules']:
        assert x['module'] in modules
        assert sha(H/'data'/(x['module']+'-audit.json'))==x['receipt_sha256']
    assert set(modules)=={'RawChunksAssoc146','AssemblyAssoc146','PrefixAssoc146'}|{x['module'] for x in progress['checked_modules']}
    for source in (H/'lean').rglob('*.lean'):
        assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text(encoding='utf-8')),source
    print('Verified all accepted Lean receipts and their dependencies.',flush=True)
    paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
    pr=read(H/'data/paper-source-review.json');rev=read(H/'data/paper-revision.json')
    assert sha(paper)==sha(editor)==pr['source_sha256']
    assert rev['full_revision'] and rev['revision']==146
    assert paper.read_bytes().split(b'\\begin{document}',1)[0]==(H/'audit/paper-before.tex.txt').read_bytes().split(b'\\begin{document}',1)[0]
    assert pr['definition_environment_count']==1
    assert sha(H/'data/paper-revision.json')==pr['revision_receipt_sha256']
    amendment=read(H/'data/paper-amendment.json')
    assert sha(H/'data/paper-amendment.json')==pr['amendment_receipt_sha256']
    assert amendment['source_sha256_after']==sha(paper) and amendment['source_sha256_before']==rev['source_sha256_after']
    assert amendment['review_sha256']==sha(H/'data/paper-final-review.json')
    before=(H/'audit/paper-before-terminology.tex.txt').read_bytes()
    assert hashlib.sha256(before).hexdigest()==rev['source_sha256_after']
    assert before.count(amendment['old_phrase'].encode())==1
    assert before.replace(amendment['old_phrase'].encode(),amendment['new_phrase'].encode())==paper.read_bytes()
    comp=read(H/'data/paper-compile.json');assert comp['paper_sha256']==sha(paper)
    payload=json.loads(comp['result']['content'][0]['text'])
    assert payload['kind']=='compile-failed' and 'Compiler helper failed' in payload['diagnostics']['log']
    assert (H/'data/paper-final-review.json').exists()
    verification=dict(status='PASS_INITIAL_TREE_PREFIX_AND_FULL_PAPER_REVISION',
        checked_modules=modules,axiom_reports=reports,semantic_checked_modules=len(progress['checked_modules']),
        semantic_total_modules=105,semantic_status=progress['status'],
        original_core_clauses=13224,initial_tree_truth_bridge_complete=True,
        checked_prefix_deductions=1055,checked_prefix_references=6006,
        actual_share16_theorem_complete=False,actual_share18_theorem_complete=False,
        full_share18_replay_complete=False,new_global_upper_bound=False,
        paper_sha256=sha(paper),full_paper_revision=146,pdf_rebuilt=False,
        evidence_sha256={p.relative_to(H).as_posix():sha(p) for p in [H/'data/bridge-completion.json',H/'data/semantic-plan.json',H/'data/semantic-progress.json',H/'data/paper-revision.json',H/'data/paper-source-review.json',H/'data/paper-final-review.json',H/'data/paper-compile.json']})
    (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8',newline='\n')
    checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
        base_commit='8e16400c85ecb96faafd6a82dd50710f15869420',verification_sha256=sha(H/'data/verification.json'),
        prior_checkpoint_sha256=sha(R/'milestones/145-countfree-012301/data/checkpoint.json'),
        current_interval=[191,235],interval_scope='Maintained contributor upper proof; complete independent rebuild pending.',
        selected_next_task='Complete the exact012301 core interpretation, then bounded full Lean replay and actual-snake transfer including cycle cuts and reversal. Keep012032 and012340 as joint share dependencies.',
        last_full_paper_revision=146,next_full_paper_revision=156,paper_sha256=sha(paper),pdf_rebuilt=False,
        semantic_status=progress['status'],semantic_checked_modules=len(progress['checked_modules']),
        all146_jobs_complete_or_stopped=True,total115_complete=True)
    (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8',newline='\n')
    selected=set()
    for folder,dirs,files in os.walk(H,followlinks=False):
        dirs[:]=[n for n in dirs if not n.startswith('build') and n!='__pycache__']
        for name in files:
            p=Path(folder)/name
            if p==manifest or p.suffix in ['.tmp','.pending','.lock','.olean','.ilean'] or name=='stage-paths.nul':continue
            selected.add(p)
    selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
    assert all(x['bytes']<100000000 for x in rows)
    manifest.write_text(json.dumps(dict(status='EXACT_146_PUBLICATION_MANIFEST',files=rows),indent=2)+'\n',encoding='utf-8',newline='\n')
rows=read(manifest)['files']
for row in rows:assert sha(R/row['path'])==row['sha256'] and (R/row['path']).stat().st_size==row['bytes'],row['path']
paths=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
if '--stage' in sys.argv:
    existing=subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0')
    assert not [p for p in existing if p]
    pathlist=H/'data/stage-paths.nul';pathlist.write_bytes(b'\0'.join(p.encode() for p in paths)+b'\0')
    subprocess.run(g+['add','-f','--pathspec-from-file='+str(pathlist),'--pathspec-file-nul'],cwd=R,check=True)
if '--check-staged' in sys.argv or '--stage' in sys.argv:
    staged=set(x.decode() for x in subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0') if x)
    assert staged==set(paths),(staged-set(paths),set(paths)-staged)
    proc=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    for path in paths:
        proc.stdin.write((':'+path+'\n').encode());proc.stdin.flush()
        header=proc.stdout.readline().decode().split();assert len(header)==3 and header[1]=='blob',header
        left=int(header[2]);d=hashlib.sha256()
        while left:
            block=proc.stdout.read(min(1048576,left));assert block;d.update(block);left-=len(block)
        assert proc.stdout.read(1)==b'\n' and d.hexdigest()==sha(R/path),path
    proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_EXACT_146_PUBLICATION_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows),staged_checked='--check-staged' in sys.argv or '--stage' in sys.argv)))
