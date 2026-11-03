"""Verify exact saved evidence, then stage only an explicit publication manifest."""
from pathlib import Path
import gzip,hashlib,json,os,re,subprocess,sys,tarfile
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
    assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='b96c43f1395105155b1052ceb22839a5019c4c56'
    native=read(H/'data/native-review.json')
    assert native['status']=='PASS_INPUT_CORE_AND_ARCHIVE_RECONSTRUCTION_NO_NEW_PROOF_REPLAY';pins(native)
    conversion=read(H/'data/conversion-long.json');pins(conversion)
    assert conversion['status']=='PASS_RUP_ONLY_CONVERSION_DIRECT_REPLAY_PENDING'
    assert (conversion['variables'],conversion['original_clauses'],conversion['core_clauses'],conversion['lemmas'],conversion['hints'])==(11378,92656,12977,285541,31017505)
    for p,d in conversion['preserved_files_sha256'].items():assert sha(H/'work/conversion-long'/p)==d
    replay=read(H/'data/direct-replay.json');pins(replay)
    assert replay['status']=='PASS_COMPLETE_DIRECT_RUP_REPLAY' and replay['final_empty_clause']
    assert (replay['lemmas_checked'],replay['hints_checked'],replay['core_inputs_used'])==(285541,31017505,12977)
    assert read(H/'data/compact-certificate.json')['status']=='TIMEOUT'
    assert read(H/'data/conversion.json')['status']=='CONVERSION_INCOMPLETE'
    for name,status in [('joint-floor-analysis','PASS_EXACT_SAVED_CYCLE_JOINT_FLOOR_AUDIT'),('two-cycle-analysis','PASS_EXACT_TWO_SAVED_CYCLE_AUDIT'),('joint-floor-review','PASS_BOUNDED_JOINT_FLOOR_CYCLE_AND_ARITHMETIC_REVIEW')]:
        j=read(H/f'data/{name}.json');assert j['status']==status;pins(j)
    receipts=list((H/'data').glob('*-audit.json'));assert len(receipts)==31
    reports=0
    for receipt in receipts:
        j=read(receipt);assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
        assert sha(j['source'])==j['source_sha256'] and sha(j['object'])==j['olean_sha256']
        assert sha(j['log'])==j['log_sha256']
        folder=Path(j['log']).parent
        assert sha(folder/'source.lean.txt')==j['source_sha256']
        assert sha(folder/'checker.py.txt')==j['checker_sha256']
        pins(j,'dependencies')
        assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])
        reports+=len(j['axioms'])
    assert reports==435
    bridge=read(H/'data/chunked-bridge-completion.json')
    assert bridge['status']=='PARTIAL_ALL104_PART_TRUTH_CHECKED_FINAL_ASSEMBLY_TIMEOUT'
    assert (bridge['checked_modules'],bridge['checked_axiom_reports'])==(28,419)
    for x in bridge['passed']:assert sha(x['receipt'])==x['receipt_sha256']
    end=read(H/'logs/ChunkTruthAssemblyFixed145-1793728907954267000/record.json')
    assert end['stop_reason']=='TIMEOUT' and end['status']=='FAILED' and not end['axioms']
    assert not (H/'data/ChunkTruthAssemblyFixed145-audit.json').exists()
    assert not (H/'data/PrefixTruth145-audit.json').exists()
    for source in (H/'lean').rglob('*.lean'):
        assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text(encoding='utf-8'))
    archives=read(H/'data/proof-archives.json')['files']+[read(H/'data/first-conversion-archive.json')]
    excluded=set()
    for x in archives:
        source=H/x['source'];archive=H/x['archive'];excluded.add(source)
        assert sha(source)==x['source_sha256'] and sha(archive)==x['archive_sha256']
        d=hashlib.sha256();n=0
        with gzip.open(archive,'rb') as f:
            for b in iter(lambda:f.read(1048576),b''):d.update(b);n+=len(b)
        assert d.hexdigest()==x['source_sha256'] and n==x['source_bytes']
    total=read(H/'data/total115-completion.json')
    assert total['status']=='PASS_COMPLETE_TOTAL115_RECEIPT_AND_DEPENDENCY_AUDIT' and total['checked_modules']==1397
    pins(total);pins(total,'dependencies')
    assert sha(H/total['archive'])==total['archive_sha256']
    excluded.add(H/total['archive'])
    combined=hashlib.sha256()
    for part in total['archive_parts']:
        assert sha(H/part['path'])==part['sha256'] and (H/part['path']).stat().st_size==part['bytes']
        with (H/part['path']).open('rb') as f:
            for b in iter(lambda:f.read(1048576),b''):combined.update(b)
    assert combined.hexdigest()==total['archive_sha256']
    expected={x['path']:x for x in total['archive_members']}
    with tarfile.open(H/total['archive'],'r:gz') as tar:
        for member in tar:
            row=expected.pop(member.name);f=tar.extractfile(member);d=hashlib.sha256();n=0
            for b in iter(lambda:f.read(1048576),b''):d.update(b);n+=len(b)
            assert d.hexdigest()==row['sha256'] and n==row['bytes']
    assert not expected
    paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
    pr=read(H/'data/paper-source-review.json');rev=read(H/'data/paper-revision.json')
    assert sha(paper)==sha(editor)==pr['source_sha256']==rev['after_sha256']
    assert paper.read_bytes().split(b'\\begin{document}',1)[0]==(H/'audit/paper-before.tex.txt').read_bytes().split(b'\\begin{document}',1)[0]
    assert pr['definition_environment_count']==1 and rev['new_named_definitions']==0
    compile_record=read(H/'data/compilation.json')
    assert compile_record['source_sha256']==sha(paper) and compile_record['status']=='FAILED_BEFORE_TEX_PREPARATION'
    for row in read(H/'data/batch-observation.json')['batches']:assert sha(H/row['snapshot'])==row['sha256']
    verification=dict(status='PASS_SAVED_TWO_CYCLE_OBSTRUCTION_NATIVE_SHARE_CERTIFICATE_AND_COMPLETED_COUNT_THEOREM',
        new_arithmetic_reports=14,all145_passed_modules=31,all145_axiom_reports=435,
        native_deductions=285541,native_hints=31017505,native_core_inputs=12977,
        comparison_lower_bound='551875/2348',necessary_joint_floors='325F+159G>9074',
        initial_tree_truth_bridge_complete=False,share16_actual_theorem_complete=False,
        total115_complete=True,total115_modules=1397,total115_theorem='012310 five internal counts sum to at least19',
        new_global_upper_bound=False,paper_sha256=sha(paper),pdf_rebuilt=False)
    (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n')
    checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
        base_commit='b96c43f1395105155b1052ceb22839a5019c4c56',verification_sha256=sha(H/'data/verification.json'),
        prior_checkpoint_sha256=sha(R/'milestones/144-countfree-share18/data/checkpoint.json'),
        current_interval=[191,235],interval_scope='Maintained contributor upper proof; complete independent rebuild still pending.',
        selected_next_task='Split original-CNF-to-chunk truth extraction from final initial-tree constructor assembly, then transport the fully replayed012301 proof. Keep012032 and012340 as joint share dependencies.',
        last_full_paper_revision=136,targeted_paper_revision=145,next_full_paper_revision=146,
        paper_sha256=sha(paper),pdf_rebuilt=False,total115_complete=True,all145_jobs_complete_or_stopped=True)
    (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
    selected=set()
    for folder,dirs,files in os.walk(H,followlinks=False):
        dirs[:]=[n for n in dirs if not n.startswith('build') and n!='__pycache__']
        for name in files:
            p=Path(folder)/name
            if p==manifest or p in excluded or p.suffix in ['.tmp','.pending','.lock','.olean','.ilean'] or name=='stage-paths.nul':continue
            selected.add(p)
    selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
    assert all(x['bytes']<100000000 for x in rows)
    manifest.write_text(json.dumps(dict(status='EXACT_145_PUBLICATION_MANIFEST',files=rows,
        excluded_large_originals=[p.relative_to(H).as_posix() for p in sorted(excluded)]),indent=2)+'\n')
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
print(json.dumps(dict(status='PASS_EXACT_145_PUBLICATION_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows),
    staged_checked='--check-staged' in sys.argv or '--stage' in sys.argv)))
