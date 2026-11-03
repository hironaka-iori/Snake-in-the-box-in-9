"""Preserve146 mathematical input while removing the full catalogue import."""
from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/146-initial-tree-and-paper'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for n in ['data','lean','scripts','logs','build']:(H/n).mkdir(parents=True,exist_ok=True)
assert read(P/'data/semantic-progress.json')['status']=='PASS_BOUNDED_SEMANTIC_PREFIX'
prior=read(P/'data/semantic-plan.json')
framework=['LocalWindowModel','LocalWindowShareModel','LocalWindowTags','LocalWindowTagsPacked','LocalWindowTagsShare','LocalWindowTagsSharePacked']
rows=[]
for m in framework:
    p=R/'milestones/28-direct-share-certificates/upstream'/(m+'.lean');out=H/'lean'/(m+'.lean')
    assert not out.exists();out.write_bytes(p.read_bytes())
    rows.append(dict(module=m,kind='unchanged_generic_source',source=p.relative_to(R).as_posix(),source_sha256=sha(p),path=out.relative_to(H).as_posix(),sha256=sha(out)))
for x in prior['artifacts']:
    p=P/x['path'];assert sha(p)==x['sha256'];old=p.read_bytes();new=old
    if x['path']=='lean/LocalWindowCnf/ShareWindow146.lean':
        assert old.count(b'import Port98CombinedCatalogue')==1
        new=old.replace(b'import Port98CombinedCatalogue',b'import LocalWindowShareModel')
    elif x['path']=='lean/Share146/Data.lean':
        assert old.count(b'import Port98CombinedCatalogue')==1
        new=old.replace(b'import Port98CombinedCatalogue',b'import LocalWindowTagsPacked\nimport LocalWindowTagsSharePacked')
    else:assert b'Port98CombinedCatalogue' not in old
    out=H/x['path'];out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();out.write_bytes(new)
    # All non-import lines remain exactly the same, including literal bytes.
    strip=lambda b:b'\n'.join(l for l in b.split(b'\n') if not l.startswith(b'import '))
    assert strip(old)==strip(new)
    m=Path(x['path']).relative_to('lean').with_suffix('').as_posix().replace('/','.')
    rows.append(dict(module=m,kind='import_only_change' if new!=old else 'unchanged_concrete_source',source=p.relative_to(R).as_posix(),source_sha256=sha(p),path=out.relative_to(H).as_posix(),sha256=sha(out)))
audit=H/'lean/Generic147Audit.lean'
audit.write_text('import LocalWindowTagsPacked\nimport LocalWindowTagsSharePacked\n'+''.join('#print axioms '+n+'\n' for n in [
    'Snake9.LocalWindow.Tags.sound_cut','Snake9.LocalWindow.Tags.sound',
    'Snake9.LocalWindow.Tags.soundS','Snake9.LocalWindow.Tags.refutedShare_of_check',
    'Snake9.LocalWindow.RefutedShare.anti']),encoding='utf-8',newline='\n')
rows.append(dict(module='Generic147Audit',kind='axiom_audit_only',path=audit.relative_to(H).as_posix(),sha256=sha(audit)))
plan=dict(status='PREPARED_MINIMAL_IMPORTS_WITH_UNCHANGED_MATHEMATICAL_INPUT',
    framework_modules=framework+['Generic147Audit'],concrete_modules=prior['module_order'],
    module_order=framework+['Generic147Audit']+prior['module_order'],artifacts=rows,
    source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [Path(__file__),P/'data/semantic-plan.json',P/'data/share146.json',P/'certificates/share146.cnf',P/'data/semantic-progress.json',P/'data/semantic-import-repair.json']},
    mathematical_source_changes=False,prior_milestone_unchanged=True,concrete_clause_modules=102,
    scope='Generic models freshly recompiled, only import lines replaced in concrete sources. Full clause checks, contradiction replay and actual-snake transfer remain required.')
(H/'data/semantic-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8',newline='\n')
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
repo=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),previous_goal_turn='PROGRESS',goal_status='ACTIVE',
    head=subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip(),
    remote_tips=subprocess.check_output(g+['for-each-ref','--format=%(refname) %(objectname)','refs/remotes/origin'],cwd=R,text=True))
(H/'data/repository-check.json').write_text(json.dumps(repo,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status=plan['status'],framework_modules=7,concrete_modules=105)))
