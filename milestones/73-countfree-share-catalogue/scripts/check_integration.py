"""Check all completed local cases with both earlier shares and the global budget."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=ROOT/'milestones/72-four-count-proof-closure'
case_roots=[p.parent.parent for p in sorted((HERE/'cases').glob('*/data/proof-audit.json'))]
roots=case_roots+[old/'critical-current/share-proof',old/'critical-charge/share-proof']
for root in roots:assert read(root/'data/proof-audit.json')['status']=='PASS_LOCAL_SHARE_THEOREM'
bridge=HERE/'bridge';assert read(bridge/'data/proof-audit.json')['status']=='PASS_CORE_SHARE_BUDGET'
extras=[bridge]
for folder in ['coverage','adapter']:
    root=HERE/folder
    if (root/'data/proof-audit.json').exists():
        assert read(root/'data/proof-audit.json')['status'].startswith('PASS_')
        extras.append(root)
BUILD=HERE/'build';merged=BUILD/'combined';merged.mkdir(parents=True,exist_ok=True)
origins={};objects=[]
for root in roots+extras:
    object_root=root/('build' if root in extras else 'build/semantic')
    for obj in object_root.rglob('*.olean'):
        if obj.name.endswith('.fresh.olean'):continue
        rel=obj.relative_to(object_root);source=root/'lean'/rel.with_suffix('.lean')
        if not source.exists() and root in extras:source=root/'upstream'/rel.with_suffix('.lean')
        assert source.exists(),source
        key=rel.as_posix()
        if key in origins:assert sha(origins[key])==sha(source),f'Conflicting shared module {key}';continue
        origins[key]=source;dest=merged/rel;dest.parent.mkdir(parents=True,exist_ok=True)
        if not dest.exists() or sha(dest)!=sha(obj):shutil.copyfile(obj,dest)
        objects.append(dict(module=key,source_sha256=sha(source),object_sha256=sha(obj)))
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
paths=[merged,old/'critical-current/build']
paths += [Path((ROOT/p).read_text().strip()) for p in ['milestones/32-seven-count-four-screen/build/proofs-latest.txt','milestones/49-six-direction-pair-catalogue/build/latest.txt','milestones/28-direct-share-certificates/build/latest.txt']]
paths += [ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy']]
for root in extras:
    records=read(root/'logs/build-record.json')
    records=records if isinstance(records,list) else [records]
    for record in records:
        paths += [Path(p) for p in record.get('paths',[]) if Path(p) not in paths]
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
imports=['Share120.Geometry','Share12.Geometry','FiveCentreOverlap','CountFreeTarget']
names=['Snake9.LocalWindow.ShareWindow120.share_bound','Snake9.LocalWindow.ShareWindow12.share_bound',
    'Snake9.CountFreeBridge.shareN_eq_coreShare','Snake9.CountFreeBridge.core_share12_charge_le',
    'Snake9.CountFreeBridge.core_share_five_centre_overlap','Snake9.CountFreeBridge.core_share12_five_centre_charge_le',
    'Snake9.CountFreeTarget.upper234_of_weight_bounds','Snake9.CountFreeTarget.strict_margin']
for root in extras[1:]:
    imports += [p.stem for p in sorted((root/'lean').glob('*.lean'))]
    names += [r['theorem'] for r in read(root/'data/proof-audit.json')['theorem_audits']]
wrappers=[];remaining=[]
for root in case_roots:
    case=read(root/'data/case.json');imports.append(case['prefix']+'.Reversal')
    names += ['Snake9.LocalWindow.'+case['namespace']+'.'+s for s in ['share_bound','share_bound_rev']]
    if HERE/'adapter' in extras:
        number=case['case_number'];ds=case['selected']['directions'];lower=case['selected']['required_share']
        wrappers.append(f'''namespace Snake9.CatalogueIntegration73
open LocalWindow WindowAutomaton DirectionWindow CountFreeAdapter73
theorem canonical{number} {{m : Nat}} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = {ds} ∨ canon (dsOf p r 6).reverse = {ds}) :
    {lower} ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  apply share_bound_of_either_canonical_match (K := {lower-1}) p r {ds} hr hshape
  exact LocalWindow.{case['namespace']}.refuted
end Snake9.CatalogueIntegration73
''')
        names.append(f'Snake9.CatalogueIntegration73.canonical{number}')
if HERE/'adapter' in extras and (HERE/'adapter/lean/ConditionalCatalogueDispatch.lean').exists():
    completed={read(p/'data/case.json')['case_number'] for p in case_roots}
    portfolio=read(old/'critical-current/data/portfolio.json')['selected'];parameters=[];proofs=[]
    for index,case in enumerate(portfolio):
        number=7300+index
        if number in completed:proofs.append(f'LocalWindow.ShareWindow{number}.refuted')
        else:
            remaining.append(number);proofs.append(f'h{number}')
            parameters.append(f"    (h{number} : RefutedShare (winOf {case['directions']}) broadBounds 12 {case['required_share']-1})")
    wrappers.append('namespace Snake9.CatalogueIntegration73\nopen LocalWindow DirectionWindow CountFreeAdapter73\n'+
        'theorem partial_catalogue_share\n'+'\n'.join(parameters)+
        '\n    {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m) :\n'+
        '    windowLower p r ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by\n'+
        '  exact catalogue_share_bound '+' '.join(proofs)+' p r hr\n'+
        '#check @partial_catalogue_share\nend Snake9.CatalogueIntegration73\n')
    names.append('Snake9.CatalogueIntegration73.partial_catalogue_share')
(HERE/'lean').mkdir(exist_ok=True);(HERE/'logs').mkdir(exist_ok=True);(HERE/'data').mkdir(exist_ok=True)
source=HERE/'lean/CombinedCatalogue.lean'
source.write_text('\n'.join('import '+s for s in imports)+'\n\n'+'\n'.join(wrappers)+'\n'+'\n'.join('#print axioms '+s for s in names)+'\n',encoding='utf-8',newline='\n')
log=HERE/'logs/CombinedCatalogue.log';dest=BUILD/'CombinedCatalogue.olean';start=time.monotonic()
with log.open('w',encoding='utf-8') as f:
    r=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(dest.with_suffix('.fresh.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=180)
assert r.returncode==0,log.read_text();os.replace(dest.with_suffix('.fresh.olean'),dest)
text=log.read_text();assert not any(s in text for s in ['error:','sorryAx','failed to delete'])
if 'Snake9.CatalogueIntegration73.partial_catalogue_share' in names:
    signature=text.split("'Snake9.LocalWindow.ShareWindow120.share_bound'",1)[0]
    compact=re.sub(r'\s+','',signature)
    assert compact.count('RefutedShare(winOf')==len(remaining)
    for number in remaining:
        case=portfolio[number-7300]
        expected=f"RefutedShare(winOf{case['directions']})broadBounds12{case['required_share']-1}"
        assert re.sub(r'\s+','',expected) in compact,(number,signature)
checks=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
checks += [(s,'') for s in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert {s for s,_ in checks}==set(names) and len(checks)==len(names)
for _,axs in checks:assert set(re.findall(r'[A-Za-z][\w.]*',axs))<={'propext','Classical.choice','Quot.sound'}
out=dict(status='PASS_COMBINED_LOCAL_CATALOGUE_AND_BUDGET',case_numbers=[read(p/'data/case.json')['case_number'] for p in case_roots],
    remaining_local_certificate_cases=remaining,
    remaining_certificate_signature_checked=True,
    source_sha256=sha(source),seconds=time.monotonic()-start,checks=[dict(theorem=n,axioms=a) for n,a in checks],
    local_audit_sha256={p.relative_to(ROOT).as_posix():sha(p/'data/proof-audit.json') for p in roots},bridge_audit_sha256=sha(bridge/'data/proof-audit.json'),
    extra_audit_sha256={p.name:sha(p/'data/proof-audit.json') for p in extras[1:]},
    overlay_objects=objects,scope='Completed local theorems, previous shares and global budget coexist. The graph interpretation and a new global numerical bound remain unproved; cached support is reused.')
(HERE/'data/integration-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],out['case_numbers'],len(checks),'theorem audits',flush=True)
