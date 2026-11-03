"""Prepare a fresh14-module dependency chain and two conditional wrappers."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1];Q=R/'milestones/147-countfree-clause-semantics'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
known_comment="/- A snake's length is its number of edges. No optimality axiom is declared. -/"
reviewpath=H/'audit/import-review.json';review=read(reviewpath)
assert sha(reviewpath)=='14592e14439daded334456dca8c57002abf283ad7d8de965e427ec432778df9d'
assert review['status']=='PASS_BOUNDED_IMPORT_CLOSURE_AND_SOURCE_OBJECT_HASH_AUDIT'
for p,d in review['external_pins'].items():assert sha(p)==d,p
mapping={x['module']:x for x in review['adapter_source_mapping']};rows=[]
for m in review['new148_dependency_compile_order']:
    x=mapping[m];source=Path(x['source']);assert sha(source)==x['source_sha256']
    raw=source.read_bytes();s=raw.decode('utf-8')
    if m=='CanonicalShareAdapter':
        assert s.count('import Mathlib.Tactic\n')==1
        s=s.replace('import Mathlib.Tactic\n','import Mathlib.Tactic.IntervalCases\n')
    dest=H/'lean'/(m+'.lean')
    if dest.exists():assert dest.read_bytes()==s.encode('utf-8')
    else:dest.write_bytes(s.encode('utf-8'))
    strip=lambda b:b'\n'.join(l for l in b.split(b'\n') if not l.startswith(b'import '))
    assert strip(raw)==strip(dest.read_bytes())
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s.replace(known_comment,''))
    rows.append(dict(module=m,path=dest.relative_to(H).as_posix(),sha256=sha(dest),source=str(source),source_sha256=sha(source)))
for m in ['ShareTransfer148','ShareFromCore148']:
    p=H/'lean'/(m+'.lean');assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',p.read_text())
    rows.append(dict(module=m,path=p.relative_to(H).as_posix(),sha256=sha(p)))
plan=dict(status='PREPARED_FRESH_PROJECT_TRANSFER_CHAIN_UNCHECKED',
    module_order=[x['module'] for x in rows],framework_modules=[x['module'] for x in rows],artifacts=rows,
    prior_semantic_build=str(Q/'build'),prior_semantic_receipt_root=str(Q/'data'),
    external_library_search_paths=review['external_library_search_paths'],external_pins=review['external_pins'],
    import_review_sha256=sha(reviewpath),preparer_sha256=sha(__file__),
    shared_model_modules=['LocalWindowModel','LocalWindowShareModel'],
    selected_scope='Freshly check14 additional project dependencies and two conditional wrappers. Reuse the already checked147 semantic chain. External standard and Mathlib libraries remain trusted, with pinned entry modules and manifest.',
    local_refutation_still_required=True,core_unsat_still_required=True,new_global_upper_bound=False)
p=H/'data/transfer-plan.json';assert not p.exists();p.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8',newline='\n')
def one(s,a,b):assert s.count(a)==1,(a,s.count(a));return s.replace(a,b)
s=(Q/'scripts/check_module.py').read_text(encoding='utf-8')
s=one(s,"assert not re.search(r'\\b(sorry|admit|native_decide|axiom)\\b',source)",
    "assert not re.search(r'\\b(sorry|admit|native_decide|axiom)\\b',source.replace("+repr(known_comment)+",''))")
s=one(s,"H=Path(__file__).resolve().parents[1];R=H.parents[1]","H=Path(__file__).resolve().parents[1];R=H.parents[1];Q=R/'milestones/147-countfree-clause-semantics'")
s=one(s,"planpath=H/'data/semantic-plan.json'","planpath=H/'data/transfer-plan.json'")
s=one(s,"env['LEAN_PATH']=str(build)","external=[Path(p) for p in plan['external_library_search_paths']]\nenv['LEAN_PATH']=';'.join(map(str,[build,Q/'build']+external))")
s=one(s,"if name=='Std':continue","if name=='Std' or name.startswith('Mathlib.'):continue")
s=one(s,"rp=H/'data'/(name+'-audit.json');q=read(rp)","rp=H/'data'/(name+'-audit.json')\n    if not rp.exists():rp=Q/'data'/(name+'-audit.json')\n    q=read(rp)")
s=one(s,"for value in direct:","for p,d in plan['external_pins'].items():\n    assert sha(p)==d,p;deps[p]=d\nfor value in direct:")
s=one(s,"assert p.is_relative_to(build.resolve()) or p.is_relative_to((B.parent/'lib/lean').resolve()),p",
    "assert any(p.is_relative_to(q.resolve()) for q in [build,Q/'build',B.parent/'lib/lean']+external),p")
s=one(s,"log=str(log),paths=[str(build)]","log=str(log),paths=[str(build),str(Q/'build')]+list(map(str,external))")
s=s.replace('The standard Lean4.19 library is trusted; compiler and direct standard-library objects are pinned. All project models are freshly checked from saved sources.',
    'Lean4.19 and Mathlib libraries are trusted; compiler, direct library objects, selected entry sources and library manifest are pinned. Additional project helpers are freshly checked here;147 project semantics are reused with their exact accepted receipts.')
checker=H/'scripts/check_module.py';assert not checker.exists();checker.write_text(s,encoding='utf-8',newline='\n')
s=(Q/'scripts/run_semantics.py').read_text(encoding='utf-8')
s=s.replace('semantic-plan.json','transfer-plan.json').replace('PREPARED_MINIMAL_IMPORTS_WITH_UNCHANGED_MATHEMATICAL_INPUT','PREPARED_FRESH_PROJECT_TRANSFER_CHAIN_UNCHECKED')
s=s.replace('semantic-batch','transfer-batch').replace('semantic-progress','transfer-progress').replace('semantic-launch','transfer-launch')
s=s.replace('PASS_BOUNDED_SEMANTIC_PREFIX','PASS_BOUNDED_TRANSFER_PREFIX').replace('PASS_COMPLETE_GENERIC_AND_CONCRETE_CLAUSE_CHECKS','PASS_COMPLETE_CONDITIONAL_TRANSFER_CHAIN')
s=s.replace('Fresh generic models and exact concrete clause checks. Full contradiction and actual-snake theorem remain separate.',
    'Fresh transfer chain and actual-snake consequences with explicit local-refutation or core-Unsat premises. Complete contradiction remains separate.')
driver=H/'scripts/run_transfer.py';assert not driver.exists();driver.write_text(s,encoding='utf-8',newline='\n')
print(json.dumps(dict(status=plan['status'],modules=len(rows),source_bytes=sum((H/x['path']).stat().st_size for x in rows))))
