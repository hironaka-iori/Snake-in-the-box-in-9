"""Publish local checkpoint status only after the declared proof gates pass."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
audit=read(HERE/'share-proof/data/proof-audit.json');assert audit['status']=='PASS_LOCAL_SHARE_THEOREM'
integration=read(HERE/'data/integration-audit.json');assert integration['status']=='PASS_COMBINED_IMPORTS_AND_ARITHMETIC'
portfolio=read(HERE/'data/portfolio.json');assert portfolio['status']=='ALL_NINE_NATIVE_PREMISES_VERIFIED' and portfolio['uniform_complete']
native=read(HERE/'data/native-audit.json');assert native['share16_pending_shapes']==[]
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='d422a0b3dea2c2e81cb2d63294c14ff37b2237447faf5fca193ee2664951d341'
out=dict(status='VERIFIED_RESEARCH_CHECKPOINT_GLOBAL_PROBLEM_OPEN',date='2026-11-02',unconditional_interval=[191,235],conditional_upper=234,local_share12_theorem=True,local_modules=audit['modules'],local_theorem_audits=len(audit['theorem_audits']),native_share16_shapes=9,native_mixed_shapes=9,conditional_mean=496,conditional_potential_range=600,strict_margin=32,paper_sha256=sha(paper),source_head='48919e3d4d9602f2fcf145f9dff8f96128b37c75',reviewed_contributor='e26fd1b7',scope='The count-free distinct-direction share-12 theorem passes Lean. Both stronger nine-shape portfolios pass native Boolean checking. Their geometric Lean proofs and the global bridges remain open; 234 is conditional and the exact Q9 optimum is unresolved.')
(HERE/'data/checkpoint.json').write_text(json.dumps(out,indent=2)+'\n')
p=HERE/'README.md';s=p.read_text()
old='`share-proof/` contains the count-free distinct-direction share-12 proof attempt. The 73 geometric semantic batches and their composition have passed Lean. The core has 9,303 clauses and the refutation contains 3,478,301 LRAT hints. Refutation replay and the final source/axiom audit must finish before this directory reports the local theorem as checked. Consult the actual build records and `share-proof/data/proof-audit.json` if present; generated source files alone do not establish a theorem.'
new=f'''The count-free distinct-direction share-12 theorem has passed Lean, including its arbitrary-snake wrapper: **{audit['modules']} modules and {len(audit['theorem_audits'])} printed theorem audits**. The five internal counts have no additional hypotheses. The proof checks 73 geometric semantic batches, the 9,303-clause core and its 3,478,301 LRAT hints. The final axioms are limited to propext, Classical.choice and Quot.sound; no sorry, admit or native_decide is used. See `share-proof/data/proof-audit.json`. A combined-import check confirms compatibility with the earlier share-120 theorem; its generic append lemma has a distinct name to avoid duplicate declarations. Four additional axiom audits cover these imports and the conditional arithmetic.'''
assert old in s;s=s.replace(old,new)
s=s.replace('Next priority: finish the distinct-direction share-12 replay, then check the nine certificates','Next priority: check the nine certificates')
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'README.md';s=p.read_text()
s=s.replace('Next research priority: finish the count-free share-12 Lean replay, then check the nine direction-shape share certificates and their geometric meaning.','Next research priority: check the nine direction-shape share certificates and their geometric meaning. The count-free distinct-direction share-12 theorem has passed Lean and the final source audit.')
p.write_text(s,encoding='utf-8',newline='\n')
p=ROOT/'milestones/72-four-count-proof-closure/README.md';s=p.read_text().replace('The count-free distinct-direction share-12 theorem is undergoing Lean replay.','The count-free distinct-direction share-12 theorem has passed Lean and the source audit, including arbitrary coordinate normalization and removal of all count hypotheses.')
p.write_text(s,encoding='utf-8',newline='\n')
for p in [ROOT/'RESEARCH_LEDGER.md',ROOT/'handoff/2026-11-01/RESUMED_UPDATE.md']:
 p.write_text(p.read_text()+f'\nThe count-free distinct-direction share-12 theorem subsequently completed {audit["modules"]} Lean modules and {len(audit["theorem_audits"])} theorem audits. Both the uniform and mixed nine-shape targets have complete native certificates. The unconditional interval remains 191 <= a(9) <= 235; 234 remains conditional.\n',encoding='utf-8',newline='\n')
print(out)
