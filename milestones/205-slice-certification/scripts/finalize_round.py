"""Record the terminal proof state and update the existing manuscripts in place."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
assert not (H/'data/replay-batch.lock').exists()
gate=snapshot();assert not gate['processes'] and not gate['errors'],gate
cache={}
def sha(path):
 p=Path(path);key=str(p)
 if key not in cache:cache[key]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[key]
proofs=[]
for receipt in sorted((H/'data').glob('*-audit.json')):
 d=json.loads(receipt.read_bytes());assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
 for name,key in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[name])==d[key],d['module']
 for p,v in d['dependencies'].items():assert sha(p)==v,p
 assert len(d['axioms'])==Path(d['source']).read_text(encoding='utf-8').count('#print axioms')
 assert all(set(t['axioms'])<={'propext','Classical.choice','Quot.sound'} for t in d['axioms'])
 proofs.append(dict(module=d['module'],reports=len(d['axioms']),receipt=receipt.relative_to(H).as_posix(),sha256=sha(receipt),seconds=d['seconds']))
names={p['module'] for p in proofs};covers=sorted(int(n.rsplit('_',1)[1]) for n in names if n.startswith('PartitionCover205_'));active=sorted(n for n in names if n.startswith('ActivePair205_'))
finiteplan=json.loads((H/'data/batch-plan.json').read_bytes());finite=sum(n in names for n in finiteplan['module_order'])
finite_status=f'Lean accepts complete coverage for {len(covers)} of the 254 explicit finite models, using {finite} of the 625 planned data, elimination and cover modules. This statement concerns assignments to the literal domains and compatibility tables.'
allgraphs=len(active)==28
cube_status=('Lean checks the three-coordinate parity/antipodal identities, the induced injective correspondence of selected labels, and two complete four-dimensional paths with different endpoint distances.' if 'CubeThree205' in names else 'The three-coordinate extension argument has a written proof and independent review; its proposed Lean component checks have no accepted receipt.')
history_status=('All 56 source-specific active graphs are now checked in Lean after splitting the assertions into blocks of eight positions. The complete geometric classification and its count still require an assembled Lean proof.' if allgraphs else f'{2*len(active)} of the 56 source-specific active graphs have accepted Lean certificates. The remaining graph checks and the assembled geometric classification are pending; native spanning trees are saved for all 56 graphs.')
contributor=json.loads((H/'data/contributor.json').read_bytes())
completion=dict(round=205,status='PROGRESS',pause_requested=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_head=subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse','HEAD'],cwd=R,text=True).strip(),new_q9_record=False,new_global_bound=False,accepted_lean_modules=len(proofs),theorem_reports=sum(p['reports'] for p in proofs),proofs=proofs,finite_models=dict(accepted_partitions=covers,total_partitions=254,accepted_modules=finite,planned_modules=625,leaves=321,scope='Finite encoded constraint coverage only; geometric domain/table/leaf bridges remain pending.'),active_graphs=dict(accepted_pairs=active,accepted_graphs=2*len(active),total_graphs=56,scope=history_status),history_theorem=dict(written_proof=True,independent_review=True,complete_lean_assembly=False,ordered_target_count='2^(1+c0+c1)',restricted_class_count='2^(c0+c1-r)'),contributor=contributor,source_sha256=sha(H/'data/lower-dimensional-input.json'),native_leaf_witnesses=321,resource_state_at_close=gate)
completion['three_coordinate_extension']=dict(written_proof=True,independent_review=True,complete_lean_assembly=False,component_module_accepted='CubeThree205' in names,saved_parent_consequence='At least four changed coordinate histories are necessary for a new class up to global cube isometry and possible reversal, conditional on the retained native all-partition comparison.')
completion['native_forward_leaf_witnesses']=321
(H/'data/completion.json').write_text(json.dumps(completion,indent=2)+'\n')
note=H/'MATHEMATICAL_NOTE.md';s=note.read_text(encoding='utf-8')
s=s.replace('Consult data/completion.json for the accepted finite-model coverage at publication.',finite_status)
s=s.replace('@@CUBE_THREE_STATUS@@',cube_status)
if 'CubeThree205' in names:
 s=s.replace('The local extension theorem fails in Q4: map 0000 to 0000 and 0011 to 1111. Parity, injection, and selected-pair adjacency/nonadjacency are preserved, but the distance changes from two to four. This is a counterexample for selected subsets; it does not supply a pair of whole snakes or establish that a four-coordinate change succeeds on the saved parent.','The extension theorem fails in Q4 even for whole induced paths. Take P=(0,1,3,7,6) and Q=(0,1,3,7,15), with integers interpreted as four-bit words. Both have four edges, and corresponding vertices have equal parity. The indexed correspondence preserves every selected edge and nonedge. Their endpoint distances are two and four, so no cube isometry can carry one path to the other, even allowing reversal. Lean checks both entire paths, distinctness, parity alignment and endpoint distances. This supplies a small sharpness example for the extension theorem; it constructs no new Q8 parent or Q9 record.')
if allgraphs:
 s=s.replace('The source-specific active graphs have native spanning trees; their attempted Lean certificates exceeded the existing memory limit.','The source-specific active graphs now have accepted Lean spanning-tree certificates; earlier unchunked attempts exceeded the existing memory limit.')
 s=s.replace('The general spanning-tree constancy theorem passes Lean. The large source-specific tree assertions did not pass within the 256 MiB per-process limit. Both quantified and Boolean-list versions were stopped by the guard; neither is counted as accepted. Splitting the finite assertions into smaller independently checked files is the next concrete step. No missing proof is replaced by a trusted native computation.','The general spanning-tree constancy theorem and all 56 source-specific graph certificates pass Lean. The initial quantified and Boolean-list versions were stopped by the 256 MiB guard. Splitting the finite assertions into eight-position lemmas resolved that failure. The complete geometric theorem and counting assembly remain pending.')
 s=s.replace('finish the finite tree certificates and assemble the coordinate-history theorems','assemble the coordinate-history theorems')
s=s.replace('## Finite slice-model coverage','The same native calculation on the saved 26-edge Q6 and 50-edge Q7 inputs also finds one restricted block-isometry class for every coordinate pair: 15 of 15 and 21 of 21, respectively. The Q8 result is 28 of 28. These are comparisons of one saved parent in each dimension, with fixed length and indexed base words; they do not establish a universal dimensional recurrence. See data/dimension-history-counts.json.\n\n## Finite slice-model coverage')
note.write_text(s,encoding='utf-8')
main_add=(H/'data/paper-addition.tex.txt').read_text(encoding='utf-8').replace('@@FINITE_STATUS@@',finite_status).replace('@@CUBE_THREE_STATUS@@',cube_status)
front_add=(H/'data/frontier-addition.tex.txt').read_text(encoding='utf-8').replace('@@FINITE_STATUS@@',finite_status).replace('@@CUBE_THREE_STATUS@@',cube_status)
if 'CubeThree205' in names:
 main_add=main_add.replace('The local extension assertion fails in $Q_4$: the correspondence\n$0000\\mapsto0000$, $0011\\mapsto1111$ preserves parity and all\nselected-pair adjacency relations, yet changes distance from two\nto four. It cannot extend to a cube isometry. This is a local\ncounterexample; it supplies no whole-snake construction.','The extension assertion fails in $Q_4$ even for whole induced\npaths. In integer encoding, take\n\\[\nP=(0,1,3,7,6),\\qquad Q=(0,1,3,7,15).\n\\]\nBoth are induced four-edge paths with matching parity at each\nindex. Their endpoint distances are two and four, so their\nindexed correspondence cannot extend to a cube isometry. They\nremain inequivalent when reversal is allowed. Lean checks both\ncomplete paths, distinctness, parity alignment and these distances.\nThis example constructs no new $Q_8$ parent or $Q_9$ record.')
 front_add=front_add.replace('In four coordinates\nthe local extension principle fails: $0000,0011$ can map to\n$0000,1111$, preserving parity and nonadjacency while changing\ndistance. This identifies an available direction; it gives no\nwhole-snake construction.','In four coordinates\nthe extension principle fails even for whole paths: $(0,1,3,7,6)$\nand $(0,1,3,7,15)$ are induced paths with matching indexed parity\nand endpoint distances two and four. Lean checks both entire\nexamples. This establishes the extension theorem\'s dimensional\nboundary; it supplies no new $Q_8$ or $Q_9$ construction.')
if allgraphs:
 main_add=main_add.replace('The attempted source-specific graph checks exceeded the existing\nmemory limit and are excluded from the accepted results.','All 56 source-specific graph certificates also pass after the\nfinite assertions are split into blocks of eight positions. Earlier\nunchunked attempts exceeded the existing memory limit.')
 front_add=front_add.replace('The source-specific graph checks exceeded\nthe memory limit and are saved for smaller proof units.','All 56 source-specific graph certificates also pass after splitting\nthe finite assertions into blocks of eight positions. The initial\nunchunked attempts exceeded the memory limit.')
main_add=main_add.replace('\\paragraph{Finite slice certificates.}','The saved 26-edge $Q_6$ and 50-edge $Q_7$ examples also have\none restricted block-isometry class for all 15 and 21 coordinate\npairs, respectively, by native component calculation. These three\nindividual examples do not establish a dimensional recurrence.\n\n\\paragraph{Finite slice certificates.}')
doc_records=[]
for basename,addition,marker in [('snake9_research.tex',main_add,'\\section{Construction experiments and their scope}'),('snake9_frontier_explanation.tex',front_add,'\\textbf{7. What is proved, and what remains.}')]:
 p=Path('D:/Codex/2026-10-13/new-chat/outputs')/basename;before=p.read_bytes();text=before.decode('utf-8').replace('\r\n','\n');head=text.split('\\begin{document}',1)[0]
 assert marker in text and 'Two-coordinate history classification' not in text
 text=text.replace(marker,addition+marker,1)
 if basename=='snake9_research.tex':
  text=text.replace('single-three-cycle operations leave the saved 191-edge bank closed.','single-three-cycle operations leave the saved 191-edge bank closed.\nA separate classification counts all ordered embeddings with only two\ncoordinate histories free and proves whole-path rigidity when the two\nactive base graphs are connected. Its proof is written; the complete\nLean assembly remains pending.')
  bib='\\bibitem{research205}\nI.~Hironaka, T.~Ma, and S.~Zhan. \\emph{Two-coordinate history\nclassification and finite slice certificates}. Research record 205,\n14 November 2026.\n\\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/205-slice-certification}.\n\n'
  text=text.replace('\\end{thebibliography}',bib+'\\end{thebibliography}',1)
  assert text.split('\\begin{document}',1)[0]==head
 else:
  text=text.replace('and no new witness. The current sufficient pending-share profile','and no new witness. A whole-path classification now restricts changes\nto one or two coordinate histories; its argument and proof-assistant\nboundaries are explained in Section 6. The current sufficient pending-share profile')
  text=text.replace('Research state after round 204','Research state after round 205').replace('records 175--204','records 175--205')
  text=text.replace('The next certification task is to check the complete 254-partition\ncalculation in Lean. A construction beyond this restriction must','Round 205 advances certification of the 254-partition calculation\nas described below. A construction beyond this restriction must')
 data=text.replace('\n','\r\n').encode('utf-8') if b'\r\n' in before else text.encode('utf-8')
 p.write_bytes(data);(R/'paper'/basename).write_bytes(data)
 doc_records.append(dict(editor=str(p),mirror=str(R/'paper'/basename),before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(data).hexdigest()))
(H/'data/manuscript-edits.json').write_text(json.dumps(doc_records,indent=2)+'\n')
summary=f'''# Round 205: coordinate-history rigidity and slice certificates

For a nonempty ordered induced path with all indexed coordinates except two fixed, the exact number of target paths is 2^(1+c0+c1), where c0,c1 count the two active base graphs' components. There are 2^(c0+c1-r) classes under global isometries of the two free coordinates, with r nonempty parity graphs. Connected active graphs force one global isometry on the whole snake. The theorem has a written proof and independent review; its complete Lean assembly is pending.

The three-coordinate partial-extension theorem goes further: every parity-preserving induced selected correspondence in Q3 extends to a cube isometry. Therefore changes to at most three coordinate histories are already included in the saved parent's native slice-rigidity comparison. A new class, up to global cube isometry and reversal, requires at least four changed histories at the same length and fixed index matching. {cube_status} This consequence still inherits the native census's verification boundary.

{finite_status}

{history_status}

There are {len(proofs)} accepted Lean modules with {sum(p['reports'] for p in proofs)} theorem dependency reports. Explicit native global-isometry witnesses are saved for all 321 finite leaves. The actual geometry-to-domain bridge, table interpretation and leaf-witness replay remain pending. No longer Q9 snake or improved global bound is claimed.

Read [the proof and scope](MATHEMATICAL_NOTE.md), [verification receipts](data/completion.json), [active trees](data/active-trees.json), [leaf witnesses](data/leaf-witnesses.json) and [the count review](logs/history-count-review.md). All failed attempts are retained under logs. The user requested a pause after this round; resume only on a subsequent instruction.
'''
(H/'README.md').write_text(summary,encoding='utf-8')
rootreadme=R/'README.md';old=rootreadme.read_text(encoding='utf-8');prefix=summary.replace('# Round 205: coordinate-history rigidity and slice certificates','# Current result after round 205').replace('](MATHEMATICAL_NOTE.md)','](milestones/205-slice-certification/MATHEMATICAL_NOTE.md)').replace('](data/','](milestones/205-slice-certification/data/').replace('](logs/','](milestones/205-slice-certification/logs/')
rootreadme.write_text(prefix+'\n## Earlier checkpoints\n\n'+old,encoding='utf-8')
handoff=f'''# Current state after round 205

The user requested a pause after this round. Finish publication, pause the goal and stop; resume only on a subsequent user instruction. Round205 is PROGRESS. No new Q9 witness, improved global numerical bound or proof of optimality was obtained. The hypothesis 196 remains unresolved.

Read milestones/205-slice-certification/MATHEMATICAL_NOTE.md, data/completion.json and the four independent review reports under logs. The latest focus is a symmetry applying to the whole snake and fundamental proofs.

GENERAL RESULT: For a nonempty ordered induced path P=((z_i,u_i)), u_i in Q2, preserve each indexed base word z_i. The two active graphs have occupied base words of each source block parity and base-cube adjacency. Their component counts are c0,c1 (zero for empty); r is the number of nonempty graphs. There are exactly 2^(1+c0+c1) ordered target induced paths, and 2^(c0+c1-r) classes under GLOBAL ISOMETRIES OF THE TWO BLOCK COORDINATES ONLY. No starting word or endpoints are fixed. Full cube isometries and reversal can merge further classes.

PROOF: Full parity alternates, so the block-parity difference is constant. Normalize it by one global bit flip. In each base slice and parity diagonal, injection extends uniquely to identity or diagonal transposition. Unequal switches on neighbouring active base words toggle adjacency, so switches are constant on components. Conversely, component-constant switches preserve every selected pair. Distinct choices differ at a selected word. The eight square isometries have stabilizer size 2^(2-r), which gives the class count. All steps have a written proof and independent review. A one-coordinate change is directly forced to be one global flip.

THREE COORDINATES: A parity-preserving injection of any selected subset of Q3 preserving adjacency AND nonadjacency extends to a cube isometry. Four even antipodal representatives label the words; the selected correspondence induces a partial injective map of labels. All 24 full label permutations are realized by even translations and coordinate permutations. Thus the common parity normalization places every three-history change inside the slice-isometry family. Together with native all-partition rigidity, a new class of the saved98-edge parent up to global cube isometry AND POSSIBLE REVERSAL requires at least FOUR changed histories at the same length and fixed index matching. {cube_status} Full Lean assembly remains pending. The Q4 pair 0000,0011 -> 0000,1111 is a local failure of extension (distance2 becomes4); it is not a whole-snake construction. Search beyond slice isometries only in blocks of at least four coordinates, or change the parent/length/order.

SAVED PARENTS: All 28 pairs of the saved 98-edge Q8 parent have both active graphs connected. {history_status} One-/two-coordinate history changes cannot give a different class for this parent under the written theorem. Native comparisons of the saved Q6/Q7 parents give 15/15 and 21/21 rigid pairs too. This is not a recurrence or a classification of all optimal parents. Three or more coordinate histories, changed length/order, and different parents remain outside this restriction.

FINITE CERTIFICATE: {finite_status} The complete prepared model has 5821 variables, 23892 initial candidates, 460858 compatibility entries, 16166 initial arc removals, 7726 surviving values, and 321 complete leaves. The exact files partition-i.json and cover-i.json are indexed 0..253. Elimination rejects a value only against the ENTIRE current neighbour domain. Pointwise selected-image deduplication has a written completeness proof. All leaf isometry witnesses are in data/leaf-witnesses.json with permutation, offset, orientation and all 99 images, checked natively.

LEAN BOUNDARY: {len(proofs)} accepted modules, {sum(p['reports'] for p in proofs)} reports, exact hashes in completion.json. Generic parity, diagonal extension, spanning-tree constancy and finite-domain elimination pass. The complete geometric history theorem/count is not assembled in Lean. The full finite slice rigidity proof still lacks actual-domain completeness, exact geometric table interpretation and kernel-checked global leaf witnesses. Do not turn finite constraint coverage into a geometric rigidity theorem. Source identity is pinned to the same saved lower-dimensional input.

ON RESUMPTION: first inspect completion.json and the final batch state. Keep accepted source/object/receipt bytes immutable. The existing batch driver reuses accepted modules. If any partition covers remain pending, continue the fixed module order and repair only actual failures. For active graphs, the latest source uses eight-position lemmas (chunk_active_checks.py after emit_active_trees.py); do not regenerate already accepted files with the old unchunked generator. Then assemble the generic history theorem and the three geometric bridges. Proof resources stay one heavy worker, 1 GiB free at Lean startup, 768 MiB reserve, 256 MiB private limit, 60 seconds, -j1 -s8192. No guard should be weakened to finish a certificate.

CONTRIBUTOR: origin/research/unconditional-241 was inspected at {contributor['ref']}. Its last report is 07:57 UTC 14 November: 3115/3127 modules built. This is contributor-reported, not an independent rebuild. No merge occurred. Archived235 rebuild remains pending;233/234 remain conditional. Only fetch named main and research/unconditional-241 refs, avoiding large temporary xfer branches.

PRESERVED: round204 native all-254-partition slice-isometry rigidity and its equivariant iteration consequence; Q9 bank closure under the covered switch/rotation families; round203 different Q7 parent and its examined 92-vertex pairing limit; round200's 13 secondary repair cases. Whole-paper review was round200; next is210.

DOCUMENTS: Existing D:/Codex/2026-10-13/new-chat/outputs manuscripts were edited in place and mirrored byte-for-byte to E:/Snake-in-a-box/paper. Compile with the built-in editor tool before publication, frontier first and main last, and preserve authors and local hypersetup. Unrelated .gitignore and milestone50 critical-family.json edits are outside publication scope. Publication uses the exact-byte helper in this milestone. No background research job should remain when the goal is paused.
'''
handoff=handoff.replace('Three or more coordinate histories, changed length/order, and different parents remain outside this restriction.','The extension theorem above also excludes three-coordinate changes at the native comparison level. Four or more changed histories, changed length/order, and different parents remain available directions.')
if 'CubeThree205' in names:
 handoff=handoff.replace('The Q4 pair 0000,0011 -> 0000,1111 is a local failure of extension (distance2 becomes4); it is not a whole-snake construction.','Lean also checks the whole Q4 paths (0,1,3,7,6) and (0,1,3,7,15), with matching indexed parity and endpoint distances2 and4. They establish failure of extension in dimension4 even for whole induced paths. They supply no new Q8 parent or Q9 record.')
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_text(handoff,encoding='utf-8')
pub=H/'scripts/publication.py';pub.write_text(pub.read_text(encoding='utf-8').replace('Round204 research artifacts','Round205 research artifacts'),encoding='utf-8')
print('SAVED',len(proofs),'accepted modules;',len(covers),'partition covers;',2*len(active),'active graphs;',sum(p['reports'] for p in proofs),'reports')
