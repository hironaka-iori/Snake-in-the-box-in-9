from pathlib import Path
import datetime,hashlib,json,re
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports';D=Path('D:/Codex/2026-10-13/new-chat');W=D/'work';O=D/'outputs'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(name):return json.loads((H/'data'/name).read_text())
assert read('gain1-omit4-cross-1.json')['status']=='INFEASIBLE'
assert read('gain1-omit6-cross2.json')['status']=='UNKNOWN'
native=read('coordinated-squares.json');assert native['status']=='COMPLETE_NO_EXTENSION' and native['endpoint_candidates']==2358 and native['new_q9_classes']==0
names=read('current-order.json')+read('square-order.json')+['SquareExtension192'];accepted=[];pins={}
for name in names:
    q=H/'data'/(name+'-audit.json');r=json.loads(q.read_text());assert r['status']=='PASS' and r['exit_code']==0 and r['stop_reason'] is None
    for field,hashfield in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(r[field])==r[hashfield]
    for p,h in r['dependencies'].items():
        if p in pins:assert pins[p]==h
        pins[p]=h
    accepted.append({'module':name,'receipt_sha256':sha(q),'reports':len(r['axioms'])})
for p,h in pins.items():assert sha(p)==h,p
lean_text=r'''For the selected 191-edge witness, the corresponding geometric
exclusion is checked in Lean for both endpoints and all nine extension
directions. The proof permits arbitrary Boolean choices at all 190
internal positions and checks the actual alternate-corner coordinates.
It uses only nonconsecutive vertex separation and separation from the
proposed extension vertex, which are necessary conditions for an induced
path. All 18 candidate contradictions and their combined statement pass.
The complete 131-witness census remains a native computation; this Lean
result certifies the selected witness, without asserting its optimality.
'''
main=O/'snake9_research.tex';short=O/'snake9_frontier_explanation.tex';a=main.read_text(encoding='utf-8');b=short.read_text(encoding='utf-8');before_a=a;before_b=b
section=(W/'round192_section.tex').read_text().replace('% ROUND192_LEAN_RESULT',lean_text)
brief=(W/'round192_short.tex').read_text().replace('% ROUND192_LEAN_RESULT',lean_text)
marker='\\section{Construction experiments and their scope}\\label{app:experiments}';assert a.count(marker)==1 and 'sec:moving-endpoints' not in a;a=a.replace(marker,section+'\n'+marker)
a=a.replace('replace the common 95-edge path by a 97-edge path.\n\\end{abstract}', 'replace the common 95-edge path by a 97-edge path. Allowing endpoints\nto move introduces exact endpoint corrections to the same accounting.\nFor a selected 191-edge witness, a geometric Lean proof excludes every\nsimultaneous alternate-square substitution followed by one endpoint\nextension; this is a restricted construction obstruction.\n\\end{abstract}')
b=b.replace('Research state after round 191','Research state after round 192').replace('\\textbf{7. What is proved, and what remains.}',brief+'\n\\textbf{7. What is proved, and what remains.}')
b=b.replace('Round 191 adds attachment and colour restrictions, excludes at most seven\nomissions computationally, and compares lifts from fixed optimal middle\npaths.','Round 192 adds endpoint corrections and a geometric Lean exclusion of\ncoordinated square substitutions followed by extension for one selected\n191-edge witness. The full-bank exclusion remains native.').replace('research records 175--191','research records 175--192')
bib=r'''\bibitem{moving192archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Moving endpoints and coordinated square substitutions}. Research record 192, 11 November 2026. Endpoint-corrected counting, joint replacement models, full-bank native certificates and a concrete Lean geometric exclusion:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/192-moving-ports}.
'''
a=a.replace('\\end{thebibliography}',bib+'\n\\end{thebibliography}')
for text,old in [(a,before_a),(b,before_b)]:assert re.search(r'\\author\{[^\n]+',text).group()==re.search(r'\\author\{[^\n]+',old).group()
assert re.search(r'\\hypersetup\{.*?\n\}',a,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',before_a,re.S).group()
for p,text in [(main,a),(short,b)]:p.write_text(text,encoding='utf-8',newline='\n');(R/'paper'/p.name).write_bytes(p.read_bytes())
failed=[]
for q in (H/'logs').glob('*/record.json'):
    r=json.loads(q.read_text())
    if r['status']!='PASS':failed.append({'record':str(q.relative_to(H)),'stop_reason':r.get('stop_reason'),'exit_code':r['exit_code']})
completion={'round':192,'status':'PROGRESS','goal_status':'active; previous pause superseded by explicit resume','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'accepted_modules':accepted,'failed_lean_attempts':failed,'resource_interruption':'One startup gate found1062440960 free bytes, below1GiB. No compiler launched. Resumed remaining modules after1256591360 bytes became available. Limits unchanged.','general_result':'Endpoint-corrected edge, boundary and component balances; finite implications checked under explicit degree premises.','native_joint_search':{'selected_seed':'normalized bank25','target_edges':192,'at_most4_omissions_crossings_free':'INFEASIBLE','at_most6_omissions_two_crossings':'UNKNOWN120seconds','certificate_status':'No Lean contradiction certificate.'},'native_square_census':{'seeds':131,'endpoint_cases':2358,'status':'COMPLETE_NO_EXTENSION','valid_rooted_closures':147,'rooted_closure_sizes':native['closure_sizes'],'new_classes_among_rooted_closures':0,'rooted_closures_move_two_crossing_ports':False,'qualification':'Rooted closures do not enumerate all valid simultaneous substitution sets.'},'lean_square_scope':'Normalized bank25, arbitrary fixed alternate-corner choices at190 internal positions, both unchanged original endpoint positions, either end extended in any of9directions. Actual geometry checked; nonconsecutive and extension separation premises suffice. Does not certify the131-seed census or global optimality.','new_q9_record':False,'new_global_upper_bound':False,'next_scheduled_manuscript_review':200,'next_direction':'Allow larger replacement regions or reconnection of retained components; the fixed-corner one-batch transformation is exhausted for extension in the current bank. Recomputed batches and arbitrary replacements remain open.','contributor_head':'b2f85574241bd8d9aca499440b9bc0f3b4c0def0','contributor_change':'36 new production records; no independent proof rebuild or bound change.'}
(H/'data/completion.json').write_text(json.dumps(completion,indent=2)+'\n')
(H/'data/bank9-input.json').write_bytes((R/'work/bank9.json').read_bytes())
(H/'data/input-audit.json').write_text(json.dumps({'bank_source_sha256':sha(R/'work/bank9.json'),'archived_bank_sha256':sha(H/'data/bank9-input.json'),'seed_sha256':sha(H/'data/seed.json'),'script_sha256':{p.name:sha(p) for p in (H/'scripts').glob('*.py')},'main_sha256':sha(main),'short_sha256':sha(short),'mirrors_match':all(sha(O/n)==sha(R/'paper'/n) for n in [main.name,short.name]),'authors_preserved':True,'hypersetup_preserved':True,'coordinate_mapping_for_certificates':'Raw coordinate5 moved to8; raw6,7,8 moved to5,6,7. Exact vertex-by-vertex map checked before generating concrete Lean cases.','preparation_note':'First generator assertion caught using raw extension-direction labels on the normalized seed; labels were mapped before any concrete cases were saved or checked.'},indent=2)+'\n')
(H/'scripts/close.py').write_bytes(Path(__file__).read_bytes());(H/'scripts/publication.py').write_bytes((R/'milestones/191-coloured-replacements/scripts/publication.py').read_bytes())
print('SAVED',len(accepted),'accepted modules',sum(r['reports'] for r in accepted),'dependency reports; manuscripts and completion record')
