from pathlib import Path
import datetime,hashlib,json,re,sys
R=Path('E:/Snake-in-a-box');H=R/'milestones/191-coloured-replacements';D=Path('D:/Codex/2026-10-13/new-chat');W=D/'work';O=D/'outputs'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(n):return json.loads((H/'data'/n).read_text())
small=read('optimal-middle-6-target0.json');seven=read('optimal-middle-7-target0.json');eight=read('optimal-middle-8-target192.json')
assert small['status']=='OPTIMAL' and small['joined_edges']==48
assert seven['status']=='FEASIBLE' and seven['joined_edges']==89
assert eight['status']=='UNKNOWN', 'Inspect a changed Q9 outcome before publication.'
assert read('omissions-at-most-6.json')['status']=='INFEASIBLE'
assert read('omissions-at-most-7.json')['status']=='INFEASIBLE'
assert read('omissions-at-most-8.json')['status']=='UNKNOWN'
context=read('omissions-at-most-96-context00.json');assert context['status']=='UNKNOWN'
enumeration=read('fixed26-enumeration.json') if (H/'data/fixed26-enumeration.json').exists() else None
context_text='''A separate query retains the outer components of the first saved
nine-dimensional configuration while allowing the middle path to change
without an omission limit. The 97-edge target remains unresolved after
120 seconds. This supplies neither a construction nor an exclusion.
'''
lift_text=r'''\paragraph{Optimal middle paths need not give optimal lifts.}
For a fixed middle path of $b$ edges, let the two compatible outer
paths together use $u$ vertices. Their total edge count is $u-2$, so
the lifted snake has $b+u$ edges after the two crossings are added.
This makes compatibility part of the construction objective.

With the displayed optimal 26-edge path in $Q_6$ fixed as the middle,
the maximum is $u=22$, giving a 48-edge lift. The solver establishes
this restricted optimum in 0.328 seconds and supplies a witness with
outer lengths 2 and 18. In contrast, the previously checked 50-edge
construction uses a 24-edge middle and outer lengths 18 and 6:
\[
2+26+18+2=48,\qquad 18+24+6+2=50.
\]
This comparison concerns the specified middle paths. It gives no
classification of all optimal 26-edge snakes.

% ENUMERATION_RESULT

With the displayed 50-edge $Q_7$ path fixed, a 120-second optimization
finds an 89-edge lift and does not establish optimality. The earlier
restricted exclusion of a lift of at least 98 edges remains applicable,
so the attainable maximum in this fixed family is computationally
between 89 and 97. Both numerical upper statements retain their native
certificate limitations.

Finally, fixing the displayed 98-edge $Q_8$ path and seeking a
192-edge lift gives no resolution after 180 seconds. Singleton outer
paths are allowed in all three models. The search models enforce
induced degrees at most two, degree at most one at the two ports,
two components by edge count, and a flow requiring every component
to contain a port. Hence each feasible selected graph is exactly a
pair of disjoint nonadjacent paths, one at each port. Every returned
joined witness also passes a direct all-pairs adjacency check.

The useful direction is to vary the middle path and its compatible
outer paths together. Maximizing the middle length alone can reduce
the resulting lift, as the $Q_6$ comparison demonstrates.
'''
short_lift=r'''The lower-dimensional comparison also shows why compatibility matters.
With the displayed optimal 26-edge $Q_6$ path fixed as the middle,
the solver gives a maximum 48-edge two-crossing lift, whereas the
known 50-edge construction uses a shorter 24-edge middle:
\[
2+26+18+2=48<50=18+24+6+2.
\]
This is a restriction for the displayed seed, without a classification
of all optimal 26-edge paths. With the displayed 50-edge middle in
$Q_7$, an 89-edge lift is found; its restricted optimum remains
between 89 and 97 using the earlier exclusion. The 192-edge target
with the displayed 98-edge middle in $Q_8$ remains unresolved after
180 seconds. These computations support searching for compatible
middle and outer components together. They provide no new record.
'''
if enumeration:
    assert enumeration['status']=='COMPLETE' and enumeration['maximum_joined_edges']==48
    enum_text=('An independent enumeration lists all '+str(enumeration['path_counts'][0])+
      ' and '+str(enumeration['path_counts'][1])+' induced paths from the respective ports\n'
      'in the allowed graph, including singleton paths. Examining compatible\n'
      'pairs, with pruning only by their total size, again gives a maximum\n'
      'of 22 outer vertices. This is a complete native enumeration; a Lean\n'
      'completeness certificate remains pending.')
else:enum_text='An independent path-pair enumeration did not complete within its resource limit; the restricted optimum above relies on the solver result.'
lift_text=lift_text.replace('% ENUMERATION_RESULT',enum_text)
section=(W/'round191_section.tex').read_text().replace('% ROUND191_CONTEXT_RESULT',context_text).replace('% ROUND191_LIFT_RESULT',lift_text)
brief=(W/'round191_short.tex').read_text().replace('% ROUND191_CONTEXT_RESULT',context_text).replace('% ROUND191_SHORT_LIFT_RESULT',short_lift)
main=O/'snake9_research.tex';short=O/'snake9_frontier_explanation.tex';a=main.read_text(encoding='utf-8');b=short.read_text(encoding='utf-8');old_a=a;old_b=b
assert 'sec:attachment-colour' not in a
marker='\\section{Construction experiments and their scope}\\label{app:experiments}'
assert a.count(marker)==1;a=a.replace(marker,section+'\n'+marker)
a=a.replace('computational exclusions require at least six omitted vertices to','computational exclusions require at least eight omitted vertices to')
a=a.replace('five-omission replacements. Together with the earlier cases, the current\ncomputational restriction is','five-omission replacements. Together with the earlier cases, the round-190\ncomputational restriction was')
a=a.replace('Thus the current lower restriction of six omitted vertices and the','The lower restriction of six omitted vertices at that stage and the')
a=a.replace('explicit example omitting 44 leave a substantial gap for the minimum','explicit example omitting 44 left a substantial gap for the minimum')
b=b.replace('Research state after round 190','Research state after round 191')
b=b.replace('The combined computational restriction is now at least six omitted','The round-190 computational restriction was at least six omitted')
b=b.replace('Thus the current lower restriction of six omitted vertices and the','The lower restriction of six omitted vertices at that stage and the').replace('explicit example omitting 44 leave a substantial gap for the minimum','explicit example omitting 44 left a substantial gap for the minimum')
b=b.replace('\\textbf{7. What is proved, and what remains.}',brief+'\n\\textbf{7. What is proved, and what remains.}')
b=b.replace('Round 190 adds the replacement component balance and the five-omission\nexclusion. The manuscript-wide consistency review is complete; it does\nnot replace the pending certificate and proof rebuilds.','Round 191 adds attachment and colour restrictions, excludes at most seven\nomissions computationally, and compares lifts from fixed optimal middle\npaths. The manuscript-wide review completed in round 190 remains separate\nfrom the pending certificate and proof rebuilds.')
b=b.replace('research records 175--190','research records 175--191')
bib=r'''\bibitem{replacement191archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Attachment balance, coloured replacements and fixed-middle lifts}. Research record 191, 11 November 2026. Finite counting proofs, replacement models, dimensional comparisons and proof receipts:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/191-coloured-replacements}.
'''
a=a.replace('\\end{thebibliography}',bib+'\n\\end{thebibliography}')
for text,old in [(a,old_a),(b,old_b)]:
    assert re.search(r'\\author\{[^\n]+',text).group()==re.search(r'\\author\{[^\n]+',old).group()
assert re.search(r'\\hypersetup\{.*?\n\}',a,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',old_a,re.S).group()
for p,text in [(main,a),(short,b)]:p.write_text(text,encoding='utf-8',newline='\n');(R/'paper'/p.name).write_bytes(p.read_bytes())
accepted=[];pins={}
for name in read('current-order.json'):
    p=H/'data'/(name+'-audit.json');j=json.loads(p.read_text());assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
    assert sha(j['source'])==j['source_sha256'] and sha(j['object'])==j['olean_sha256'] and sha(j['log'])==j['log_sha256']
    for f,h in j['dependencies'].items():assert sha(f)==h; pins[f]=h
    accepted.append({'module':name,'receipt_sha256':sha(p),'reports':len(j['axioms'])})
failed=[]
for p in (H/'logs').glob('*/record.json'):
    j=json.loads(p.read_text())
    if j['status']!='PASS':failed.append({'record':str(p.relative_to(H)),'reason':j.get('stop_reason'),'exit_code':j['exit_code']})
completion={'round':191,'status':'PROGRESS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'goal_status':'pause_after_publication_requested_by_user','accepted_modules':accepted,'failed_attempts':failed,'minimum_omissions_for_fixed_port97':{'value':8,'status':'native solver exclusion; Lean contradiction certificate pending'},'unknown_queries':['at most eight omissions','unrestricted middle with first outer context fixed','fixed98-middle Q9 target192'],'fixed_optimal_middle_lifts':{'Q6_middle26':{'optimum':48,'solver_status':small['status'],'native_enumeration':enumeration is not None},'Q7_middle50':{'witness':89,'inherited_restricted_upper':97,'optimum_known':False},'Q8_middle98':{'target':192,'status':eight['status']}},'new_q9_record':False,'new_global_upper_bound':False,'next_scheduled_manuscript_review':200,'contributor_head':'f393c48e5e583e57d3cbb66e4330f960033229b1','next_direction':'Optimize the middle path together with its compatible two outer paths; fixed optimal low-dimensional seeds need not give the best lifts. Eight-omission local search remains unresolved.'}
(H/'data/completion.json').write_text(json.dumps(completion,indent=2)+'\n')
(H/'scripts/close.py').write_bytes(Path(__file__).read_bytes())
(H/'scripts/publication.py').write_bytes((R/'milestones/190-exchange-constraints/scripts/publication.py').read_bytes())
(H/'data/document-update.json').write_text(json.dumps({'main_before_sha256':hashlib.sha256(old_a.encode()).hexdigest(),'short_before_sha256':hashlib.sha256(old_b.encode()).hexdigest(),'main_after_sha256':sha(main),'short_after_sha256':sha(short),'authors_preserved':True,'hypersetup_preserved':True,'mirrors_match':all(sha(O/n)==sha(R/'paper'/n) for n in [main.name,short.name])},indent=2)+'\n')
print(json.dumps(completion,indent=2))
