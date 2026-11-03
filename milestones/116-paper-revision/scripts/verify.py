"""Check manuscript preservation, actual printed data and saved proof evidence."""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re,zipfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paper=ROOT/'paper/snake9_research.tex'
with zipfile.ZipFile(HERE/'data/paper-before.zip') as z:raw=z.read('snake9_research.tex')
old=raw.decode('utf-8').replace('\r\n','\n');new=paper.read_text(encoding='utf-8')
revision=read(HERE/'data/revision.json')
assert sha(paper)==revision['paper_sha256']
assert paper.read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert old.split(r'\begin{abstract}')[0]==new.split(r'\begin{abstract}')[0]
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
prior=[m.group() for m in re.finditer(pattern,old,re.S)]
current=[m.group() for m in re.finditer(pattern,new,re.S)]
for statement in prior:assert statement in new,statement[:120]
assert len(prior)==135 and len(current)==138
added=[s for s in current if s not in prior]
assert [re.search(r'\\label\{([^}]+)\}',s)[1] for s in added]==revision['added_statement_labels']
assert old.count(r'\begin{definition}')==new.count(r'\begin{definition}')==1
refmarker=r'\clearpage'+'\n'+r'\addcontentsline{toc}{section}{References}'
assert old.split(r'\appendix',1)[1].split(refmarker,1)[0]==new.split(r'\appendix',1)[1].split(refmarker,1)[0]
labels=re.findall(r'\\label\{([^}]+)\}',new)
assert len(labels)==len(set(labels))
assert set(re.findall(r'\\label\{([^}]+)\}',old))<=set(labels)
assert set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',new))<=set(labels)
cites={k for g in re.findall(r'\\cite\{([^}]+)\}',new) for k in g.split(',')}
assert cites<=set(re.findall(r'\\bibitem\{([^}]+)\}',new))
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',new):
    if m[1]=='begin':stack.append(m[2])
    else:assert stack and stack.pop()==m[2],m[2]
assert not stack and '.lean' not in new and 'sorryAx' not in new
clean=re.sub(r'\\url\{[^}]*\}',r'\\url{URL}',new)
clean=re.sub(r'(?<!\\)%[^\n]*','',clean);clean=re.sub(r'\\[{}$%]','',clean)
level=0
for char in clean:
    if char=='{':level+=1
    elif char=='}':level-=1
    assert level>=0
assert level==0 and clean.count('$')%2==0
for left,right in [(r'\[',r'\]'),(r'\(',r'\)')]:assert clean.count(left)==clean.count(right)
previous=(ROOT/'milestones/56-packing-limit-and-revision/scripts/verify.py').read_text()
fragment=previous[previous.index('quotes=lambda'):previous.index('# Check the cycle')]
exec(compile(fragment,'printed-witness-check','exec'))
assert pairs==118673

# Check the literal arithmetic and rows printed in this revision.
assert r'111960\cdot13-227\cdot6309=23337>0' in new
assert 111960*13-227*6309==23337
assert 116160-226*496==4064
assert 1378-12==1366 and sum([43,27,24,9,1,1])==105
assert Fraction(1098960*13+8*6309+7656,4200*13+6309)==Fraction(4781536,20303)
assert Fraction(1098960+8*496+602,4200+496)==Fraction(551765,2348)
assert 5*221136-4200-2520==1098960
assert 1098960-4200*235==111960 and 1098960-4200*234==116160
table=new.split('Directions & Condition & Positions summed & Lower bound',1)[1].split(r'\end{tabular}',1)[0]
rows=re.findall(r'\$(\d{6})\$ &\s*(.*?)\s*& \$([\d,]+)\$ & (\d+)\\\\',table)
assert len(rows)==10
graph=read(ROOT/'milestones/115-total-count-certificate/data/universal345-total22/results.json')
printed={(shape,tuple(int(p)-1 for p in pos.split(',')),int(lower)) for shape,_,pos,lower in rows}
saved={(''.join(map(str,row['directions'])),tuple(row['positions']),row['lower']) for row in graph['rules']}
assert printed==saved
assert all(row['all_edge_inequalities_checked'] for row in graph['profiles'])
assert {row['comparison_bound'] for row in graph['profiles']}=={'4781536/20303','551765/2348'}

# Reused source/object/log receipts are evidence, not a new compiler run.
pins=read(HERE/'data/new-result-pins.json');checked=0
for name,digest in pins['source_pins'].items():assert sha(ROOT/name)==digest,name
for record in pins['checked_receipts']:
    receipt=read(ROOT/record['receipt'])
    assert receipt['exit_code']==0 and receipt['status'].startswith('PASS_')
    assert sha(ROOT/record['source'])==receipt['source_sha256']
    assert sha(ROOT/record['object'])==receipt['olean_sha256']
    assert sha(ROOT/record['log'])==receipt['log_sha256']
    for entry in receipt['theorem_audits']:assert set(entry['axioms'])<={'propext','Classical.choice','Quot.sound'}
    checked+=len(receipt['theorem_audits'])
extra=[]
for folder,module in [('109-relaxed-graph-test','ActualRelaxed109'),('109-relaxed-graph-test','NewRelaxed109'),('109-relaxed-graph-test','ReferenceCoverage109'),('110-critical-cycle-core-screen','PlainCount110')]:
    base=ROOT/'milestones'/folder;p=base/'data'/(module+'-audit.json');r=read(p)
    assert r['exit_code']==0 and r['status'].startswith('PASS_')
    source=base/'lean'/(module+'.lean');log=base/r['log']
    objects=[base/b/(module+'.olean') for b in ['build','build-isolated']]
    objects=[p for p in objects if p.exists() and sha(p)==r['olean_sha256']]
    assert len(objects)==1,module
    assert sha(source)==r['source_sha256'] and sha(log)==r['log_sha256']
    assert sha(base/r['source_snapshot'])==sha(source)
    for entry in r['theorem_audits']:assert set(entry['axioms'])<={'propext','Classical.choice','Quot.sound'}
    checked+=len(r['theorem_audits'])
    extra.append(dict(module=module,receipt=p.relative_to(ROOT).as_posix(),receipt_sha256=sha(p),source_sha256=sha(source),log_sha256=sha(log),object_sha256=sha(objects[0])))
out=dict(status='PASS_PAPER116_SOURCE_AND_MATHEMATICAL_DATA',paper_sha256=sha(paper),
    prior_statements=len(prior),current_statements=len(current),unchanged_prior_statements=len(prior),
    named_definitions=1,new_definitions=0,added_statement_labels=revision['added_statement_labels'],
    metadata_preserved=True,all_appendices_preserved=True,editor_identical=True,labels=len(labels),
    references_resolved=True,printed_snakes=13,vertex_pair_checks=pairs,parsed_sum_rules=rows,
    graph_results_sha256=sha(ROOT/'milestones/115-total-count-certificate/data/universal345-total22/results.json'),
    proof_pins_sha256=sha(HERE/'data/new-result-pins.json'),additional_receipts=extra,
    reused_modules=len(pins['checked_receipts'])+len(extra),printed_axiom_reports=checked,new_lean_checks=0,
    scope='Source structure and preservation, all printed snakes, numerical table/arithmetic, reused exact proof receipts. No new compiler or full-edge scan, clean dependency rebuild, completed potential certificate or new global bound. PDF compilation and layout are separate.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['parsed_sum_rules','additional_receipts']},indent=2))
