"""Independently compare generated Lean literal rules with the pinned model rows."""
from pathlib import Path
import ast,hashlib,json,re

HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1];PREV=HERE.parent/'94-history-share-dispatch'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=read(PREV/'data/variants.json')['rows'];proofs=read(PREV/'data/credit-provenance.json')['rows']
assert len(rows)==len(proofs)==55
inputs={str(p.relative_to(ROOT)):sha(p) for p in [PREV/'data/variants.json',PREV/'data/credit-provenance.json',Path(__file__)]}
seen_rules=[];seen_words=[];seen_caps=[]
for batch in range(11):
    rf=HERE/'lean'/f'ConcreteRules95Batch{batch:02}.lean';wf=HERE/'lean'/f'ConcreteWords95Batch{batch:02}.lean'
    inputs[str(rf.relative_to(ROOT))]=sha(rf);inputs[str(wf.relative_to(ROOT))]=sha(wf)
    rtext=rf.read_text();wtext=wf.read_text()
    matches=re.findall(r'def rule(\d{3}) : Rule :=\s*⟨signature(\d{3}), variants(\d{3}), (\[[^\]]*\]), (\d+), (\d+)⟩',rtext)
    assert len(matches)==5
    for sid,sig,var,caps,geo,strong in matches:
        i=int(sid);r=rows[i]
        assert sid==sig==var and r['share_index']==i
        assert ast.literal_eval(caps)==sorted((int(k),v) for k,v in r['caps'].items())
        assert (int(geo),int(strong))==(r['geometric_lower'],r['lower'])
        seen_rules.append(i)
    matches=re.findall(r'theorem word_(\d{3})_(\d+) : WordShareBound (\[[^\]]*\]) (\d+) := by(.*?)(?=\n#print axioms)',wtext,re.S)
    for sid,j,word,lower,body in matches:
        i=int(sid);j=int(j);r=rows[i];p=proofs[i]['word_proofs'][j]
        assert ast.literal_eval(word)==r['variants'][j]==p['word']
        assert int(lower)==r['geometric_lower']
        assert p['geometry_theorem']+' p P s hr hP' in body
        assert ('word_share_of_final_nine' in body)==(i==6)
        seen_words.append((i,j))
    matches=re.findall(r'theorem capped_(\d{3})_(\d+) : WordCappedShareBound (\[[^\]]*\]) (\[[^\]]*\]) (\d+) := by(.*?)(?=\n#print axioms)',wtext,re.S)
    for sid,j,word,caps,lower,body in matches:
        i=int(sid);j=int(j);r=rows[i];p=proofs[i]['word_proofs'][j]
        assert ast.literal_eval(word)==r['variants'][j]
        assert ast.literal_eval(caps)==sorted((int(k),v) for k,v in r['caps'].items())
        assert int(lower)==r['lower']
        assert p['capped_theorem'].replace('CountPropagation65','CountPropagationPort95')+' p P s hr hP hb' in body
        seen_caps.append((i,j))
assert seen_rules==list(range(55))
assert seen_words==[(i,j) for i,r in enumerate(rows) for j in range(len(r['variants']))]
assert seen_caps==[(i,0) for i in range(8)]
final=HERE/'lean/ConcreteRules95.lean';inputs[str(final.relative_to(ROOT))]=sha(final);text=final.read_text()
order=re.search(r'def concreteRules : List Rule :=\s*\[([^\]]*)\]',text)[1]
assert re.findall(r'rule(\d{3})',order)==[f'{i:03}' for i in range(55)]
for name,field in [('concreteModelIndices','model_index'),('concreteEdgeNumbers','edge')]:
    literal=re.search(r'def '+name+r' : List Nat :=\s*(\[[^\]]*\])',text)[1]
    assert ast.literal_eval(literal)==[r[field] for r in rows]
assert 'import DefinedProofGraph\n' in text
result=dict(status='PASS_EXACT_LITERAL_CREDIT_CATALOGUE',rules=55,geometric_word_statements=69,capped_word_statements=8,inputs=inputs,
    scope='Independent syntax/data comparison. The successful Lean receipts separately certify the deductions and final actual-snake inequality.')
(HERE/'data/credit-literal-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],'55 rules;69 geometric statements;8 capped statements')
