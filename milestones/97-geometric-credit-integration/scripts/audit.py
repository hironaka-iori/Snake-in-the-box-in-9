"""Independently check literal geometry ports and successful partial/full receipts."""
from pathlib import Path
import ast,hashlib,json,re,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
plan=read(HERE/'data/generation.json');order=read(HERE/'data/compile-order.json')
for rel,digest in plan['inputs'].items():assert sha(ROOT/rel)==digest,rel
rows=read(ROOT/'milestones/59-extended-share-window/data/geometry.json')['patterns']
strip=lambda b:re.sub(rb'^import [^\r\n]*(?:\r?\n|$)',b'',b,flags=re.M)
mapped={};port_by_module={}
for p in plan['ports']:
    original=ROOT/p['original_source'];source=ROOT/p['source']
    assert sha(original)==p['original_sha256'] and sha(source)==p['source_sha256']
    assert strip(original.read_bytes())==strip(source.read_bytes())
    expected=original.read_bytes().replace(b'import ExtendedShareBridge',b'import Port95M59ExtendedShareBridge').replace(b'import MaskShareBridge',b'import Port95M59MaskShareBridge')
    assert expected==source.read_bytes()
    # Parse each actual theorem block rather than trusting the generator indices.
    text=source.read_text()
    blocks=re.findall(r'^namespace G(\d+)\n(.*?)^end G\d+\s*$',text,re.S|re.M)
    assert len(blocks)==len(p['indices'])
    for index,block in blocks:
        i=int(index);assert i not in mapped
        ds=ast.literal_eval(re.search(r'^def ds : List Nat := (\[.*\])$',block,re.M)[1])
        W=ast.literal_eval(re.search(r'^def W : List Nat := (\[.*\])$',block,re.M)[1])
        C=ast.literal_eval(re.search(r'^def C : List Nat := (\[.*\])$',block,re.M)[1])
        D=ast.literal_eval(re.search(r'^def D : List Nat := (\[.*\])$',block,re.M)[1])
        credit=int(re.search(r'theorem in_snake.*?\n\s*(\d+) ≤',block,re.S)[1])
        assert (ds,W,C,D,credit)==(rows[i]['directions'],rows[i]['vertices'],rows[i]['centres'],rows[i]['forced_absent'],rows[i]['share_lower'])
        assert C==W[4:9] and len(ds)==9 and len(W)==10
        assert all(W[j+1]==W[j]^(1<<ds[j]) for j in range(9))
        assert all(((W[j]^W[k]).bit_count()==1)==(abs(j-k)==1) for j in range(10) for k in range(j))
        mapped[i]=p['module']
    port_by_module[p['module']]=p
assert len(mapped)==357 and set(mapped)=={i for i,r in enumerate(rows) if r['share_lower']>0}
credits=ast.literal_eval(re.search(r'def geometricCredits : List Nat := (\[[^\n]*\])',(HERE/'lean/GeometricData97.lean').read_text())[1])
assert credits==[r['share_lower'] for r in rows] and len(credits)==505
model=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
assert model['extensions']==[r['directions'] for r in rows]
checked=[];pending=[];proved_indices=[]
for name in order['modules']:
    source=HERE/'lean'/(name+'.lean');assert sha(source)==order['source_sha256'][name],name
    receipt=HERE/'data'/(name+'-audit.json')
    if not receipt.exists():pending.append(name);continue
    r=read(receipt);assert r['exit_code']==0 and r['status']=='PASS_GEOMETRIC_CREDIT_MODULE'
    assert sha(source)==r['source_sha256'] and sha(HERE/'build'/(name+'.olean'))==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
    assert sha(HERE/r['source_snapshot'])==r['source_sha256']
    assert sha((HERE/r['source_snapshot']).parent/'checker.py.txt')==r['checker_sha256']
    for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
    assert source.read_text().count('#print axioms')==len(r['theorem_audits'])
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['theorem_audits'])
    checked.append(dict(module=name,receipt=receipt.relative_to(ROOT).as_posix(),receipt_sha256=sha(receipt),theorem_audits=len(r['theorem_audits'])))
    if name in port_by_module:proved_indices+=port_by_module[name]['indices']
if '--complete' in sys.argv:assert not pending,pending
result=dict(status='PASS_COMPLETE_GEOMETRIC_CREDIT_INTEGRATION' if not pending else 'PASS_PARTIAL_GEOMETRIC_CREDIT_CHECKPOINT',shapes=505,positive=357,zero=148,checked_positive_indices=sorted(proved_indices),modules=checked,pending_modules=pending,theorem_audits=sum(r['theorem_audits'] for r in checked),literal_table_matches=True,non_import_proof_bytes_preserved=True,complete_actual_credit_theorem_checked=not pending,source_model_sha256=sha(ROOT/'milestones/59-extended-share-window/extended/data/model.json'),generation_sha256=sha(HERE/'data/generation.json'),scope='Existing geometry catalogue and exact actual-index integration. A partial checkpoint does not establish the full catalogue in the common environment. Other weight families and global upper-bound obligations remain separate.')
(HERE/'data/proof-summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],len(checked),'modules;',len(proved_indices),'positive indices;',len(pending),'pending modules')
