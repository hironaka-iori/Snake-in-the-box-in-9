"""Read-only audit of source transport; writes only its own report.

This is independent of the Lean emitter's tree traversal. It checks the concrete
CNF chunks, the pre-order input transport, and the prepared source inventory.
It does not run Lean or claim a kernel-checked replay.
"""
import ast, gzip, hashlib, json, re
from pathlib import Path
import prepare_replay as p

def main():
    h=p.HERE;plan=json.loads((h/'data/pilot-source-plan.json').read_text())
    sizing=json.loads((h/'data/sizing.json').read_text())
    transport=json.loads((h/'data/transport.json').read_text())
    replay=json.loads((h/'data/packed-replay.json').read_text())
    actual=p.ROOT/'milestones/147-countfree-clause-semantics/lean/LocalWindowCnf/ShareWindow146.lean'
    text=actual.read_text(encoding='utf-8')
    chunks=re.findall(r'def raw(\d+)\s*:\s*List \(List Nat\)\s*:=\s*(\[.*?\])(?=\s*(?:\n|$))',text,re.S)
    assert len(chunks)==102,len(chunks)
    raw=[]
    for expected,(n,body) in enumerate(chunks):
        assert int(n)==expected;raw.extend(ast.literal_eval(body))
    core=p.cnf(p.CORE);expected=[[2*abs(l)+(l<0) for l in c] for c in core]
    assert raw==expected
    keys={int(a):b for a,b in transport['slot_to_tree_key'].items()}
    inputs=transport['input_ordinal_to_slot'];pre=p.preorder(sizing['tree_height'])
    assert [keys[s] for s in inputs]==pre[:len(core)]
    assert len(set(keys.values()))==len(keys)==17523
    # The literal data's preorder is read directly from the emitted InputTree
    # declarations. Their concatenation omits only the small root spine.
    part_rows=[]
    for path in sorted((h/'lean').glob('ReplayParts147*.lean')):
        t=path.read_text()
        for ix,body in re.findall(r'theorem part(\d+)_clauses : input\d+\.clauses = (\[.*?\]) := by rfl',t,re.S):
            part_rows.append((int(ix),ast.literal_eval(body)))
    assert [i for i,_ in part_rows]==list(range(102))
    # Each slice statement independently identifies its exact raw range.
    checked=[]
    for path in sorted((h/'lean').glob('ReplayTruth147*.lean')):
        t=path.read_text()
        pattern=r'theorem part(\d+)_slice : input\d+\.clauses = \(\((.*?)\)\.drop (\d+)\)\.take (\d+) := by'
        for i,expr,off,count in re.findall(pattern,t,re.S):
            cs=[int(x) for x in re.findall(r'\.raw(\d+)',expr)]
            source=[]
            for c in cs:source.extend(expected[c*128:(c+1)*128])
            assert part_rows[int(i)][1]==source[int(off):int(off)+int(count)]
            checked.append(int(i))
    assert sorted(checked)==list(range(102))
    prohibited=[]
    for a in plan['artifacts']:
        path=h/a['path'];assert p.sha(path)==a['sha256']
        text=path.read_text()
        if re.search(r'\b(?:sorry|admit|native_decide|axiom)\b',text):prohibited.append(a['path'])
    assert not prohibited,prohibited
    assert not re.search(r'\b(?:Lrat144|LratFast144|ShareWindow144|InputTree145)\b',
                        (h/'lean/LratFast147Replay.lean').read_text())
    for rel,digest in plan['copied_source_pins'].items():assert p.sha(p.ROOT/rel)==digest
    hashes=[]
    for name in ['renamed.lrat.gz','packed-index.jsonl.gz']:
        digest=hashlib.sha256();size=0
        with gzip.open(h/'data'/name,'rb') as f:
            for b in iter(lambda:f.read(1048576),b''):digest.update(b);size+=len(b)
        hashes.append({'path':'data/'+name,'uncompressed_sha256':digest.hexdigest(),'uncompressed_bytes':size})
    result={'status':'PASS_STATIC_TRANSPORT_AND_SOURCE_AUDIT','actual147_cnf_path':str(actual),
        'actual147_cnf_sha256':p.sha(actual),'actual147_raw_chunks':102,'actual147_input_clauses':len(raw),
        'initial_tree_core_preorder_verified':True,'literal_subtree_slices_verified':len(checked),
        'complete_packed_replay_receipt_sha256':p.sha(h/'data/packed-replay.json'),
        'pilot_source_plan_sha256':p.sha(h/'data/pilot-source-plan.json'),
        'sources_verified':len(plan['artifacts']),'uncompressed_artifact_hashes':hashes,
        'gzip_reproducibility_note':'gzip headers include write time; uncompressed SHA256 values identify reproducible content.',
        'source_python_sha256':p.sha(Path(__file__)),'lean_invoked':False,'solver_invoked':False,
        'scope':'Source and Python certificate transport only; no Lean compilation or actual-snake conclusion.'}
    p.save(h/'data/preparation-audit.json',result);print(json.dumps(result,indent=2))

if __name__=='__main__':main()
