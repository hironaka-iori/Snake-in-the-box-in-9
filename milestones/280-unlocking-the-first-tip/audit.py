"""Independently check the geometry reductions, archived completions and saved LRAT files."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json
from tempfile import TemporaryDirectory
from interval import BANK, HERE, N, check, encode, free_graph, rebuild


def audit_geometry(core, donor=None):
    # Build the graph by literal addition to a set, independently of free_graph.
    sites=set(core)
    exits={core[0],core[-1]}
    all_allowed=set(exits)
    for v in set(range(512))-sites:
        contacts={u for u in core if (v^u).bit_count()==1}
        if not contacts or (len(contacts)==1 and contacts<=exits):
            all_allowed.add(v)
    reached=set(exits)
    while True:
        added={v for v in all_allowed-reached if any((v^u).bit_count()==1 for u in reached)}
        if not added:
            break
        reached.update(added)
    assert reached==set(free_graph(core))
    if donor is not None:
        check(donor)
        assert sites<=set(donor) and set(donor)-set(core[1:-1])<=reached
        assert Counter(v.bit_count()%2 for v in donor)=={0:96,1:96}
    return len(reached)


def small_cube_capacity(d):
    maximum=0
    for m in range(1<<(1<<d)):
        vs={v for v in range(1<<d) if m>>v&1}
        nb={v:{u for u in vs if (u^v).bit_count()==1} for v in vs}
        if any(len(n)>2 for n in nb.values()):
            continue
        rest=set(vs)
        while True:
            tips={v for v in rest if len(nb[v]&rest)<2}
            if not tips:
                break
            rest-=tips
        if not rest:
            maximum=max(maximum,len(vs))
    return maximum


def replay_case(core, row, folder, scratch, verifier):
    f,_=encode(core,row['target'],row['majority'],row['cycles'],row['required'],row['forbidden'])
    formula=scratch/'audit.cnf'
    assert f.save(formula)==row['cnf_sha256']
    if row['status']=='excluded':
        proof=folder/'proofs'/row['proof']
        assert rebuild.masks.p.check_proof(formula,proof,verifier)==row['replay']
        return sha256(proof.read_bytes()).hexdigest()
    if row['status']=='witness':
        check(row['path'])
        assert len(row['path'])==row['target']+1
        assert any(row['path'][j:j+len(core)] in (core,core[::-1]) for j in range(len(row['path'])-len(core)+1))
    return row['status']


def main():
    donor=json.loads(BANK.read_bytes())[0]['vertex_sequence']
    caps=[small_cube_capacity(i) for i in (2,3)]
    assert caps==[3,5]
    decisions=json.loads((HERE/'decisions.json').read_bytes())
    forced=json.loads((HERE/'forced-step.json').read_bytes())
    result=dict(face_capacities=caps,proofs={},free_vertex_counts={})
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        verifier,_=rebuild.masks.compilers(scratch)
        for n,r in decisions.items():
            assert r['core']==donor[:int(n)+1]
            result['free_vertex_counts'][n]=audit_geometry(r['core'],donor)
            for maj,row in r['cases'].items():
                result['proofs'][n+'-'+maj]=replay_case(r['core'],row,HERE,scratch,verifier)
        audit_geometry(forced['core'])
        check(forced['best'])
        assert any(forced['best'][i:i+len(forced['core'])] in (forced['core'],forced['core'][::-1]) for i in range(len(forced['best'])-len(forced['core'])+1))
        for t,rows in forced['cases'].items():
            for maj,row in rows.items():
                result['proofs']['forced-'+t+'-'+maj]=replay_case(forced['core'],row,HERE,scratch,verifier)
    (HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Geometry and certificate replay',len(result['proofs']),'entries.')


if __name__=='__main__':
    main()
