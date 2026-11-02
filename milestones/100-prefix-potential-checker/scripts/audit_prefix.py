"""Check shared-prefix enumeration against every previously audited class."""
from pathlib import Path
import gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic()
ap=ROOT/'milestones/99-defined-potential-certificates/data/defined-potential-audit.json'
dp=ROOT/'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz'
audit=read(ap);dag=json.loads(gzip.decompress(dp.read_bytes()))
assert audit['status']=='PASS_ALL_DEFINED_GRAPH_POTENTIAL_INEQUALITIES'
for path,digest in audit['source_files_sha256'].items():assert sha(ROOT/path)==digest,path
nodes=dag['nodes'];roots=dag['roots'];rows=[]
def enumerate_root(root):
    found=[];stats=dict(visited=0,transitions=0,rejected_prefixes=0,rejected_codes=0,accepted_codes=0)
    def visit(depth,prefix,node):
        stats['visited']+=1
        if node==0:
            stats['rejected_prefixes']+=1;stats['rejected_codes']+=6**depth
            return
        if depth==0:
            assert node==1
            found.append(prefix);stats['accepted_codes']+=1
            return
        for j in range(6):
            stats['transitions']+=1
            visit(depth-1,6*prefix+j,node if node<2 else nodes[node-2][j+1])
    visit(6,0,root)
    return np.asarray(found,dtype='<i8'),stats
for row,root in zip(audit['class_counts'],roots):
    assert row['root']==root
    codes,stats=enumerate_root(root)
    assert len(codes)==row['accepted_codes'] and hashlib.sha256(codes.tobytes()).hexdigest()==row['codes_i64_sha256']
    assert np.all(codes[1:]>codes[:-1])
    assert stats['accepted_codes']+stats['rejected_codes']==46656
    assert stats['transitions']==stats['visited']-1
    rows.append(dict(class_id=row['class_id'],root=root,**stats,
        flat_six_step_transitions=6*46656,codes_i64_sha256=row['codes_i64_sha256']))
assert len(rows)==127
selected=[]
for d,q in [(35,0),(177,43),(223,0),(66,0)]:
    ctx=next(r for r in audit['context_counts'] if r['direction']==d and r['history']==q)
    selected.append(dict(direction=d,history=q,**rows[ctx['diagram_class']]))
out=dict(status='PASS_ALL127_PREFIX_ENUMERATIONS',classes=rows,selected_contexts=selected,
    all_classes_exactly_equal_prior_accepted_codes=True,
    global_context_weighted_accepted=sum(rows[r['diagram_class']]['accepted_codes'] for r in audit['context_counts']),
    source_files_sha256={ap.relative_to(ROOT).as_posix():sha(ap),dp.relative_to(ROOT).as_posix():sha(dp)},
    script_sha256=sha(Path(__file__)),seconds=time.monotonic()-start,
    scope='Exact Python prefix enumeration compared with every accepted-code hash. Operation counts are not Lean timings or a speedup claim; no edge inequality or global bound is proved by this audit.')
assert out['global_context_weighted_accepted']==4947008
(HERE/'data/prefix-enumeration-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],selected=selected,seconds=out['seconds']),indent=2))
