"""Bounded exact context reuse analysis; no solver or Lean invocation."""
from pathlib import Path
import gzip
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parents[1]
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np

def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def canon(w):
    names={}
    return tuple(names.setdefault(x,len(names)) for x in w)
def enc(s):
    c=0
    for x in s:c=6*c+x-1
    return c

def main():
    start=time.monotonic()
    receipt=read(HERE/'data/defined-potential-audit.json')
    assert receipt['status']=='PASS_ALL_DEFINED_GRAPH_POTENTIAL_INEQUALITIES'
    assert all(sha((ROOT/p).read_bytes())==h for p,h in receipt['source_files_sha256'].items())
    dag=json.loads(gzip.decompress((ROOT/'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz').read_bytes()))
    model=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
    history=read(ROOT/'milestones/67-critical-family-charge/data/full-model.json')
    geom=read(ROOT/'milestones/59-extended-share-window/data/geometry.json')['patterns']
    prefixes=[tuple(p) for p in history['prefixes']]
    shapes={tuple(s):i for i,s in enumerate(model['direction_shapes'])}
    codes=np.arange(46656,dtype=np.int64)
    digits=np.stack([codes//6**j%6+1 for j in range(5,-1,-1)],axis=1)
    suffixcodes=codes%7776
    entering=120*(codes%6+1)
    rules=[((0,1,2,3,1,4),(3,3,3,6,5),48),((0,1,2,3,4,5),(3,6,2,3,6),96),
           ((0,1,2,0,3,4),(6,3,6,3,3),96),((0,1,2,3,4,5),(4,6,2,3,6),96),
           ((0,1,2,3,4,5),(4,5,4,2,6),120)]
    completed={'012031':16,'012032':0,'012034':0,'012301':0,'012304':16,'012310':12,'012314':16,'012340':0,'012345':12}
    conditional={'012031':16,'012032':16,'012034':18,'012301':16,'012304':16,'012310':12,'012314':16,'012340':16,'012345':16}
    potentials={}
    for name,path,floors in [
        ('completed','milestones/73-countfree-share-catalogue/data/proved-potential.i64.gz',completed),
        ('conditional_floor18','milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18-potential.i64.gz',conditional)]:
        buf=gzip.decompress((ROOT/path).read_bytes())
        assert sha(buf)==receipt['profiles'][name]['potential_raw_sha256']
        arr=np.frombuffer(buf,dtype='<i8').reshape((206,7776))
        potentials[name]=dict(blocks=arr,floors=floors,block_hashes=[sha(v.tobytes()) for v in arr],
                              groups=[],lookup={},context_group={},accepted_weight_hash=hashlib.sha256())
    children=np.zeros((len(dag['nodes'])+2,7),dtype=np.int64)
    children[1]=1;children[2:]=dag['nodes']
    accepted={}
    for cls,root in enumerate(dag['roots']):
        node=np.full(len(codes),root,dtype=np.int64)
        for j in range(6):node=children[node,digits[:,j]]
        accepted[cls]=codes[node==1]

    def values(di,qi,floors):
        ds=model['extensions'][di]
        a,b=canon(ds[3:]),canon(ds[3:][::-1])
        shape=''.join(map(str,min(a,b)))
        credit=np.full(46656,geom[di]['share_lower'],dtype=np.int64)
        for word,symbols,lower in rules:
            hit=((a==word)&(suffixcodes==enc(symbols)))|((b==word)&(suffixcodes==enc(symbols[::-1])))
            credit[hit]=np.maximum(credit[hit],lower)
        emitted=prefixes[qi]+(di,)
        for rule in history['patterns']:
            if rule['mode']!='share' or len(emitted)<3 or emitted[-3:]!=tuple(rule['signature']):continue
            np.maximum(credit,rule['geometric_lower'],out=credit)
            hit=np.ones(46656,dtype=bool)
            for k,cap in rule['caps'].items():hit&=digits[:,int(k)]<=cap
            credit[hit]=np.maximum(credit[hit],rule['lower'])
        return entering+np.maximum(credit,floors[shape])

    context_info={}
    exact_reuse_checks=0
    for block,cls in dag['blocks']:
        di,qi=divmod(block,75);ds=model['extensions'][di]
        emitted=prefixes[qi]+(di,)
        matches=[j for j,p in enumerate(prefixes) if p and len(p)<=len(emitted) and emitted[-len(p):]==p]
        nq=max(matches,key=lambda j:len(prefixes[j])) if matches else 0
        source=shapes[canon(ds[:8])] if qi==0 else 132+qi-1
        target=shapes[canon(ds[1:])] if nq==0 else 132+nq-1
        take=accepted[cls];root=dag['roots'][cls]
        context_info[block]=dict(direction=di,history=qi,diagram_class=cls,root=root,source_block=source,target_block=target,accepted=len(take))
        for name,p in potentials.items():
            w=values(di,qi,p['floors'])
            wh=sha(w.astype('<i8',copy=False).tobytes())
            key=(root,p['block_hashes'][source],p['block_hashes'][target],wh)
            if key in p['lookup']:
                gi=p['lookup'][key];g=p['groups'][gi];r=g['representative']
                assert np.array_equal(p['blocks'][source],p['blocks'][r['source_block']])
                assert np.array_equal(p['blocks'][target],p['blocks'][r['target_block']])
                assert np.array_equal(w,values(r['direction'],r['history'],p['floors']))
                exact_reuse_checks+=1
            else:
                gi=len(p['groups']);p['lookup'][key]=gi
                slack=w[take]+p['blocks'][source][take//6]-p['blocks'][target][take%7776]-receipt['profiles'][name]['P']
                assert int(slack.min())>=0
                critical=int(take[int(np.argmin(slack))])
                g=dict(group_id=gi,representative=context_info[block],minimum_slack=int(slack.min()),
                       tight_accepted_edges=int((slack==0).sum()),critical_count_code=critical,
                       source_potential_block_sha256=key[1],target_potential_block_sha256=key[2],
                       full_weight_i64_sha256=wh,contexts=[])
                p['groups'].append(g)
            g['contexts'].append([di,qi]);p['context_group'][block]=gi
            p['accepted_weight_hash'].update(w[take].astype('<i8',copy=False).tobytes())
    report={}
    for name,p in potentials.items():
        assert p['accepted_weight_hash'].hexdigest()==receipt['profiles'][name]['accepted_weight_i64_sha256']
        ordered=sorted(p['groups'],key=lambda g:(g['representative']['accepted'],g['group_id']))
        choices={label:ordered[index] for label,index in [('low',0),('median',len(ordered)//2),('high',len(ordered)-1)]}
        report[name]=dict(distinct_groups=len(p['groups']),saved_context_checks=791-len(p['groups']),
                          distinct_potential_blocks=len(set(p['block_hashes'])),
                          representative_examples={label:dict(g['representative'],group_id=g['group_id'],
                              minimum_slack=g['minimum_slack'],critical_count_code=g['critical_count_code'],
                              tight_accepted_edges=g['tight_accepted_edges'],group_size=len(g['contexts'])) for label,g in choices.items()},
                          groups=p['groups'])
    joint={}
    for block,cls in dag['blocks']:
        key=tuple(p['context_group'][block] for p in potentials.values())
        joint.setdefault(key,[]).append([block//75,block%75])
    elapsed=time.monotonic()-start;assert elapsed<120
    result=dict(status='PASS_EXACT_CONTEXT_TUPLE_CLASSIFICATION',contexts=791,profiles=report,
                joint_distinct_groups=len(joint),joint_saved_context_checks=791-len(joint),
                joint_groups=[dict(completed_group=k[0],conditional_floor18_group=k[1],contexts=v) for k,v in joint.items()],
                exact_array_equality_checks_within_hash_buckets=exact_reuse_checks,numerical_seconds=elapsed,
                source_audit_sha256=sha((HERE/'data/defined-potential-audit.json').read_bytes()),
                source_inputs_sha256=receipt['source_files_sha256'],script_sha256=sha(Path(__file__).read_bytes()),
                tuple_definition='acceptance root, ordered source potential block of7776values, ordered target potential block of7776values, weight array for all46656codes; each profile separately and both jointly',
                scope='Numerical reuse classification with exact equality checked within hash buckets. A Lean transport theorem and table equalities remain necessary; no proof checking or graph optimization was run.')
    (HERE/'data/context-compression.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],profiles={name:{k:p[k] for k in ['distinct_groups','saved_context_checks','distinct_potential_blocks','representative_examples']} for name,p in report.items()},joint_distinct_groups=len(joint),numerical_seconds=elapsed),indent=2))

if __name__=='__main__':main()
