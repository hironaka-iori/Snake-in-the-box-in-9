"""Bounded saved-cycle/source-row review; no optimizer or all-edge scan."""
from pathlib import Path
from fractions import Fraction
import ast, datetime, gzip, hashlib, json, zipfile
import numpy as np

H=Path(__file__).resolve().parents[1]
ROOT=H.parents[1]
F=H/'data/share18-impact'
PINS={}

def sha(path):
    path=Path(path); digest=hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda:stream.read(1048576),b''): digest.update(chunk)
    value=digest.hexdigest()
    PINS[path.relative_to(ROOT).as_posix()]=value
    return value

def read(path):
    sha(path)
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))

def canon(word):
    names={}
    return tuple(names.setdefault(int(x),len(names)) for x in word)

def shape(word):
    return min(canon(word),canon(word[::-1]))

def main():
    run=read(F/'run-status.json'); result=read(F/'results.json'); prep=read(H/'data/graph-preparation.json')
    assert run['status']==result['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA' and run['returncode']==0
    evaluator=H/'scripts/evaluate_graph.py'; generator=H/'scripts/prepare_graph.py'
    assert sha(evaluator)==sha(F/'evaluate_graph.exact.py')==run['script_sha256']==result['script_sha256']==prep['evaluate_sha256']
    assert sha(generator)==prep['prepare_sha256']
    original=ROOT/'milestones/142-retuned-occurrence-credit/scripts/evaluate_graph.py'
    assert sha(original)==prep['source_sha256']=='c057930ea46b47ad896105c37c668c01c60c235c738479d764c83a479d9b1208'
    # Interpret only literal replacement operations, never execute the generator.
    expected=original.read_text(encoding='utf-8')
    for node in ast.parse(generator.read_text(encoding='utf-8')).body:
        if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='s' for t in node.targets):
            call=node.value
            if isinstance(call,ast.Call) and isinstance(call.func,ast.Attribute) and isinstance(call.func.value,ast.Name) and call.func.value.id=='s' and call.func.attr=='replace':
                expected=expected.replace(*(ast.literal_eval(a) for a in call.args))
            elif isinstance(call,ast.Call) and isinstance(call.func,ast.Attribute) and call.func.attr=='replace':
                # Chained replacements of the label and parent process variable.
                inner=call.func.value
                assert isinstance(inner,ast.Call) and isinstance(inner.func,ast.Attribute) and inner.func.attr=='replace'
                assert isinstance(inner.func.value,ast.Name) and inner.func.value.id=='s'
                expected=expected.replace(*(ast.literal_eval(a) for a in inner.args)).replace(*(ast.literal_eval(a) for a in call.args))
            else:
                assert isinstance(call,ast.Call) and isinstance(call.func,ast.Attribute) and call.func.attr=='read_text'
        elif isinstance(node,ast.Expr) and isinstance(node.value,ast.Call) and isinstance(node.value.func,ast.Name) and node.value.func.id=='change':
            a,b=map(ast.literal_eval,node.value.args)
            assert expected.count(a)==1
            expected=expected.replace(a,b)
    assert expected==evaluator.read_text(encoding='utf-8')
    for rel,digest in result['source_files_sha256'].items(): assert sha(ROOT/rel)==digest,rel
    assert result['credit']=='0' and result['weight_multiplier']==1 and result['coefficients']==[24]*5
    assert result['added_share_floor']['shape']==[0,1,2,0,3,4] and result['added_share_floor']['floor']==18
    assert not result['added_share_floor']['actual_lean_theorem_complete']
    previous=ROOT/'milestones/142-retuned-occurrence-credit/data/credit533-over12'
    assert sha(F/'removed-indices.json')==sha(previous/'removed-indices.json')
    assert sha(F/'baseline121-removed-indices.json')==sha(previous/'baseline121-removed-indices.json')
    removed=read(F/'removed-indices.json'); assert removed==sorted(set(removed))
    removed_set=set(removed)
    p=result['profiles'][0]; assert len(result['profiles'])==1 and read(F/'completed-profile.json')==p
    selected=sorted(e['edge'] for e in p['cycle']); assert len(selected)==len(set(selected))==11
    rows={k:{} for k in selected}
    meta=read(ROOT/'milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
    ds=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')['extensions']
    completed=read(ROOT/'milestones/73-countfree-share-catalogue/data/proved-model.json')
    floors={tuple(x['shape']):x['share'] for x in completed['countfree_floors']}
    assert floors.get((0,1,2,0,3,4),0)==0
    graph=ROOT/'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
    members=[]
    with zipfile.ZipFile(graph) as archive:
        for name in ['U','V','weight','direction','history','count_code']:
            with archive.open(name+'.npy') as stream:
                version=np.lib.format.read_magic(stream)
                if version==(1,0): dimensions,fortran,dtype=np.lib.format.read_array_header_1_0(stream)
                else:
                    assert version==(2,0)
                    dimensions,fortran,dtype=np.lib.format.read_array_header_2_0(stream)
                assert dimensions==(4947008,) and not fortran and dtype.itemsize==4
                digest=hashlib.sha256(); offset=0
                while True:
                    raw=stream.read(1048576)
                    if not raw:break
                    assert len(raw)%4==0
                    digest.update(raw); a=np.frombuffer(raw,dtype=dtype)
                    for k in selected:
                        if offset<=k<offset+len(a):rows[k][name]=int(a[k-offset])
                    offset+=len(a)
                assert offset==4947008 and digest.hexdigest()==meta['arrays_sha256'][name]
                members.append(dict(name=name,elements=offset,sha256=digest.hexdigest(),maximum_chunk_bytes=1048576))
    assert 4947008-len(removed)==result['edges']==4661572

    rebuilt=[]; details=[]
    for saved in p['cycle']:
        k=saved['edge']; a=rows[k]; word=ds[a['direction']]
        counts=[a['count_code']//6**j%6+1 for j in range(5,-1,-1)]
        suffix=shape(word[-6:]); oldbonus=0
        for rule in result['rules']:
            target=shape(rule['directions'])
            if suffix!=target:continue
            five=counts[1:6] if canon(word[-6:])==target else counts[1:6][::-1]
            if all(x>=lo and (21 if x==6 else x)<=hi for x,(lo,hi) in zip(five,rule['bounds'])):
                oldbonus=max(oldbonus,24*max(0,rule['lower']-sum(five[j] for j in rule['positions'])))
        pairbonus=24*max(0,9-counts[2]-counts[4]) if suffix==(0,1,2,0,3,2) else 0
        sixmatch=shape(word[2:])==shape([0,1,2,3,1,0,4]); sixguard=sixmatch and counts[0]<6
        sixbonus=24*max(0,25-sum(counts)) if sixguard else 0
        shared=max(oldbonus,pairbonus,sixbonus)
        base=max(a['weight'],120*counts[-1]+floors.get(suffix,0))
        delta=max(a['weight'],120*counts[-1]+18)-max(a['weight'],120*counts[-1]) if suffix==(0,1,2,0,3,4) else 0
        event=suffix==(0,1,2,0,3,2) and counts[2]<6 and counts[4]<6 and counts[2]+counts[4]<=9
        row=dict(edge=k,u=a['U'],v=a['V'],direction=a['direction'],history=a['history'],count_code=a['count_code'],directions=word,counts=counts,weight=base+delta+shared,base_weight=base,weight_multiplier=1,occurrence_event=event,occurrence_credit_scaled=0,countfree_012034_bonus=delta,old_bonus24=oldbonus,pair_bonus24=pairbonus,six_bonus24=sixbonus,shared_bonus=shared,six_shape_matches=sixmatch,six_guard=sixguard)
        assert row==saved and k not in removed_set
        assert suffix!=(0,1,2,0,3,4) and delta==0
        rebuilt.append(row)
        details.append(dict(edge=k,canonical_suffix=''.join(map(str,suffix)),forward_suffix=''.join(map(str,canon(word[-6:]))),reverse_suffix=''.join(map(str,canon(word[-6:][::-1]))),source_base_weight=a['weight'],weight=row['weight'],event=event,shape18_bonus=delta))
    assert all(e['v']==rebuilt[(i+1)%11]['u'] for i,e in enumerate(rebuilt))
    total=sum(e['weight'] for e in rebuilt); mean=Fraction(total,11)
    assert total==5399 and mean==Fraction(p['mean']) and (p['p'],p['d'])==(5399,11)
    assert sum(e['occurrence_event'] for e in rebuilt)==4
    raw=gzip.decompress((F/p['potential_file']).read_bytes()); sha(F/p['potential_file'])
    assert hashlib.sha256(raw).hexdigest()==p['potential_sha256'] and len(raw)==8*result['states']
    potential=np.frombuffer(raw,dtype='<i8')
    assert len(potential)==1601856 and int(potential.min())==0 and int(potential.max())==6523
    slacks=[11*e['weight']+int(potential[e['u']])-5399-int(potential[e['v']]) for e in rebuilt]
    assert slacks==[0]*11
    width=Fraction(6523,11); assert width==593==Fraction(p['range'])
    comparison=Fraction(1098960*11+8*5399+6523,4200*11+5399)
    zero=Fraction(1098960*11+8*5399,4200*11+5399)
    assert comparison==Fraction(p['comparison_bound'])==Fraction(12138275,51599)
    assert zero==Fraction(p['zero_range_comparison'])==Fraction(12131752,51599) and zero>235
    assert p['iterations']==29
    sha(Path(__file__))
    out=dict(status='PASS_BOUNDED_GRAPH_CYCLE_REVIEW',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_derivation_reproduced=True,removed_indices_byte_identical_to142=True,profile=p['profile'],cycle_rows=rebuilt,cycle_details=details,cycle_closed=True,cycle_length=11,weight_sum=total,mean=str(mean),events=4,countfree_012034_suffixes=0,range=str(width),range_scaled=6523,potential_length=len(potential),cycle_slacks=slacks,potential_sha256=p['potential_sha256'],iterations=29,comparison=str(comparison),comparison_gap_from235=str(comparison-235),zero_range_comparison=str(zero),zero_range_gap_from235=str(zero-235),source_array_members=members,selected_source_rows=11,source_arrays_fully_loaded=False,independent_all_edge_potential_scan=False,independent_full_weight_hash_reconstruction=False,optimizer_invoked=False,solver_invoked=False,lean_invoked=False,obstruction=dict(scope='Same retained graph and other completed-profile weights; credit fixed at zero; vary only the canonical012034 suffix share floor.',cycle_unchanged_for_every_floor=True,mean_cap='5399/11',comparison_lower_bound=str(zero),reason='The saved cycle has no012034 suffix in either orientation. Its weights therefore stay fixed. For nonnegative potential range and mu>=0, the comparison is at least its zero-range value at the cycle mean cap, which exceeds235.',positive_uniform_credit_covered=False),inherited_hypotheses=result['inherited_hypotheses'],limitations=['All-edge potential inequalities and exact graph minimality remain producer checks; this audit independently checks the attaining saved cycle only.','Potential range was verified, not proved optimal.','Source array payload hashes were streamed and only11 rows extracted; no full arrays were retained.','The cycle has four occurrence events, so the zero-credit obstruction does not apply unchanged when that credit is varied.','Actual share18 Lean theorem and full graph-to-snake assembly remain separate.'],source_files_sha256=PINS)
    target=H/'data/graph-review.json';assert not target.exists()
    target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['source_files_sha256','cycle_rows','source_array_members']},indent=2))

if __name__=='__main__':main()
