"""Bounded saved-cycle/source-row review; no optimizer or all-edge scan."""
from pathlib import Path
from fractions import Fraction
import ast, datetime, gzip, hashlib, json, zipfile
import numpy as np

H=Path(__file__).resolve().parents[1]
ROOT=H.parents[1]
F=H/'data/share18-credit601-over36'
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
    run=read(F/'run-status.json'); result=read(F/'results.json'); prep=read(H/'data/retuned-preparation.json')
    assert run['status']==result['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA' and run['returncode']==0
    evaluator=H/'scripts/evaluate_retuned.py'; generator=H/'scripts/prepare_retuned.py'
    assert sha(evaluator)==sha(F/'evaluate_graph.exact.py')==run['script_sha256']==result['script_sha256']==prep['generated_sha256']
    sha(generator)
    original=H/'scripts/evaluate_graph.py'
    assert sha(original)==prep['source_sha256']=='25bb5aab4657577caf2e5941f23b44e18a36f9e4fe8a44bc538ca277306168ba'
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
            assert expected.count(a)>=1
            expected=expected.replace(a,b)
    assert expected==evaluator.read_text(encoding='utf-8')
    for rel,digest in result['source_files_sha256'].items(): assert sha(ROOT/rel)==digest,rel
    assert result['credit']=='601/36' and result['weight_multiplier']==36 and result['coefficients']==[24]*5
    assert result['added_share_floor']['shape']==[0,1,2,0,3,4] and result['added_share_floor']['floor']==18
    assert not result['added_share_floor']['actual_lean_theorem_complete']
    previous=ROOT/'milestones/142-retuned-occurrence-credit/data/credit533-over12'
    assert sha(F/'removed-indices.json')==sha(previous/'removed-indices.json')
    assert sha(F/'baseline121-removed-indices.json')==sha(previous/'baseline121-removed-indices.json')
    removed=read(F/'removed-indices.json'); assert removed==sorted(set(removed))
    removed_set=set(removed)
    p=result['profiles'][0]; assert len(result['profiles'])==1 and read(F/'completed-profile.json')==p
    selected=sorted(e['edge'] for e in p['cycle']); assert len(selected)==len(set(selected))==14
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
        row=dict(edge=k,u=a['U'],v=a['V'],direction=a['direction'],history=a['history'],count_code=a['count_code'],directions=word,counts=counts,weight=36*(base+delta+shared)+601*int(event),base_weight=base,weight_multiplier=36,occurrence_event=event,occurrence_credit_scaled=601,countfree_012034_bonus=delta,old_bonus24=oldbonus,pair_bonus24=pairbonus,six_bonus24=sixbonus,shared_bonus=shared,six_shape_matches=sixmatch,six_guard=sixguard)
        assert row==saved and k not in removed_set
        assert suffix!=(0,1,2,0,3,4) and delta==0
        rebuilt.append(row)
        details.append(dict(edge=k,canonical_suffix=''.join(map(str,suffix)),forward_suffix=''.join(map(str,canon(word[-6:]))),reverse_suffix=''.join(map(str,canon(word[-6:][::-1]))),source_base_weight=a['weight'],weight=row['weight'],unscaled_weight=str(Fraction(row['weight'],36)),event=event,shape18_bonus=delta,actual_occurrence_credit_scaled=601*int(event),reported_occurrence_credit_scaled=601))
    assert all(e['v']==rebuilt[(i+1)%14]['u'] for i,e in enumerate(rebuilt))
    total=sum(e['weight'] for e in rebuilt); mean=Fraction(total,36*14)
    assert total==248040 and mean==Fraction(3445,7)==Fraction(p['mean']) and (p['p'],p['d'])==(124020,7)
    assert sum(e['occurrence_event'] for e in rebuilt)==0
    raw=gzip.decompress((F/p['potential_file']).read_bytes()); sha(F/p['potential_file'])
    assert hashlib.sha256(raw).hexdigest()==p['potential_sha256'] and len(raw)==8*result['states']
    potential=np.frombuffer(raw,dtype='<i8')
    assert len(potential)==1601856 and int(potential.min())==0 and int(potential.max())==153216
    slacks=[7*e['weight']+int(potential[e['u']])-124020-int(potential[e['v']]) for e in rebuilt]
    assert slacks==[0]*14
    width=Fraction(153216,36*7); assert width==608==Fraction(p['range'])
    comparison=Fraction(1098960*36*7+8*124020+24*601*7+153216,4200*36*7+124020)
    zero=Fraction(1098960*36*7+8*124020+24*601*7,4200*36*7+124020)
    no_cost=(1098960+8*mean)/(4200+mean)
    assert no_cost==235+Fraction(341,6569)
    assert comparison==Fraction(p['comparison_bound'])==Fraction(23182022,98535)
    assert zero==Fraction(p['zero_range_comparison'])==Fraction(23169254,98535) and zero>235
    assert p['iterations']==35
    sha(Path(__file__))
    out=dict(status='PASS_BOUNDED_RETUNED_CYCLE_REVIEW',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_derivation_reproduced=True,removed_indices_byte_identical_to142=True,profile=p['profile'],cycle_rows=rebuilt,cycle_details=details,cycle_closed=True,cycle_length=14,scaled_weight_sum=total,unscaled_weight_sum=total//36,mean=str(mean),events=0,countfree_012034_suffixes=0,range=str(width),range_scaled=153216,potential_length=len(potential),cycle_slacks=slacks,potential_sha256=p['potential_sha256'],iterations=35,comparison=str(comparison),comparison_gap_from235=str(comparison-235),zero_range_comparison=str(zero),zero_range_gap_from235=str(zero-235),zero_cost_zero_range_comparison=str(no_cost),zero_cost_zero_range_gap_from235=str(no_cost-235),source_array_members=members,selected_source_rows=14,source_arrays_fully_loaded=False,independent_all_edge_potential_scan=False,independent_full_weight_hash_reconstruction=False,optimizer_invoked=False,solver_invoked=False,lean_invoked=False,obstruction=dict(scope='Same retained graph and other completed-profile weights; vary only the canonical012034 suffix share floor and uniform credit on the same suffix event.',cycle_unchanged_for_every_floor=True,mean_cap='3445/7',comparison_lower_bound=str(no_cost),reason='The saved cycle has no012034 suffix in either orientation and no occurrence events. Its unscaled weights therefore stay fixed for every floor and uniform credit. For nonnegative occurrence cost and potential range, the comparison is bounded below by its zero-cost zero-range value at the cycle mean cap, which exceeds235.',positive_uniform_credit_covered=True),metadata_note=dict(field='occurrence_credit_scaled',interpretation='Global scaled credit coefficient, not per-row applied increment.',reported_constant=601,actual_cycle_increments=[0]*14,impact='Exact weight expression is36*(base+shared)+601*event; all reconstructed weights agree.'),suffix_shape_counts=dict(__import__('collections').Counter(x['canonical_suffix'] for x in details)),inherited_hypotheses=result['inherited_hypotheses'],limitations=['All-edge potential inequalities and exact graph minimality remain producer checks; this audit independently checks the attaining saved cycle only.','Potential range was verified, not proved optimal.','Source array payload hashes were streamed and only14 rows extracted; no full arrays were retained.','The occurrence_credit_scaled field is the global coefficient601; the actual applied increment601*event is zero on all14 cycle rows.','Actual share18 Lean theorem and full graph-to-snake assembly remain separate.'],source_files_sha256=PINS)
    target=H/'data/retuned-review.json';assert not target.exists()
    target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['source_files_sha256','cycle_rows','source_array_members']},indent=2))

if __name__=='__main__':main()
