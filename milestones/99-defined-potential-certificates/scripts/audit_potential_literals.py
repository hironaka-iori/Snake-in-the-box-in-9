"""Parse actual Lean tree literals and compare all values with saved potentials.

No generator, solver or compiler is imported. The optional pilot checks use
the previously audited saved graph and the expanded literal potential arrays.
"""
from pathlib import Path
import gzip
import hashlib
import json
import re
import sys
import time

HERE=Path(__file__).resolve().parents[1]
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
PINS={}

def sha(b):return hashlib.sha256(b).hexdigest()
def raw(rel):
    b=(ROOT/rel).read_bytes();h=sha(b)
    assert rel not in PINS or PINS[rel]==h,('input changed',rel)
    PINS[rel]=h
    return b
def text(rel):return raw(rel).decode('utf-8-sig')
def read(rel):return json.loads(raw(rel))

class Parser:
    def __init__(self,source):
        self.tokens=[];at=0
        pattern=re.compile(r'\s*(Table\.node|Table\.leaf|Table\.empty|\.node|\.leaf|n[1-5]_\d+|\d+|[()])')
        while at<len(source):
            if not source[at:].strip():break
            m=pattern.match(source,at);assert m,('unparsed input',source[at:at+100])
            self.tokens.append(m.group(1));at=m.end()
        self.i=0
    def pop(self):
        assert self.i<len(self.tokens)
        t=self.tokens[self.i];self.i+=1;return t
    def expression(self):
        t=self.pop()
        if t=='(':
            e=self.expression();assert self.pop()==')';return e
        if t in ('.leaf','Table.leaf'):
            v=self.pop()
            assert v.isdigit() if t=='.leaf' else re.fullmatch(r'n5_\d+',v)
            return ('leaf',int(v)) if t=='.leaf' else ('table_leaf',v)
        if t in ('.node','Table.node'):
            w=self.pop();assert w.isdigit()
            return (('node' if t=='.node' else 'table_node'),int(w),
                    tuple(self.expression() for _ in range(6 if t=='.node' else 2)))
        if t=='Table.empty':return ('empty',)
        assert re.fullmatch(r'n[1-5]_\d+',t),t
        return ('ref',t)
    def all(self):
        e=self.expression();assert self.i==len(self.tokens),(self.i,len(self.tokens));return e

def table_leaves(tree):
    if tree[0]=='empty':return []
    if tree[0]=='table_leaf':return [tree[1]]
    assert tree[0]=='table_node'
    left,right=map(table_leaves,tree[2])
    assert tree[1]==len(left),('incorrect actual Table.node leftSize',tree[1],len(left))
    return left+right

def table_lookup(tree,index):
    if tree[0]=='empty':return None
    if tree[0]=='table_leaf':return tree[1] if index==0 else None
    w=tree[1]
    return table_lookup(tree[2][0],index) if index<w else table_lookup(tree[2][1],index-w)

def main():
    start=time.monotonic()
    semantics=text('milestones/99-defined-potential-certificates/lean/PotentialTree99.lean')
    expected='''def value : Tree → Nat → Nat
      | .leaf n, _ => n
      | .node w a b c d e f, i =>
          if i < w then value a i
          else if i < 2*w then value b (i-w)
          else if i < 3*w then value c (i-2*w)
          else if i < 4*w then value d (i-3*w)
          else if i < 5*w then value e (i-4*w)
          else value f (i-5*w)'''
    body=semantics.split('def value',1)[1].split('end ',1)[0]
    assert re.sub(r'\s+','', 'def value'+body)==re.sub(r'\s+','',expected)
    text('milestones/89-shared-cover-certification/lean/BalancedLookup.lean')
    previous=read('milestones/99-defined-potential-certificates/data/defined-potential-audit.json')
    assert previous['status']=='PASS_ALL_DEFINED_GRAPH_POTENTIAL_INEQUALITIES'
    profiles={};expanded={}
    for label,name,cap,pfile in [
        ('Completed','completed',551,'milestones/73-countfree-share-catalogue/data/proved-potential.i64.gz'),
        ('Conditional','conditional_floor18',602,'milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18-potential.i64.gz')]:
        arrays={};counts={};refs=0
        def expand(expr,length):
            nonlocal refs
            kind=expr[0]
            if kind=='leaf':return np.full(length,expr[1],dtype='<i8')
            if kind=='ref':
                refs+=1
                assert expr[1] in arrays,('forward or missing child reference',expr[1])
                arr=arrays[expr[1]];assert len(arr)==length,(expr[1],len(arr),length)
                return arr
            assert kind=='node' and 6*expr[1]==length,(kind,expr[1],length)
            return np.concatenate([expand(child,expr[1]) for child in expr[2]])
        for depth in range(1,6):
            source=text(f'milestones/99-defined-potential-certificates/lean/{label}Values99D{depth}.lean')
            definitions=re.findall(r'^def (n(\d+)_(\d+)) : Tree := (.+)$',source,re.M)
            assert definitions and len(definitions)==len(re.findall(r'^def ',source,re.M))
            assert [int(i) for _,_,i,_ in definitions]==list(range(len(definitions)))
            for ident,level,index,expression in definitions:
                assert int(level)==depth and ident not in arrays
                tree=Parser(expression).all()
                assert tree[0]=='node' and tree[1]==6**(depth-1)
                arrays[ident]=expand(tree,6**depth)
            counts[str(depth)]=len(definitions)
        source=text(f'milestones/99-defined-potential-certificates/lean/{label}Potential99.lean')
        rootbody=source.split('def roots : Table Tree :=',1)[1].split('def potential',1)[0].strip()
        root=Parser(rootbody).all();order=table_leaves(root)
        assert len(order)==206
        assert [table_lookup(root,i) for i in range(206)]==order
        assert all(table_lookup(root,i) is None for i in [206,207,1000,1601856])
        potential=re.search(r'def potential \(s : Nat\) : Nat := (.+)',source).group(1)
        expected_potential=f'min {cap} (value (lookup roots (s/7776) (.leaf 0)) (s%7776))'
        assert re.sub(r'\s+','',potential)==re.sub(r'\s+','',expected_potential)
        assert f'theorem potential_le (s : Nat) : potential s ≤ {cap} := Nat.min_le_left _ _' in source
        values=np.concatenate([arrays[ref] for ref in order])
        assert len(values)==206*7776==1601856
        savedbytes=gzip.decompress(raw(pfile));saved=np.frombuffer(savedbytes,dtype='<i8')
        assert sha(savedbytes)==previous['profiles'][name]['potential_raw_sha256']
        mismatch=np.flatnonzero(values!=saved)
        assert len(mismatch)==0,(name,'literal mismatch',mismatch[:10].tolist())
        assert int(values.min())==0 and int(values.max())==cap
        clamped=np.minimum(values,cap)
        assert np.array_equal(clamped,saved) and sha(values.tobytes())==sha(savedbytes)
        expanded[name]=values
        profiles[name]=dict(checked_values=len(values),raw_blocks=206,block_width=7776,
                            literal_definitions_by_depth=counts,child_reference_uses=refs,
                            distinct_root_references=len(set(order)),root_order=order,
                            balanced_split_sizes_valid=True,lookup_order_matches_flatten=True,
                            minimum=0,maximum=cap,min_clamp_changes_values=False,mismatches=0,
                            expanded_raw_i64_sha256=sha(values.tobytes()),saved_raw_i64_sha256=sha(savedbytes),
                            source_index_expression=potential,upper_bound_source_checked=True)
    # Optional benchmark counts on the requested half-open code interval.
    meta=read('milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
    graphrel='milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
    raw(graphrel)
    with np.load(ROOT/graphrel) as z:a={k:z[k] for k in z.files}
    assert {k:sha(v.tobytes()) for k,v in a.items()}==meta['arrays_sha256']
    assert previous['counts']==dict(accepted=4947008,saved_intersection=4947008,extra=0,missing=0)
    model=read('milestones/59-extended-share-window/extended/data/model.json')
    def canon(w):
        names={};return tuple(names.setdefault(x,len(names)) for x in w)
    floors={'completed':{'012031':16,'012032':0,'012034':0,'012301':0,'012304':16,'012310':12,'012314':16,'012340':0,'012345':12},
            'conditional_floor18':{'012031':16,'012032':16,'012034':18,'012301':16,'012304':16,'012310':12,'012314':16,'012340':16,'012345':16}}
    pilots=[]
    for name,di,qi in [('completed',35,0),('conditional_floor18',177,43)]:
        hit=(a['direction']==di)&(a['history']==qi)&(9720<=a['count_code'])&(a['count_code']<11880)
        ix=np.flatnonzero(hit);code=a['count_code'][ix].astype(np.int64)
        ds=model['extensions'][di][3:];shape=''.join(map(str,min(canon(ds),canon(ds[::-1]))))
        w=np.maximum(a['weight'][ix].astype(np.int64),120*(code%6+1)+floors[name][shape])
        pi=expanded[name];p=previous['profiles'][name]['P']
        slack=w+pi[a['U'][ix]]-pi[a['V'][ix]]-p
        assert len(ix) and int(slack.min())>=0
        k=int(np.argmin(slack));e=int(ix[k])
        pilots.append(dict(profile=name,direction=di,history=qi,start=9720,stop_exclusive=11880,
                           total_codes=2160,accepted=len(ix),rejected=2160-len(ix),minimum_slack=int(slack.min()),
                           tight_edges=int((slack==0).sum()),critical=dict(count_code=int(code[k]),source=int(a['U'][e]),
                           target=int(a['V'][e]),weight=int(w[k]),source_potential=int(pi[a['U'][e]]),target_potential=int(pi[a['V'][e]]),P=p),
                           scope='Saved accepted rows equal the defined accepted set by the pinned prior independent enumeration. Weights reuse the pinned source graph plus the selected floor.'))
    elapsed=time.monotonic()-start;assert elapsed<300
    assert all(sha((ROOT/p).read_bytes())==h for p,h in PINS.items())
    result=dict(status='PASS_PARSED_LEAN_POTENTIAL_LITERAL_VALUES',profiles=profiles,pilots=pilots,
                numerical_seconds=elapsed,source_files_sha256=PINS,script_sha256=sha(Path(__file__).read_bytes()),
                total_checked_values=sum(p['checked_values'] for p in profiles.values()),
                scope='Independent parsing and expansion of actual generated Lean source bytes, including child references, balanced-table split sizes, root order and bounded lookup indices. No generator levels imported, no compiler, solver or Lean certification claimed.')
    (HERE/'data/potential-literal-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],profiles={name:{k:p[k] for k in ['checked_values','literal_definitions_by_depth','distinct_root_references','minimum','maximum','mismatches','expanded_raw_i64_sha256']} for name,p in profiles.items()},pilots=pilots,numerical_seconds=elapsed),indent=2))

if __name__=='__main__':main()
