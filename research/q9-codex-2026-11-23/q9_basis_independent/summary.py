from collections import Counter,defaultdict
from pathlib import Path
from itertools import combinations
from subprocess import run
import json
D=Path(__file__).resolve().parent;Q=D.parent/'q9_change_basis'
def test_points(p,s,h,axes):
    assert len(p)==len(s)+h and len(set(p))==len(p) and set(s)<=set(p)
    S={0}
    for x in axes:S|={x^u for u in S}
    assert len(S)==512 and len(axes)==9
    for i,j in combinations(range(len(p)),2):assert ((p[i]^p[j]) in axes)==(j==i+1)
def records(name):
    inputs=[set(map(int,line.split())) for line in (D/(name+'.pts')).read_text().splitlines()]
    output=[l.split() for l in (D/(name+'.log')).read_text().splitlines()];assert len(inputs)==len(output)
    results=Counter();ranked=Counter();leaves=Counter()
    for row,(s,v) in enumerate(zip(inputs,output)):
        assert int(v[1])==row;results[v[2]]+=1;ranked[row]=int(v[6]);leaves[row]=int(v[10])
        if v[2]=='FOUND':
            idx=v.index('path');test_points(list(map(int,v[idx+1:])),s,2,set(map(int,v[v.index('basis')+1:idx])))
    return dict(rows=len(inputs),status=dict(results),nodes=sum(int(v[4]) for v in output),ranked=sum(ranked.values()),hole_sets=sum(leaves.values())),ranked
def root_counts(fn):
    counts=Counter()
    for line in (Q/fn).open():
        v=line.split()
        if v[0]=='FORM':assert v[3]=='CLOSED';counts[int(v[1])]+=int(v[5])
    return counts
def regression():
    word=(D.parent/'q9_gap_generations/prior191.words').read_text().split()[0][:189]
    out={}
    cmds={'historical_general':['general','191','5000000','0'],'repaired_general':['general_fixed','191','5000000','0'],'augmented':['augment','191','5000000','511','augment']}
    for name,(exe,*args) in cmds.items():
        txt=run([str(Q/exe),*args],input=word+'\n',text=True,check=True,capture_output=True).stdout
        out[name]=[s for s in txt.splitlines() if s.startswith('FOUND') or s.startswith('FORM 0 511')]
    (D/'endpoint_regression.json').write_text(json.dumps({'input_189_steps':word,'results':out},indent=2)+'\n')
    return {k:any(v.startswith('FOUND') for v in val) for k,val in out.items()}
def main():
    stats={}
    for name in ('full192','full195','full196','allbank','all190','positive','twoholes'):
        footer,rs=records(name)
        if name in ('allbank','all190'):
            counts=root_counts('plus_one.log' if name=='allbank' else 'plus_two.log');assert rs==counts
            footer['rowwise_candidate_basis_counts_equal_to_primary']=True
        stats[name]=footer
    fs=[json.loads(l) for l in (D/'forest_sat.jsonl').read_text().splitlines()];assert len(fs)==70
    stats['fixed_basis_sat']={str(h):dict(Counter(('found' if r['agreed'] else 'closed') for r in fs if r['holes']==h)) for h in range(1,6)}
    stats['native_cardinality_sat']=dict(Counter(q['status'] for q in map(json.loads,(D/'independent.jsonl').read_text().splitlines())))
    stats['tip_regression']=regression()
    print(json.dumps(stats,indent=2))
if __name__=='__main__':main()
