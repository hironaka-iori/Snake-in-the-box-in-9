"""Check the new clause families on canonical images of actual bank snakes.
The deliberately unmatched alpha/cap premises may fail; all other clauses must hold.
"""
import gzip,json,sys
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from direct import census
sys.path.insert(0,str(ROOT/'milestones/27-empty-square-packing/scripts'))
from packing import canon

def main():
    prefix=HERE/'certificates/supported0_95';meta=json.loads((HERE/'data/supported0_95.json').read_text());meta['dirs']=meta['directions']
    with gzip.open(prefix.with_suffix('.meanings.json.gz'),'rt') as f:info=json.load(f)
    meaning={int(k):v for k,v in info['meaning'].items()};sm={int(k):v for k,v in info['smeaning'].items()}
    clauses=[]
    for line in prefix.with_suffix('.full.cnf').read_text().splitlines():
        if not line.startswith('p'):clauses.append(list(map(int,line.split()))[:-1])
    assert len(clauses)==len(info['tags'])==meta['clauses']
    bank=json.loads((ROOT/'work/bank9.json').read_text());examples=[]
    plain=json.loads((ROOT/'milestones/51-exact-bucket-pressure/pass2/data/queries/w018-plain.json').read_text())
    assert plain['directions']==meta['dirs'] and plain['bounds']==meta['bounds'] and plain['status']=='SAT'
    examples.append(('local',0,set(plain['selected'])))
    for bi,row in enumerate(bank):
        p=row['vertex_sequence'];ds=[(a^b).bit_length()-1 for a,b in zip(p,p[1:])]
        found=False
        for start in range(len(ds)-5):
            word=ds[start:start+6]
            if canon(word)!=tuple(meta['dirs']):continue
            images=dict(zip(word,meta['dirs']))
            for a,b in zip(sorted(set(range(9))-images.keys()),sorted(set(range(9))-set(images.values()))):images[a]=b
            def perm(v):return sum(((v>>a)&1)<<images[a] for a in range(9))
            S={perm(v^p[start]) for v in p};assert set(meta['window'])<=S
            examples.append((bi,start,S));found=True;break
        if len(examples)>=4:break
    assert examples
    output=[]
    for bi,start,S in examples:
        deg,empty={},{}
        import itertools
        for q in range(512):
            deg[q]=sum((q^(1<<a)) in S for a in range(9))
            empty[q]=sum(not S.intersection((q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b))) for a,b in itertools.combinations(range(9),2))
        tau={}
        for v,m in meaning.items():
            if m[0]=='p':tau[v]=m[1] in S
            elif m[0]=='e':tau[v]=m[1] in S and deg[m[1]]==1
        def val(l):return tau[abs(l)]==(l>0)
        for v,m in sm.items():
            if m[0]=='sq':_,q,a,b=m;tau[v]=not S.intersection((q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)))
            elif m[0]=='u':_,q,t=m;tau[v]=t<=(12*empty[q]//deg[q] if deg[q] else 0)
        ctrcounts=[]
        for lits,k,kind in info['ctrs']:
            counts=[0]
            for l in lits:counts.append(counts[-1]+int(val(l)))
            ctrcounts.append(counts)
        for v,m in meaning.items():
            if m[0]=='r':_,ci,i,j=m;tau[v]=ctrcounts[ci][i+1]>=j+1
        totcounts=[]
        for lits,kind in info['tots']:
            counts=[0]
            for l in lits:counts.append(counts[-1]+int(val(l)))
            totcounts.append(counts)
        for v,m in sm.items():
            if m[0]=='t':_,ti,lo,hi,c=m;tau[v]=totcounts[ti][hi]-totcounts[ti][lo]>=c
        failures=[]
        for i,(cl,tag) in enumerate(zip(clauses,info['tags'])):
            if any(val(l) for l in cl):continue
            allowed=tag[0]=='shareCap' or (tag[0]=='old' and tag[1][0]=='over' and info['ctrs'][tag[1][1]][2][0] in ('lo','hi'))
            assert allowed,(i,tag,cl)
            failures.append(tag)
        if bi=='local':assert len(failures)==1 and failures[0][0]=='shareCap'
        output.append(dict(bank_index=bi,start=start,clauses_checked=len(clauses),only_expected_premise_failures=len(failures)))
    (HERE/'data/assignment-controls.json').write_text(json.dumps(dict(status='PASSED',rows=output),indent=2)+'\n')
    print('PASSED',len(output),'assignments (one matching forest and three bank snakes);',len(clauses),'clauses each')
if __name__=='__main__':main()
