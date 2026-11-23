from check import *
import sys
sys.path.insert(0,str(R))
from q9_rigid_ports_tree import export
from verify_q9_intact98_all_crossings import integer_bound
LOGS='snapshot converted diffuse8 supplement diffuse12'.split()
def selected():
    best={}
    for n in LOGS:
        for r in loadrows([n+'.jsonl']):
            k=r['i'],r['x']
            if k not in best or r['bound']/r['scale']<best[k]['bound']/best[k]['scale']:best[k]=dict(r,source=n)
    assert set(best)==set(jobs);return best
def rec(r):
    i,x=r['i'],r['x'];w=words[i];p=[0]
    for z in w:p.append(p[-1]^(1<<int(z)))
    m=x.bit_count()%2;L=set(p)|{x};ends=[int(a==m) for a in (0,1)];delta=sum((-1)**v.bit_count() for v in L)-(-1)**m
    c=json.load(gzip.open(D/r['cert'],'rt'))
    return dict(word=w,lower_vertices=sorted(L),ports=sorted((0,p[-1],x)),majority=m,upper_endpoint_counts=ends,upper_delta=delta,total_scaled=r['bound'],cert=c)
def main():
    dest=D/'trees';dest.mkdir(exist_ok=True)
    best=selected();(D/'manifest.jsonl').write_text(''.join(json.dumps(best[k],separators=(',',':'))+'\n' for k in jobs))
    remaining={z['rank'] for l in (D/'trees.jsonl').read_text().splitlines() if (z:=json.loads(l)) and ' open 0 ' not in z['generator']}
    with (D/'deep_trees.jsonl').open('w') as out,tempfile.TemporaryDirectory() as tmp:
        tmp=Path(tmp);tag=tmp/'case';tab=tmp/'case.tables';tree=tmp/'case.tree';tool=R/'q9_facet_priced_tree_20261121'
        for k in jobs:
            r=best[k]
            if r['rank'] not in remaining:continue
            obj=rec(r);export(obj,tab)
            result=subprocess.check_output([str(tool/'tree'),str(tag),str(tree),'193','1250000'],text=True).strip()
            verified=subprocess.check_output([str(tool/'replay'),str(tab),str(tree),'193'],text=True).strip()
            store=f'trees/{r["rank"]}_deep.tree.gz'
            with gzip.open(D/store,'wb') as g:g.write(tree.read_bytes())
            print(json.dumps(dict(rank=r['rank'],i=k[0],x=k[1],tree=store,generator=result,replay=verified)),file=out,flush=True)
            if ' found 0 ' not in result:break
if __name__=='__main__':main()
