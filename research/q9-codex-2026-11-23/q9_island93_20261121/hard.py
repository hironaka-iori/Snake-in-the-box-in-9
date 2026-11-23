from geom import *
from itertools import combinations
import random,sys,subprocess
sys.path.insert(0,str(R))
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
from q9_rigid_ports_tree import export
def main():
    stage=sys.argv[1]
    if stage=='freeze':
        known,rows=regs();raw={}
        for r in rows:
            k=r['i'],r['c']
            if k in known:continue
            if k not in raw or r['score']<raw[k]['score']:raw[k]=r
        pending=sorted(raw.values(),key=lambda r:(-r['best_previous'],-r['score'],r['i'],r['c']))
        assert len(known)+len(pending)==6040
        (D/'lp_jobs.json').write_text(json.dumps(pending));print(len(pending));return
    part,mod=map(int,sys.argv[2:4]);alljobs=json.loads((D/'lp_jobs.json').read_text());jobs=alljobs[part::mod]
    dest=D/stage;dest.mkdir(exist_ok=True);A=list(combinations(range(8),3));random.Random(403215).shuffle(A)
    with (D/(stage+f'_{part}.jsonl')).open('x') as out:
        for r in jobs:
            i,c=r['i'],r['c'];L,P,m,eps,delta=geometry(i,c);tag=dest/f'{i}_{c}'
            for n in (12,16):
                base,scale,t,dual=build(cases[i]['lo'],P,L,eps,delta,A[:n])
                v=base+sum(o[0][2] for _,o in t)+len(L)*scale;assert v==integer_bound(dual,L,P,eps,delta)+len(L)*scale
                if v<1930000:break
            rec=dict(i=i,c=c,score=v,best_previous=r['best_previous'],source='lp'+str(n))
            masks=[sum(1<<d for d in x) for x in A[:n]]
            text=' '.join(map(str,masks))+'\n'+f'R {i} {c} {v} {scale} {dual["balance_weight"]} '+' '.join(map(str,dual['end_weights']))+' 0\n'
            data=gzip.compress((text+''.join(' '.join(map(str,k))+'\n' for k in dual['weights'])).encode(),compresslevel=3,mtime=0);tag.with_suffix('.gz').write_bytes(data)
            if v<1930000:rec['file']=stage+'/'+tag.name+'.gz'
            else:
                raw=dict(word=cases[i]['w'],lower_vertices=sorted(L),ports=sorted(P),majority=m,upper_endpoint_counts=eps,upper_delta=delta,cert=dual,total_scaled=v)
                export(raw,tag.with_suffix('.tables'));tree=tag.with_suffix('.tree')
                rec['tree']=subprocess.check_output([R/'q9_facet_priced_tree_20261121/tree',tag,tree,'193','240000'],text=True).strip()
                rec['replay']=subprocess.check_output([R/'q9_facet_priced_tree_20261121/replay',tag.with_suffix('.tables'),tree,'193'],text=True).strip()
                rec['pricefile']=stage+'/'+tag.name+'.gz'
                picks=[l for l in tree.read_text().splitlines() if l.startswith('H ')]
                if picks:
                    print('WITNESS',picks,flush=True);(D/'FOUND.txt').write_text('\n'.join(picks)+'\n')
                compressed=gzip.compress(tree.read_bytes(),compresslevel=6,mtime=0);assert gzip.decompress(compressed)==tree.read_bytes();tree.with_suffix('.tree.gz').write_bytes(compressed);tree.unlink()
            print(json.dumps(rec,separators=(',',':')),file=out,flush=True)
if __name__=='__main__':main()
