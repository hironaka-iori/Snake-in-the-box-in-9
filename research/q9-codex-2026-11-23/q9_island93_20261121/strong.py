from geom import *
import sys,random
from itertools import combinations
sys.path.insert(0,str(R))
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound
def main():
    name,start,count=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]);out=D/name;out.mkdir(exist_ok=True)
    known,seen=regs();todo=[r for r in seen if (r['i'],r['c']) not in known and 'pass' not in r]
    uniq={}; 
    for r in todo:
        k=r['i'],r['c']
        if k not in uniq or r['score']<uniq[k]['score']:uniq[k]=r
    todo=sorted(uniq.values(),key=lambda r:(-r['best_previous'],-r['score'],r['i'],r['c']))[start:start+count]
    A=list(combinations(range(8),3));random.Random(403215).shuffle(A);A=A[:12]
    with (D/(name+'.jsonl')).open('x') as log:
        for r in todo:
            i,c=r['i'],r['c'];L,P,m,eps,delta=geometry(i,c)
            bc,scale,t,du=build(cases[i]['lo'],P,L,eps,delta,A)
            val=bc+len(L)*scale+sum(a[0][2] for _,a in t);assert val==integer_bound(du,L,P,eps,delta)+len(L)*scale
            rec=dict(i=i,c=c,score=val,best_previous=r['best_previous'],source='lp12')
            if val<193*scale:
                rec['file']=name+f'/{i}_{c}.gz'
                masks=[sum(1<<v for v in x) for x in A]
                st=' '.join(map(str,masks))+'\n'+f'R {i} {c} {val} {scale} {du["balance_weight"]} '+ ' '.join(map(str,du['end_weights']))+' 0\n'
                (D/rec['file']).write_bytes(gzip.compress((st+''.join(' '.join(map(str,z))+'\n' for z in du['weights'])).encode(),compresslevel=6,mtime=0))
            print(json.dumps(rec,separators=(',',':')),file=log,flush=True)
if __name__=='__main__':main()
