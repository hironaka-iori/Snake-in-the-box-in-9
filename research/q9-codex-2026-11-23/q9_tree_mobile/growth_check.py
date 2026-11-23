from pathlib import Path
import json,collections,sys
from audit import checked
D=Path(__file__).resolve().parent
def audit(log='growth.log'):
 root=json.loads((D/'verified.json').read_text())['best_tree_witness']['path'];pool=[root];dest=[];levels=[];best=root;moves=[];pairs=0
 for line in (D/log).read_text().splitlines():
    r=json.loads(line)
    if r['kind']=='level':
        assert len(pool)==r['parents'] and r['length']==len(pool[0])-1 and r['unique_next']==len(dest) and sum(r['status'].values())==r['trials']
        levels.append(r);pool=dest;dest=[];continue
    p=r['path'];parent=pool[r['parent']];s=set(parent[::2]);z=set(p[::2]);assert len(p)==len(parent)+2 and p[0].bit_count()%2==0
    pairs+=checked(p);lost=s-z;new=z-s;mask=r['mask'];free=dict(r['free'])
    assert len(lost)==r['moves']>=r['minimum'] and len(new)==len(lost)+1
    assert all(u in free and free[u]==(u^mask) and free[u] in new for u in lost)
    assert len(new-{free[u] for u in lost})==1
    assert all(p!=q for q in dest);dest.append(p);moves.append(len(lost));best=p
 return dict(log=log,solved_stages=levels,best_edges=len(best)-1,best_path=best,checked_nonroot_witnesses=len(moves),pair_checks=pairs,moves_range=[min(moves),max(moves)],parents_in_final_frontier=len(pool))
if __name__=='__main__':
 out=audit(*sys.argv[1:]);(D/'growth_verified.json').write_text(json.dumps(out,indent=2)+'\n');print(out['best_edges'],out['checked_nonroot_witnesses'],out['pair_checks'],out['moves_range'])
