import collections,itertools,json
from pathlib import Path
D=Path(__file__).resolve().parent
def checked(path):
    n=len(path)
    assert len(set(path))==n
    for i,j in itertools.combinations(range(n),2):
        assert ((path[i]^path[j]).bit_count()==1)==(j==i+1)
    return n*(n-1)//2
def verify_tree(row,src):
    _,idx,stored,edges,w=src;assert idx==row['root'];assert len(edges)==8==len(set(edges))
    assert all(0<m<512 and m.bit_count()==2 for m in edges)
    reached={0}
    for _ in range(9):
        for m in edges:
            u,v=[i for i in range(9) if m&(1<<i)]
            if u in reached or v in reached:reached.update((u,v))
    assert len(reached)==9
    c=[0];t=[0]
    for d in w:
        c.append(c[-1]^1<<int(d));t.append(t[-1]^edges[int(d)])
    checked(c);S=set(t);assert len(t)==len(S) and S==set(stored)
    z=set(row['path'][::2]);assert len(z)==len(S);left=S-z;right=z-S
    assert right=={x^row['mask'] for x in left} and len(left)==row['moves']
    return dict(edges=len(row['path'])-1,moved=len(left),fixed=len(S)-len(left),mask=row['mask'],source_word=w,edge_masks=edges,base_even=t,path=row['path'],outgoing=sorted(left),incoming=sorted(right),vertex_pairs=checked(row['path']))
def main():
    checked_rows={};trees=[];ncert=0;tested=collections.Counter();high=collections.Counter();sources=set()
    for f in sorted(D.glob('*.jsonl')):
        a=[json.loads(l) for l in f.read_text().splitlines()];assert all(z['i']==i and z['mode']==f.stem for i,z in enumerate(a))
        c=collections.Counter(z['status'] for z in a)
        if not f.stem.startswith(('treegrow','control')):high.update(c)
        checked_rows[f.stem]=dict(rows=len(a),states=c,moving_pairs=[min(z['free'] for z in a),max(z['free'] for z in a)],separation_cuts=sum(z['cuts'] for z in a))
        if f.stem.startswith('treegrow'):source=json.loads((D/(f.stem+'_sources.json')).read_text())
        for r in a:
            if r['status']=='FOUND':
                p=r['path'];ncert+=checked(p);assert all(x.bit_count()%2==i%2 for i,x in enumerate(p))
                if f.stem.startswith('treegrow'):trees.append(verify_tree(r,source[r['i']%len(source)]))
                elif f.stem in ('control','controlgain'):assert len(p)==191 and r['moves']>=r['minimum']
                else:assert len(p)==193
    cross=json.loads((D/'crosscheck.json').read_text())
    out=dict(search192_trials=sum(high.values()),search192_status=high,grouped=checked_rows,independent_native_small_models=len(cross),independent_native_even_sets=sum(r['enum'] for r in cross),independent_small_status=collections.Counter(r['sat'] for r in cross),all_positive_vertex_pairs=ncert,best_tree_witness=max(trees,key=lambda r:r['edges']),short_tree_lengths=[(r['edges'],r['moved']) for r in trees])
    (D/'verified.json').write_text(json.dumps(out,indent=2)+'\n');print(out['search192_trials'],dict(high),out['short_tree_lengths'],ncert)
if __name__=='__main__':main()
