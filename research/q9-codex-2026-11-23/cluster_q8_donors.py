from collections import defaultdict
from pathlib import Path
import json

def decode(w):
    p=[0]
    for c in w:p.append(p[-1] ^ 1<<int(c))
    return p
def identity(w):
    def one(s):
        d={};return tuple(d.setdefault(c,len(d)) for c in s)
    return min(one(w),one(w[::-1]))
def anchors(p):
    for arr in (p,p[::-1]):
        dims=[(x^y).bit_length()-1 for x,y in zip(arr,arr[1:])]
        for i in range(len(dims)-17):
            seq=dims[i:i+18];order=tuple(dict.fromkeys(seq))
            if len(order)<7:continue
            order=order+tuple(x for x in range(8) if x not in order)
            chars=bytes(order.index(x) for x in seq)
            yield chars,arr[i],order

def run():
    data=sorted(Path('q8_catalogue_96_98.words').read_text().splitlines(),key=lambda w:-len(w))
    assert len(set(map(identity,data)))==len(data)
    cache={}
    def mapping(a,b):
        k=(a,b)
        if k not in cache:
            img=[0]*256;unit={1<<i:1<<j for i,j in zip(a,b)}
            for v in range(1,256):img[v]=img[v&(v-1)]^unit[v&-v]
            cache[k]=img
        return cache[k]
    index=defaultdict(list);groups=[];rows=[]
    for ri,w in enumerate(data):
        p=decode(w);best=5;choice=None;seen=set()
        for key,orig,axes in anchors(p):
            for group,base,other in index.get(key,()):
                img=mapping(axes,other);shift=base^img[orig]
                transform=group,axes,other,shift
                if transform in seen:continue
                seen.add(transform);ref=groups[group]
                shared=sum((img[v]^shift) in ref for v in p)
                loss=len(ref)-shared
                if loss<best:best=loss;choice=group,[img[v]^shift for v in p]
                if not loss:break
            if not best:break
        if choice is None:
            g=len(groups);groups.append(set(p));choice=g,p
            for key,base,other in anchors(p):index[key].append((g,base,other))
        group,placed=choice
        assert len(set(placed))==len(p)
        newword=''.join(str((x^y).bit_length()-1) for x,y in zip(placed,placed[1:]))
        assert identity(newword)==identity(w)
        rows.append((group,ri,*placed))
    Path('q8_registered_donor_clusters.txt').write_text(''.join(' '.join(map(str,row))+'\n' for row in rows))
    print(json.dumps(dict(donors=len(rows),clusters=len(groups),largest=max(sum(r[0]==i for r in rows) for i in range(len(groups))),max_rep_points_missing=max(len(groups[r[0]]-set(r[2:])) for r in rows))))
if __name__=='__main__':run()
