from pathlib import Path
from collections import Counter
import json
from half_inputs import valid,word
D=Path(__file__).resolve().parent;R=D.parent
W=(R/'q8_catalogue_96_98.words').read_text().split()
def normalize(s):
    m={};return tuple(m.setdefault(c,len(m)) for c in s)
def forest(ms):
    groups=[{i} for i in range(9)]
    for m in set(ms):
        a,b=[i for i in range(9) if m>>i&1];ga=next(z for z in groups if a in z);gb=next(z for z in groups if b in z)
        if ga==gb:return False
        groups=[g for g in groups if g!=ga and g!=gb]+[ga|gb]
    return True
def main():
    words={}
    for i,w in enumerate(W):
        for rev in [0,1]:
            for j in range(len(w)):
                for n in range(1,min(9,len(w)-j)+1):
                    s=(w[::-1] if rev else w)[j:j+n];words.setdefault(normalize(s),(i,rev,j,s))
    report=json.loads((D/'warm_verified.json').read_text());r=report['best'];line=next(l.split() for l in (D/'blind.log').read_text().splitlines() if l.startswith('W ') and list(map(int,l.split()[11:]))==r['path'])
    _,it,idx,b,start,keep,size,style,left,right,e=map(str,line[:11]);size=int(size);left=int(left);keep=int(keep);right=int(right);assert int(style)==0
    par=[list(map(int,l.split())) for l in (D/'public191.txt').read_text().splitlines()][int(idx)];v=par[int(b)+2*int(start)];ev=[x for x in r['path'] if (v^x).bit_count()%2==0];d=[x^y for x,y in zip(ev,ev[1:])]
    segs={}
    for tag,seq in [('left',d[:left][::-1]),('core',d[left:left+keep-1]),('right',d[left+keep-1:])]:
        j=0;blocks=[]
        while j<len(seq):
            n=min(size,len(seq)-j)
            while n and (normalize(seq[j:j+n]) not in words or not forest(seq[j:j+n])):n-=1
            assert n and (tag=='core' or n==min(size,len(seq)-j))
            i,rev,offset,w=words[normalize(seq[j:j+n])];masks=dict(zip(w,seq[j:j+n]));assert len(set(masks.values()))==len(masks)
            q=[0]
            for c in w:q.append(q[-1]^1<<int(c))
            assert valid(q)
            blocks.append(dict(donor_index=i,reversed=rev,offset=offset,source_word=w,label_to_mask=masks));j+=n
        segs[tag]=blocks
    a=report['best'];out=dict(archive=a['archive'],from_run=a['run'],step_block_size=size,ordered_segments=segs,proof_of_representation='Each listed substring independently realizes the used equality pattern. Original sampled donor indices can differ when the same pattern occurs in multiple donors.',edges=a['edges'],path=a['path'])
    (D/'dictionary_witness.json').write_text(json.dumps(out,indent=2)+'\n');print([(k,len(a)) for k,a in segs.items()])
if __name__=='__main__':main()
