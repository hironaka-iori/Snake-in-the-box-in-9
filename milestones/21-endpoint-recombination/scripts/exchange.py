"""Enumerate single segment exchanges under the common-endpoint stabilizer."""
import hashlib, itertools, json, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def check(p):
    assert len(set(p))==len(p) and all(0<=v<512 for v in p)
    for j,v in enumerate(p):
        for i,w in enumerate(p[:j]): assert ((v^w).bit_count()==1)==(j==i+1)
def parents():
    a=json.loads((ROOT/'milestones/19-coordinate-face-repair/data/two-arm-seed186.json').read_text())['path_vertices']
    b=json.loads((ROOT/'milestones/20-middle-path-release/data/paired-seed190.json').read_text())['path_vertices']
    if a[0]!=41:a.reverse()
    check(a);check(b);assert a[0]==b[0]==41 and a[-1]==b[-1]==67
    return a,b
def transforms(b):
    one=[1,3,5,6];zero=[0,2,4,7,8]
    for op in itertools.permutations(one):
        for zp in itertools.permutations(zero):
            perm=list(range(9))
            for x,y in zip(one+zero,list(op)+list(zp)):perm[x]=y
            base=[sum(((v^41)>>k&1)<<perm[k] for k in range(9))^41 for v in b]
            yield perm,False,base
            yield perm,True,[v^106 for v in reversed(base)]
def run():
    begin=time.monotonic();a,b=parents();aset=set(a)
    closed=[sum(1<<w for w in [v]+[v^(1<<k) for k in range(9)]) for v in range(512)]
    pre=[0]
    for v in a:pre.append(pre[-1]|1<<v)
    rows=[];best=a;valid=0;examined=0;lengths={};alignments=[]
    for index,(perm,swap,q) in enumerate(transforms(b)):
        pos={v:i for i,v in enumerate(q)}
        anchors=[i for i,v in enumerate(a) if v in pos]
        qp=[0];table=[[closed[v] for v in q]]
        for v in q:qp.append(qp[-1]|1<<v)
        span=1
        while 2*span<=len(q):
            last=table[-1];table.append([last[i]|last[i+span] for i in range(len(q)-2*span+1)]);span*=2
        accepted=0;largest=186
        for ai,i in enumerate(anchors):
            for j in anchors[ai+1:]:
                u,w=pos[a[i]],pos[a[j]];lo,hi=sorted((u,w));gain=hi-lo-(j-i)
                if gain<=0 or j-i<2:continue
                examined+=1
                n=hi-lo-1;k=n.bit_length()-1
                blocked=table[k][lo+1]|table[k][hi-(1<<k)]
                retained=pre[i]|(pre[-1]^pre[j+1])
                if blocked&retained:continue
                middle=q[lo+1:hi]
                if u>w:middle=middle[::-1]
                child=a[:i+1]+middle+a[j:];check(child)
                edges=len(child)-1;accepted+=1;valid+=1;largest=max(largest,edges)
                lengths[edges]=lengths.get(edges,0)+1
                if len(child)>len(best):best=child
                rows.append({'alignment':index,'cut_indices':[i,j],'donor_indices':[u,w],'edges':edges})
        overlap=len(aset&set(q))
        alignments.append({'index':index,'permutation':perm,'swap':swap,'overlap':overlap,'union_size':378-overlap,'valid_exchanges':accepted,'best_edges':largest})
        if index%500==0:print(json.dumps({'alignment':index,'valid':valid,'best':len(best)-1}),flush=True)
    data={'script_sha256_lf':sha(Path(__file__)),'alignments':alignments,'exchanges':rows,'positive_gain_candidates':examined,'valid_exchanges':valid,'length_counts':lengths,'best_path':best,'best_edges':len(best)-1,'seconds':time.monotonic()-begin,'scope':'All 5760 endpoint-set-preserving coordinate isometries of the donor; one contiguous recipient interval replaced by one donor interval. No general recombination exclusion.'}
    (HERE/'data').mkdir(parents=True,exist_ok=True)
    (HERE/'data/exchanges.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k not in ('alignments','exchanges','best_path')}),flush=True)
if __name__=='__main__':run()
