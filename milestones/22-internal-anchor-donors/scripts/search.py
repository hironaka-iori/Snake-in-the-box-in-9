"""Complete donor paths, internal-anchor alignments, and endpoint-tail exchanges."""
import ast,itertools,json,re,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/21-endpoint-recombination/scripts'))
from exchange import sha,check
def sources():
    a=json.loads((ROOT/'milestones/19-coordinate-face-repair/data/two-arm-seed186.json').read_text())['path_vertices']
    if a[0]!=41:a.reverse()
    values=ast.literal_eval('['+re.search(r'def witnessValues : Array Nat := #\[(.*?)\]',(ROOT/'work/final_lean/Snake9.lean').read_text()).group(1)+']')
    order=[0,1,3,2,6,4,5,7,8]
    b=[sum(((v>>k)&1)<<j for j,k in enumerate(order))^41 for v in values]
    check(a);check(b);assert len(b)==192 and b[:191]==json.loads((ROOT/'milestones/20-middle-path-release/data/paired-seed190.json').read_text())['path_vertices']
    return a,b
def alignments(b,s,t):
    d=b[s]^b[t];assert d.bit_count()==4
    one=[k for k in range(9) if d>>k&1];zero=[k for k in range(9) if not(d>>k&1)]
    for op in itertools.permutations([1,3,5,6]):
        for zp in itertools.permutations([0,2,4,7,8]):
            perm=[0]*9
            for k,v in zip(one+zero,list(op)+list(zp)):perm[k]=v
            q=[sum(((v^b[s])>>k&1)<<perm[k] for k in range(9))^41 for v in b]
            assert q[s]==41 and q[t]==67
            yield perm,False,q
            yield perm,True,[v^106 for v in reversed(q)]
def choose_pairs(b):
    possible=[(i,j) for i in range(1,191) for j in range(i+1,191) if (b[i]^b[j]).bit_count()==4]
    pairs=[(0,190)]
    for gap in [180,140,100]:
        pair=min(possible,key=lambda p:(abs(p[1]-p[0]-gap),abs(p[0]+p[1]-191),p))
        assert pair not in pairs;pairs.append(pair)
    return pairs
def run():
    begin=time.monotonic();a,b=sources();pairs=choose_pairs(b);pre=[0]
    for v in a:pre.append(pre[-1]|1<<v)
    closed=[(1<<v)|sum(1<<(v^(1<<k)) for k in range(9)) for v in range(512)]
    reports=[];witnesses=[];near=[]
    for pair in pairs:
        counts={'interior_candidates_ge192':0,'tail_candidates_ge192':0,'interior_valid':0,'tail_valid':0,'simple_196_candidates':0};best={};sample=[]
        for index,(perm,swap,q) in enumerate(alignments(b,*pair)):
            pos={v:i for i,v in enumerate(q)};anchors=[i for i,v in enumerate(a) if v in pos]
            qp=[0];table=[[closed[v] for v in q]]
            for v in q:qp.append(qp[-1]|1<<v)
            span=1
            while span*2<=len(q):
                last=table[-1];table.append([last[i]|last[i+span] for i in range(len(q)-span*2+1)]);span*=2
            def masks(lo,hi):
                n=hi-lo
                if n==0:return 0,0
                k=n.bit_length()-1
                return qp[hi]^qp[lo],table[k][lo]|table[k][hi-(1<<k)]
            def consider(kind,edges,bm,cm,retained,cut,donor,make):
                if edges<192:return
                counts[kind+'_candidates_ge192']+=1
                if bm&retained:return
                bad=(cm&retained).bit_count()
                if edges==196:
                    counts['simple_196_candidates']+=1
                    if kind not in best or bad<best[kind]['conflicting_retained_vertices']:
                        path=make();assert len(path)==197 and len(set(path))==197
                        defects=[[i,j] for j in range(len(path)) for i in range(j-1) if (path[i]^path[j]).bit_count()==1]
                        best[kind]={'kind':kind,'anchor_pair':pair,'alignment':index,'permutation':perm,'swap':swap,'recipient_cut':cut,'donor_cut':donor,'path_vertices':path,'conflicting_retained_vertices':bad,'chords':defects}
                if bad:return
                path=make();check(path);assert len(path)==edges+1
                counts[kind+'_valid']+=1;witnesses.append({'edges':edges,'path_vertices':path,'anchor_pair':pair,'alignment':index,'kind':kind,'recipient_cut':cut,'donor_cut':donor})
            for ai,i in enumerate(anchors):
                for j in anchors[ai+1:]:
                    u,w=pos[a[i]],pos[a[j]];lo,hi=sorted((u,w));edges=186+hi-lo-(j-i)
                    if edges<192 or j-i<2:continue
                    bm,cm=masks(lo+1,hi);retained=pre[i]|(pre[-1]^pre[j+1])
                    def make(i=i,j=j,u=u,w=w,lo=lo,hi=hi):return a[:i+1]+(q[lo+1:hi] if u<w else q[lo+1:hi][::-1])+a[j:]
                    consider('interior',edges,bm,cm,retained,[i,j],[u,w],make)
            for i in anchors:
                u=pos[a[i]]
                for reverse_a in (False,True):
                    prefix=a[:i+1] if not reverse_a else a[i:][::-1]
                    retained=pre[i] if not reverse_a else pre[-1]^pre[i+1]
                    for reverse_b in (False,True):
                        lo,hi=(u+1,len(q)) if not reverse_b else (0,u)
                        edges=len(prefix)-1+hi-lo
                        if edges<192:continue
                        bm,cm=masks(lo,hi)
                        def make(prefix=prefix,lo=lo,hi=hi,reverse_b=reverse_b):return prefix+(q[lo:hi][::-1] if reverse_b else q[lo:hi])
                        consider('tail',edges,bm,cm,retained,[i,int(reverse_a)],[u,int(reverse_b)],make)
            if index in (0,1000,2000,3000,4000,5000,5759):
                sample.append({'index':index,'overlap':len(anchors),'donor_endpoints':[q[0],q[-1]]})
        near.extend(best.values());reports.append({'anchor_pair':pair,'alignments':5760,'counts':counts,'samples':sample})
        (HERE/'data').mkdir(parents=True,exist_ok=True)
        data={'script_sha256_lf':sha(Path(__file__)),'source_core_sha256_lf':sha(ROOT/'work/final_lean/Snake9.lean'),'recipient_sha256_lf':sha(ROOT/'milestones/19-coordinate-face-repair/data/two-arm-seed186.json'),'donor_vertices':b,'reports':reports,'witnesses':witnesses,'near_candidates':near,'seconds':time.monotonic()-begin,'scope':'All 5760 isometries mapping each selected donor anchor pair to recipient endpoints, with either orientation. One interval replacement or one endpoint-tail replacement. Near candidates have chords and are not snakes.'}
        (HERE/'data/search.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({'pair':pair,'counts':counts,'best_chords':{k:len(v['chords']) for k,v in best.items()},'seconds':data['seconds']}),flush=True)
if __name__=='__main__':run()
