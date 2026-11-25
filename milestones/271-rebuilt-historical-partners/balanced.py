"""Split a paired-crossing construction according to which Q7 segment is long."""
from argparse import ArgumentParser
from collections import Counter,defaultdict
from tempfile import TemporaryDirectory
from time import monotonic
from matched import HERE,R270,walk,insert_axis,remove_axis,read,write,checked,CSC,Path,subprocess

ADJ=[sum(1<<(v^(1<<d)) for d in range(7)) for v in range(128)]
ALL=(1<<128)-1
def mask(path):return sum(1<<v for v in path)

def between(blocked,port,minimum,maximum,seconds,audit):
    start,finish=(port,0) if audit else (0,port)
    stop=monotonic()+seconds
    found=[];seen=0;done=True;seq=[start]
    def dfs(tip,free,depth):
        nonlocal seen,done
        if not done:return
        seen+=1
        if seen%8192==0 and monotonic()>stop:done=False;return
        d=(tip^finish).bit_count()
        if d==1:
            if depth+1>=minimum and depth+1<=maximum and free&(1<<finish):
                p=seq+[finish];found.append(bytes(p[::-1] if audit else p))
            return
        if depth+d>maximum or depth+free.bit_count()<minimum:return
        choices=ADJ[tip]&free
        rest=free&~ADJ[tip]
        while choices and done:
            bit=choices&-choices
            w=bit.bit_length()-1
            seq.append(w);dfs(w,rest,depth+1);seq.pop()
            choices-=bit
    dfs(start, ALL&~mask(set(blocked)|{start}),0)
    return found,done

def census(exe,tmp,A,bit,threshold,seconds,audit):
    cut,=[i for i,(u,v) in enumerate(zip(A,A[1:])) if u^v==bit]
    fixed0=set(remove_axis(v,bit) for v in A[:cut+1])
    fixed1=set(remove_axis(v,bit) for v in A[cut+1:])
    upperhalf=threshold//2
    # ceil((threshold-1)/2) equals floor(threshold/2).
    engine="array" if audit else "mask"
    hist=Counter();best=None;complete=True;segments={};branches={}
    def accept(p,q):
        nonlocal best
        length=len(p)+len(q)-1
        if length<threshold or set(p[:-1])&set(q):return
        hist[length]+=1
        if best is None or length>len(best)-1:
            best=[insert_axis(v,bit) for v in p]+[insert_axis(v,bit)|bit for v in q]
    ok,first,_=walk(exe,tmp,fixed0-{0},0,upperhalf,seconds,engine)
    complete=ok;segments["long_first"]=len(first);segments["long_first_complete"]=ok
    groups=defaultdict(list)
    for p in first:
        if p[-1] not in fixed1:groups[p[-1]].append(p)
    for port,paths in groups.items():
        common=set(paths[0][:-1])
        for part in paths[1:]:common.intersection_update(part[:-1])
        minright=threshold-1-max(len(p)-1 for p in paths)
        closed,right,_=walk(exe,tmp,fixed1|common,port,minright,seconds,engine)
        complete &= closed
        for p in paths:
            for q in right:accept(p,q)
        branches["first/"+str(port)]=[len(paths),len(right),closed]
    for port in sorted(set(range(128))-fixed0-fixed1):
        closed,right,_=walk(exe,tmp,fixed1|{0},port,threshold-upperhalf,seconds,engine)
        complete &= closed
        if not right:
            branches["second/"+str(port)]=[0,0,closed];continue
        mandatory=set(right[0][1:])
        for part in right[1:]:mandatory.intersection_update(part[1:])
        minleft=threshold-1-max(len(q)-1 for q in right)
        left,ok=between((fixed0-{0})|mandatory,port,minleft,upperhalf-1,seconds,audit) if minleft<upperhalf else ([],True)
        complete &= ok
        for p in left:
            for q in right:accept(p,q)
        branches["second/"+str(port)]=[len(left),len(right),closed and ok]
    return dict(threshold=threshold,split=upperhalf,segments=segments,branches=branches,
            complete=complete,histogram=hist,best=checked(A,best) if best else None)

def main():
    ap=ArgumentParser()
    ap.add_argument("--target",type=int,default=189)
    ap.add_argument("--seconds",type=int,default=6)
    ap.add_argument("--control",choices=["Casella-A1","Bitterman-D1"],default="Casella-A1")
    ap.add_argument("--audit",action="store_true")
    a=ap.parse_args()
    roots=read(R270/"opposite-constructions.json")["roots"]
    k,r=next((k,r) for k,r in roots.items() if a.control in r["history"]);p=r["parent"]
    bit,=[u for u,n in Counter(x^y for x,y in zip(p,p[1:])).items() if n==1]
    stem="balanced-"+a.control+"-"+str(a.target)
    with TemporaryDirectory() as f:
        tmp=Path(f);exe=tmp/"Q7.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(R270/"PrimerPartners.cs")],capture_output=True,check=True)
        row=census(exe,tmp,p,bit,a.target-len(p),a.seconds,a.audit)
    row.update(root=k,matched_axis=bit.bit_length()-1,parent=p)
    if a.audit and row["complete"]:
        orig=read(HERE/(stem+".json"))
        if orig["complete"]:
            assert {str(n):c for n,c in row["histogram"].items()}==orig["histogram"]
            assert orig["segments"]==row["segments"] and row["branches"]==orig["branches"]
    write(HERE/(stem+("-replay" if a.audit else "")+".json"),row)
    print(a.control,a.target,row["complete"],dict(row["histogram"]),sum(not v[-1] for v in row["branches"].values()))
    if row["best"] and row["best"]["edges"]>=192:write(HERE/"candidate-192.json",row)
if __name__=="__main__":main()
