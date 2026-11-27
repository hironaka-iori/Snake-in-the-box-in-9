"""Construct lower-bound examples in the 570-shape class by trimming earlier explicit paths."""
from enumerate_groups import HERE,R270,R272,read,write,paircheck,unrooted,wordof

def main():
    family={k for k in read(R272/"q7-single-crossings.json")["q7_shapes"] if len(k)==96}
    out={}
    def add(p,q,file,source,trim):
        if len(p)!=49 or len(q)!=47 or unrooted(p) not in family:return
        assert p[0]==q[0]==0 and set(p)&set(q)=={0}
        j=p[::-1]+[128+x for x in q];s=unrooted(j)
        assert len(j)==96
        if s not in out:
            out[s]=dict(q8_edges=95,joined_q8=j,parent48=p,partner=q,all_pairs=paircheck(j,8),
                        source_file=file,source_shape=source,trimmed_from_longer_arm=trim)
    for w,r in read(R272/"q8-arms.json").items():
        add(r["parent49"][:-1],r["partner"],"272-forty-nine-edge-parents/q8-arms.json",w,1)
    for w,r in read(R270/"q8-primer-arms.json").items():
        j=r["joined_q8"];a=wordof(j).index(7)
        p=j[:a+1][::-1];q=[v^128 for v in j[a+1:]]
        if p[0]!=0 or q[0]!=0:raise ValueError("Expected normalized crossing")
        add(p[:-2],q,"270-optimal-seven-dimensional-arms/q8-primer-arms.json",w,2)
    write(HERE/"shorter-witnesses.json",out)
    print("95-edge constructions",len(out),flush=True)

if __name__=="__main__":main()
