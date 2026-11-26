"""Combine optimal-parent windows with the independently enumerated Q7 single-crossing family."""
from parents import HERE,R270,read,write,points,unrooted,grow
def main():
    source=read(HERE/"q7-single-crossings.json")
    small={w for w in source["q7_shapes"] if len(w)//2==48}
    single=set(source["parents"])
    extends={}
    for w in sorted(small):
        p=points(bytes.fromhex(w))
        for i,d in enumerate((p,p[::-1])):
            for q in grow(d):extends.setdefault(unrooted(q),[]).append([w,i])
    known50={unrooted(r["q7_parent"]) for r in read(R270/"palani-q7.json")["paths"].values()}
    assert {w for w in source["q7_shapes"] if len(w)//2==50}=={w for w in known50 if min(bytes.fromhex(w).count(i) for i in range(7))==1}
    window=set(read(HERE/"parents-wide-20.json")["parents"]);archive=set(read(HERE/"project-intervals.json")["parents"])
    kinds=dict(window=sorted(window),single_crossing=sorted(single),grown_from_48=extends,archive=sorted(archive))
    parents=sorted(window|single|set(extends)|archive)
    write(HERE/"seeds.json",dict(parents=parents,source_families=kinds))
    print("Seed classes",[(k,len(v)) for k,v in kinds.items()],"union",len(parents))
if __name__=="__main__":main()
