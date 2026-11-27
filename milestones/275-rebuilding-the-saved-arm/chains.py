"""Carry each 189-to-190-to-191 repair chain into the coordinates of the saved crossing."""
from collections import Counter
from repair_whole import construct
from rebuild_saved import HERE,MS,MAIN,face,read,resolve,save

def mapping(source,target):
    def axes(path):
        flips=[u^v for u,v in zip(path,path[1:])]
        dims=list(dict.fromkeys(flips))
        return bytes(dims.index(b) for b in flips),dims
    word,left=axes(source)
    for p in (target,target[::-1]):
        w,right=axes(p)
        if w!=word:continue
        assert len(left)==len(right)==9
        def move(v):
            t=v^source[0]
            return p[0]^sum(b for a,b in zip(left,right) if t&a)
        assert [move(v) for v in source]==list(p)
        return move
    raise ValueError("Different path shapes")

def main():
    hunt=face.dependencies(MS);starts=read(HERE/"whole-path-repairs.json")
    family=read(HERE/"growth-from-190.json");ref=read(HERE/"classified.json")["shapes"]
    sibling=resolve(starts,"948d");p=starts[MAIN]["start"];s=starts[sibling]["start"]
    assert len(set(p)-set(s))==len(set(s)-set(p))==2 and len(p)==len(s)==190
    assert p[p.index(256+44):]==s[s.index(256+44):]
    chains={}
    for code,v in starts[sibling]["shapes"].items():
        small=v["joined"];record=family["roots"][code];org=tuple(record["ordered"])
        move=mapping(org,small)
        bits=[1<<u for u in org];mask=sum(bits)
        for sig,omit in record["children"].items():
            if sig in chains:continue
            raw=next(q for q in construct(org,mask,bits,tuple(omit),191,192)
                     if hunt.original_audit.shape(q).hex()==sig)
            final=[move(u) for u in raw]
            assert hunt.original_audit.path_edges(final,9)==191
            chain=[p,s,small,final]
            changes=[]
            for v1,v2 in zip(chain,chain[1:]):
                removed=sorted(set(v1)-set(v2));added=sorted(set(v2)-set(v1))
                assert len(removed)<=2 and (len(added)-len(removed))==len(v2)-len(v1)
                changes.append(dict(removed=removed,added=added))
            assert hunt.original_audit.shape(final).hex()==sig and len(final)==192
            chains[sig]=dict(lengths=[len(v)-1 for v in chain],changes=changes,intermediate_190=small,
                         final_191=final,archive=ref[sig]["archive"],once_crossed=ref[sig]["once_crossed"])
    best=min(chains,key=lambda k:(bool(chains[k]["once_crossed"]),sum(len(c["removed"]) for c in chains[k]["changes"]),k))
    save(HERE/"chains-to-191.json",dict(primary=MAIN,sibling=sibling,primary_path=p,sibling_path=s,
            all_in_original_coordinates=True,chains=chains,selected=best))
    op=chains[best]
    save(HERE/"example-chain.json",dict(primary=MAIN,sibling=sibling,ordered=[p,s,op["intermediate_190"],op["final_191"]],
                                      edits=op["changes"],final_bank_matches=op["archive"],coordinate_uses=ref[best]["coordinate_uses"]))
    print("Coordinate-consistent 191 chains",len(chains),"selected",op["archive"],flush=True)
if __name__=="__main__":main()
