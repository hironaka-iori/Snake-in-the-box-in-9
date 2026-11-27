"""Gather archived 97/98-edge arms and reconcile the published 98-edge witness by coordinates."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import gzip
import json

HERE=Path(__file__).resolve().parent
MS=HERE.parent if (HERE.parent/"249-long-parent-joins").is_dir() else Path("E:/Snake-in-a-box/milestones")
CARLSON="https://www.ou.edu/content/dam/CoE/CS/Thesis_Dissertations/2016/Spring%2016/Carlson%20-%20Dissertation.pdf"
ROKICKI="https://www.minortriad.com/snake/"
OPTIMAL="https://doi.org/10.1007/s00373-014-1423-3"
INDEX=[1,2,3,6,11,10,9,24,21,44,53,60,57,40,89,88,73,74,75,70,91,38,219,198,203,202,201,216,
       209,48,49,50,51,46,211,238,239,242,241,244,141,132,129,130,159,158,163,190,179,178,175,170,167,186,185,188,
       181,172,173,84,77,68,65,66,95,34,223,194,193,196,221,36,29,100,97,112,113,114,115,110,107,150,139,138,
       137,152,153,156,229,252,249,250,231,26,103,122,121,124,117]
TRANSITIONS="0123104154 3146340134 6743104274 0147514016 3104154314 2340134274 3104674014 7561340142 7410431641 04764013"

def read(p):return json.loads(p.read_bytes())
def save(p,x):p.write_bytes((json.dumps(x,separators=(",",":"))+"\n").encode())
def path_of(word):
    path=[0]
    for c in word:path.append(path[-1]^(1<<c))
    return path
def canonical(p):
    def code(seq):
        bits=[u^v for u,v in zip(seq,seq[1:])]
        axes={b:i for i,b in enumerate(dict.fromkeys(bits))}
        return bytes(axes[b] for b in bits)
    return min(code(p),code(p[::-1])).hex()
def valid(p,d):
    rank={v:i for i,v in enumerate(p)}
    assert len(rank)==len(p) and all(0<=v<1<<d for v in p)
    for i,v in enumerate(p):
        assert {rank[v^(1<<b)] for b in range(d) if v^(1<<b) in rank}=={j for j in (i-1,i+1) if 0<=j<len(p)}
    return len(p)*(len(p)-1)//2

def main():
    rows={};pins={}
    def load(file):
        p=MS/file;raw=p.read_bytes()
        pins[file]=sha256(raw).hexdigest()
        return json.loads(gzip.decompress(raw) if p.suffix==".gz" else raw)
    def add(name,p,reference):
        if len(p) not in (98,99):return
        valid(p,8);c=canonical(p)
        row=rows.setdefault(c,dict(path=path_of(bytes.fromhex(c)),sources={}))
        row["sources"].setdefault(name,[]).append(reference)
    u1=[(i-1)^((i-1)>>1) for i in INDEX]
    u2=path_of([int(c) for c in TRANSITIONS if c!=" "])
    add("Carlson 2016 Appendix C.2 p.148",u1,CARLSON)
    add("Rokicki sn8 attributed to Carlson 2010",u2,ROKICKI)
    snakepit=read(HERE/"snakepit-source.json");raw=snakepit["row"];occupied=set(raw["vertices"])
    ends=sorted(v for v in occupied if sum((v^(1<<i)) in occupied for i in range(8))==1)
    assert len(ends)==2 and (raw["n"],raw["k"],raw["L"])==(8,1,98)
    sp=[ends[0]];remaining=occupied-{sp[0]}
    while remaining:
        options=[v for v in remaining if (v^sp[-1]).bit_count()==1]
        assert len(options)==1
        sp.append(options[0]);remaining.remove(options[0])
    add("Math-AI-Caltech Snakepits",sp,snakepit["url"])
    maps=[]
    for backwards,other in enumerate((sp,sp[::-1])):
        left=[a^b for a,b in zip(other,other[1:])];right=[a^b for a,b in zip(u1,u1[1:])]
        correspondence=dict(zip(left,right))
        if len(set(correspondence.values()))!=8:continue
        mapped=[u1[0]^sum(w for bit,w in correspondence.items() if (v^other[0])&bit) for v in other]
        if mapped==u1:maps.append(dict(reversed=bool(backwards),root=other[0],axes=[correspondence[1<<i].bit_length()-1 for i in range(8)]))
    for i,r in enumerate(load("246-eight-dimensional-parents/donors.json")["shapes"]):add("R246",r["path"],i)
    for k,p in load("253-repeated-segment-growth/closure.json")["paths"].items():add("R253",p,k)
    for w,p in load("267-fixed-arm-extensions/donor-paths.json.gz"):
        if len(w) in (194,196):add("R267",path_of(bytes.fromhex(w)),w)
    for k,r in load("270-optimal-seven-dimensional-arms/uga270.json")["paths"].items():
        add("R270 UGA thesis",path_of(bytes.fromhex(r["canonical"])),k)
    for f in ("270-optimal-seven-dimensional-arms/q8-primer-arms.json","272-forty-nine-edge-parents/q8-arms.json"):
        for k in load(f):
            if len(k) in (194,196):add(f.split("-")[0],path_of(bytes.fromhex(k)),k)
    for k,r in load("274-rebuilding-near-a-fixed-arm/union-paths.json")["shapes"].items():
        add("R274",r["path"],k)
    fixed=load("249-long-parent-joins/direct98.json")
    audit=load("249-long-parent-joins/audit98.json");positive=load("249-long-parent-joins/positive98.json")
    for k,v in fixed["pins"].items():
        if k in pins:assert v==pins[k]
    archived=fixed["roots"]["0"]; known={}
    for case in audit["cases"]:
        root=case["root"];p=fixed["roots"][str(root)]
        w=next(r["witness"] for r in positive["cases"] if r["root"]==root)
        if fixed["witnesses"][str(root)]["partner_edges"]>w["partner_edges"]:w=fixed["witnesses"][str(root)]
        assert w["joined"]==p[::-1]+[256+v for v in w["partner"]] and valid(w["joined"],9)
        assert len(p)+len(w["partner"])-1==case["joined_lower"]
        known[str(root)]=dict(parent=p,partner=w["partner"],lower=case["joined_lower"],upper=case["joined_upper"])
    assert len(archived)==99 and canonical(u1)==canonical(u2)==canonical(archived)
    assert u1==archived
    import sys
    sys.path.insert(0,str(MS/"274-rebuilding-near-a-fixed-arm"))
    from known274 import normalize,transfer
    indexed={}
    for root,r in known.items():
        nd=normalize(r["parent"])[0];k=sha256(nd).hexdigest()
        indexed[k]=dict(parent=r["parent"],normalized=list(nd),raw_endpoint=int(root))
    prior=transfer(MS,indexed)
    earlier=load("274-rebuilding-near-a-fixed-arm/results.json")["roots"]
    for k,r in indexed.items():
        row=known[str(r["raw_endpoint"])]
        matches=prior["roots"].get(k,{}).get("reasons",[])[:]
        for n in range(94,len(r["normalized"])+1):
            prefix=bytes(r["normalized"][:n]);ref=sha256(prefix).hexdigest()
            if ref in earlier:
                assert bytes(earlier[ref]["normalized"])==prefix
                extra=len(r["normalized"])-n
                matches.append(dict(round=274,kind="rooted_prefix",source_root=ref,
                                    added_free_end_vertices=extra,ceiling=earlier[ref]["maximum"]+extra))
        row["other_prior_reasons"]=matches
        row["upper"]=min([row["upper"]]+[x["ceiling"] for x in matches])
    report=dict(reference_shape=canonical(archived),sources_sha256=pins,
        audited_previous_transfer_sources=prior["sha256"],
        published=dict(Carlson=dict(url=CARLSON,section="Appendix C.2, printed page 148",printed_vertices=INDEX,
                       geometric_vertices=u1,unordered_pairs=valid(u1,8)),
                       Rokicki=dict(url=ROKICKI,sample_id="sn8",word=TRANSITIONS,geometric_vertices=u2,
                       unordered_pairs=valid(u2,8)),Snakepits=dict(url=snakepit["url"],source=raw["source"],
                       file_sha256=snakepit["file_sha256"],sorted_endpoints=ends,path=sp,unordered_pairs=valid(sp,8),
                       maps_to_Carlson=maps),optimality=OPTIMAL),
        known_endpoints=known,classification=rows,by_length=Counter(len(r["path"])-1 for r in rows.values()))
    save(HERE/"input-arms.json",report)
    print("Input shapes by edge length",dict(report["by_length"]),"previous bounds",
          [(k,v["lower"],v["upper"]) for k,v in known.items()],flush=True)

if __name__=="__main__":main()
