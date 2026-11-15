"""Check both placements of each middle against a long-arm catalogue, with a free short arm."""
import argparse,json,subprocess
from pathlib import Path
from punctured_lift import project
from two_eight_layers import decode
from solve import BANK,BANK_HASH,sha256,defects,save
from bank_pivots import canonical_word

def labels(seq):
    m={};return bytes(48+m.setdefault(x,len(m)) for x in seq)

def long_words(expanded,minimum):
    forms=json.loads(Path("eight-face-catalogue.json").read_bytes())["forms"]
    if expanded:
        for f in sorted(Path(".").glob("eight-regrow-*-160000000.json")):forms.update(json.loads(f.read_bytes())["forms"])
    rooted=set()
    for s in forms:
        q=s.encode()
        for word in (q,q[::-1]):
            for i in range(len(word)-minimum+2):rooted.add(labels(word[i:]))
    return sorted(rooted)

def run(middles,words,minimum,cap,target):
    lines=[f"{len(middles)} {len(words)} {minimum} {cap} {target}".encode()]
    for q in middles:lines.append(" ".join(map(str,[len(q),*q])).encode())
    proc=subprocess.run([str(Path("middle-long-arm.exe").resolve())],input=b"\n".join(lines+words),capture_output=True,check=True)
    out=[];trie=int(proc.stderr.split()[1])
    for line in proc.stdout.splitlines():
        tag,*nums=line.split();ns=list(map(int,nums));i=ns[0]
        if tag==b"done":out.append(dict(index=i,status="EXHAUSTED",states=ns[1],placements=ns[2],short_states=ns[3]));continue
        assert tag==b"found";side,l=ns[1:3];A=ns[3:3+l];z=ns[3+l];B=ns[4+l:];assert len(B)==z
        M=middles[i][::-1] if side else middles[i];q=A[::-1]+[v|256 for v in M]+B
        assert len(q)==target and not defects(q)
        out.append(dict(index=i,status="FOUND",vertices=q))
    assert len(out)==len(middles) or out[-1]["status"]=="FOUND"
    return dict(trie=trie,words=len(words),rows=out)

def known_control():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    for r in json.loads(raw):
        for j in range(9):
            P,sw=project(r["vertex_sequence"],j)
            if len(sw)!=2:continue
            a,b=sw;A=P[:a+1][::-1];B=P[b:];M=P[a:b+1]
            if sorted([len(A),len(B)])==[2,94]:
                long=max((A,B),key=len);w=labels([(x^y).bit_length()-1 for x,y in zip(long,long[1:])])
                z=run([M],[w],94,2,192);assert z["rows"][0]["status"]=="FOUND";return z
    raise AssertionError("missing 94+2 control")

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--expanded",action="store_true");p.add_argument("--minimum",type=int,default=84)
    p.add_argument("--size",type=int,default=96);p.add_argument("--catalogue-min",type=int)
    p.add_argument("--target",type=int,choices=(192,193),default=193);p.add_argument("--skip-registered",action="store_true")
    a=p.parse_args();ctrl=known_control()
    banks={96:"96-32",95:"95-29",94:"94-24",97:"97-37"}
    forms=json.loads(Path(f"eight-regrow-{banks[a.size]}-160000000.json").read_bytes())["forms"]
    ms=[];indices=[];registered={canonical_word(r["parent"]) for r in json.loads(Path("double-cross-bank.json").read_bytes())}
    for i,s in enumerate(sorted(forms)[a.first:a.stop],a.first):
        q=decode(s.encode())
        if a.skip_registered and canonical_word(q) in registered:continue
        ms.append(q);indices.append(i)
    words=long_words(a.expanded,a.catalogue_min or a.minimum)
    ans=run(ms,words,a.minimum,a.target-a.size-a.minimum,a.target)
    if a.target==192 and a.skip_registered:
        bank={canonical_word(r["vertex_sequence"]) for r in json.loads(BANK.read_bytes())}
        for r in ans["rows"]:
            if r.get("vertices"):assert canonical_word(r["vertices"]) not in bank
    ext=(f"-menu{a.catalogue_min}" if a.catalogue_min else "")+(f"-target{a.target}" if a.target!=193 else "")+("-new" if a.skip_registered else "")
    name=f"middle-long-arm-{a.size}-{a.first}-{a.stop}-{a.minimum}-{int(a.expanded)}{ext}.json"
    save(Path(name),dict(first=a.first,indices=indices,control=ctrl,**ans));print(name,len(ms),ans["trie"],ans["rows"][-1]["status"],flush=True)
