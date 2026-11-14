"""Close both complete two-window surveys and replay their residual rooted-path proofs."""
from collections import Counter
import gzip,json,re,subprocess
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile,ZIP_STORED
from layer_frontier import canonical
from resolve_layer_frontier import trial
from solve import defects,save


def run():
    surveys={};groups={};all_inputs=[]
    for widths in ((14,14),(10,16)):
        counts=Counter();indices=set()
        for f in sorted(Path().glob("two-layer-windows-*.json")):
            r=json.loads(f.read_text())
            if (r["width"],r.get("second_width",r["width"]))!=widths:continue
            key=(r["source"],r["orientation"]);assert key not in indices;indices.add(key)
            all_inputs.append(f.name)
            assert r["selected"]==r["capacity_survivors"] and r["excluded_selected"]+len(r["open_cases"])==r["selected"]
            for k in ("window_pairs","candidates","capacity_survivors","excluded_selected"):counts[k]+=r[k]
            counts["unresolved_occurrences"]+=len(r["open_cases"])
            for z in r["open_cases"]:
                a,c=canonical(r["first"],z["third"]);g=groups.get((a,c))
                if g is None:
                    free=set(range(128))-set(a)-set(c)
                    g=dict(first=a,third=c,middle_domain=sorted(free|{a[-1],c[0]}),final_domain=sorted(free|{c[-1]}),
                           occurrences=[],**{k:z[k] for k in ("required_sum","middle_lower","middle_upper","last_lower","last_upper")})
                    groups[a,c]=g
                g["occurrences"].append([*widths,*key])
                for k in ("middle_upper","last_upper"):g[k]=min(g[k],z[k])
        assert indices=={(i,o) for i in range(15) for o in (0,1)}
        surveys[str(widths)]=counts
    checker=Path("drat-check.exe").resolve();res=[];proofs={}
    for i,g in enumerate(groups.values(),3000):
        result=trial(i,g,180000,checker);res.append(dict(anchors=g,decision=result))
        if result["status"]!="EXHAUSTED":continue
        cap=g["last_upper"];ruled=set();a=g["first"];c=g["third"]
        for split in result["splits"]:
            for name,size in (("middle",split["middle_size"]),("last",split["last_size"])):
                if name not in split:continue
                r=split[name];tag="final" if name=="last" else name
                if r["status"]=="FOUND":
                    q=r["path"];assert len(q)==size and not defects(q) and set(q)<=set(g[tag+"_domain"])
                    assert q[0]==(c[-1] if name=="last" else a[-1]) and (name=="last" or q[-1]==c[0])
                else:
                    assert r["status"]=="UNSAT" and not r["cuts"]
                    proofs[f"free-last-proof-frontier-{i}-{tag}-{size}"]=r
                    if name=="last":cap=min(cap,size-1)
                    else:ruled.add(size)
        assert all(b in ruled for b in range(g["required_sum"]-cap,g["middle_upper"]+1)
                   if (b-1)%2==(a[-1]^c[0]).bit_count()%2)
    archive=Path("two-window-certificates.zip");steps=0
    with ZipFile(archive,"w",ZIP_STORED) as z:
        for prefix in sorted(proofs):
            for tag in ("cnf","core"):
                name=prefix+"."+tag+".gz";z.write(name,name)
    with ZipFile(archive) as z,TemporaryDirectory() as tmp:
        for prefix,r in proofs.items():
            cmd=[str(checker)]
            for tag in ("cnf","core"):
                raw=gzip.decompress(z.read(prefix+"."+tag+".gz"));assert sha256(raw).hexdigest()==r[tag+"_sha256"]
                dest=Path(tmp)/tag;dest.write_bytes(raw);cmd.append(str(dest))
            replay=subprocess.run(cmd,capture_output=True,check=True).stdout
            assert b"s VERIFIED" in replay.splitlines();steps+=int(re.search(rb"using (\d+) resolution steps",replay).group(1))
    report=dict(surveys=surveys,inputs=all_inputs,distinct=len(groups),results=res,proofs=len(proofs),steps=steps,
                archive_sha256=sha256(archive.read_bytes()).hexdigest())
    save(Path("two-window-campaign.json"),report)
    print(surveys,len(res),Counter(x["decision"]["status"] for x in res),len(proofs),steps,flush=True)


if __name__=="__main__":run()
