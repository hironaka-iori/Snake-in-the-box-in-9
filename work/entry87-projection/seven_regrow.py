"""Independently check every regenerated Q7 path and make the new shapes usable in layer searches."""
import argparse,json,subprocess
from pathlib import Path
from four_layer_bank import menus
from solve import defects,save


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("size",type=int);p.add_argument("trim",type=int)
    p.add_argument("--bank",type=Path,default=Path("highdim-seven-39.json"))
    p.add_argument("--classes",type=int,default=100000);p.add_argument("--nodes",type=int,default=250000000)
    a=p.parse_args();forms={s.encode():v for s,v in json.loads(a.bank.read_text())["forms"].items()}
    seeds=menus(forms,a.size)
    cmd=[str(Path("seven-regrow.exe").resolve()),str(a.size),str(a.trim),str(a.classes),str(a.nodes)]
    proc=subprocess.run(cmd,input=b"\n".join(seeds),capture_output=True,check=True)
    first,*words=proc.stdout.decode().splitlines();status,old,total,nroots,nodes=first.split()
    assert len(set(words))==len(words)==int(total) and int(old)>0
    for s in words:
        q=[0]
        for c in s:q.append(q[-1]^(1<<int(c)))
        assert len(q)==a.size and max(q)<128 and not defects(q)
    save(Path(f"seven-regrow-{a.size}-{a.trim}-{a.nodes}.json"),dict(status=status,size=a.size,trim=a.trim,
         input=a.bank.name,old=int(old),count=int(total),roots=int(nroots),nodes=int(nodes),forms=dict.fromkeys(words,"verified")))
    print(status,old,total,nroots,nodes,flush=True)
