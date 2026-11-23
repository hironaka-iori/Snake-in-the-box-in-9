from pathlib import Path
import json,subprocess,sys
from q9_rigid_ports_tree import export

def main():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    work=Path("q9_other_rigid_donors");work.mkdir(exist_ok=True)
    for idx,w in enumerate(bank):
        if idx in {43,44,464,472,576}:continue
        p=[0]
        for c in w:p.append(p[-1]^1<<int(c))
        if any(v not in p and all((v^u).bit_count()!=1 for u in p[1:-1]) for v in range(256)):continue
        cf=work/f"donor{idx}.jsonl"
        if not cf.exists():
            raw=subprocess.check_output([sys.executable,"-B","q9_rigid_facet_ports.py","9",str(idx)])
            cf.write_bytes(raw)
        for line in cf.read_text().splitlines():
            r=json.loads(line);tag=work/("d%d_m%d_p%s"%(idx,r["majority"],"-".join(map(str,r["ports"]))))
            log=tag.with_suffix(".log")
            if log.exists():continue
            export(r,tag.with_suffix(".tables"))
            cmd=["q9_facet_priced_tree_20261121/tree",str(tag),str(tag.with_suffix(".tree")),"193","160000"]
            text=subprocess.check_output(cmd,text=True)
            log.write_text(text);print(tag,text.strip(),flush=True)
            if " found 0 " not in text:return
if __name__=="__main__":main()
