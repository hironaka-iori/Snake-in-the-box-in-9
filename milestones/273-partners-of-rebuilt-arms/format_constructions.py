"""Export the two longest endpoint extensions as ordered arms in their original coordinates."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def read(name):return json.loads((HERE/name).read_bytes())

def signature(path):
    digits=[(u^v).bit_length()-1 for u,v in zip(path,path[1:])]
    def normalize(seq):
        names={v:i for i,v in enumerate(dict.fromkeys(seq))}
        return bytes(names[v] for v in seq)
    return min(normalize(digits),normalize(digits[::-1])).hex()

def main():
    growth=read("endpoint-growth.json")
    roots=read("opposite-constructions.json")["roots"]
    paths=[]
    for rows in growth["by_shape"].values():
        for row in rows:
            if row["max_edges"]!=growth["longest"]:continue
            q=row["joined"];cut=q.index(256)
            a=q[:cut][::-1];b=[v-256 for v in q[cut:]]
            assert a[:-1]==roots[row["root"]]["parent"] and q==a[::-1]+[256+v for v in b]
            sig=signature(q)
            paths.append(dict(source_96_root=row["root"],vertices_at_new_free_end=[q[0]],edges=len(q)-1,
              parent_edges=len(a)-1,partner_edges=len(b)-1,A=a,B=b,joined=q,shape=sig,
              unordered_pairs=len(q)*(len(q)-1)//2,archive_matches=growth["archive_matches"][sig]))
    paths.sort(key=lambda r:(bool(r["archive_matches"]),r["source_96_root"]))
    out=dict(constructions=paths,inequivalent=len({r["shape"] for r in paths})==len(paths),
             sources=["endpoint-growth.json","opposite-constructions.json"])
    (HERE/"extensions-188.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8",newline="\n")

if __name__=="__main__":main()
