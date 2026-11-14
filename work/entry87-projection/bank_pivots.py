"""Exhaust all single rooted pivots on the 180 one-chord candidates."""
from hashlib import sha256
from itertools import combinations
import csv,io,json,subprocess
from pathlib import Path
from solve import BANK,defects,save


def near_walks(path):
    for b in range(9):
        bit=1<<b
        # Shifted suffix interacts differently with the prefix only across the cut.
        change=[0]*193
        for i,x in enumerate(path):
            for j in range(i+1,192):
                if (x^path[j]^bit).bit_count()<=1:
                    change[i]+=1;change[j+1]-=1
        count=0
        for t in range(192):
            count+=change[t]
            if count!=1: continue
            q=path[:t+1]+[v^bit for v in path[t:]]
            ds=defects(q)
            if len(ds)==1 and ds[0][2]!=ds[0][3]:
                yield b,t,q,ds[0]


def canonical_word(q):
    sequence=[(a^b).bit_length()-1 for a,b in zip(q,q[1:])]
    def canon(seq):
        labels={}
        return tuple(labels.setdefault(x,len(labels)) for x in seq)
    return min(canon(sequence),canon(reversed(sequence)))


if __name__=="__main__":
    bank=json.loads(BANK.read_bytes())
    out=[];representatives={}
    path=Path("bank-pivots.json")
    for k,row in enumerate(bank):
        for b,t,q,chord in near_walks(row["vertex_sequence"]):
            key=canonical_word(q)
            if key in representatives:
                out.append(dict(entry=k,flip=b,insertion=t,chord=chord,representative=representatives[key]))
                continue
            idx=len(out);representatives[key]=idx
            proc=subprocess.run([str(Path("pivot.exe").resolve())],
                                input=" ".join(map(str,q)),text=True,capture_output=True,check=True)
            rows=list(csv.DictReader(io.StringIO(proc.stdout)))
            assert len(rows)==193
            eligible=[int(r["pivot"]) for r in rows if int(r["eligible"])]
            assert eligible==list(range(chord[0]+1,chord[1]))
            valid=[r for r in rows if int(r["valid"])]
            assert all(int(rows[i]["attempted"])==362880 for i in eligible)
            out.append(dict(entry=k,flip=b,insertion=t,chord=chord,representative=idx,
                            eligible=len(eligible),attempted=len(eligible)*362880,
                            witnesses=[[int(x) for x in r["first_witness"].split()] for r in valid]))
            if valid:
                assert all(not defects(w) for w in out[-1]["witnesses"])
                save(path,out)
                print("WITNESS",k,b,t,flush=True)
                raise SystemExit(0)
        save(path,out)
    assert len(out)==180
    print(len(out),len(representatives),sum(r.get("attempted",0) for r in out),flush=True)
