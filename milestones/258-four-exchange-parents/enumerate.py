"""Compare the spanning-cycle solver against spanning orders on every surviving 48-set."""
from collections import defaultdict
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"256-two-exchange-parents"))
from enumerate_shell import read, check_path, digest, search, word
from replay_exchange import CSC


def examine(label, exe, radius, folder):
    reference_file=MS/"256-two-exchange-parents"/("shell-"+label+".json")
    reference=read(reference_file)["reference"]
    base=set(reference[1::2])
    output=subprocess.run([str(exe),str(radius)],input=",".join(map(str,sorted(base)))+"\n",
                          text=True,capture_output=True,check=True)
    positive=[]
    shapes={}
    active=None
    expected_index=0
    transcript=sha256()
    coverage=None
    for line in output.stdout.splitlines():
        action,*args=line.split()
        if action=="C":
            index=int(args[0])
            if index!=expected_index or active is not None: raise ValueError("Unexpected candidate index")
            removed,added=(tuple(map(int,a.split(","))) for a in args[1:])
            if (len(set(removed))!=radius or len(set(added))!=radius or not set(removed)<=base
                or set(added)&base or any((y^reference[1]).bit_count()%2 for y in added)):
                raise ValueError("Exchange does not have the stated distance")
            active=(removed,added)
            transcript.update(bytes((*removed,*added)))
            supplied=[]
        elif action=="P":
            path=tuple(map(int,args[2].split(",")))
            check_path(path)
            if active is None or int(args[0])!=expected_index or len(path)!=97 or set(path[1::2])!=(base-set(removed))|set(added):
                raise ValueError("Invalid completion")
            supplied.append(min(path,path[::-1]))
        elif action=="S":
            if active is None or int(args[0])!=expected_index or int(args[-1])!=len(supplied):
                raise ValueError("Invalid cycle census")
            direct,_=search(sorted((base-set(removed))|set(added)))
            if sorted(supplied)!=sorted(direct): raise ValueError("Spanning orders and cycles disagree")
            if supplied:
                records=[]
                for path in sorted(supplied):
                    key=sha256(word(path)).hexdigest()
                    shapes.setdefault(key,path)
                    records.append(dict(shape=key,vertices=path))
                positive.append(dict(removed=removed,inserted=added,paths=records))
            active=None
            expected_index+=1
        elif action=="T": coverage=tuple(map(int,args))
        else: raise ValueError(action)
    if active is not None or coverage!=(comb(48,radius),expected_index): raise ValueError("Partial census")
    result=dict(reference=reference,reference_shape=sha256(word(reference)).hexdigest(),label=label,radius=radius,
                removed_subsets=coverage[0],candidate_sets=comb(48,radius)*comb(80,radius),
                supply_survivors=expected_index,survivor_digest=transcript.hexdigest(),positive_classes=positive,
                labelled_arms=sum(len(r["paths"]) for r in positive),shapes=shapes,
                pins={str(f.relative_to(MS)):digest(f) for f in [reference_file,Path(__file__),
                  MS/"256-two-exchange-parents/EnumerateExchanges.cs",MS/"255-parity-exchange-arms/replay_exchange.cs",
                  MS/"255-parity-exchange-arms/enumerate_arms.py"]})
    (folder/("shell-"+label+".json")).write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print(label,"supply",expected_index,"classes",len(positive),"paths",result["labelled_arms"],"shapes",len(shapes),flush=True)


if __name__=="__main__":
    folder=Path(sys.argv[1]).resolve()
    radius=int(sys.argv[2])
    with TemporaryDirectory() as tmp:
        exe=Path(tmp)/"enumerate.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/main:EnumerateExchanges","/out:"+str(exe),
                        str(MS/"255-parity-exchange-arms/replay_exchange.cs"),str(MS/"256-two-exchange-parents/EnumerateExchanges.cs")],
                       capture_output=True,check=True)
        for label in sys.argv[3:]: examine(label,exe,radius,folder)
