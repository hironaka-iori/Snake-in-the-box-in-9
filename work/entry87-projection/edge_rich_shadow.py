"""Check edge-rich seven-face censuses by counting one-vertex extensions in two ways."""
import argparse
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from dense_rigidity import next_sites
from solve import save


def rows(n):
    file=Path(f"seven-face-classes-{n}.txt")
    if not file.exists():
        file=Path(f"rich-46-classes-{n}.txt")
    for line in file.read_text().splitlines():
        a,b,c,w,s=map(int,line.split())
        if n-c>=46:
            assert w*s==645120
            yield a|(b<<64),n-c,w,s


def compare(n,binary):
    with TemporaryDirectory() as tmp:
        source=Path(tmp)/"deletions.txt"
        output=Path(tmp)/"canonical.txt"
        with source.open("w") as stream:
            for mask,edges,weight,_ in rows(n+1):
                for v in range(128):
                    if not mask>>v&1:
                        continue
                    lost=sum((mask>>(v^(1<<j)))&1 for j in range(7))
                    if edges-lost<46:
                        continue
                    child=mask^(1<<v)
                    print(child%2**64,child>>64,n-(edges-lost),weight,file=stream)
        subprocess.run([str(binary),str(source),str(output),"--incidences"],check=True)
        counts={}
        for line in output.read_text().splitlines():
            a,b,c,w,s=map(int,line.split())
            counts[a|(b<<64)]=w
    total=0;maximal=0;maximal_labels=0;classes=0
    for mask,edges,weight,stab in rows(n):
        vertices={v for v in range(128) if mask>>v&1}
        extensions=len(next_sites(vertices))
        incidence=weight*extensions
        assert counts.pop(mask,0)==incidence
        classes+=1;total+=incidence
        if not extensions:
            maximal+=1;maximal_labels+=weight
    assert not counts
    return dict(classes=classes,maximal_classes=maximal,maximal_labelled=maximal_labels,
                labelled_extension_pairs=total)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("canonicalizer",type=Path)
    a=p.parse_args()
    data={n:compare(n,a.canonicalizer.resolve()) for n in range(57,61)}
    save(Path("edge-rich-extension-audit.json"),data)
    print(data)
