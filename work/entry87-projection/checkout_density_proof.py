"""Export the files used by the density proof from immutable Git objects."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import verify_q9_density


def export(revision, destination):
    here = Path(__file__).resolve().parent
    root = here.parents[1]
    prefix = here.relative_to(root).as_posix()+"/"
    commit = subprocess.check_output(["git","-C",str(root),"rev-parse",revision+"^{commit}"],text=True).strip()
    destination.mkdir(parents=True,exist_ok=True)
    with subprocess.Popen(["git","-C",str(root),"cat-file","--batch"],stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE) as git:
        def blob(path):
            git.stdin.write((commit+":"+path+"\n").encode())
            git.stdin.flush()
            header = git.stdout.readline().decode().split()
            assert len(header) == 3 and header[1] == "blob", (path,header)
            raw = git.stdout.read(int(header[2]))
            assert git.stdout.read(1) == b"\n"
            assert hashlib.sha1(b"blob "+header[2].encode()+b"\0"+raw).hexdigest() == header[0]
            return raw
        needed = {"marked-seven-64.txt","seven-deletion-classes.json","dense-facet-audit.json",
                  "edge-window-117-104-all.json","edge-window-117-104-all.weights.gz",
                  "rich-46-classes-57.txt","rich-46-classes-58.txt",
                  "seven-face-classes-59.txt","seven-face-classes-60.txt","seven-face-classes-61.txt",
                  "near_full_faces.cpp","seven_face_classes.cpp"}
        modules = (Path(m.__file__).resolve() for m in list(sys.modules.values()) if getattr(m,"__file__",None))
        needed.update(f.name for f in modules if f.parent == here and f.suffix==".py")
        old = json.loads(blob(prefix+"dense-facet-audit.json"))
        for population,group in old.items():
            for r in group["records"]:
                needed.add(f"forest-role-weight-{population}-{r['index']}.json")
                if r["method"] == "resolution":
                    needed.update((r["receipt"],r["formula"],r["proof"]))
        window = json.loads(blob(prefix+"edge-window-117-104-all.json"))
        for name in window["resolution_receipts"]:
            needed.update((name,Path(name).stem+"-proof.core.gz"))
        paths = [verify_q9_density.BANK.relative_to(root).as_posix()]
        assert all(Path(f).name==f for f in needed)
        paths += [prefix+f for f in sorted(needed)]
        for path in paths:
            raw = blob(path)
            file = destination / path
            file.parent.mkdir(parents=True,exist_ok=True)
            if file.exists():
                assert file.read_bytes() == raw, file
            else:
                file.write_bytes(raw)
        git.stdin.close()
    assert git.returncode == 0
    print(commit,len(paths),destination/prefix,flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("revision")
    p.add_argument("destination",type=Path)
    a = p.parse_args()
    export(a.revision,a.destination.resolve())
