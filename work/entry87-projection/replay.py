"""Regenerate and recheck the entry-87 clique with Lean 4.19.0."""
import argparse
import os
from pathlib import Path
import subprocess
import sys
import witnesses


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--lean",default="lean")
    args=ap.parse_args()
    root=Path(__file__).resolve().parent
    os.chdir(root)
    witnesses.main()
    env=os.environ.copy()
    env["LEAN_PATH"]=str(root)
    modules=["Clique","TraceData"]+[f"TraceRow{i}" for i in range(33)]+["Concrete"]
    for name in modules:
        subprocess.run([args.lean,"-j1","-s8192","-o",name+".olean",name+".lean"],
                       check=True,env=env)
    print(f"Accepted {len(modules)} modules, 528 concrete pair witnesses.",flush=True)


if __name__=="__main__":
    main()
