"""Compile the generic neighbour-supply implications with the project's pinned Lean compiler."""
from pathlib import Path
import json
import os
import re
import shutil
import sys
from tempfile import TemporaryDirectory

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"242-seed-trade-construction"))
from guarded import compile_receipt as build, memory_limit, wait_for_gate

def main():
    prior=json.loads((MS/"255-parity-exchange-arms/Subpath255-compile.json").read_bytes())
    compiler=Path(prior["compiler"])
    base=MS/"188-dimensional-constructions/lean/LayerJoining.lean"
    if build.digest(compiler)!=prior["compiler_sha256"] or build.digest(base)!=prior["modules"][0]["source_sha256"]:
        raise ValueError("Inherited inputs differ")
    memory_limit(256)
    steps=[]
    with TemporaryDirectory(prefix="snake257-lean-") as folder:
        tmp=Path(folder)
        os.environ["LEAN_PATH"]=folder
        for src in (base,HERE/"Supply257.lean"):
            shutil.copyfile(src,tmp/src.name)
            log=tmp/"compiler.log"
            args=["-j","1","-s","8192","-o",src.stem+".olean",src.name]
            result=wait_for_gate([str(compiler),*args],tmp,log,60)
            output=log.read_text(encoding="utf-8")
            if "sorryAx" in output or "warning:" in output or "error:" in output: raise ValueError(output)
            if src.stem=="Supply257":
                reports=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",output)
                if [s for s,_ in reports]!=["Supply257.degree_two","Supply257.insertion_supply"] or any(
                    set(re.findall(r"[\w.]+",a))-{"propext","Quot.sound","Classical.choice"} for _,a in reports):
                    raise ValueError(output)
            steps.append(dict(module=src.name,source_sha256=build.digest(src),arguments=args,
                              object_sha256=build.digest(tmp/(src.stem+".olean")),compiler_output=output,execution=result))
    (HERE/"Supply257-compile.json").write_text(json.dumps(dict(compiler=str(compiler),
            compiler_sha256=build.digest(compiler),modules=steps),indent=2)+"\n",encoding="utf-8",newline="\n")
    print(steps[-1]["compiler_output"])

if __name__=="__main__": main()
