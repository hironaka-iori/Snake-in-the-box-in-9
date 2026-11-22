"""Compile the abstract exchange-chain argument under the saved Lean limits."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import re
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0, str(MS/"242-seed-trade-construction"))
from guarded import compile_receipt as build, memory_limit, wait_for_gate

prior = json.loads((MS/"257-three-exchange-parents/Supply257-compile.json").read_bytes())
compiler = Path(prior["compiler"])
source = HERE/"Bridges259.lean"
if build.digest(compiler) != prior["compiler_sha256"]: raise ValueError("Lean compiler changed")
memory_limit(256)
with TemporaryDirectory() as tmp:
    log = Path(tmp)/"lean.log"
    obj = Path(tmp)/"Bridges259.olean"
    args = ["-j","1","-s","8192","-o",str(obj),source.name]
    result = wait_for_gate([str(compiler),*args],HERE,log,60)
    output = log.read_text(encoding="utf-8")
    entries = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",output)
    if (len(entries)!=3 or any(set(re.findall(r"[\w.]+",names))-{"propext","Quot.sound","Classical.choice"}
        for _,names in entries) or "warning:" in output or "sorryAx" in output):
        raise ValueError(output)
    data = dict(compiler=str(compiler),compiler_sha256=build.digest(compiler),source_sha256=build.digest(source),
                object_sha256=build.digest(obj),compiler_output=output,execution=result)
    (HERE/"Bridges259-compile.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(output)
