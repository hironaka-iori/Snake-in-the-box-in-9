"""Compile the authoritative and byte-identical paper sources under project resource limits."""
from pathlib import Path
from hashlib import sha256
import json
import shutil
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"242-seed-trade-construction"))
from guarded import wait_for_gate, compile_one, compile_receipt


def main():
    dest=Path(sys.argv[1]).resolve()
    compile_receipt.run=wait_for_gate
    for name in ("snake9_frontier_explanation","snake9_research"):
        result=compile_one(name)
        pdf=Path("D:/Codex/2026-10-13/new-chat/outputs")/(name+".pdf")
        shutil.copyfile(pdf,MS.parent/"paper/pdf"/pdf.name)
        (dest/(name+"-receipt.json")).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
        print(name,result["pages"],result["pdf_sha256"],flush=True)

if __name__=="__main__": main()
