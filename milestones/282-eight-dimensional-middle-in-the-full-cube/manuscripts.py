"""Compile the two authoritative papers and record hashes of their repository mirrors."""
from hashlib import sha256
import json
from pathlib import Path
import shutil
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(next(HERE.parent.glob('242-*'))))
from guarded import compile_one,compile_receipt,wait_for_gate


def main():
    name=sys.argv[1]
    assert name in ('snake9_research','snake9_frontier_explanation')
    compile_receipt.run=wait_for_gate
    receipt=compile_one(name)
    src=Path('D:/Codex/2026-10-13/new-chat/outputs')/(name+'.pdf')
    mirror=ROOT/'paper/pdf'/src.name
    shutil.copyfile(src,mirror)
    assert sha256(mirror.read_bytes()).hexdigest()==receipt['pdf_sha256']
    (HERE/(name+'-receipt.json')).write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
    file=HERE/'manuscripts.json'
    manifest=json.loads(file.read_bytes()) if file.exists() else {}
    manifest[name]={key:receipt[key] for key in ('pages','source_sha256','pdf_sha256','references_settled')}
    file.write_bytes((json.dumps(manifest,indent=2)+'\n').encode())
    print(name,receipt['pages'],'pages, settled references, matching source and PDF.')


if __name__=='__main__':
    main()
