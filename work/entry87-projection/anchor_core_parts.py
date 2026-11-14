"""Reassemble and optionally replay the six-substitution proofs for entry 87."""
import argparse,json
from pathlib import Path
from parent_core_parts import check,split

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("side",choices=("majority","minority"))
    p.add_argument("--split",action="store_true");p.add_argument("--checker",type=Path);a=p.parse_args()
    short=a.side=="minority";prefix=Path(f"anchor-radius-proof-118-6-9-{int(short)}")
    receipt=json.loads(Path("anchor-radius-6-9-118-119-2500000"+("-short" if short else "")+"-checked.json").read_bytes())[0]
    if a.split:split(prefix,receipt)
    check(prefix,receipt,a.checker.resolve() if a.checker else None)
