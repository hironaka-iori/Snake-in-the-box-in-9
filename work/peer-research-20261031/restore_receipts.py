from pathlib import Path
import gzip
root=Path(__file__).resolve().parent
for p in (root/"work/branch241-lean").glob("*remote*.json.gz"):
 target=p.with_suffix("")
 data=gzip.decompress(p.read_bytes())
 if target.exists() and target.read_bytes()!=data: raise RuntimeError("conflicting receipt: "+str(target))
 target.write_bytes(data)
print("Historical receipts restored; no Lean compiler was invoked.")
