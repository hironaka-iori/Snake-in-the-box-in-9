from collections import Counter
from pathlib import Path
from control_common import defects
import hashlib
import subprocess

root=Path(__file__).resolve().parent
src=Path("q9_onechord_expanded_800.txt")
assert hashlib.sha256(src.read_bytes()).hexdigest()=="c4f44d3483e28110b1f2bd499cd9613c8692fce6e7d99ade59d652e2fb31fc32"
rows=[list(map(int,line.split())) for line in src.read_text().splitlines()]
assert len(rows)==800
hist=Counter()
for p in rows:
    assert len(p)==193
    bad=defects(p)
    assert bad is not None and len(bad)==1
    hist[len(bad)]+=1
print("Checked all unordered vertex pairs in 800 walks of 193 vertices:",dict(hist))
for name in ["control","control_cross"]:
    out=subprocess.check_output(["python3",str(root/(name+".py"))],text=True)
    print(out.split("vertices")[0].strip())
for filename,expected in [
    ("target.log","DONE rows 800 permutations 269 transform_grid 110182400 passing_crossing_filter 25468532 closures 47067048"),
    ("cross.log","DONE trials 80000 translation_grid 40960000 passing_crossing_filter 19554336 closures 39108672"),
]:
    lines=(root/filename).read_text().splitlines()
    assert lines[-1]==expected and not any(row.startswith("FOUND") for row in lines)
    print(filename,lines[-1])

