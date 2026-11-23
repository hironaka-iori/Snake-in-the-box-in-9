"""Account for every line of the two sources relative to the previous full review."""
from collections import Counter
from difflib import SequenceMatcher
from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
BASE="5853c4d91"
prior=ROOT/"milestones/250-corner-partners/review/manuscripts.json"
def digest(b): return sha256(b).hexdigest()

if __name__=="__main__":
    result={}
    for name in ("snake9_research","snake9_frontier_explanation"):
        path="paper/"+name+".tex"
        old=subprocess.run(["git","show",BASE+":"+path],cwd=ROOT,capture_output=True,check=True).stdout
        new=(ROOT/path).read_bytes()
        checked=json.loads(prior.read_bytes())[name]["source_sha256"]
        if all(digest(x)!=checked for x in (old,old.replace(b"\r\n",b"\n"),old.replace(b"\r\n",b"\n").replace(b"\n",b"\r\n"))):
            raise ValueError("Baseline differs from the Round 250 source")
        a,b=old.decode("utf-8-sig").splitlines(),new.decode("utf-8-sig").splitlines()
        changes=[]
        same=0
        for op,i,j,k,l in SequenceMatcher(a=a,b=b,autojunk=False).get_opcodes():
            if op=="equal": same+=l-k
            else: changes.append(dict(operation=op,baseline_start=i,baseline_stop=j,reviewed_start=k,reviewed_stop=l))
        text="\n".join(b)
        labels=Counter(re.findall(r"\\label\{([^}]+)\}",text))
        bib=Counter(re.findall(r"\\bibitem(?:\[[^\]]+\])?\{([^}]+)\}",text))
        refs=set(re.findall(r"\\(?:eqref|pageref|autoref|ref)\{([^}]+)\}",text))
        cites={k.strip() for c in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}",text) for k in c.split(",")}
        if (refs-set(labels) or cites-set(bib) or max(labels.values(),default=0)>1 or max(bib.values(),default=0)>1):
            raise ValueError((name,"Unresolved or duplicate key",refs-set(labels),cites-set(bib)))
        result[name]=dict(baseline_raw_sha256=digest(old),baseline_review_sha256=checked,
            reviewed_sha256=digest(new),previous_lines=len(a),reviewed_lines=len(b),unchanged_lines=same,
            changed_or_added_lines=len(b)-same,reference_labels=len(labels),bibliography_keys=len(bib),
            changed_ranges_zero_based_half_open=changes)
    (HERE/"source-coverage.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
    for key,row in result.items(): print(key,row["unchanged_lines"],row["changed_or_added_lines"],row["reviewed_lines"])
