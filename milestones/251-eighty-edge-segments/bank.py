"""Construct best partners from contiguous subpaths of the 903 archived Q8 donors."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "249-long-parent-joins"))
from geometry import placements, permute
from direct98 import witness
from audit import verified_partner, path_ok


def library(donors, length):
    records = {}
    for i, path in enumerate(donors):
        for start in range(len(path)-length):
            segment = path[start:start+length+1]
            for rev, order in enumerate((segment, segment[::-1])):
                axes, p = {}, [0]
                for a, b in zip(order, order[1:]):
                    axis = axes.setdefault(a ^ b, len(axes))
                    p.append(p[-1] ^ (1 << axis))
                records.setdefault(bytes(p), (i, start, rev))
    words = list(records)
    # For each eight-vertex block and each forbidden subset, index which
    # oriented words hit it. Filtering these indices implements disjointness.
    hits = [0]*256
    for i, word in enumerate(words):
        for v in word[1:]:
            hits[v] |= 1 << i
    tables = []
    for b in range(0,256,8):
        table = [0]*256
        for mask in range(1,256):
            low = mask & -mask
            table[mask] = table[mask-low] | hits[b+low.bit_length()-1]
        tables.append(table)
    return words, records, tables


def first_fit(parent, words, records, tables):
    all_words = (1<<len(words))-1
    for forbidden, axes in placements(parent[1:]):
        remaining = all_words
        for table in tables:
            remaining &= ~table[forbidden & 255]
            if not remaining:
                break
            forbidden >>= 8
        if remaining:
            word = words[(remaining & -remaining).bit_length()-1]
            inverse = [axes.index(i) for i in range(8)]
            p = [permute(v,inverse) for v in word]
            result = witness(parent,p)
            verified_partner(parent,result,len(p)-1)
            return dict(donor_segment=records[word], parent_axes=list(axes), **result)
    return None


def main():
    source = HERE.parent/"246-eight-dimensional-parents"/"donors.json"
    census = HERE/"census-72.json"
    donors = [r["path"] for r in json.loads(source.read_bytes())["shapes"]]
    for p in donors:
        path_ok(p,8)
    roots = {}
    for r in json.loads(census.read_bytes())["new_shapes"]:
        for end, order in enumerate((r["path"],r["path"][::-1])):
            roots[r["id"],end] = [x^order[0] for x in order]
    found, widths = {}, {}
    for length in range(95,79,-1):
        words, records, tables = library(donors,length)
        widths[length] = len(words)
        for case,parent in roots.items():
            if case in found: continue
            result = first_fit(parent,words,records,tables)
            if result:
                found[case] = result
                print(case[0][:10],case[1],length,flush=True)
        if len(roots)==len(found): break
    result = dict(inputs={p.name:sha256(p.read_bytes()).hexdigest() for p in
                  (source,census,Path(__file__),HERE.parent/"249-long-parent-joins"/"geometry.py")},
                  donor_lengths=Counter(len(p)-1 for p in donors),oriented_classes=widths,
                  cases=[dict(id=k[0],end=k[1],**found.get(k,{"status":"no fit down to 80"})) for k in roots])
    (HERE/"bank.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")


if __name__=="__main__":
    main()
