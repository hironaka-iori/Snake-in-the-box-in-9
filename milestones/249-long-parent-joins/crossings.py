"""Calculate and independently verify the admissible cuts of archived projected paths."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import csv
import json
import zipfile

from joins import HERE, partner, save_json
from placements import shape


def project(v, axis):
    return (v & ((1<<axis)-1)) | ((v>>(axis+1))<<axis)


def cut_interval(word):
    pos = {v:i for i,v in enumerate(word)}
    if len(pos)!=len(word) or any((a^b).bit_count()!=1 for a,b in zip(word,word[1:])):
        raise ValueError("A simple projected word is required")
    chords = [(i,pos[n]) for i,v in enumerate(word) for n in partner.NEIGHBOURS[v]
              if pos.get(n,-1)>i+1]
    left = max((i+1 for i,_ in chords),default=0)
    right = min((j-1 for _,j in chords),default=len(word)-1)
    return left,right,len(chords)


def longest_prefix(word):
    used = set()
    for i,v in enumerate(word):
        if v in used or sum((v^u).bit_count()==1 for u in used)!=(i>0):
            return i-1
        used.add(v)
    return len(word)-1


def main():
    root = HERE.parents[1]
    bank = root/"work/bank9.json"
    archive = root/"work/record_snakes.csv.zip"
    with zipfile.ZipFile(archive) as source:
        raw = source.read("snakes_dim9_190.csv")
    digest = sha256(raw).hexdigest()
    old = HERE.parent/"244-190-path-construction/results.json"
    if digest!=json.loads(old.read_bytes())["member_sha256"]:
        raise ValueError("Archived 190-edge source changed")
    banks = {191:[r["vertex_sequence"] for r in json.loads(bank.read_bytes())],
             190:[list(map(int,r["vertices"].split())) for r in csv.DictReader(raw.decode().splitlines())]}
    donor_file = partner.PREV/"donors.json"
    donors = {shape(r["path"]):i for i,r in enumerate(json.loads(donor_file.read_bytes())["shapes"])}
    records, summaries = [], {}
    bank191 = {shape(p):i for i,p in enumerate(banks[191])}
    for length, paths in banks.items():
        known = {shape(p) for p in paths}
        family, results, additions = set(), set(), set()
        counts = Counter()
        for index,path in enumerate(paths):
            moves = [a^b for a,b in zip(path,path[1:])]
            for axis in range(9):
                if moves.count(1<<axis)!=1:
                    continue
                partner.verify(path,9)
                k = moves.index(1<<axis)
                word = [project(v,axis) for v in path[:k+1]+path[k+2:]]
                left,right,chords = cut_interval(word)
                if (left,right)!=(len(word)-1-longest_prefix(word[::-1]),longest_prefix(word)):
                    raise ValueError("Direct induced-arm lengths disagree with the chord calculation")
                if not left<=k<=right:
                    raise ValueError("Input lift is outside the calculated interval")
                cuts = []
                for cut in range(left,right+1):
                    arm1,arm2 = word[:cut+1],word[cut:]
                    joined = arm1+[v+256 for v in arm2]
                    partner.verify(joined,9)
                    signature = shape(joined)
                    if cut==k and signature!=shape(path):
                        raise ValueError("Original placement was lost")
                    results.add(signature)
                    long = max((arm1,arm2),key=len)
                    cuts.append(dict(cut=cut,donor=donors.get(shape(long)),in_bank=signature in known))
                extended = []
                for end,endpoint in enumerate((word[0],word[-1])):
                    for v in partner.NEIGHBOURS[endpoint]:
                        if v in word:
                            continue
                        trial = [v]+word if end==0 else word+[v]
                        lo,hi,_ = cut_interval(trial)
                        for cut in range(lo,hi+1):
                            lift = trial[:cut+1]+[a+256 for a in trial[cut:]]
                            partner.verify(lift,9)
                            additions.add(shape(lift))
                            extended.append(dict(end=end,vertex=v,cut=cut,joined=lift))
                family.add(shape(word))
                counts[right-left+1] += 1
                records.append(dict(length=length,seed=index,axis=axis,original_cut=k,
                                    interval=[left,right],chords=chords,cuts=cuts,extensions=extended))
        covered = [r for r in records if r["length"]==length]
        summaries[length] = dict(bank=len(paths),projections=sum(counts.values()),widths=counts,
            word_classes=len(family),lift_classes=len(results),lift_classes_outside_bank=len(results-known),
            projections_with_extension=sum(bool(r["extensions"]) for r in covered),
            labelled_extensions=sum(len(r["extensions"]) for r in covered),
            one_edge_longer_classes=len(additions),
            extension_bank191_ids=sorted(bank191[x] for x in additions if x in bank191))
    save_json(HERE/"crossings.json",dict(source_sha256=partner.digest(Path(__file__)),bank_sha256=partner.digest(bank),
              donor_sha256=partner.digest(donor_file),member190_sha256=digest,summary=summaries,records=records))
    print(json.dumps(summaries),flush=True)


if __name__=="__main__":
    main()
