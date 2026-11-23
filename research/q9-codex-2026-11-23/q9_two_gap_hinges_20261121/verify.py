from pathlib import Path
import hashlib
import subprocess
root=Path(__file__).resolve().parent
def unpack(w):
    p=[0]
    for s in w:
        assert '0'<=s<='8'
        p.append(p[-1]^(1<<int(s)))
    return p
def defects(p):
    assert len(set(p))==len(p) and all(0<=v<512 for v in p)
    assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
    return [(i,j) for i,x in enumerate(p) for j in range(i+2,len(p)) if (x^p[j]).bit_count()==1]
def key(p):
    def word(s):
        m={}
        return ''.join(str(m.setdefault(a^b,len(m))) for a,b in zip(s,s[1:]))
    return min(word(p),word(p[::-1]))
def read_path(line):return list(map(int,line.split('vertices ')[1].split()))
source=Path("q9_new189_nearmisses.words")
words=[line.split()[1] for line in source.read_text().splitlines() if line.split()[0]=='2']
assert len(words)==34 and all(len(w)==192 and len(defects(unpack(w)))==2 for w in words)
print("34 independently verified labelled two-chord, 192-edge inputs; distinct unsigned coordinate/reversal classes",len({key(unpack(w)) for w in words}),"input SHA256",hashlib.sha256(source.read_bytes()).hexdigest())
bank=Path('q9_reordered_segments_20261120/reference191.words').read_text().splitlines()
known={key(unpack(w)) for w in bank}
cp=unpack(subprocess.check_output(['python3',str(root/'damaged_control.py')],text=True).split()[1])
out=read_path((root/'control.log').read_text())
assert len(out)==192 and len(defects(cp))==2 and defects(out)==[] and cp[9:183]==out[9:183]
print("Independent original-index control check: both injected chords, clean repaired 191-edge path, unchanged central vertices 9 through 182.")
cs=(root/'tip_control.log').read_text().splitlines()
cw=[read_path(row) for row in cs if row.startswith("CLASS191")]
assert all(len(w)==192 and not defects(w) for w in cw) and key(unpack(bank[0])) in {key(w) for w in cw}
print("Independent tip control: recovered reference 191-edge class.")
for name in ('target','tip'):
    log=(root/(name+'.log')).read_text().splitlines()
    winners=[read_path(row) for row in log if row.startswith('FOUND')]
    assert all(len(w)>=193 and not defects(w) for w in winners)
    assert any(row.startswith('DONE') for row in log) or winners
    paths=[read_path(row) for row in log if row.startswith('CLASS191')]
    assert all(len(w)==192 and not defects(w) for w in paths)
    keys={key(w) for w in paths}
    assert len(keys)==len(paths)
    print(name,"target witnesses",len(winners),"verified classes at 191",len(keys),"absent from reference bank",len(keys-known))
    for row in log:
        if row.startswith(('TIPS','DONE')):print(row)

