"""Validate every logged witness directly, then rederive it from the declared part of its Q10 source."""
from pathlib import Path
import json
root=Path(__file__).resolve().parent
sources=[list(map(int,l.split()))[1:] for l in (root/'external_q10.steps').read_text().splitlines()]
control=list(map(int,(root/'control.steps').read_text().split()))[1:]
def points(steps):
    path=[0]
    for k in steps:
        if k is not None:path.append(path[-1]^(1<<k))
    return path
def verify(path,dim):
    assert len(path)==len(set(path)) and all(0<=x<1<<dim for x in path)
    for j,v in enumerate(path):
        for i in range(j):
            assert ((v^path[i]).bit_count()==1)==(i+1==j)
def can(w):
    def n(seq):
        labels={}
        return ''.join(str(labels.setdefault(x,len(labels))) for x in seq)
    return min(n(w),n(w[::-1]))
old=(root.parent/'q9_reordered_segments_20261120/reference191.words').read_text().split()
trims={can(t) for w in old for t in (w[1:],w[:-1])}
for s in sources+[control]:verify(points(s),10)
assert len(set(control))==10
report={'external_Q10_rows':len(sources),'unique_lengths':sorted(set(map(len,sources))),'control_min_axis_frequency':min(control.count(i) for i in range(10)),'runs':{}}
for name in ['control','single','back','alias','alias_back','alias_all_intervals','delete_all_intervals']:
    lines=(root/(name+'.log')).read_text().splitlines()
    assert lines[-1].startswith('DONE')
    for line in lines[:-1]:
        head,raw=line.split(' vertices ')
        _,length,_,row,_,h,_,j,_,a,b,_,end=head.split()
        length,row,h,j,a,b,end=map(int,(length,row,h,j,a,b,end)); w=list(map(int,raw.split()))
        assert len(w)==length+1
        verify(w,9)
        source=control if name=='control' else sources[row]
        orig=[None if q==h else q-(q>h) for q in range(10)]
        alt=orig[:]
        if name.startswith('alias'):
            first,second=divmod(j,10);orig[h]=orig[first];alt[h]=alt[second]
        else:
            alt[h],alt[j]=alt[j],alt[h]
        result=points((alt if a<=i<b else orig)[v] for i,v in enumerate(source[:end+1]))
        assert result[-len(w):]==w
    moves=''.join(str((x^y).bit_length()-1) for x,y in zip(w,w[1:]))
    report['runs'][name]={'max_edges':length,'matches_reference_or_its_190_trim':can(moves) in (set(old) if length==191 else trims),'stats':lines[-1]}
print(json.dumps(report,indent=2))
