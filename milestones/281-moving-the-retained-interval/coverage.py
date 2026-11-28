"""Transfer each checked interval to the two archives by literal cube isometries."""
from collections import Counter
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from windows import BASE, HERE, PREV, compile_worker, native, prefix_hits, save, shape
sys.path.insert(0,str(BASE))
from archive import input_paths
from overlap import literal_isometry, transitions, normal
from interval import rebuild
audit_spec=spec_from_file_location('interval_audit280',PREV/'audit.py')
interval_audit=module_from_spec(audit_spec)
audit_spec.loader.exec_module(interval_audit)


def verified():
    known=prefix_hits()
    windows=json.loads((HERE/'windows.json').read_bytes())
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        verifier,_=rebuild.masks.compilers(scratch)
        workers={n:compile_worker(BASE/(n+'.cs'),scratch) for n in ('Target','TargetReplay')}
        for r in windows.values():
            if r['status']!='excluded':
                continue
            core=r['core']
            if r['method']=='two independent native searches':
                for name,exe in workers.items():
                    old=r['native'][name]
                    assert native(exe,core,scratch,old['budget'])==old
                    assert old['status']=='excluded'
            else:
                assert set(r['cases'])=={'0','1'}
                for row in r['cases'].values():
                    assert row['status']=='excluded'
                    interval_audit.replay_case(core,row,HERE,scratch,verifier)
            known[shape(core)]=core
    return known


def main():
    known=verified()
    lookup={}
    for key,core in known.items():
        lookup.setdefault(len(key),{})[key]=(sha256(key).hexdigest(),core)
    previous=json.loads((BASE/'consecutive-overlap.json').read_bytes())['paths']
    results={}
    stats={190:Counter(),191:Counter()}
    for label,p in input_paths():
        word=transitions(p)
        n=len(word)
        matches=[]
        for length,entries in lookup.items():
            for i in range(n-length+1):
                w=word[i:i+length]
                match=entries.get(min(normal(w),normal(w[::-1])))
                if match:
                    ident,core=match
                    assert literal_isometry(core,p[i:i+length+1])
                    matches.append([i,i+length,ident])
        old=previous[label]
        # For a start i, the earliest end of any forbidden interval with start >=i
        # is the first forbidden endpoint. Recompute all window positions.
        earliest=[n+1]*(n+1)
        for lo,hi,*_ in old['cover']+matches:
            earliest[lo]=min(earliest[lo],hi)
        first=n+1
        bound=-1
        example=None
        for i in reversed(range(n+1)):
            first=min(first,earliest[i])
            if first-1-i>bound:
                bound=first-1-i
                example=[i,first-1]
        assert bound<=old['bound']
        results[label]=dict(old=old['bound'],upper=bound,longest_unsettled=example,matches=matches)
        stats[n][bound]+=1
    result=dict(certificate_shapes=len(known),improved={n:sum(r['upper']<r['old'] for k,r in results.items()
                if k.startswith(str(n)+'-')) for n in stats},bound_histograms=stats,paths=results)
    save(HERE/'coverage.json',result)
    print('Seed maximum possible overlap',results['191-0']['upper'],'improved',result['improved'],
          'archive ceilings',{n:max(c) for n,c in stats.items()})


if __name__=='__main__':
    main()
