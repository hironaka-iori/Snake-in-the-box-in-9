import itertools,json,sys
from collections import Counter
from pathlib import Path
from prepare import D,R,words,graph,parts,majority,NB
from solve import solve,valid
rngdata=list(map(json.loads,(D/'jobs.jsonl').read_text().splitlines()))
def analyze(A,C):
    adj=graph(A);groups=parts(adj,C);leaves={v for v in A if len(adj[v])==1}
    demanded=len(C&leaves)+sum(max(len(leaves&g),2-min(2,len(set.union(*(adj[v] for v in g))&C))) for g in groups)
    return len(groups),demanded,len(leaves)
def main():
    hist=Counter();records=[];seen=set();n=0;cuts_repaired=0;connected=0
    for i,k,st,paths in map(json.loads,(D/'small.jsonl').read_text().splitlines()):
        hist[st]+=1
        if not paths:continue
        if st=='FOUND':assert valid(paths) and len(paths)==193;print('FOUND',*paths);sys.exit()
        c=rngdata[i];parent=majority(words[c['row']]);C=set(c['cut'])
        A={v for p in paths for v in p[::2]};S=set().union(*map(set,paths))
        assert len(A)==97 and len(parent-A)==k and set(c['qs'])<=S
        assert len(S)==sum(map(len,paths)) and all(valid(p) for p in paths)
        assert all(not NB[v]&set(q) for j,p in enumerate(paths) for q in paths[j+1:] for v in p)
        assert C<=A and set(c['ends'])<=A and all(len(A&NB[q])==2 for q in c['qs'])
        cc,need,tips=analyze(A,C);isconn=len(parts(graph(A),set()))==1
        ok=(cc<=len(C)+1 and need<=2);cuts_repaired+=ok;connected+=isconn;n+=1
        key=tuple(sorted(A))
        if key in seen:continue
        seen.add(key);records.append(dict(i=i,k=k,A=key,pc=len(paths),lengths=[len(p)-1 for p in paths],original_cut_repaired=ok,connected=isconn,cc_after=cc,demand_after=need))
    (D/'repairs.jsonl').write_text(''.join(json.dumps(x,separators=(',',':'))+'\n' for x in records))
    (D/'repairs.sets').write_text(''.join('97 '+' '.join(map(str,x['A']))+'\n' for x in records))
    print(json.dumps(dict(gaindirected_trials=dict(hist),models=n,unique=len(records),cuts_repaired=cuts_repaired,connected=connected,
        new_cc=Counter((x['cc_after']) for x in records),covers=Counter(x['pc'] for x in records),
        unique_repaired=sum(x['original_cut_repaired'] for x in records),unique_connected=sum(x['connected'] for x in records),
        longest=max((max(x['lengths']) for x in records),default=0))))
if __name__=='__main__':main()
