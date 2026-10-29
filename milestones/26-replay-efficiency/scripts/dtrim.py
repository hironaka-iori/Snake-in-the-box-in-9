import json, os, sys, subprocess, time
ROOT=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
S=os.environ.get('STUDY', '/tmp/replay-study') + '/oleanstudy'
CORE=ROOT+'/milestones/10-window-aggregate/data/lean_core_direction_k6'
CAD=os.environ.get('CADICAL', '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical'); DT=ROOT+'/milestones/10-window-aggregate/.build/drat-trim'
for name in sys.argv[1:]:
    meta=json.load(open(os.path.join(CORE,name+'.json')))
    cl=[l for l in open(S+'/work/'+name+'.cnf') if l[0] not in 'pc' and l.strip()]
    core=[cl[i-1] for i in meta['core_ids']]
    nv=max(abs(int(x)) for c in core for x in c.split())
    d=S+'/dt/'; open(d+'c.cnf','w').write('p cnf %d %d\n'%(nv,len(core))+''.join(core))
    best=None
    for seed in (1,2):
        t=time.time()
        subprocess.run(['nice','-n','15',CAD,'-q','--no-binary','--seed=%d'%seed,d+'c.cnf',d+'p.drat'],capture_output=True)
        subprocess.run(['nice','-n','15',DT,d+'c.cnf',d+'p.drat','-L',d+'p.lrat','-t','600'],capture_output=True)
        H=L=0
        for line in open(d+'p.lrat'):
            t2=line.split()
            if t2[1]=='d': continue
            z=t2.index('0',1); H+=len(t2)-z-2; L+=1
        best=min(best or (H,L),(H,L))
        print(json.dumps(dict(name=name,seed=seed,lemmas=L,hints=H,sec=round(time.time()-t,1))),flush=True)
    for f in ('c.cnf','p.drat','p.lrat'): os.remove(d+f)
