# cpstats.py SEG CP NAME... : checkpoint entries unchanged since the start database / the previous checkpoint
import json, os, sys
ROOT=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
sys.path.insert(0, ROOT+'/milestones/10-window-aggregate/scripts')
import gen_lean_lrat as G
S=os.environ.get('STUDY', '/tmp/replay-study') + '/oleanstudy'
CORE=ROOT+'/milestones/10-window-aggregate/data/lean_core_direction_k6'
seg, cpe = int(sys.argv[1]), int(sys.argv[2])
G.set_width(13, True, 4000, True)
for name in sys.argv[3:]:
    meta=json.load(open(os.path.join(CORE,name+'.json')))
    core_ids=meta['core_ids']; core=G.read_cnf_core(os.path.join(S,'work',name+'.cnf'), core_ids)
    lem=G.read_lrat(os.path.join(S,'work',name+'.lrat'))
    inp, steps, last, ns = G.plan(core_ids, lem)
    h, key = G.perfect_keys(ns)
    cuts=[0]; acc=0
    for i,(_,_,hs) in enumerate(steps):
        acc+=len(hs)
        if acc>=seg and i+1<len(steps): cuts.append(i+1); acc=0
    cuts.append(len(steps))
    # slot contents over time: (clause id) per slot
    born={c:-1 for c in core_ids}; slot_at={c:s for c,s in zip(core_ids,inp)}; lits={c:l for c,l in zip(core_ids,core)}
    for i,((cid,l,_),(s,_,_)) in enumerate(zip(lem,steps)): born[cid]=i; slot_at[cid]=s; lits[cid]=l
    def live(j): return {slot_at[c]:c for c,l in last.items() if born[c]<j and l>=j}
    start=live(0); prev=start; tot=same0=sameprev=bits=bits_new=0; n=0
    for k in range(2,len(cuts)):
        if (k-1)%cpe: continue
        cur=live(cuts[k-1]); n+=1
        for s,c in cur.items():
            tot+=1; w=(len(lits[c])+1)*13
            bits+=w
            if start.get(s)==c: same0+=1
            if prev.get(s)==c: sameprev+=1
            else: bits_new+=w
        prev=cur
    print(json.dumps(dict(name=name, checkpoints=n, live_per_cp=round(tot/max(n,1)), slots=2**h-1,
        frac_input_unchanged=round(same0/max(tot,1),3), frac_unchanged_since_prev_cp=round(sameprev/max(tot,1),3),
        cp_lit_KB=round(bits/8/1024/max(n,1),1), cp_delta_lit_KB=round(bits_new/8/1024/max(n,1),1))))
