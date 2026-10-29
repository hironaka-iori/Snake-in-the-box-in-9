# gen.py OUT SEG CP GROUP NAME...  -> production pipeline (fast, split, noncomputable, packed checkpoints)
import json, os, subprocess, sys
ROOT=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
S10=ROOT+'/milestones/10-window-aggregate/scripts'
sys.path.insert(0,S10); import pack_checkpoints as PK
S=os.environ.get('STUDY', '/tmp/replay-study') + '/oleanstudy'
CORE=ROOT+'/milestones/10-window-aggregate/data/lean_core_direction_k6'
out, seg, cp, group = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
extra = os.environ.get('EXTRA','').split()
for name in sys.argv[5:]:
    meta=json.load(open(os.path.join(CORE,name+'.json'))); nv=meta['variables']
    off = 2400 if nv < 2400 else 3000 if nv < 3000 else 4000 if nv < 4000 else 5000
    for bits in ((14,15,16,17) if off==5000 else (13,14,15,16,17)):
        cmd=[sys.executable, ROOT+'/milestones/23-k6-lean/scripts/gen_lean_lrat_o5k.py' if off==5000 else S10+'/gen_lean_lrat.py',
             '--work', S+'/work','--data',CORE,'--out',out,'--seg',seg,'--cp',cp,'--group',group,'--wbits',str(bits),
             '--off',str(off),'--noncomputable-data','--fast','--split','--check',*extra,name]
        r=subprocess.run(['nice','-n','15',*cmd],capture_output=True,text=True)
        if r.returncode==0:
            st=json.loads(r.stdout.strip().splitlines()[-1]); mod=st['module']
            if not os.environ.get('NOPACK'):
                d=os.path.join(out,'LocalWindowUnsat',mod)
                for f in sorted(os.listdir(d)):
                    if f.startswith('Data'):
                        p=os.path.join(d,f); t=open(p).read(); new,k=PK.rewrite(t)
                        if k: open(p,'w').write(new)
            st.pop('seg_hints',None); st['wbits']=bits; st['off']=off
            print(json.dumps(st)); break
        if 'too many slots' not in r.stderr: print(r.stderr[-1500:]); sys.exit(1)
