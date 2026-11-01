"""Reuse the audited share pipeline in a separate count-free proof directory."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
OLD=HERE.parent/'critical-charge'
OUT=HERE/'share-proof'
for d in ['lean/Share12','logs','data','certificates','build']:
    (OUT/d).mkdir(parents=True,exist_ok=True)
def write(path,text):path.write_text(text,encoding='utf-8',newline='\n')
def renamed(s):return s.replace('ShareWindow120','ShareWindow12').replace('Share120','Share12').replace('share120','share12').replace('share0-cap119','general8-cap11').replace('ckAllS_append_true','ckAllS_append_true12')
for name in ['prepare_lean.py','replay_share.py','complete_share.py','export_share.py','audit_share.py']:
    s=renamed((OLD/'scripts'/name).read_text())
    if name in ['prepare_lean.py','audit_share.py']:
        s=s.replace(",119)",",11)").replace(", 119)",", 11)").replace('cap : Nat := 119','cap : Nat := 11').replace('share_lower=120','share_lower=12')
        if name=='prepare_lean.py':
            s=s.replace("prior=read(HERE/'data/screen/w000-native.json')","prior={'cycle_cuts':[]}")
        else:s=s.replace("read(HERE/'data/screen/w000-native.json')['cycle_cuts']","[]")
    if name=='replay_share.py':
        s=s.replace("range(59)","range(json.loads((OUT/'data/share12.json').read_text())['shards'])")
        s=s.replace("'Share12/Shard58'","'Share12/Shard00'")
        s=s.replace("'-o',str(dest)","'-o',str(dest.with_suffix('.fresh.olean'))")
        s=s.replace("code=r.returncode","code=r.returncode\n  if code==0:os.replace(dest.with_suffix('.fresh.olean'),dest)")
    if name=='complete_share.py':
        s=s.replace('pending=set(sources)-complete',"pending=set(sources)-complete\nif '--lrat-only' in sys.argv:pending={n for n in pending if n.startswith(('Lrat','LocalWindowUnsat/'))}")
    write(HERE/'scripts'/name,s)
for name in ['Compose','Refuted']:
    write(OUT/f'lean/Share12/{name}.lean',renamed((OLD/f'share-proof/lean/Share120/{name}.lean').read_text()))
write(OUT/'lean/LocalWindowShareBridge.lean',(OLD/'share-proof/lean/LocalWindowShareBridge.lean').read_text())
write(OUT/'data/bridge-source.json',(OLD/'share-proof/data/bridge-source.json').read_text())
s=renamed((OLD/'share-proof/lean/Share120/Geometry.lean').read_text())
start=s.index('    (hb :')
end=s.index('120 ≤',start)
s=s[:start]+'    :\n    12 ≤'+s[end+len('120 ≤'):]
s=s.replace('    (by simpa [bounds] using hb)', '''    (by
      intro i hi
      have hi5 : i < 5 := by simpa [bounds] using hi
      have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
      interval_cases i <;> simpa [bounds] using hu)''')
write(OUT/'lean/Share12/Geometry.lean',s)
write(OUT/'.gitignore','build/\ncertificates/*.cnf\ncertificates/*.lrat\nlean/LocalWindowUnsat/ShareWindow12/\n')
write(OUT/'.gitattributes','lean/** -text whitespace=cr-at-eol\nlogs/** -text -whitespace\ndata/** -text whitespace=cr-at-eol\n')
print('Count-free proof pipeline prepared; generated claims remain unverified.')
