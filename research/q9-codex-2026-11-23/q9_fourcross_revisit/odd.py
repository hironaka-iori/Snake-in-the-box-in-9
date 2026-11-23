from pathlib import Path
import json,sys
import oddmodel as mod
D=Path(__file__).resolve().parent;B=D.parent/'q9_fourcross_new94'
case=json.loads((D/'cases.json').read_text())[0]
arr=mod.load(D/'fullalt_0.dat')+mod.load(D/'fullalt_1.dat')
for i,(q,s) in enumerate(arr):
    hint={v-256 for v in case['hint'] if v>=256}
    mod.run(q,s,185,-1,180000,i,'real185',hint)
