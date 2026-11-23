from pathlib import Path
import subprocess
d=Path(__file__).resolve().parent
for idx,w in enumerate((d/'outside189.words').read_text().splitlines()):
    out=subprocess.check_output(['/tmp/q9_far189tips21','300','19','26000','40'],input=w+'\n',text=True)
    print('SOURCE',idx,flush=True);print(out,flush=True)
    if 'FOUND ' in out:break
