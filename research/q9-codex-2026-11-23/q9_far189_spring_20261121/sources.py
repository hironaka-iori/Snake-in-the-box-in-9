from pathlib import Path
import gzip,zipfile,shutil,json,sys,subprocess
D=Path(__file__).resolve().parent;R=D.parent;docs=Path.home()/'Documents/Codex'
repo=next(docs.glob('*/*/Snake-in-the-box-in-9'))
fmt={'.txt','.words','.pts','.vertices','.paths','.csv','.tsv','.log','.out','.json','.jsonl','.gz','.dat','.in','.zip','.sol','.raw','.records','.walks','.seq','.factors','.fits','.seeds','.bank','.routes'}
exclude={'.git','__pycache__','.lake','.venv','venv','node_modules','formulas','lrat','proofs','certs','certificates'}
files=set()
for base in [R,repo,*[p for p in (docs/'2026-11-20').glob('q[89]*') if p.is_dir()]]:
    for f in base.rglob('*'):
        if not f.is_file() or exclude.intersection(f.parts) or D in f.parents or (R/'q9_far_seedgrowth_20261121') in f.parents:continue
        if f.suffix.lower() in fmt or (not f.suffix and '189' in f.name):files.add(f)
for f in Path('/private/tmp').glob('*'):
    if f.is_file() and f.name.lower().startswith(('q8','q9','snake')) and (f.suffix.lower() in fmt or not f.suffix):files.add(f)
source=0;manifest={};issues={};binary=0
p=subprocess.Popen(['/tmp/q9_spring_scan21',(R/'q9_far_seedgrowth_20261121/new189.words').read_text().strip(),str(D)],stdin=subprocess.PIPE,stdout=(D/'comparison.log').open('wb'))
def stream(f,name):
    global source,binary
    head=f.read(65536)
    if b'\0' in head or head.startswith((b'\xcf\xfa\xed\xfe',b'\x7fELF')):binary+=1;return
    source+=1;manifest[source]=name;p.stdin.write(b'\n#SRCPATH '+str(source).encode()+b'\n');p.stdin.write(head);shutil.copyfileobj(f,p.stdin,1024*1024);p.stdin.write(b'\n')
for file in sorted(files,key=str):
    try:
        if file.suffix=='.zip':
            with zipfile.ZipFile(file) as z:
                for m in z.infolist():
                    if m.is_dir() or Path(m.filename).suffix.lower() not in fmt:continue
                    with z.open(m) as f:stream(f,str(file)+'!'+m.filename)
        elif file.suffix=='.gz':
            # Solver proof logs and CNFs have no ordered Q9 path encoding.
            if file.name.endswith(('.drat.gz','.cnf.gz','.lrat.gz')):continue
            with gzip.open(file,'rb') as f:stream(f,str(file))
        else:
            with file.open('rb') as f:stream(f,str(file))
    except (OSError,EOFError,zipfile.BadZipFile) as e:issues[str(file)]=str(e)
p.stdin.close();assert p.wait()==0
(D/'source_manifest.json').write_text(json.dumps(manifest,indent=2))
print(json.dumps(dict(selected_files=len(files),scanned_text_streams=source,binary_skipped=binary,unreadable=issues),indent=2))
