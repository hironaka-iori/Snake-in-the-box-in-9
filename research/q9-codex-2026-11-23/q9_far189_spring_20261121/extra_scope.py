from pathlib import Path
import hashlib,io,gzip,zipfile,subprocess,shutil,os,json
D=Path(__file__).resolve().parent;R=D.parent;E=D/'additional';E.mkdir(exist_ok=True)
docs=Path.home()/'Documents/Codex';download=Path.home()/'Downloads/Snake-in-the-box-in-9-main';repo=next(docs.glob('*/*/Snake-in-the-box-in-9'))
ordinary={'.txt','.words','.pts','.vertices','.paths','.csv','.tsv','.log','.out','.json','.jsonl','.gz','.dat','.in','.sol','.raw','.records','.walks','.seq','.factors','.fits','.seeds','.bank','.routes'}
extra={'.seed','.snapshot','.ckpt','.sample','.steps','.sets','.layers','.result','.rows','.sections','.hosts','.new','.old','.domains','.novel96','.novel97','.side96','.side97','.md','.py','.cpp','.c','.hpp','.inc','.cjs'}
skip={'.git','__pycache__','.lake','.venv','venv','node_modules','formulas','lrat','proofs','certs','certificates'}
known_files=set(json.loads((D/'source_manifest.json').read_text()).values()); pool=set()
for base in [R,repo,download,Path('/private/tmp/q9_four_arc_20261120'),*[p for p in (docs/'2026-11-20').glob('q[89]*') if p.is_dir()]]:
    for b,ds,fs in os.walk(base):
        ds[:]=[n for n in ds if n not in skip and Path(b)/n not in (D,R/'q9_far_seedgrowth_20261121')]
        for n in fs:
            f=Path(b)/n
            if str(f) in known_files:continue
            if f.suffix.lower() in ordinary|extra and not f.name.endswith(('.drat.gz','.cnf.gz','.lrat.gz')):pool.add(f)
for f in Path('/private/tmp').glob('*'):
    if f.is_file() and f.name.lower().startswith(('q8','q9','snake')) and f.suffix.lower() in extra:pool.add(f)
id=0;seen={};manifest={};aliases=0;binary=0;issues={}
proc=subprocess.Popen(['/tmp/q9_spring_scan21',(R/'q9_far_seedgrowth_20261121/new189.words').read_text().strip(),str(E)],stdin=subprocess.PIPE,stdout=(E/'comparison.log').open('wb'))
def record(data,name):
    global id,aliases,binary
    if b'\0' in data[:65536]:binary+=1;return
    h=hashlib.sha256(data).digest()
    if h in seen:aliases+=1;return
    id+=1;seen[h]=id;manifest[id]=name;proc.stdin.write(b'\n#SRCPATH '+str(id).encode()+b'\n'+data+b'\n')
for f in sorted(pool):
    try:record(gzip.decompress(f.read_bytes()) if f.suffix=='.gz' else f.read_bytes(),str(f))
    except (OSError,EOFError) as e:issues[str(f)]=str(e)
zf=download.with_suffix('.zip')
with zipfile.ZipFile(zf) as z:
    for m in z.infolist():
        q=Path(m.filename)
        if m.is_dir() or skip.intersection(q.parts) or q.suffix.lower() not in ordinary|extra or m.filename.endswith(('.drat.gz','.cnf.gz','.lrat.gz')):continue
        data=z.read(m)
        try:record(gzip.decompress(data) if q.suffix=='.gz' else data,str(zf)+'!'+m.filename)
        except (OSError,EOFError) as e:issues[m.filename]=str(e)
proc.stdin.close();assert proc.wait()==0
(E/'source_manifest.json').write_text(json.dumps(manifest,indent=2))
print(json.dumps(dict(selected_disk_files=len(pool),unique_text_streams=id,duplicate_streams_by_sha256=aliases,skipped_binary=binary,errors=issues),indent=2))
