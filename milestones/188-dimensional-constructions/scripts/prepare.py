from pathlib import Path
import json,hashlib,re,urllib.request,datetime,subprocess
R=Path('E:/Snake-in-a-box');H=R/'milestones/188-dimensional-constructions'
for d in ['data','scripts','lean','build','logs','sources']:(H/d).mkdir(parents=True,exist_ok=True)
url='https://minortriad.com/snake/'
raw=urllib.request.urlopen(url,timeout=25).read();(H/'sources/minortriad-index.html').write_bytes(raw)
s=raw.decode('utf-8')
print('SCRIPT_SOURCES',re.findall(r'<script[^>]+src=[\"\x27]([^\"\x27]+)',s))
for line in s.splitlines():
    if any(x in line.lower() for x in ['snake6','snake7','snake8','data-seq','26','98']):print(line[:700])
old=R/'milestones/187-clause-interpretation'
for name in ['check_core.py','native_resources.py']:(H/'scripts'/name).write_bytes((old/'scripts'/name).read_bytes())
(H/'.gitattributes').write_bytes((old/'.gitattributes').read_bytes())
(H/'data/preparation.json').write_text(json.dumps({'round':188,'previous_turn':'PROGRESS','start_utc':'2026-11-11T02:08:34+00:00','focus':'Dimension lifting 6 to 7, 7 to 8, and 8 to 9; user steering replaces share-certificate priority for this round','initial_construction_hypothesis':194,'hypothesis_is_not_optimality_claim':True,'source_url':url,'source_sha256':hashlib.sha256(raw).hexdigest()},indent=2)+'\n')
(H/'scripts/prepare.py').write_bytes(Path(__file__).read_bytes())
