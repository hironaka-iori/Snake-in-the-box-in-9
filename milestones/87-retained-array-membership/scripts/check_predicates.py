"""Check the actual-retention conjunction using pinned successful module receipts."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as stream:
        for b in iter(lambda:stream.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
dependencies={};paths=[str(HERE/'build')]
for folder,module in [
    ('85-reference-catalogue-union','ReferenceUnion'),
    ('81-recovered-short-rule-retention','ShortRetention'),
    ('84-history-exclusion-retention','HistoryExclusions'),
    ('79-retained-edge-guards','IntervalCatalogue'),
    ('78-numeric-history-transition','StateWalk')]:
    base=ROOT/'milestones'/folder;rp=base/'data'/f'{module}-audit.json'
    row=json.loads(rp.read_text());assert row['status']=='PASS_LEAN_MODULE'
    for sub,suffix,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(base/sub/(module+suffix))==row[key],module+': '+key
    support={}
    for key,name in [('short_support_sha256','short-support.json'),('interval_support_sha256','interval-support.json')]:
        if key in row:
            p=base/'data'/name;assert sha(p)==row[key];support[p.relative_to(ROOT).as_posix()]=sha(p)
    dependencies[module]=dict(receipt=rp.relative_to(ROOT).as_posix(),receipt_sha256=sha(rp),
        source_sha256=row['source_sha256'],object_sha256=row['olean_sha256'],
        log_sha256=row['log_sha256'],support_metadata=support)
    paths.extend(x for x in row['paths'] if x not in paths)
for folder in ['build','data','logs']:(HERE/folder).mkdir(exist_ok=True)
module='RetainedPredicates'
overlay=HERE/'build'/'RetainedPredicates-support';support_modules={}
for relative in ['milestones/81-recovered-short-rule-retention/data/short-support.json',
                 'milestones/79-retained-edge-guards/data/interval-support.json']:
    receipt=ROOT/relative;data=json.loads(receipt.read_text());receipt_hash=sha(receipt)
    for name,item in data['modules'].items():
        source=Path(item['source']);original=Path(item['object'])
        assert sha(source)==item['source_sha256'],name+': inherited source'
        assert sha(original)==item['object_sha256'],name+': inherited object'
        if name in support_modules:
            prior=support_modules[name]
            assert prior['source_sha256']==item['source_sha256'] and prior['object_sha256']==item['object_sha256'],name+': conflicting support objects'
            continue
        destination=overlay/(name.replace('.','/')+'.olean');destination.parent.mkdir(parents=True,exist_ok=True)
        if destination.exists():
            assert os.path.samefile(original,destination) or sha(destination)==item['object_sha256'],name+': different existing overlay'
        else:
            try:os.link(original,destination)
            except OSError:shutil.copy2(original,destination)
        assert os.path.samefile(original,destination) or sha(destination)==item['object_sha256']
        support_modules[name]=dict(source=source.as_posix(),source_sha256=item['source_sha256'],
            original_object=original.as_posix(),object_sha256=item['object_sha256'],
            object=destination.as_posix(),receipt=relative,receipt_sha256=receipt_hash)
support_path=HERE/'data'/'RetainedPredicates-support.json'
support_path.write_text(json.dumps(dict(status='PINNED_COMBINED_PREDICATE_SUPPORT',overlay=overlay.as_posix(),
    modules=support_modules,scope='Exact existing source/object hashes verified; copied or hard-linked into one namespace search root. No certificate recompilation.'),indent=2)+'\n')
paths.insert(1,str(overlay))
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
src=HERE/'lean'/f'{module}.lean';obj=HERE/'build'/f'{module}.olean';log=HERE/'logs'/f'{module}.log'
if log.exists() and 'error: object file' in log.read_text():
    saved=HERE/'logs'/f'{module}-import-failure.log'
    if not saved.exists():shutil.copy2(log,saved)
    record=HERE/'logs'/f'{module}-record.json';saved_record=HERE/'logs'/f'{module}-import-failure-record.json'
    if record.exists() and not saved_record.exists():shutil.copy2(record,saved_record)
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=300)
row=dict(module=module,exit_code=p.returncode,seconds=time.monotonic()-start,
    source_sha256=sha(src),log_sha256=sha(log),paths=paths,dependencies=dependencies,
    combined_support_sha256=sha(support_path),pinned_support_modules=len(support_modules))
(HERE/'logs'/f'{module}-record.json').write_text(json.dumps(row,indent=2)+'\n')
if p.returncode:print(log.read_text()[-16000:]);raise SystemExit(p.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==src.read_text().count('#print axioms')
checked=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    checked.append(dict(theorem=name,axioms=values))
row.update(status='PASS_ACTUAL_RETENTION_PREDICATES',olean_sha256=sha(obj),theorem_audits=checked,
    scope='Composition of all four semantic filter families, actual history compatibility, coding ranges and endpoints. AllRefuted6K235 and AllRefuted236 remain explicit premises. Numeric keep-predicate equivalence and retained-array membership remain separate. Direct inherited source/object/log hashes and combined support source/object hashes checked; full inherited closure not rebuilt.')
(HERE/'data'/f'{module}-audit.json').write_text(json.dumps(row,indent=2)+'\n')
print(module,'PASS',round(row['seconds'],3),'seconds;',len(checked),'audits',flush=True)
