"""Independently enumerate seven-transition shapes and inspect saved coverage evidence.

No compiler or solver is invoked. --output exclusively creates an evidence file.
"""
from pathlib import Path
from itertools import product, combinations
import argparse, ast, hashlib, json, re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/32-seven-count-four-screen';B=R/'milestones/123-six-count-recovery'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lfsha=lambda p:hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
pins={}
def pin(p):
 p=Path(p);d=sha(p);pins[p.relative_to(R).as_posix()]=d;return d

def canon(word):
 seen=[];out=[]
 for value in word:
  if value not in seen:seen.append(value)
  out.append(seen.index(value))
 return tuple(out)

def vertices(word):
 out=[0]
 for a in word:out.append(out[-1]^(1<<a))
 return out

def induced(word):
 vs=vertices(word)
 return len(vs)==len(set(vs)) and all(((a^b).bit_count()==1)==(j==i+1)
  for i,a in enumerate(vs) for j,b in enumerate(vs) if i<j)

# Generate all 7^6 words with initial coordinate0, then filter canonical words.
# This does not import the earlier recursive restricted-growth enumerator.
rgs=[(0,)+tail for tail in product(range(7),repeat=6) if canon((0,)+tail)==(0,)+tail]
patterns=[word for word in rgs if induced(word)]
assert len(rgs)==877 and len(patterns)==34
cases_path=P/'data/cases.json';cases=read(cases_path);pin(cases_path)
assert [list(w) for w in patterns]==[c['dirs'] for c in cases]
assert all(c['bounds']==[[4,4]]*6 for c in cases)
shapes_path=P/'data/six/shapes.json';pin(shapes_path)
assert read(shapes_path)==[list(w) for w in patterns]
family=P/'lean/FamilyCoverage.lean';source=family.read_text(encoding='utf-8-sig')
match=re.search(r'def patterns : List \(List Nat\) := (\[.*\])',source)
assert match and ast.literal_eval(match.group(1))==[list(w) for w in patterns]
classes={}
for i,w in enumerate(patterns):
 reverse=canon(w[::-1]);assert reverse in patterns and canon(reverse[::-1])==w
 rep=min(w,reverse);classes.setdefault(rep,[]).append(i)
assert len(classes)==21
self_reverse=[w for w in patterns if canon(w[::-1])==w]
assert len(self_reverse)==8 and sorted(map(len,classes.values()))==[1]*8+[2]*13

manifest_path=P/'data/source-manifest.json';manifest=read(manifest_path);pin(manifest_path)
family_expected=next(x['sha256_lf'] for x in manifest['files'] if x['path'].endswith('/FamilyCoverage.lean'))
assert lfsha(family)==family_expected
up_path=P/'data/upstream.json';up=read(up_path);pin(up_path)
assert lfsha(P/'upstream/WindowAutomatonDefs.lean')==up['sha256_lf']
support_path=P/'data/normalization-support.json';support=read(support_path);pin(support_path)
support_rows=[]
for row in support:
 p=P/'upstream'/Path(row['path']).name
 assert lfsha(p)==row['sha256_lf'];pin(p)
 support_rows.append(dict(path=p.relative_to(R).as_posix(),sha256=sha(p),sha256_lf=row['sha256_lf']))
assert len(support_rows)==9
build_pointer=P/'build/proofs-latest.txt';pin(build_pointer)
build=Path(build_pointer.read_text().strip());assert build.resolve().is_relative_to((P/'build').resolve())
proof_path=P/'data/proof-verification.json';proof=read(proof_path);pin(proof_path)
assert proof['status']=='PASSED' and proof['audited_theorems']==18
modules=[]
for name,n in [('FamilyCoverage',3),('ParityCoverage',2),('SnakeCoverage',3)]:
 src=P/'lean'/(name+'.lean');log=P/'logs'/('bridge-'+name+'.log');obj=build/(name+'.olean')
 assert src.is_file() and log.is_file() and obj.is_file()
 src_text=src.read_text(encoding='utf-8-sig');text=log.read_text(encoding='utf-8-sig')
 assert not re.search(r'\b(sorry|admit|native_decide)\b',src_text)
 assert all(s not in text for s in ['error:','sorryAx','Lean.ofReduceBool','failed to'])
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
 assert len(rows)==src_text.count('#print axioms')==n
 reports=[dict(theorem=t,axioms=re.findall(r'[A-Za-z][\w.]*',s)) for t,s in rows]
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
 for p in [src,log,obj]:pin(p)
 modules.append(dict(module=name,source=src.relative_to(R).as_posix(),source_sha256=sha(src),
  source_sha256_lf=lfsha(src),object=obj.relative_to(R).as_posix(),object_sha256=sha(obj),
  log=log.relative_to(R).as_posix(),log_sha256=sha(log),axiom_reports=reports,
  historical_source_manifest_match=(name=='FamilyCoverage'),
  historical_receipt_binds_source_object=False,
  scope='Saved successful axiom log and existing object inspected; current hashes recorded. No new compiler run and no historical source/object hash-binding receipt is present for this bridge module.'))
for name in ['scripts/build_coverage.ps1','scripts/check_bridge.ps1','scripts/build_support.ps1','scripts/verify.py','scripts/verify_proofs.py']:
 pin(P/name)

bank_path=B/'data/six-sum-bank.json';bank=read(bank_path);pin(bank_path)
assert bank['status']=='PASS_SAVED_SNAKES_AND_SIX_COUNT_SCAN'
assert bank['paths']==134 and bank['case10_occurrences']==1298
for name,d in bank['source_pins'].items():assert sha(R/name)==d;pin(R/name)
assert sha(B/'scripts/scan_six_sum.py')==bank['script_sha256'];pin(B/'scripts/scan_six_sum.py')
bank_rows={tuple(row['canonical']):row for row in bank['by_shape']}
assert len(bank_rows)==len(bank['by_shape'])==21
assert set(bank_rows)<=set(classes)
missing=[list(x) for x in sorted(set(classes)-set(bank_rows))]
assert missing==[]
all_bank=read(R/'work/bank9.json')
boundaries=read(R/'milestones/121-replacement-window-pressure/data/boundary-paths.json')['paths']
paths={'bank'+str(i):row['vertex_sequence'] for i,row in enumerate(all_bank)}
paths.update({'boundary'+row['label']:row['order'] for row in boundaries})
checked_paths={};checked_pairs=0
minima=[]
for rep,row in sorted(bank_rows.items()):
 vs=paths[row['label']];selected=set(vs)
 if row['label'] not in checked_paths:
  assert len(vs)==len(selected) and all(0<=v<512 for v in vs)
  for i,a in enumerate(vs):
   for j in range(i+1,len(vs)):
    assert ((a^vs[j]).bit_count()==1)==(j==i+1);checked_pairs+=1
  checked_paths[row['label']]=len(vs)-1
 r=row['start'];assert r+7<len(vs)
 word=[(vs[k]^vs[k+1]).bit_length()-1 for k in range(r,r+7)]
 assert word==row['directions'] and min(canon(word),canon(word[::-1]))==rep
 counts=[sum(all(z not in selected for z in [v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)])
   for a,b in combinations(range(9),2)) for v in vs[r+1:r+7]]
 assert counts==row['counts'] and sum(counts)==row['total']
 minima.append(dict(representative=list(rep),word=''.join(map(str,rep)),case_indices=classes[rep],
  minimum_in_saved_scan=row['total'],source_label=row['label'],start=r,counts=counts,
  witness_rechecked=True,minimum_claim_scope='Minimum reported by the pinned prior whole-bank scan; present audit rechecks the displayed attaining witness only.'))
assert min(x['minimum_in_saved_scan'] for x in minima)==bank['global_minimum']['total']==31
out=dict(status='PASS_ENUMERATION_AND_HISTORICAL_COVERAGE_AUDIT',initial_word_candidates=7**6,
 restricted_growth_words=len(rgs),induced_words=len(patterns),patterns=[list(w) for w in patterns],
 reversal_classes=len(classes),self_reverse_patterns=[list(w) for w in self_reverse],
 representatives=[dict(word=''.join(map(str,w)),directions=list(w),case_indices=indices) for w,indices in sorted(classes.items())],
 coverage_modules=modules,printed_axiom_reports=sum(len(x['axiom_reports']) for x in modules),
 archived_normalization_sources=support_rows,bank_shapes=len(bank_rows),missing_bank_shapes=missing,
 bank_minima=minima,attaining_paths_rechecked=checked_paths,attaining_path_pairs_checked=checked_pairs,
 prior_bank_paths=bank['paths'],prior_bank_pairs_checked=bank['pairs_checked'],
 limitations=[
  'No Lean compiler, SAT solver, whole-graph check or certificate replay was run.',
  'Prior FamilyCoverage source matches its archived LF hash; bridge logs and objects exist and are fingerprinted now, but historical source/object binding receipts are absent.',
  'The prior no_six_fours_of_refuted bridge concerns exact counts4 and does not prove a lower bound on their sum.',
  'A uniform sum25 or26 requires count-sum semantic refutations and transfer for every canonical pattern, plus a checked reversal argument if only21 representatives are certified.',
  'The finite bank covers all shapes but cannot establish a universal floor; only its displayed minimum witnesses were rechecked here.'],
 verified_file_hashes=pins,script_sha256=sha(Path(__file__)))
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
if args.output:
 with args.output.open('x',encoding='utf-8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(dict(status=out['status'],rgs=len(rgs),induced=len(patterns),reversal_classes=len(classes),
 bank_shapes=len(bank_rows),missing=missing,axiom_reports=out['printed_axiom_reports'],
 witness_paths=len(checked_paths),witness_pairs=checked_pairs,verified_files=len(pins),
 output_sha256=sha(args.output) if args.output else None,script_sha256=sha(Path(__file__))),indent=2))
