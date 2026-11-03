"""Audit the transported core, emitted packed data, and semantic source; no compiler."""
from pathlib import Path
from collections import Counter
import ast,hashlib,json,re,time,datetime

H=Path(__file__).resolve().parents[1];R=H.parents[1];pins={}
def sha(p):
 p=Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 v=h.hexdigest();pins[p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p)]=v;return v
def read(p):sha(p);return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def text(p):sha(p);return Path(p).read_text(encoding='utf-8-sig')
def parse_lrat(line):
 a=list(map(int,line.split()));i=a.index(0,1);assert a[-1]==0
 return a[0],a[1:i],a[i+1:-1]
def lists(source):
 out={}
 for name,body in re.findall(r'noncomputable def (inputSlots|proof\d+|cp\d+) : List Nat := \[(.*?)\]',source,re.S):
  nums=re.findall(r'nat_lit (0x[0-9a-fA-F]+|\d+)',body)
  assert not re.sub(r'nat_lit (?:0x[0-9a-fA-F]+|\d+)|[\s,]','',body)
  assert name not in out;out[name]=[int(x,0) for x in nums]
 return out
def unpack(x):
 words=[]
 while x:words.append(x&8191);x>>=13
 return words
def lit_word(word):
 b=word-1;assert 0<b<4800 and b!=2400
 return b if b<2400 else -(b-2400)
def main():
 started=time.monotonic();sha(Path(__file__))
 s=read(H/'data/selected-core-semantics.json');plan=read(H/'data/proof-plan.json')
 original_audit=read(H/'data/endpoint-core-review.json');encoding=read(H/'data/encoding.json')
 assert original_audit['status']=='PASS_ORIGINAL_CORE_NATIVE_REPLAY_AND_GEOMETRY_REVIEW'
 assert sha(H/'data/selected-core-semantics.json')==plan['semantic_data_sha256']
 for rel,d in plan['source_files_sha256'].items():assert sha(R/rel)==d
 for item in plan['export_receipts']:assert sha(H/item['path'])==item['sha256']
 assert sha(plan['checker_object'])==plan['checker_object_sha256']
 assert sha(plan['checker_receipt'])==plan['checker_receipt_sha256']
 ids=s['core_ids'];triples=original_audit['core_clause_tags'];assert len(ids)==683
 assert ids==[r['original_id'] for r in triples]
 assert s['original_raw']==[r['clause'] for r in triples] and s['tags']==[r['tag'] for r in triples]
 rename={int(k):v for k,v in s['old_to_new'].items()};inverse={int(k):v for k,v in s['new_to_old'].items()}
 assert set(rename)==set(rename.values())==set(inverse)==set(range(1,2427))
 assert all(inverse[v]==k for k,v in rename.items())
 def transport(lit):return rename[abs(lit)]*(1 if lit>0 else -1)
 assert s['renamed_signed_raw']==[[transport(x) for x in c] for c in s['original_raw']]
 assert s['raw']==[[2*abs(x)+(x<0) for x in c] for c in s['renamed_signed_raw']]
 assert s['base_raw']==s['raw'][:676] and s['endpoint_raw']==s['raw'][676:]
 assert s['base_core_ids']==ids[:676] and s['endpoint_core_ids']==ids[676:]
 assert s['base_tags']==s['tags'][:676] and s['endpoint_tags']==s['tags'][676:]
 assert s['used_endpoint_units']==[0,10,18,34,66,130,258]
 assert s['parity_clauses_present'] is False and s['used_counter_indices']==[1]
 assert all(t[0] not in ['one_even_endpoint','one_odd_endpoint'] for t in s['tags'])
 assert s['endpoint_raw']==[[2*rename[513+v]+1] for v in s['used_endpoint_units']]
 oldproof=H/'work/certificate/trimmed.lrat';newproof=H/'data/proof-export/endpoint132.lrat'
 sha(oldproof);sha(newproof);lemmas=[];active={abs(x) for c in s['original_raw'] for x in c}
 with oldproof.open() as a,newproof.open() as b:
  for line in a:
   old=parse_lrat(line);new=parse_lrat(next(b))
   assert new==(old[0],[transport(x) for x in old[1]],old[2])
   active.update(map(abs,old[1]));lemmas.append(new)
  assert next(b,None) is None
 assert len(lemmas)==13299 and sum(len(h) for _,_,h in lemmas)==554859
 assert len(active)==311 and sorted(active)==s['proof_active_old_ids']
 order=sorted(active)+sorted(set(range(1,2427))-active)
 assert all(rename[v]==i+1 for i,v in enumerate(order))
 assert max(abs(x) for _,c,_ in lemmas for x in c)<=311
 # Check every original full-input row under the same bijection, without rebuilding encoders.
 with (H/'work/base.cnf').open() as a,(H/'data/proof-export/endpoint132.cnf').open() as b:
  assert next(a)==next(b)=='p cnf 2426 96552\n'
  count=0
  for line in a:
   old=list(map(int,line.split()));new=list(map(int,next(b).split()))
   assert old[-1]==new[-1]==0 and new[:-1]==[transport(x) for x in old[:-1]];count+=1
  assert count==96552 and next(b,None) is None
 needed=active|set(range(1,1025));meanings={int(k):v for k,v in s['meaning'].items()}
 assert meanings=={rename[k]:encoding['variable_meaning'][str(k)] for k in needed}
 assert s['counters'][0]=={'index':0,'dummy':True}
 c=s['counters'][1]
 assert c['upper']==9 and c['original_literals']==encoding['pair_literals']
 assert c['literals']==[transport(x) for x in encoding['pair_literals']]
 assert len(c['literals'])==42 and len(set(c['literals']))==37
 sources={}
 for item in plan['artifacts']:
  path=H/item['path'];assert sha(path)==item['sha256']
  name=path.relative_to(H/'lean').as_posix()[:-5].replace('/','.')
  sources[name]=text(path)
 assert len(sources)==51 and set(sources)==set(plan['module_order'])
 position={m:i for i,m in enumerate(plan['module_order'])};external=set()
 for name,source in sources.items():
  assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
  for imp in re.findall(r'^import ([\w.]+)$',source,re.M):
   if imp in sources:assert position[imp]<position[name]
   else:
    assert not imp.startswith(('Recovered132G.','LocalWindowCnf.Endpoint132','LocalWindowUnsat.Endpoint132'))
    external.add(imp)
 assert external=={'LratFast','LocalWindowDirModel'}
 snapshots=read(H/'data/proof-export/original-generated-sources.json')
 assert len(snapshots)==50
 for rel,row in snapshots.items():
  assert hashlib.sha256(row['source'].encode()).hexdigest()==row['sha256']
  current=sources['Recovered132G.'+rel[:-5].replace('/','.')]
  suffix='\n#print axioms Snake9.LocalWindow.Endpoint132.unsat\n' if rel=='LocalWindowUnsat/Endpoint132.lean' else ''
  assert current==re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.Endpoint132(?:\.[A-Za-z0-9]+)?)$',r'import Recovered132G.\1',row['source'],flags=re.M)+suffix
 cnf=sources['Recovered132G.LocalWindowCnf.Endpoint132']
 parsed=[]
 for name in ['baseRaw','endpointRaw']:
  body=cnf.split('noncomputable def '+name+' : List (List Nat) := ',1)[1].split('\nnoncomputable def',1)[0]
  parsed.extend(ast.literal_eval(body.strip()))
 assert parsed==s['raw'] and 'baseRaw ++ endpointRaw' in cnf
 data={}
 for name,source in sources.items():
  if '.Data' in name:
   for key,value in lists(source).items():assert key not in data;data[key]=value
 assert set(data)=={'inputSlots'}|{'proof'+str(i) for i in range(1,94)}|{'cp'+str(i) for i in range(5,94,4)}
 slots=data['inputSlots'];assert len(slots)==len(set(slots))==683
 state=dict(zip(slots,ids));clauses=dict(zip(ids,s['renamed_signed_raw']))
 keys=[]
 def preorder(h,base=0):
  if h:
   k=base+(1<<(h-1));keys.append(k);preorder(h-1,base);preorder(h-1,k)
 preorder(11);index=0;segment_hints=[];cp_checked=0
 for segment in range(1,94):
  cp='cp'+str(segment)
  if cp in data:
   assert len(data[cp])==2047;retained={}
   for key,packed in zip(keys,data[cp]):
    if packed:
     clause=[lit_word(w) for w in unpack(packed)]
     assert key in state and clause==clauses[state[key]];retained[key]=state[key]
   state=retained;cp_checked+=1
  nh=0
  for packed in data['proof'+str(segment)]:
   words=unpack(packed);z=words.index(0,1);destination=words[0]
   clause=[lit_word(w) for w in words[1:z]];hintslots=words[z+1:]
   cid,expected,hints=lemmas[index]
   assert clause==expected and [state[k] for k in hintslots]==hints
   assert len(clause)<255 and len(hintslots)<4095 and 0<destination<2048
   state[destination]=cid;clauses[cid]=clause;index+=1;nh+=len(hints)
  segment_hints.append(nh)
 assert index==13299 and cp_checked==23 and segment_hints==plan['stats']['seg_hints']
 assert state[1024]==lemmas[-1][0] and clauses[state[1024]]==[]
 allsources='\n'.join(sources.values())
 assert sorted(map(int,re.findall(r'^theorem ok(\d+)\s*:',allsources,re.M)))==list(range(1,94))
 final=sources['Recovered132G.LocalWindowUnsat.Endpoint132']
 assert Counter(map(int,re.findall(r'\bok(\d+)\b',final)))==Counter(range(1,94))
 assert 'theorem unsat : Unsat cnf := by' in final
 # Semantic source review uses the final saved sources, without running their compiler.
 sem=text(H/'lean/CoreSemantics132.lean');actual=text(H/'lean/ActualEndpoint132.lean');counters=text(H/'lean/ActualCounters132.lean')
 repair=read(H/'data/semantic-repair2.json')
 for rel,digest in repair['source_files_sha256'].items():assert sha(R/rel)==digest
 assert 'rw [lit_negE hn,hf]\n    rfl' in sem
 for source in [sem,actual,counters]:assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
 treebody=sem.split('noncomputable def meaning : MT :=',1)[1].split('noncomputable def counters',1)[0]
 tokens=re.findall(r'\(|\)|\.[a-z]+|\d+',treebody);cursor=0
 def tree():
  nonlocal cursor
  token=tokens[cursor];cursor+=1
  if token=='.z':return ('z',)
  assert token=='(';kind=tokens[cursor][1:];cursor+=1
  if kind=='n':value=('n',tree(),tree())
  else:
   count=3 if kind=='r' else 1;assert kind in ['p','e','r']
   value=(kind,*map(int,tokens[cursor:cursor+count]));cursor+=count
  assert tokens[cursor]==')';cursor+=1;return value
 mt=tree();assert cursor==len(tokens)
 def lookup(n):
  t=mt
  while t[0]=='n':t=t[1+n%2];n//=2
  return list(t)
 # MT leaves may alias larger unused indices. Check the entire supplied domain,
 # plus that every variable referenced by this core, proof and counter is in it.
 for i in range(max(meanings)+1):assert lookup(i)==meanings.get(i,['z'])
 referenced={abs(x) for row in s['renamed_signed_raw'] for x in row}
 referenced.update(abs(x) for _,row,_ in lemmas for x in row)
 referenced.update(map(abs,c['literals']))
 assert referenced<=set(meanings)
 body=sem.split('noncomputable def counters : List Ctr := [dfltCtr,',1)[1].split('theorem pair_checked',1)[0]
 encoded=ast.literal_eval(re.search(r'⟨(\[[^]]*\]),9,\.ends⟩',body).group(1))
 assert encoded==[2*abs(x)+(x<0) for x in c['literals']]
 assert Counter(lookup(x//2)[1] for x in encoded)==Counter(v for row in encoding['corner_lists'] for v in row)
 raw_chunks=[];tag_chunks=[]
 for k in range(11):
  raw_chunks.extend(ast.literal_eval(re.search(r'def rs'+str(k)+r' : List \(List Nat\) := (\[[^\n]*\])',sem).group(1)))
  body=re.search(r'def ts'+str(k)+r' : List Tag := (\[[^\n]*\])',sem).group(1)
  tag_chunks.extend([[name,*map(int,args.split())] for name,args in re.findall(r'\.([A-Za-z][A-Za-z0-9]*)([ 0-9]*)',body)])
 assert raw_chunks==s['base_raw'] and tag_chunks==s['base_tags']
 units=ast.literal_eval(re.search(r'def units : List Nat := (\[[^\n]*\])',sem).group(1))
 assert [[u] for u in units]==s['endpoint_raw']
 assert [lookup(u//2) for u in units]==[['e',v] for v in s['used_endpoint_units']]
 assert all(u%2==1 for u in units)
 assert 'JointTags.Good' in sem and 'JointTags.Valid' in sem and 'JointTags.sound_all tags_checked hv ax' in sem
 assert 'countP_permuted_corners' in counters and '.Perm' in counters
 assert 'CoreSemantics132.actual_frame_endpoint Endpoint132.unsat' in actual
 assert 'hunsat' not in actual and not re.search(r'\b(hodd|heven|parity)\b|%\s*2',actual)
 declarations=re.findall(r'^theorem ([\w]+)',actual,re.M)
 assert declarations==['actual_pair_endpoint','actual_pair_ge_ten_without_endpoint']
 assert '(hr : r+6 ≤ m)' in actual and 'canon (dsOf p r 6) = [0,1,2,0,3,2]' in actual
 assert '(hpair : coreAlpha p (r+2)+coreAlpha p (r+4) ≤ 9)' in actual
 assert '∃ k, (k=0 ∨ k=m) ∧\n      hamming (vx p (r+2)) (vx p k) = 2 ∧\n      hamming (vx p (r+4)) (vx p k) = 2' in actual
 assert '10 ≤ coreAlpha p (r+2)+coreAlpha p (r+4)' in actual
 # Recheck all fixed source pins after decoding and source inspection.
 before=dict(pins)
 for rel,digest in before.items():
  p=Path(rel);p=p if p.is_absolute() else R/p
  assert sha(p)==digest,('Input changed during audit',rel)
 out=dict(status='PASS_BOUNDED_ENDPOINT_EXPORT_AND_STATIC_SEMANTICS_REVIEW',
  renaming_bijection_size=2426,active_variables=311,active_first_order_checked=True,
  original_selected_clauses=683,full_input_rows_transport_checked=96552,
  original_ids_tags_signs_and_occurrences_preserved=True,counter_occurrences=42,counter_distinct_literals=37,
  parity_premises=False,endpoint_units=7,counter0_dummy=True,
  module_count=51,module_order=plan['module_order'],external_imports=sorted(external),
  generated_snapshot_count=50,generated_snapshots_only_import_prefix_and_final_axiom_print_changed=True,
  packed_lemmas_checked=13299,packed_hint_references_checked=554859,segments=93,checkpoints_checked=23,
  checkpoint_words_checked=23*2047,proof_slots=1119,tree_height=11,literal_offset=2400,packed_word_bits=13,
  final_empty_clause_slot=1024,semantic_meanings_checked=len(meanings),semantic_chunks_checked=11,
  every_referenced_variable_has_checked_meaning=True,
  semantic_tables_and_units_match_export=True,actual_theorem_declarations=declarations,
  final_semantic_repair2_source_and_preserved_failure_pins_checked=True,
  actual_theorem_source=actual,
  limits=['Packed data was decoded against the transported LRAT; no new native RUP replay, solver or Lean compiler was run.',
   'Semantic and final theorem sources were inspected statically; their successful kernel compilation is a separate requirement.',
   'Full replay completion receipts and final theorem axiom reports are outside this bounded export audit.',
   'No endpoint occurrence bound or global snake bound is claimed.'],
  completed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-started,source_files_sha256=pins)
 destination=H/'data/endpoint-export-review.json'
 if destination.exists():
  prior=json.loads(destination.read_text())
  assert prior['status']=='PASS_BOUNDED_ENDPOINT_EXPORT_AND_STATIC_SEMANTICS_REVIEW'
  assert 'prior_static_source_review' not in prior
  out['prior_static_source_review']=prior
  out['prior_review_note']='Preserved the provisional static assessment of repair1 before final repair2; neither static assessment certifies successful Lean compilation.'
 destination.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
 print(json.dumps({k:v for k,v in out.items() if k not in ['module_order','actual_theorem_source','source_files_sha256']},indent=2))
if __name__=='__main__':main()
