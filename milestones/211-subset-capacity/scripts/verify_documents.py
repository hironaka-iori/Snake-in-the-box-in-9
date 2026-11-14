"""Record compilation receipts and exact document preservation for publication."""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
record={'scope':'Document source preservation and saved compilation success; no page-by-page visual audit.'}
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=D/name;q=R/'paper'/name;assert p.read_bytes()==q.read_bytes()
 old=(H/'data'/('before-'+name)).read_text(encoding='utf-8');new=p.read_text(encoding='utf-8')
 assert re.search(r'\\author\{[^\n]*',old).group()==re.search(r'\\author\{[^\n]*',new).group()
 if name=='snake9_research.tex':
  assert re.search(r'\\hypersetup\{.*?\n\}',old,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',new,re.S).group()
  labels=re.findall(r'\\label\{([^}]+)\}',new);assert len(labels)==len(set(labels))
  assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',new))<=set(labels)
  bib=set(re.findall(r'\\bibitem\{([^}]+)\}',new))
  cites={x.strip() for group in re.findall(r'\\cite\{([^}]+)\}',new) for x in group.split(',')}
  assert cites<=bib
  record['labels']=len(labels)
 receipt=H/'data'/('main-compile-retry1.json' if name=='snake9_research.tex' else 'frontier-compile-retry1.json')
 result=json.loads(receipt.read_bytes());assert not result.get('isError',False)
 assert any(json.loads(c['text']).get('kind')=='success' for c in result['content'] if c['type']=='text')
 record[name]={'sha256':sha(p),'compile_receipt':str(receipt.relative_to(H)),'compile_sha256':sha(receipt)}
(H/'data/document-verification.json').write_text(json.dumps(record,indent=2)+'\n')
path=H/'data/completion.json';d=json.loads(path.read_bytes());d['document_verification']='data/document-verification.json'
d['compile_success']=True;d['final_math_review']='logs/final-math-review.md'
path.write_text(json.dumps(d,indent=2)+'\n')
for p in [H/'README.md',H/'MATHEMATICAL_NOTE.md']:
 with p.open('a',encoding='utf-8') as f:f.write('\nBoth final editor documents compiled successfully after one stale-input retry each. Source mirrors, author declarations, hyperlink settings, labels and citations are verified in data/document-verification.json.\n')
print('DOCUMENTS_VERIFIED',record['labels'],'labels; exact mirrors and successful saved compiles.')
