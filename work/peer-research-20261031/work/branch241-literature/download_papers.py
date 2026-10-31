from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import urllib.request,json,hashlib
from pypdf import PdfReader
H=Path(__file__).resolve().parent;D=H/'papers';D.mkdir(exist_ok=True)
urls={'coil_lp_2026':'https://arxiv.org/pdf/2610.36461','branch_cut_2021':'https://arxiv.org/pdf/2104.09227','ilp_experiments_2020':'https://arxiv.org/pdf/2002.07012','perfect_density_2020':'https://arxiv.org/pdf/2009.09037','lukito_2001':'https://combinatorialpress.com/article/jcmcc/Volume%20039/vol-039-paper%2012.pdf','zemor_1997':'https://electronicsandbooks.com/edt/manual/Magazine/C/Combinatorica/Volume17-Number2-June-1997/An%20upper%20bound%20on%20the%20size%20of%20the%20snakeinthebox.pdf'}
def get(kv):
 name,u=kv
 try:
  data=urllib.request.urlopen(u,timeout=45).read();assert data.startswith(b'%PDF');p=D/(name+'.pdf');p.write_bytes(data);r=PdfReader(p);text='\n'.join('---PAGE '+str(i+1)+'---\n'+(p.extract_text() or '') for i,p in enumerate(r.pages));(D/(name+'.txt')).write_text(text,encoding='utf-8');return {'name':name,'url':u,'bytes':len(data),'pages':len(r.pages),'sha256':hashlib.sha256(data).hexdigest(),'status':'downloaded and text extracted'}
 except Exception as e:return {'name':name,'url':u,'status':'unavailable','error':str(e)}
with ThreadPoolExecutor(max_workers=4) as pool:rows=list(pool.map(get,urls.items()))
(H/'download_manifest.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
