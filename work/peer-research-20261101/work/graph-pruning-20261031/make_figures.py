"""Generate reproducible vector research figures; no external plotting packages."""
from pathlib import Path
import json,math,html
H=Path(__file__).resolve().parent;O=H/'figures';O.mkdir(exist_ok=True)
def svg(w,h,body):return f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}"><rect width="100%" height="100%" fill="#f8fafc"/><g font-family="Segoe UI,Arial,sans-serif">'+''.join(body)+'</g></svg>'
def text(x,y,s,size=17,color='#0f172a',anchor='middle'):return f'<text x="{x}" y="{y}" font-size="{size}" fill="{color}" text-anchor="{anchor}">{html.escape(str(s))}</text>'
def line(x,y,u,v,color='#94a3b8',width=2):return f'<line x1="{x}" y1="{y}" x2="{u}" y2="{v}" stroke="{color}" stroke-width="{width}"/>'
def real():
 d=json.loads((H/'global235_probe.json').read_text());w=d['first_block_prune'];B=[set(b) for b in w['decomposition']['blocks']];arts=set(w['decomposition']['articulations']);head=w['path'][-1]
 T={('b',i):[] for i in range(len(B))}
 for a in arts:
  T['a',a]=[]
  for i,b in enumerate(B):
   if a in b:T['a',a].append(('b',i));T['b',i].append(('a',a))
 root=('a',head) if head in arts else ('b',next(i for i,b in enumerate(B) if head in b));pos={};edges=[];leaves=[]
 def layout(v,p,dep):
  ch=[c for c in T[v] if c!=p]
  for c in ch:edges.append((v,c));layout(c,v,dep+1)
  x=sum(pos[c][0] for c in ch)/len(ch) if ch else len(leaves)
  if not ch:leaves.append(v)
  pos[v]=(x,dep)
 layout(root,None,0);maxdep=max(y for x,y in pos.values());W=1400;HH=240+(maxdep+1)*90
 body=[text(W/2,38,'A real Q9 branch excluded by global graph structure',28),text(W/2,72,'84 prefix vertices; a 235-edge target requires 153 suffix vertices (head included).',19)]
 for i,(name,val) in enumerate(w['bounds'].items()):
  x=140+i*350;body.append(text(x,116,f'{name}: {val}',23,'#b91c1c' if name=='block' else '#334155'))
 xy={v:(100+x*1200/max(1,len(leaves)-1),190+y*90) for v,(x,y) in pos.items()}
 for a,b in edges:body.append(line(*xy[a],*xy[b]))
 for v,(x,y) in xy.items():
  if v[0]=='b':
   size=len(B[v[1]]);fill='#1e3a8a' if size>2 else '#475569';body.append(f'<rect x="{x-55}" y="{y-20}" width="110" height="40" rx="9" fill="{fill}"/>');body.append(text(x,y+6,f'B{v[1]} |V|={size}',14,'white'))
  else:
   body.append(f'<circle cx="{x}" cy="{y}" r="22" fill="#eab308" stroke="#a16207"/>');body.append(text(x,y+5,str(v[1]),14))
 body.append(text(W/2,HH-34,'Blue/gray = complete vertex blocks; gold = articulation vertices. This branch has at most 234 edges.',18))
 (O/'q9_block_prune.svg').write_text(svg(W,HH,body),encoding='utf-8')
def counter():
 P={0:(200,110),1:(350,110),3:(440,230),7:(350,350),6:(200,350),4:(110,230),11:(600,230),14:(200,465)};path=[0,1,3,7,6,14];selected={frozenset((a,b)) for a,b in zip(path,path[1:])};body=[text(400,37,'Counterexample to dropping off-chain cut vertices',25)]
 for i,a in enumerate(P):
  for b in list(P)[i+1:]:
   if (a^b).bit_count()==1:body.append(line(*P[a],*P[b],'#dc2626' if frozenset((a,b)) in selected else '#94a3b8',5 if frozenset((a,b)) in selected else 2))
 for v,(x,y) in P.items():
  fill='#facc15' if v in [3,6] else ('#bfdbfe' if v in path else '#e2e8f0');body.append(f'<circle cx="{x}" cy="{y}" r="24" fill="{fill}" stroke="#334155"/>');body.append(text(x,y+6,v,19))
 body.extend([text(510,380,'Red: a valid 6-vertex induced path',16),text(440,540,'Both gold vertices belong to the whole C6 block, even when only one branch is chosen.',16),text(400,575,'An unsafe partial-block count can incorrectly reduce the capacity to 4.',17,'#b91c1c')]);(O/'off_chain_counterexample.svg').write_text(svg(810,610,body),encoding='utf-8')
def bars():
 r=json.loads((H/'bank152_benchmarks.json').read_text())['runs'];body=[text(500,40,'Eight fixed-prefix exclusions: nodes explored',25)];sums={'leaf':0,'block':0}
 for i in range(8):
  rr=[x for x in r if x['entry']==i];y=95+i*58;body.append(text(65,y+20,f'entry {i}',15))
  for j,m in enumerate(['leaf','block']):
   val=next(x['stats']['nodes'] for x in rr if x['mode']==m);sums[m]+=val;color='#94a3b8' if m=='leaf' else '#2563eb';body.append(f'<rect x="145" y="{y+j*20}" width="{val*2.4}" height="16" fill="{color}"/>');body.append(text(155+val*2.4,y+j*20+13,str(val),14,anchor='start'))
 body.extend([text(500,594,f"Gray: leaf baseline {sums['leaf']} nodes; blue: block {sums['block']} nodes ({100*(1-sums['block']/sums['leaf']):.1f}% fewer).",19),text(500,628,'All are restricted 152-vertex bank prefixes; this is not a new global theorem or a runtime speedup claim.',15)]);(O/'bank_prefix_nodes.svg').write_text(svg(1000,660,body),encoding='utf-8')
def claw_progress():
 vals=[('Reachable region',165,'#94a3b8'),('Parity',164,'#64748b'),('Leaf peeling',155,'#475569'),('Whole-block chains',152,'#2563eb'),('Disjoint claws + endpoint',131,'#059669')]
 body=[text(600,40,'One Q9 branch: graph-theoretic capacity hierarchy',26),text(600,78,'The same 84-vertex prefix; a 235-edge target needs 153 suffix vertices.',18)]
 for i,(label,value,color) in enumerate(vals):
  y=135+i*72;body.append(text(285,y+25,label,19,anchor='end'));body.append(f'<rect x="310" y="{y}" width="{value*4.5}" height="38" rx="5" fill="{color}"/>');body.append(text(323+value*4.5,y+26,str(value),20,anchor='start'))
 x=310+153*4.5;body.append(line(x,115,x,482,'#dc2626',2));body.append(text(x,516,'Required: 153',18,'#b91c1c'))
 body.extend([text(600,563,'33 disjoint groups certify that at least 34 of the 165 residual vertices must be omitted.',18),text(600,602,'Suffix <=131 vertices implies <=213 edges for THIS prefix. The global target remains UNKNOWN.',17,'#065f46')])
 (O/'claw_capacity.svg').write_text(svg(1200,640,body),encoding='utf-8')

real();counter();bars();claw_progress();print('Wrote 4 SVG figures.')
# Raster previews of these simple generated SVG elements, using Pillow only.
from xml.etree import ElementTree as ET
from PIL import Image,ImageDraw,ImageFont
for src in sorted(O.glob('*.svg')):
 tree=ET.fromstring(src.read_text());ww=int(tree.attrib['width']);hh=int(tree.attrib['height']);im=Image.new('RGB',(ww,hh),'#f8fafc');draw=ImageDraw.Draw(im)
 for e in tree.iter():
  tag=e.tag.split('}')[-1];a=e.attrib
  if tag=='line':draw.line(tuple(float(a[k]) for k in ['x1','y1','x2','y2']),fill=a.get('stroke','#000000'),width=int(a.get('stroke-width',1)))
  elif tag=='rect' and '%' not in a.get('width',''):
   x=float(a.get('x',0));y=float(a.get('y',0));w=float(a['width']);h=float(a['height']);draw.rounded_rectangle((x,y,x+w,y+h),radius=float(a.get('rx',0)),fill=a.get('fill','white'))
  elif tag=='circle':
   x=float(a['cx']);y=float(a['cy']);r=float(a['r']);draw.ellipse((x-r,y-r,x+r,y+r),fill=a.get('fill','white'),outline=a.get('stroke'))
  elif tag=='text':
   x=float(a['x']);y=float(a['y']);font=ImageFont.truetype('C:/Windows/Fonts/segoeui.ttf',int(a.get('font-size',17)));anchor={'middle':'ms','end':'rs'}.get(a.get('text-anchor'),'ls');draw.text((x,y),e.text or '',font=font,fill=a.get('fill','#000000'),anchor=anchor)
 im.save(src.with_suffix('.png'))
print('Wrote 4 PNG previews.')
