from pathlib import Path
import html,json
from xml.etree import ElementTree as ET
from PIL import Image,ImageDraw,ImageFont
H=Path(__file__).resolve().parent;O=H/'figures';O.mkdir(exist_ok=True)

def render(name,W,HH,parts):
 s=f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{HH}"><rect width="100%" height="100%" fill="#f8fafc"/>'+''.join(parts)+'</svg>';p=O/(name+'.svg');p.write_text(s,encoding='utf-8');im=Image.new('RGB',(W,HH),'#f8fafc');d=ImageDraw.Draw(im)
 for e in ET.fromstring(s).iter():
  a=e.attrib;tag=e.tag.split('}')[-1]
  if tag=='line':d.line(tuple(float(a[k]) for k in ['x1','y1','x2','y2']),fill=a['stroke'],width=int(a.get('stroke-width',2)))
  elif tag=='rect' and '%' not in a.get('width',''):
   x=float(a.get('x',0));y=float(a.get('y',0));d.rounded_rectangle((x,y,x+float(a['width']),y+float(a['height'])),radius=float(a.get('rx',5)),fill=a['fill'])
  elif tag=='circle':
   x=float(a['cx']);y=float(a['cy']);r=float(a['r']);d.ellipse((x-r,y-r,x+r,y+r),fill=a['fill'],outline=a.get('stroke'))
  elif tag=='text':d.text((float(a['x']),float(a['y'])),e.text or '',font=ImageFont.truetype('C:/Windows/Fonts/segoeui.ttf',int(a.get('font-size',18))),fill=a.get('fill','#0f172a'),anchor={'middle':'ms','end':'rs'}.get(a.get('text-anchor'),'ls'))
 im.save(p.with_suffix('.png'))
def txt(p,x,y,s,size=18,color='#0f172a',anchor='middle'):p.append(f'<text x="{x}" y="{y}" font-size="{size}" fill="{color}" text-anchor="{anchor}" font-family="Segoe UI,Arial,sans-serif">{html.escape(str(s))}</text>')
def line(p,a,b,color='#2563eb',w=3):p.append(f'<line x1="{a[0]}" y1="{a[1]}" x2="{b[0]}" y2="{b[1]}" stroke="{color}" stroke-width="{w}"/>')
def rect(p,x,y,w,h,fill):p.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="8" fill="{fill}"/>')
P=[];txt(P,660,37,'A certified forbidden count window in Q9',28);txt(P,660,73,'a,b,c,d,e are distinct coordinates; the highlighted alpha conditions cannot hold together.',18)
pos={i:(180+240*i,190) for i in range(5)};pos.update({i:(1140-240*(i-5),420) for i in range(5,10)});word=['a','b','c','d','b','a','e','c','a'];V=[0,1,3,7,15,13,12,28,24,25]
for i,letter in enumerate(word):
 a,b=pos[i],pos[i+1];line(P,a,b);txt(P,(a[0]+b[0])/2+(35 if a[0]==b[0] else 0),(a[1]+b[1])/2-14,letter,20)
for i,(x,y) in pos.items():
 P.append(f'<circle cx="{x}" cy="{y}" r="28" fill="{"#fef3c7" if i in [3,4,5,7] else "#dbeafe"}" stroke="#334155"/>');txt(P,x,y+7,f'x{i}',18);txt(P,x,y+55,f'cube vertex {V[i]}',14,'#475569')
for i,label in [(3,'alpha3 = 3'),(4,'alpha4 <= 5'),(5,'alpha5 <= 3'),(7,'alpha7 <= 5')]:
 x,y=pos[i];cy=120 if i<5 else 510;rect(P,x-95,cy-25,190,38,'#fef3c7');txt(P,x,cy,label,20,'#92400e')
txt(P,660,589,'Other internal singleton counts are unconstrained in this exclusion.',20)
rect(P,120,620,1080,61,'#e8f1fb');txt(P,660,659,'776 variables | 1052 original clauses | 353 RUP steps | 30020 independently checked hints',19)
txt(P,660,716,'Ordinary computer-assisted local proof; no new global bound and no fresh Lean replay.',17,'#64748b');render('count_window_exclusion',1320,750,P)
P=[];txt(P,650,43,'Progress on the explicit critical subgraph',28);txt(P,650,84,'Four of six original cyclic components removed; surviving mean remains exactly 480.',19)
stages=[('Frozen family','6 SCCs'),('222 edge-ID histories','3 SCCs'),('431 direction histories','2 SCCs'),('+ three count exclusions','2 SCCs')]
for i,(label,value) in enumerate(stages):
 x=45+i*320;rect(P,x,150,280,160,'#1e3a8a');txt(P,x+140,195,label,17,'white');txt(P,x+140,255,value,31,'white')
 if i<3:line(P,(x+282,230),(x+318,230),'#64748b',3)
 txt(P,x+140,360,'mean = 480',21,'#b45309')
rect(P,100,410,1100,100,'#eef5fb');txt(P,650,450,'3 new count-core certificates: 353 + 1264 + 284 RUP steps',21);txt(P,650,485,'24 additional frozen critical records excluded; two large zero-slack components still survive.',17)
txt(P,650,561,'All figures describe the saved frozen subset, not a recomputation of the full current model.',18,'#64748b');render('critical_family_progress',1300,600,P)
print('Wrote two SVG figures and PNG previews.')
