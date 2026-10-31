"""Reproducible SVG/PNG diagram of the exact critical-cycle obstruction."""
from pathlib import Path
import json,html
from PIL import Image,ImageDraw,ImageFont
H=Path(__file__).resolve().parent;O=H/'figures';O.mkdir(exist_ok=True)
W=1420;HH=790;parts=[]
def text(x,y,s,size=18,color='#0f172a',anchor='middle'):
 parts.append(f'<text x="{x}" y="{y}" font-family="Segoe UI,Arial,sans-serif" font-size="{size}" fill="{color}" text-anchor="{anchor}">{html.escape(str(s))}</text>')
def line(a,b,color='#2563eb',width=3):parts.append(f'<line x1="{a[0]}" y1="{a[1]}" x2="{b[0]}" y2="{b[1]}" stroke="{color}" stroke-width="{width}"/>')
def rect(x,y,w,h,fill):parts.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="8" fill="{fill}"/>')
text(W/2,38,'A minimum-mean model cycle that cannot repeat in a real snake',26)
text(W/2,75,'Four normalized states; total cycle weight 1920 / 4 = 480. The model forgets a longer chord.',18)
C=json.loads((H/'upstream_proved_analysis.json').read_text())['cycle'];positions=[(230,150),(550,150),(870,150),(1190,150)]
for i,e in enumerate(C):
 x,y=positions[i];rect(x-125,y-25,250,50,'#1e3a8a');text(x,y+7,f"C{i}: state {e['u']}",17,'white')
 if i<3:line((x+125,y),(positions[i+1][0]-125,y),'#64748b',2);text((x+positions[i+1][0])/2,y-14,e['weight'],16)
line((1190,178),(1190,220),'#64748b',2);line((1190,220),(230,220),'#64748b',2);line((230,220),(230,178),'#64748b',2);text(710,214,'return weight 480; 7 consecutive edges on this selected cycle are forbidden',17)
text(W/2,281,'Unique overlap lifting forces the literal direction period: 0 1 2 3 4 2 1 5',21)
word=[0,1,2,3,4,2,1,5]*2;vertices=[0]
for d in word:vertices.append(vertices[-1]^(1<<d))
pos={i:(210+150*i,360) for i in range(8)};pos.update({i:(1260-150*(i-8),560) for i in range(8,16)})
for i in range(15):
 line(pos[i],pos[i+1],'#2563eb',3)
 a,b=pos[i],pos[i+1];text((a[0]+b[0])/2,(a[1]+b[1])/2-13,f'd={word[i]}',15,'#334155')
line(pos[15],pos[0],'#dc2626',5)
for i,(x,y) in pos.items():
 parts.append(f'<circle cx="{x}" cy="{y}" r="23" fill="{"#fecaca" if i in [0,15] else "#dbeafe"}" stroke="#334155"/>');text(x,y+6,i,17);text(x,y+44,f'v={vertices[i]}',14,'#475569')
rect(120,439,180,42,'#fff1f2');text(210,467,'Forbidden chord',18,'#b91c1c')
text(W/2,661,'v0 = 0 and v15 = 32: distinct nonconsecutive vertices differing in coordinate 5.',20,'#b91c1c')
text(W/2,701,'At step 16, v16 = 0 repeats the starting vertex. The 15-step prefix already fails inducedness.',18)
text(W/2,749,'This proves a history exclusion. Other critical cycles and the full global upper bound remain unresolved.',17,'#475569')
s=f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{HH}"><rect width="100%" height="100%" fill="#f8fafc"/>'+''.join(parts)+'</svg>';src=O/'critical_cycle_chord.svg';src.write_text(s)
from xml.etree import ElementTree as ET
im=Image.new('RGB',(W,HH),'#f8fafc');draw=ImageDraw.Draw(im)
for e in ET.fromstring(s).iter():
 a=e.attrib;tag=e.tag.split('}')[-1]
 if tag=='line':draw.line(tuple(float(a[k]) for k in ['x1','y1','x2','y2']),fill=a['stroke'],width=int(a['stroke-width']))
 elif tag=='rect' and '%' not in a.get('width',''):
  x=float(a.get('x',0));y=float(a.get('y',0));draw.rounded_rectangle((x,y,x+float(a['width']),y+float(a['height'])),radius=8,fill=a['fill'])
 elif tag=='circle':
  x=float(a['cx']);y=float(a['cy']);r=float(a['r']);draw.ellipse((x-r,y-r,x+r,y+r),fill=a['fill'],outline=a['stroke'])
 elif tag=='text':draw.text((float(a['x']),float(a['y'])),e.text or '',font=ImageFont.truetype('C:/Windows/Fonts/segoeui.ttf',int(a['font-size'])),fill=a['fill'],anchor={'middle':'ms','end':'rs'}.get(a['text-anchor'],'ls'))
im.save(src.with_suffix('.png'));print('Wrote critical-cycle SVG and PNG.')
