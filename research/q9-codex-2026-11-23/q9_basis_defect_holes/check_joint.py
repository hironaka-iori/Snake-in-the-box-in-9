from run import *
for h in (2,3):
 p=path((R/'q9_gap_generations/prior191.words').read_text().split()[h]);validate(p)
 kept=p[h:];extra=sorted(set(range(512))-set(p),key=lambda x:(-sum((x^v).bit_count()==1 for v in kept),x))[:h-1]
 points=extra+kept;line='points '+' '.join(map(str,points))+'\n'
 (D/f'joint_control{h}.txt').write_text(line)
 out=subprocess.run([str(D/'joint'),'191','80000',str(h)],input=line,text=True,capture_output=True,check=True).stdout
 (D/f'joint_control{h}.log').write_text(out)
 found=next(s for s in out.splitlines() if s.startswith('FOUND '));rm=list(map(int,next(s for s in out.splitlines() if s.startswith('EXTRA ')).split()[1:]))
 w=verify(found,set(points)-set(rm),191)
 assert len(rm)==h-1 and set(rm)==set(extra) and len(w['new_input_points'])==h
 print(h,'discarded',rm,'recovered',len(w['path'])-1)
