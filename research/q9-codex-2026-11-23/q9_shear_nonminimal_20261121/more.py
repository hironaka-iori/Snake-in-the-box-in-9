from pathlib import Path
import subprocess
D=Path(__file__).resolve().parent;bank=D.parent/'q9_gap_generations/prior191.words'
for en,lo,hi in ((190,8,8),(188,8,8),(186,1,8),(184,1,8)):
 for flag in ('f','i'):
  name=f'{flag}{en}'+('h' if lo==8 else '')
  with bank.open('rb') as src,(D/(name+'.log')).open('wb') as log:
   subprocess.run([str(D/'fresh'),str(en),'0','130',str(lo),str(hi),str(D/(name+'.work'))]+(['integral'] if flag=='i' else []),stdin=src,stdout=log,check=True)
