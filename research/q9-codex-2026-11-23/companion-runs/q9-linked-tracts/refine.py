from pathlib import Path
r=Path(__file__).resolve().parent
s=(r/'sweep.cpp').read_text()
i=s.index('for(int x:base)mark(x,1);P left,right;localGrow=0;bool found=')
j=s.index('\n if(found){',i)
s=s[:i]+'''bool found=false;int actualSize=base.size();
 for(int loss=0;loss<=8&&!found;loss++)for(int el=0;el<=loss&&!found;el++){
  int er=loss-el;if(n-loss<target-14 || dl+el>=A.i || dr+er>=int(p.size())-B.j)continue;
  P trial(base.begin()+el,base.end()-er);for(int x:trial)mark(x,1);
  P left,right;localGrow=0;found=grow(trial,left,right,0,target+1-int(trial.size()));if(localGrow>extensionCap)capped++;
  for(int x:trial)mark(x,-1);if(found)actualSize=trial.size();
 }
'''+s[j:]
s=s.replace('witnessExtra=witness.size()-base.size();','witnessExtra=witness.size()-actualSize;')
(r/'regrow.cpp').write_text(s)
s=(r/'sweep.cpp').read_text()
s=s.replace('if(hi>=0&&(hi-low>65||(low<i&&hi>j)))return;','if(hi>=0&&hi-low>145)return;')
i=s.index(' bool run(){build();')
j=s.index('\n};',i)
s=s[:i]+''' bool run(){build();sort(tr.begin(),tr.end(),[](auto&a,auto&b){return a.i<b.i;});long long budget=0;
 for(int i=0;i<tr.size();i++){auto&A=tr[i];M aExtra=minusM(A.clash,tipmask);bool leftBad=false;for(int x=0;x<=A.i;x++)if(has(aExtra,x))leftBad=true;if(leftBad)continue;
 for(int j=i+1;j<tr.size();j++){auto&B=tr[j];if(B.i-A.j<3)continue;M pending=minusM(plusM(minusM(A.clash,B.del),minusM(B.clash,A.del)),tipmask);
 bool forcedLeft=false;for(int x=0;x<=B.j;x++)if(has(pending,x))forcedLeft=true;if(forcedLeft)continue;
 for(int k=j+1;k<tr.size();k++){auto&C=tr[k];if(C.i-B.j<3)continue;
 if(++budget>300000)return false;++combinations;if(weight(minusM(pending,C.del)))continue;
 if(weight(minusM(minusM(minusM(C.clash,A.del),B.del),tipmask)))continue;
 M all=plusM(A.clash,plusM(B.clash,C.clash));int dl=0,dr=0;for(int x=0;x<4;x++){if(has(all,x))dl=x+1;if(has(all,p.size()-1-x))dr=x+1;}
 if(int(p.size())+A.gain+B.gain+C.gain-dl-dr<target-6)continue;++compatible;P v;
 v.insert(v.end(),p.begin()+dl,p.begin()+A.i+1);v.insert(v.end(),A.inner.begin(),A.inner.end());v.insert(v.end(),p.begin()+A.j,p.begin()+B.i+1);v.insert(v.end(),B.inner.begin(),B.inner.end());v.insert(v.end(),p.begin()+B.j,p.begin()+C.i+1);v.insert(v.end(),C.inner.begin(),C.inner.end());v.insert(v.end(),p.begin()+C.j,p.end()-dr);
 if(!valid(v))continue;++baselines;bridgeComb+=bool(A.extra+B.extra+C.extra);compensated+=bool(weight(minusM(all,tipmask)));
 for(int t=0;t<5;t++){int l=t&1?2:0,r=t&2?2:0;if(t==4)l=r=3;if(dl+l>=A.i||dr+r>=int(p.size())-C.j)continue;
 P conf(v.begin()+l,v.end()-r);for(int x:conf)mark(x,1);P ls,rs;localGrow=0;bool f=grow(conf,ls,rs,0,target+1-int(conf.size()));if(localGrow>extensionCap)capped++;for(int x:conf)mark(x,-1);
 if(f){if(!valid(witness))abort();witnessExtra=witness.size()-conf.size();return true;}}
 }}}return false;}
'''+s[j:]
(r/'triple.cpp').write_text(s)

