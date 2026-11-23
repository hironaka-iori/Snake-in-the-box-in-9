from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'tract.cpp').read_text().replace('#include <array>','#include <array>\n#include <fstream>\n#include <string>')
i=s.index('struct Work{');s=s[:i]+'''ofstream tracks;int activePair=0,minimumSpan=1;set<string> nearClasses;
string normalize(P const&p){int m[9]={},h=0;string s;for(int i=1;i<p.size();i++){int d=countr_zero(unsigned(p[i]^p[i-1]));if(!m[d])m[d]=++h;s+=('0'+m[d]-1);}return s;}
void logNear(P const&base,P const&l,P const&r){P cand(l.rbegin(),l.rend());cand.insert(cand.end(),base.begin(),base.end());cand.insert(cand.end(),r.begin(),r.end());string a=normalize(cand);reverse(cand.begin(),cand.end());string b=normalize(cand);if(!nearClasses.insert(min(a,b)).second)return;if(!valid(cand))abort();tracks<<activePair;for(int x:cand)tracks<<" "<<x;tracks<<endl;}
'''+s[i:]
s=s.replace('if(L==R||i+1==j)return;', 'if(R-L<minimumSpan||j-i-1<minimumSpan)return;')
s=s.replace('if(++localGrow>extensionCap)return false;++extensions;', 'if(++localGrow>extensionCap)return false;++extensions;if(base.size()+r.size()+l.size()==192)logNear(base,l,r);')
s=s.replace('if(argc!=8)return 2;', 'if(argc!=10)return 2;tracks.open(argv[8]);minimumSpan=atoi(argv[9]);')
s=s.replace('Work w(bank[i],bank[i+1]);','activePair=i/2;Work w(bank[i],bank[i+1]);')
(r/'sweep.cpp').write_text(s)

