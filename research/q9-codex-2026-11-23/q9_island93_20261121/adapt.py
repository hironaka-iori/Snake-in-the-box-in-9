from pathlib import Path
d=Path(__file__).resolve().parent
f=d.parent/'q9_three_cross_same_repriced_20261121'
s=(f/'replay.cpp').read_text().replace('#include <algorithm>', '#include "port.hpp"\n#include <algorithm>')
b=s.index(' vector<int> seq{0};');e=s.index(' vector<array<unsigned char,256>> sig',b)
s=s[:b]+''' Layout shape(donor,extra);auto &low=shape.low,&port=shape.port,&pool=shape.pool;int lowerSum=shape.delta,m=shape.m;
 LL out=LL(c.scale)*shape.nlow+shape.upper_ends*c.fees[m]+LL(lowerSum)*c.balance;
'''+s[e:]
s=s.replace('degree==1&&p!=m','degree==1&&shape.upper_ends&&p!=m').replace('ifstream f(argv[1]);string w;while(f>>w)words.push_back(w);','read_mothers(argv[1]);')
s=s.replace('assert(best>-1000000000000LL);out+=best;', 'if(best==-1000000000000LL)return -1000000000000LL;out+=best;')
(d/'replay.cpp').write_text(s)
s=(f/'diffuse.cpp').read_text().replace('ifstream f(argv[1]);string w;while(f>>w)words.push_back(w);','read_mothers(argv[1]);')
b=s.index(' array<bool,256>low{}');e=s.index(' vector<Vtx>',b)
s=s[:b]+''' Layout shape(i,x);auto &low=shape.low,&port=shape.port,&pool=shape.pool;
 int m=shape.m,delta=shape.delta,nlow=shape.nlow;
 gen.seed(872913+65537*i+991*x);
'''+s[e:]
b=s.index(' for(int v=0;v<256;v++){pool');e=s.index(' for(int v=0;v<256;v++)if(pool',b)
s=s[:b]+s[e:]
s=s.replace('deg==1&&popcount','deg==1&&shape.upper_ends&&popcount').replace('int total=fee+bal*delta','int total=shape.upper_ends*fee+bal*delta').replace('+cert.fees[m];\n  for(auto&q:vtx)', '+shape.upper_ends*cert.fees[m];\n  for(auto&q:vtx)').replace('assert(best!=neg);','if(best==neg)continue;')
b=s.index(' const int neg=')
s=s[:b]+''' bool empty=false;for(auto &q:vtx)if(q.v>=0&&q.st.empty())empty=true;for(auto&g:faces)empty|=g.st.empty();
 if(empty){assert(score(i,x,cert)==-1000000000000LL);cout<<"R "<<i<<" "<<x<<" -1000000000000 10000 0 0 0 0\\nE"<<endl;continue;}
'''+s[b:]
s=s.replace('array<unsigned char,12>','array<unsigned char,24>').replace('part[12]{},pos[12]{}','part[24]{},pos[24]{}').replace('K<=12','K<=24')
(d/'diffuse.cpp').write_text(s)
