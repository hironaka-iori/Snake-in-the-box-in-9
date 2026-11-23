#define main old_main
#include "search.cpp"
#undef main
struct J{
 P p,a,b,sec,q,top,full;A hu{},ha{},lu{},la{};int seed,rev,L,cut,tgt,best=0,cap,nl,nu,permax,upmax,halflimit;long long jobs=0,hcalls=0,lcalls=0,completions=0,probes=0,caps=0,ucaps=0,extensions=0;mt19937 rng{78501};array<int,8> order{0,1,2,3,4,5,6,7};ofstream out;set<string> positives;
 J(string f):out(f){}
 void emit(){int len=full.size()-1;if(len<=best)return;best=len;for(int j=0;j<(int)full.size();j++)for(int i=0;i<j;i++)if(full[i]==full[j]||near(full[i],full[j])!=(i+1==j))abort();out<<len<<" "<<seed<<" "<<L<<" "<<sec.size()-1;for(int v:full)out<<" "<<v;out<<endl;if(len>=192)cout<<"FOUND "<<len<<endl;}
 void extend(int left,bool both){extensions++;emit();if(!left||best>=192)return;if(both){reverse(full.begin(),full.end());extend(left,false);reverse(full.begin(),full.end());}
   int v=full.back()-256;for(int k:order){int x=v^1<<k;if(hu[x]||ha[x]!=1||lu[x])continue;mark(hu,ha,x,1);full.push_back(x+256);extend(left-1,both);full.pop_back();mark(hu,ha,x,-1);if(best>=192)return;}}
 void save(){completions++;full.clear();for(auto i=a.rbegin();i!=a.rend();i++)full.push_back(*i+256);full.insert(full.end(),q.begin(),q.end());for(auto i=top.rbegin();i!=top.rend();i++)full.push_back(*i+256);full.insert(full.end(),sec.begin(),sec.end());for(int v:b)full.push_back(v+256);extend(6,true);}
 void lower(int left){if(best>=192||++nl>permax)return;lcalls++;int v=q.back();if(!left){if(v==tgt)save();return;}if(popcount((unsigned)(v^tgt))>left)return;
  for(int k:order){int x=v^1<<k;if((x==tgt)!=(left==1)||lu[x]||la[x]!=1||(hu[x]&&x!=tgt))continue;mark(lu,la,x,1);q.push_back(x);lower(left-1);q.pop_back();mark(lu,la,x,-1);if(nl>permax||best>=192)break;}}
 void upper(int left){if(best>=192||++nu>upmax)return;hcalls++;int v=top.back();int d=popcount((unsigned)(q.back()^v));if(top.size()>1&&!lu[v]&&la[v]<=1&&d<=L-cut&&((d^(L-cut))&1)==0){
    if(la[v]==0||(d==1&&L-cut==1)){tgt=v;nl=0;probes++;lower(L-cut);caps+=nl>permax;}}
  if(!left)return;for(int k:order){int x=v^1<<k;if(hu[x]||ha[x]!=1||lu[x])continue;mark(hu,ha,x,1);top.push_back(x);upper(left-1);top.pop_back();mark(hu,ha,x,-1);if(nu>upmax||best>=192)break;}}
 void process(){hu={};ha={};lu={};la={};for(int x:a)mark(hu,ha,x,1);for(int x:b)mark(hu,ha,x,1);q=P(p.begin(),p.begin()+cut+1);for(int x:q)mark(lu,la,x,1);for(int x:sec)mark(lu,la,x,1);
   if(hu[sec[0]]||ha[sec[0]])return;top={sec[0]};mark(hu,ha,sec[0],1);nu=0;jobs++;upper(halflimit);ucaps+=nu>upmax;
 }
};
struct Job{int seed,rev,K,cut,j,k,L;};
int main(int argc,char**argv){if(argc!=7)return 1;J r(string(argv[6])+".paths");r.permax=stoi(argv[1]);r.upmax=stoi(argv[2]);r.halflimit=stoi(argv[3]);int maxjob=stoi(argv[4]),mode=stoi(argv[5]);ifstream f("seeds.dat");vector<array<P,3>> records;int id;while(f>>id){array<P,3> e;for(P&v:e)v=readp(f);records.push_back(e);}
 vector<Job> jobs;for(int seed=0;seed<2;seed++)for(int rev=0;rev<2;rev++){auto p=records[seed][0],a=records[seed][1],b=records[seed][2];if(rev){reverse(p.begin(),p.end());swap(a,b);}for(int K=3;K<=8;K++){int s=p[p.size()-K-1];auto good=[&](const P&v){int i=0;for(;i<(int)v.size();i++)if(v[i]==s||near(v[i],s))break;return i;};int am=good(a),bm=good(b);for(int x:{0,3,9})for(int y:{0,3,9}){int an=max(1,am-x),bn=max(1,bm-y);if(an<2||bn<2)continue;
 for(int cut=58;cut<=92-K;cut+=3)for(int L:(mode?P{92,93}:P{74,80,84}))if(L>cut)jobs.push_back({seed,rev,K,cut,an,bn,L});}}}
 shuffle(jobs.begin(),jobs.end(),r.rng);int done=0;for(auto z:jobs){r.seed=z.seed;r.rev=z.rev;r.p=records[z.seed][0];r.a=records[z.seed][1];r.b=records[z.seed][2];if(z.rev){reverse(r.p.begin(),r.p.end());swap(r.a,r.b);}r.a.resize(z.j);r.b.resize(z.k);r.sec=P(r.p.end()-z.K-1,r.p.end());r.cut=z.cut;r.L=z.L;shuffle(r.order.begin(),r.order.end(),r.rng);r.process();if(++done>=maxjob||r.best>=192)break;}
 cout<<"jobs "<<r.jobs<<" hc "<<r.hcalls<<" lc "<<r.lcalls<<" probes "<<r.probes<<" lowercaps "<<r.caps<<" uppercaps "<<r.ucaps<<" actual "<<r.completions<<" extensions "<<r.extensions<<" best "<<r.best<<endl;
}
