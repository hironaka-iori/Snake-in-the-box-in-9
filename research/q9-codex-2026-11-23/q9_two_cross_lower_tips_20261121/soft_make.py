from pathlib import Path
D=Path(__file__).resolve().parent;s=(D/'short_repair.cpp').read_text()
q=s.index('void dfs(int v)')
s=s[:q]+'''array<int,256> price,endPrice;int unit;
int defects(const Pair&s){bool in[256]{};for(int v:s.arm[0])in[v]=1;int cost=-1;for(int y:s.arm[1])cost+=in[y];int x=s.arm[1].back();cost+=2*in[x];for(int d=0;d<8;d++)cost+=in[x^(1<<d)];return cost;}
void nearout(const Pair&s,int run,int time){cout<<"NEAR "<<s.edges()<<" "<<defects(s)<<" "<<run<<" "<<time<<" "<<s.arm[0].size()<<" "<<s.arm[1].size();for(auto&a:s.arm)for(int x:a)cout<<" "<<x;cout<<endl;}
void dfs(int v,int cost)'''+s[q+len('void dfs(int v)'):]
s=s.replace('if((terminal&&endok[v])||v==dest){if(n>=threshold){finished++;if(n>best)best=n,ties=0;if(n==best&&rnd()%++ties==0)picked=path;}', '''if(terminal||v==dest){if(n>=threshold){finished++;int score=12*n-unit*(cost+(terminal?endPrice[v]:0));if(score>best)best=score,ties=0;if(score==best&&rnd()%++ties==0)picked=path;}''')
s=s.replace('dfs(y);','dfs(y,cost+price[y]);')
i=s.index(' terminal=hi==n-1;')
s=s[:i]+''' int costBefore=defects(s);
 if(costBefore&&rnd()%100<68){vector<int>hot;bool mask[256]{};for(int v:b)mask[v]=1;
   for(int j=1;j<n;j++){int v=a[j];if(mask[v]||(side==0&&popcount(unsigned(v^b.back()))<=1))hot.push_back(j);}
   if(side){int v=a.back();for(int u:b)if(popcount(unsigned(u^v))<=1){hot.push_back(n-1);break;}}
   if(!hot.empty()){int h=hot[rnd()%hot.size()];lo=max(0,h-1-int(rnd()%11));hi=min(n-1,h+1+int(rnd()%11));}
 }
'''+s[i:]
i=s.index(' for(int j=1;j<b.size();j++)deny[b[j]]++;');j=s.index(' for(int j=0;j<n;j++)if(j<lo',i)
s=s[:i]+''' price.fill(0);endPrice.fill(0);for(int j=1;j<b.size();j++)price[b[j]]++;
 if(side==0){int x=b.back();price[x]+=2;for(int d=0;d<8;d++)price[x^(1<<d)]++;}
 else for(int v:b){endPrice[v]+=2;for(int d=0;d<8;d++)endPrice[v^(1<<d)]++;}
'''+s[j:]
s=s.replace('best=-1;ties=0;picked.clear();remain=budget;calls++;dfs(a[lo]);','best=-100000;ties=0;picked.clear();remain=budget;calls++;dfs(a[lo],price[a[lo]]);')
s=s.replace('if(best<0)return false;', 'if(picked.empty())return false;')
i=s.index(' for(int run=0;run<runs;run++)');s=s[:i]+''' int mincost=999;
 for(int run=0;run<runs;run++){int id=rnd()%pool.size();for(int k=0;k<6;k++){int v=rnd()%pool.size();if(pool[v].edges()>pool[id].edges())id=v;}
 Pair state=pool[id],elite=state;int rank=1000,local=0;float slope=0.8+float(rnd()%330)/100,baseT=0.35+float(rnd()%140)/100;
 for(int t=0;t<steps;t++){Pair next=state;unit=int(12*slope)+(rnd()%17)-8;if(unit<2)unit=2;
  if(rnd()%67==0){int s=rnd()%2,d=rnd()%8,e=(d+1+rnd()%7)%8;for(auto&v:next.arm[s])if(((v>>d)^(v>>e))&1)v^=(1<<d)|(1<<e);}
  else if(!mutation(next,350+rnd()%1850,upperCap))continue;
  int dc=defects(next),n=next.edges();if(!dc){local=max(local,n);if(n>pool[id].edges())pool[id]=next;if(n>global){global=n;save(next,run,t);if(n>=192)return 0;}}
  if(n>=192&&dc<mincost){mincost=dc;nearout(next,run,t);}
  auto energy=[&](const Pair&z){return (192-z.edges())+slope*defects(z);};
  float gain=energy(state)-energy(next),temp=baseT*(0.18+1-float(t%200)/200);if(gain>=0||((rnd()+0.5)/4294967296.0<exp(gain/temp)))state=next;
  int val=3*max(0,192-n)+4*dc;if(val<rank||(val==rank&&rnd()%9==0)){elite=next;rank=val;}
  if(t%200==199&&rnd()%4){state=elite;}
 }
 if(run%100==99)cout<<"AT "<<run+1<<" best "<<global<<" near "<<mincost<<" nodes "<<nodes<<" calls "<<calls<<" changed "<<changed<<endl;
 }cout<<"DONE "<<runs<<" "<<global<<" "<<mincost<<" "<<nodes<<" "<<calls<<" "<<finished<<" "<<changed<<endl;}
'''
(D/'soft_repair.cpp').write_text(s)
