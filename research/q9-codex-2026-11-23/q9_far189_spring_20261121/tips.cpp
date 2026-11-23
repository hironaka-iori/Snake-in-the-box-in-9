#define Q9_FIXED_BRIDGE_NO_DRIVER
#include "../search_q9_fixed_bridge.cpp"
#include <deque>
#include <set>
#include <map>
using P=vector<int>;
string word(const P& p){auto s=key(p);for(char&c:s)c+='0';return s;}
P decode(const string&s){P p{0};for(char c:s)p.push_back(p.back()^(1<<(c-'0')));return p;}
struct Tips{
 array<bool,512> use{};array<int,512>near{};deque<int>p;int nodes=0,cap,goal;bool stop=false;set<string>&seen;map<int,int>&hits;P win;
 void edit(int v,int s){use[v]=s>0;for(int d=0;d<9;d++)near[v^(1<<d)]+=s;}
 void search(bool leftstage){
  if(++nodes>cap){stop=true;return;}
  int n=p.size()-1;
  if(n>=190){P q(p.begin(),p.end());string w=word(q);if(seen.insert(w).second){hits[n]++;cout<<"PATH "<<n<<" "<<w<<'\n';}
   if(n>=goal){win=q;return;}}
  if(!leftstage||!win.empty()){}else{search(false);if(stop||!win.empty())return;}
  int tip=leftstage?p.front():p.back();
  for(int d=0;d<9;d++){int x=tip^(1<<d);if(use[x]||near[x]!=1)continue;
   edit(x,1);if(leftstage)p.push_front(x);else p.push_back(x);search(leftstage);if(leftstage)p.pop_front();else p.pop_back();edit(x,-1);
   if(stop||!win.empty())return;
  }
 }
 bool run(const P&q){for(int v:q){edit(v,1);p.push_back(v);}search(true);return !win.empty();}
};
int main(int argc,char**argv){int maxstate=stoi(argv[1]),radius=stoi(argv[2]),cap=stoi(argv[3]),sweep=stoi(argv[4]);mt19937 gen(56781);
 set<string> bank,seen;deque<string> queue;string s;while(cin>>s){bank.insert(s);queue.push_back(s);}int i=0;long long calls=0,cut=0,nodes=0,considered=0;map<int,int>hits;
 auto submit=[&](const P&q){if(q.size()<189)return;Walk t(9,q);if(t.E)return;if(bank.size()>=10000)return;
    string k=word(q);if(bank.insert(k).second){if(q.size()>=190)queue.push_front(k);else queue.push_back(k);}};
 while(!queue.empty()&&i<maxstate){s=queue.front();queue.pop_front();P p=decode(s);int n=p.size();Walk w(9,p);w.verify();if(w.E)abort();
   if(i<10||i%8==0){vector<pair<int,int>> shapes;for(int l=0;l<=radius;l++)for(int r=0;r<=radius;r++)shapes.push_back({l,r});shuffle(shapes.begin(),shapes.end(),gen);
    int sd=0;for(auto [l,r]:shapes){if(i>=1&&++sd>sweep)break;P root(p.begin()+l,p.end()-r);Tips z{{},{},{},0,cap,192,false,seen,hits};calls++;
      bool got=z.run(root);nodes+=z.nodes;cut+=z.stop;
      if(got){cout<<"FOUND "<<word(z.win)<<endl;return 0;}}}
   for(int side=0;side<2;side++,reverse(p.begin(),p.end())){
    P q(p.begin()+1,p.end());submit(q);
    for(int d=0;d<9;d++){int x=p.back()^(1<<d);if(w.cnt[x])continue;
      if(w.near[x]==1){P k=p;k.push_back(x);submit(k);}
      if(w.near[x]-(popcount(unsigned(x^p[0]))==1)==1){q.push_back(x);submit(q);q.pop_back();}
    }
    for(int off=1;off<n-1;off++){int x=p[off-1]^p[off]^p[off+1];if(w.cnt[x]||w.near[x]!=2)continue;P q=p;q[off]=x;submit(q);}
    for(int v=2;v<n-2;v++)for(int z=0;z<5;z++){int a=gen()%9,b=gen()%9;if(a==b)continue;int A=1<<a,B=1<<b;P q=p;bool changed=false;
      for(int j=v+1;j<n;j++)if(bool((p[j]^p[v])&A)!=bool((p[j]^p[v])&B)){q[j]^=A|B;changed=true;}
      if(changed){considered++;submit(q);}}
   }i++;if(i%100==0)cout<<"AT "<<i<<" "<<bank.size()<<" "<<nodes<<endl;
 }
 cout<<"DONE "<<i<<" "<<bank.size()<<" "<<queue.size()<<" "<<calls<<" "<<nodes<<" "<<cut<<" "<<considered<<endl;
}
