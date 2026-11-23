#define Q9_FLEX_LIBRARY
#include "../q9_tree_lifts/flexible.cpp"
#include <fstream>
#include <map>
#include <set>
#include <sstream>
using namespace std;
struct AxisMap{array<unsigned short,8> pair{}; bool add(int d,int m){if(pair[d])return pair[d]==m;int parent[9];for(int i=0;i<9;i++)parent[i]=i;auto get=[&](int x){while(x!=parent[x])x=parent[x];return x;};for(int t:pair)if(t){int a=countr_zero(unsigned(t));int b=countr_zero(unsigned(t&(t-1)));parent[get(a)]=get(b);}int a=countr_zero(unsigned(m)),b=countr_zero(unsigned(m&(m-1)));if(get(a)==get(b))return false;pair[d]=m;return true;}};
struct Rule{int dir,block,preferred;};
struct Node{State s;array<AxisMap,2>map;array<uint16_t,205>line{};int left=102,right=102;array<int,2>step{};uint64_t hash=0;};
struct Take{float score;int from,m;uint64_t hash;};
vector<string>donors;vector<P>archive;vector<int>masks;map<string,string>wordbank;
uint64_t salt[512];mt19937_64 rng;long long tested,feasible,rejectMap,candidates,expanded,oddChanges;int global=0,emitted=0;set<string>seenWords;
string canon(string w){map<char,char> m;for(auto &c:w){if(!m.count(c))m[c]=char('0'+m.size());c=m[c];}return w;}
string key(const P&p){string w;for(int i=1;i<p.size();i++)w+=char('0'+countr_zero(unsigned(p[i]^p[i-1])));string a=canon(w);reverse(w.begin(),w.end());return min(a,canon(w));}
void prepare(){for(auto w:donors)for(int refl=0;refl<2;refl++){if(refl)reverse(w.begin(),w.end());for(int j=0;j<w.size();j++)for(int n=1;n<=10&&j+n<=w.size();n++){auto s=w.substr(j,n);wordbank.emplace(canon(s),s);}}}
vector<Rule> fits(const vector<int>&m,int width){vector<Rule> rules;int block=0;for(int j=0;j<m.size();){int n=min(width,int(m.size())-j);string matched;
 for(;n>0;n--){map<int,char>names;string w;AxisMap tree;bool ok=true;for(int k=0;k<n;k++){int mask=m[j+k];if(!names.count(mask))names[mask]=char('0'+names.size());int d=names[mask]-'0';if(d>=8||!tree.add(d,mask)){ok=false;break;}w+=names[mask];}
 if(ok&&wordbank.count(w)){matched=wordbank[w];break;}}
 assert(n>=1);for(int k=0;k<n;k++)rules.push_back({matched[k]-'0',block,m[j+k]});j+=n;block++;}return rules;}
vector<Rule> rules(const vector<int>&truth,int width,int style,int maxsize){vector<Rule>res;if(style)res=fits(truth,width);int b=res.empty()?0:res.back().block+1;while(res.size()<maxsize){auto&w=donors[rng()%donors.size()];int n=width;int j=rng()%(w.size()-n+1);bool rev=rng()%2;for(int k=0;k<n;k++)res.push_back({w[j+(rev?n-k-1:k)]-'0',b,0});b++;}return res;}
int degree1(const Node&p,int v){int count=0;for(int d=0;d<9;d++)count+=p.s.load[(v^(1<<d))>>1]==1;return count;}
int scorelen(const Node&p){return 2*(p.right-p.left)+(degree1(p,p.line[p.left])>0)+(degree1(p,p.line[p.right])>0);}
P restore(const Node&p,bool tails=true){P z;for(int i=p.left;i<=p.right;i++){int x=p.line[i];if(i==p.left&&tails){for(int d=0;d<9;d++)if(p.s.load[(x^(1<<d))>>1]==1){z.push_back(x^(1<<d));break;}}
 if(i>p.left){int y=p.line[i-1],m=x^y;int a=m&-m,b=m^a;int o=p.s.load[(y^a)>>1]==2?y^a:y^b;assert(p.s.load[o>>1]==2);z.push_back(o);}z.push_back(x);
 if(i==p.right&&tails){for(int d=0;d<9;d++)if(p.s.load[(x^(1<<d))>>1]==1){z.push_back(x^(1<<d));break;}}}assert(valid(z));return z;}
int main(int argc,char**argv){
 assert(argc==8);ifstream f(argv[1]);string l;while(getline(f,l)){istringstream in(l);P p;int x;while(in>>x)p.push_back(x);assert(p.size()==192&&valid(p));archive.push_back(p);}ifstream w(argv[2]);while(w>>l)donors.push_back(l);prepare();
 int runs=stoi(argv[3]),beam=stoi(argv[4]),style=stoi(argv[5]),goal=stoi(argv[6]);rng.seed(stoull(argv[7]));for(auto &v:salt)v=rng();for(int a=0;a<9;a++)for(int b=0;b<a;b++)masks.push_back((1<<a)|(1<<b));
 int controls=0,started=0;for(int it=0;it<runs;it++){int id=it%archive.size();auto&p=archive[id];int parity=rng()%2;P ev;for(int i=parity;i<p.size();i+=2)ev.push_back(p[i]);int size=ev.size();assert(size==96);int keep=style==2?64+it%23:55+rng()%36,start=(size-keep<2?0:1+rng()%(size-keep-1));int width=3+rng()%7,offset=ev[start];Node root;root.line[102]=0;
 vector<int>mid,original[2];for(int i=start+1;i<start+keep;i++){int m=ev[i]^ev[i-1];mid.push_back(m);root.s.push(m&-m,m^(m&-m));root.line[++root.right]=root.s.v;root.hash^=salt[root.s.v];}
 auto midRules=fits(mid,width);for(int i=start;i>0;i--)original[0].push_back(ev[i]^ev[i-1]);for(int i=start+keep;i<size;i++)original[1].push_back(ev[i]^ev[i-1]);
 int ws=style==2?1:style==0?0:rng()%2;auto L=rules(original[0],width,ws,100),Rr=rules(original[1],width,ws,100);array<vector<Rule>,2>rr{L,Rr};
 int need=97-keep;int left=style==2?start:clamp(start+int(rng()%11)-5,1,need-1);bool flip=rng()&1;vector<Node>cur{root};int best=scorelen(root);long long switched=0;float temp=1+rng()%24,wp=rng()%4,wo=rng()%3;
 auto observe=[&](const Node&v){int n=scorelen(v);best=max(n,best);if(n<187)return;if(n<global&&n<190)return;auto z=restore(v);auto word=key(z);if(!seenWords.insert(word).second)return;if(emitted>450&&n<192)return;global=max(global,n);emitted++;cout<<"W "<<it<<" "<<id<<" "<<parity<<" "<<start<<" "<<keep<<" "<<width<<" "<<ws<<" "<<v.step[0]<<" "<<v.step[1]<<" "<<n;for(int x:z)cout<<" "<<(x^offset);cout<<endl;};
 started++;int steps=style==2?96-keep:need;for(int t=0;t<steps&&!cur.empty();t++){
  int side;int a0=cur[0].step[0],a1=cur[0].step[1];if(a0==left)side=1;else if(a1==steps-left)side=0;else side=(t+flip)%2;
  long long joinCount=0;vector<Take> choices;unordered_set<uint64_t>seen;for(int si=0;si<cur.size();si++){auto &v=cur[si];int k=v.step[side],x=v.line[side?v.right:v.left];Rule u=rr[side][k];AxisMap map=v.map[side];if(!k||rr[side][k-1].block!=u.block)map={};for(int m:masks){tested++;if(style==2&&m!=u.preferred)continue;if(map.pair[u.dir]&&map.pair[u.dir]!=m)continue;AxisMap c=map;if(!c.add(u.dir,m)){rejectMap++;continue;}v.s.v=x;int a=m&-m,b=m^a;if(!v.s.possible(a,b))continue;int y=x^m;auto hash=v.hash^salt[y];if(!seen.insert(hash^salt[y>>1]).second)continue;
 State g=v.s;g.push(a,b);feasible++;joinCount++;int ext=0;g.v=y;for(int h:masks)ext+=g.possible(h&-h,h^(h&-h));float jitter=temp*(rng()%10000)/10000.;float fav=ws&&m==u.preferred?(style==2?1000:float(rng()%12)):0;choices.push_back({float(wp*.35*g.safe+wo*.45*g.empty+1.0*min(ext,10)+jitter+fav),si,m,hash});}}
  candidates+=choices.size();if(choices.size()>beam){nth_element(choices.begin(),choices.begin()+beam,choices.end(),[](auto&a,auto&b){return a.score>b.score;});choices.resize(beam);}vector<Node>next;for(auto z:choices){auto &v=next.emplace_back(cur[z.from]);int k=v.step[side]++;auto u=rr[side][k];if(!k||rr[side][k-1].block!=u.block)v.map[side]={};assert(v.map[side].add(u.dir,z.m));v.s.v=v.line[side?v.right:v.left];v.s.push(z.m&-z.m,z.m^(z.m&-z.m));int y=v.s.v;if(side)v.line[++v.right]=y;else v.line[--v.left]=y;v.hash=z.hash;observe(v);expanded++;if(global>=goal&&style!=2)goto done;}cur.swap(next);
 }
 if(style==2){assert(best>=190);controls+=best>=191;}
 if(it%100==99)cout<<"AT "<<it+1<<" "<<global<<" "<<expanded<<" "<<controls<<endl;
 }done:cout<<"DONE "<<started<<" controls191 "<<controls<<" best "<<global<<" tested "<<tested<<" feasible "<<feasible<<" retained "<<expanded<<" words "<<seenWords.size()<<endl;
}
