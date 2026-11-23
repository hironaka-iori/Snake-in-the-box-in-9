#define Q9_FLEX_LIBRARY
#include "../q9_tree_lifts/flexible.cpp"
#include <fstream>
#include <sstream>
#include <set>
using U=uint64_t;
struct Edge{int mask,next;};struct Trie{vector<Edge> kids;int leaf=-1,desc=-1,maxRank=-1;};
vector<Trie> trie(1);vector<P>arms;vector<int>indices,rankOf;int cutRank=-1;array<int,9> image;int used=0,which=-1,best=0,control=0;
U states=0,attempts=0,pairs=0,full=0,limit=0,local=0,capped=0,deep=0,rows=0;
bool hit=false;set<string>saved;array<U,55>levels{};
string key(const P&p){string w;for(int j=0;j+1<p.size();j++)w+=char('0'+countr_zero(unsigned(p[j]^p[j+1])));auto norm=[](string s){array<int,9>a;a.fill(-1);int n=0;for(char&c:s){int d=c-'0';if(a[d]<0)a[d]=n++;c='0'+a[d];}return s;};auto orig=norm(w);reverse(w.begin(),w.end());return min(orig,norm(w));}
void insert(const P&ms,int id){int node=0;for(int m:ms){int child=-1;for(auto e:trie[node].kids)if(e.mask==m)child=e.next;if(child<0){child=trie.size();trie[node].kids.push_back({m,child});trie.emplace_back();}node=child;trie[node].desc=id;if(!rankOf.empty())trie[node].maxRank=max(trie[node].maxRank,rankOf[id]);}trie[node].leaf=id;}
State seed(const P&ms){State s;for(auto it=ms.rbegin();it!=ms.rend();it++){int m=*it,a=m&-m;assert(s.possible(a,m^a));s.push(a,m^a);}return s;}
int tip(const State&s,int v){for(int b=1;b<512;b*=2)if(s.load[(v^b)>>1]==1)return v^b;return -1;}
void out(const State&s,int node,int depth){int lo=tip(s,0),hi=tip(s,s.v),n=2*s.k+(lo>=0)+(hi>=0);if(n<188||n<best)return;
 if(n>=192)hit=true;auto p=s.witness();if(lo>=0)p.insert(p.begin(),lo);if(hi>=0)p.push_back(hi);assert(valid(p));auto k=key(p);if(n>best){best=n;saved.clear();}if(saved.size()>250||!saved.insert(k).second)return;
 cout<<"W "<<n<<" "<<which<<" "<<trie[node].desc<<" "<<depth<<" "<<lo<<" "<<hi;for(int d:image)cout<<" "<<d;for(int v:p)cout<<" "<<v;cout<<endl;}
void visit(const State&s,int node,int depth){
 if(hit||local>=limit)return;states++;local++;levels[depth]++;if(depth>=46){deep++;out(s,node,depth);if(hit)return;}if(trie[node].leaf>=0){full++;if(control){auto p=s.witness();assert(valid(p));cout<<"CONTROL "<<which<<" "<<2*s.k;for(int x:p)cout<<" "<<x;cout<<endl;hit=true;}return;}
 for(auto [m,child]:trie[node].kids){if(trie[child].maxRank<cutRank)continue;int p=countr_zero(unsigned(m)),q=countr_zero(unsigned(m&(m-1)));int f=image[p],g=image[q];unsigned free=511^used;
 unsigned ai=f<0?free:(1U<<f);for(;ai;ai&=ai-1){unsigned a=ai&-ai;unsigned bi=g<0?(free&~a):(1U<<g);
 for(;bi;bi&=bi-1){unsigned b=bi&-bi;attempts++;if(!s.possible(a,b))continue;if(f<0)image[p]=countr_zero(a),used^=a;if(g<0)image[q]=countr_zero(b),used^=b;
 State t=s;t.push(a,b);visit(t,child,depth+1);
 if(f<0)image[p]=-1,used^=a;if(g<0)image[q]=-1,used^=b;if(hit||local>=limit)return;}}}}
int main(int argc,char**argv){assert(argc==7);ifstream f(argv[1]),order(argv[2]);string l;while(getline(f,l)){istringstream in(l);P a;int m;while(in>>m)a.push_back(m);assert(a.size()==48);arms.push_back(a);}
 int n;while(order>>n)indices.push_back(n);int start=stoi(argv[3]),count=stoi(argv[4]);limit=stoull(argv[5]);int mode=stoi(argv[6]);
 rankOf.resize(arms.size());for(int i=0;i<indices.size();i++)rankOf[indices[i]]=i;for(int j=0;j<arms.size();j++)insert(arms[j],j);cout<<"TRIE "<<arms.size()<<" "<<trie.size()<<endl;image.fill(-1);
 for(int i=start;i<min(int(indices.size()),start+count);i++){which=indices[i];cutRank=mode?i:-1;auto s=seed(arms[which]);local=0;rows++;visit(s,0,0);capped+=local>=limit;if(hit)break;
 if(rows%100==0)cout<<"AT "<<rows<<" "<<states<<" "<<attempts<<" "<<best<<" "<<capped<<endl;}
 cout<<"DONE rows "<<rows<<" states "<<states<<" attempts "<<attempts<<" depth46plus "<<deep<<" full "<<full<<" best "<<best<<" capped "<<capped<<" hit "<<hit<<endl;
 cout<<"DEPTH";for(int i=0;i<=48;i++)cout<<" "<<levels[i];cout<<endl;}
