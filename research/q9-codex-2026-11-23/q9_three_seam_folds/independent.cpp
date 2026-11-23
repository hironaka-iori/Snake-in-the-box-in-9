#define Q9_SEQUENTIAL_LIBRARY
#include "sequential.cpp"
#include <climits>
using U=uint64_t;using T=uint32_t;
struct Entry{const string* s=nullptr;bool ready=false;vector<string> folds;};
unordered_map<string,T> ids;vector<Entry> dataShape(1);unordered_map<U,bool> seamMemo,tripleMemo;
U windows=0,outerScreen=0,singleScreen=0,exactTrials=0,oracleCalls=0,oracleNodes=0,exactNodes=0,crossTests=0,firstPlacements=0,closedQueries=0;string answer;
T intern(const string&s){auto [it,inserted]=ids.try_emplace(s,dataShape.size());if(inserted){Entry z;z.s=&it->first;dataShape.push_back(move(z));}return it->second;}
struct RegisterPath{
 array<int,512> covered{};array<array<int,9>,2> naming;
 array<unsigned,2> used{};string w[2],result;bool want;U work=0,reachThird=0;
 void block(int v,int delta){covered[v]+=delta;for(int bit=1;bit<512;bit*=2)covered[v^bit]+=delta;}
 RegisterPath(const string& root,string m,string r,bool witness):want(witness){
   for(auto&n:naming)n.fill(-1);w[0]=move(m);w[1]=move(r);
   int v=0;for(char c:root){v^=1<<(c-'A');block(v,1);}if(want)result=string(root.rbegin(),root.rend());}
 bool extend(int part,int i,int v){if(i==w[part].size()){if(part){return true;}reachThird++;return extend(1,0,v);}
   int axis=w[part][i]-'A';int prev=naming[part][axis];unsigned avail=prev<0?(511^used[part]):(1U<<prev);work++;
   for(;avail;avail&=avail-1){unsigned bit=avail&-avail;int x=v^bit;if(covered[x])continue;
      if(prev<0){naming[part][axis]=countr_zero(bit);used[part]^=bit;}if(want)result+='A'+countr_zero(bit);
      block(v,1);if(extend(part,i+1,x))return true;block(v,-1);
      if(want)result.pop_back();if(prev<0){used[part]^=bit;naming[part][axis]=-1;}
   }return false;}
};
bool directInduced(const string&s){array<int,512> occ{};int v=0;occ[0]=1;for(char d:s){v^=1<<(d-'A');if(occ[v])return false;int neighbors=0;for(int b=1;b<512;b*=2)neighbors+=occ[v^b];if(neighbors!=1)return false;occ[v]=1;}return true;}
const vector<string>& folds(T id){auto& e=dataShape[id];if(e.ready)return e.folds;e.ready=true;string w=*e.s;int n=*max_element(w.begin(),w.end())-'A'+1;
 if(n<=9&&directInduced(w))e.folds.push_back(w);
 for(int i=0;i<n;i++)for(int j=0;j<i;j++){string q=w;for(char&c:q)if(c=='A'+i)c='A'+j;q=canonical(q);if(directInduced(q))e.folds.push_back(q);}return e.folds;}
bool seamOK(T x,T y){if(x>y)swap(x,y);U key=U(x)<<32|y;auto it=seamMemo.find(key);if(it!=seamMemo.end())return it->second;oracleCalls++;
 bool ok=false;auto&a=folds(x);auto&b=folds(y);
 for(auto&p:a){for(auto&q:b){bool rev=p.size()<q.size();RegisterPath g(rev?q:p,rev?p:q,"",false);ok=g.extend(0,0,0);oracleNodes+=g.work;if(ok)break;}if(ok)break;}
 seamMemo[key]=ok;return ok;}
U key3(T l,T m,T r){assert(max({l,m,r})<(1<<21));return U(l)<<42|U(m)<<21|r;}
bool construct(T li,T mi,T ri,bool save){bool opposite=dataShape[li].s->size()<dataShape[ri].s->size();auto&L=folds(opposite?ri:li);auto&R=folds(opposite?li:ri);
 for(const string&c:folds(mi)){string m=c;if(opposite)reverse(m.begin(),m.end());
 for(auto&l:L)for(auto&r:R){RegisterPath g(l,m,r,save);bool hit=g.extend(0,0,0);exactNodes+=g.work;crossTests+=g.reachThird;
 if(hit){if(save){answer=g.result;if(opposite)reverse(answer.begin(),answer.end());assert(valid(vertices(answer)));}return true;}}}
 return false;}
bool triple(T l,T m,T mr,T r){U k=min(key3(l,m,r),key3(r,mr,l));auto it=tripleMemo.find(k);if(it!=tripleMemo.end())return it->second;
 bool b=false;if(seamOK(l,m)&&seamOK(mr,r)){exactTrials++;b=construct(l,m,r,false);}else singleScreen++;tripleMemo.emplace(k,b);return b;}
int main(int argc,char**argv){assert(argc==8);ifstream file(argv[1]);int target=stoi(argv[2]),first=stoi(argv[3]),last=stoi(argv[4]),stride=stoi(argv[5]),grid=stoi(argv[6]),phase=stoi(argv[7]);int dimension,row=-1;string line;
 while(getline(file,line)){istringstream in(line);in>>dimension;if(dimension!=10)continue;++row;if(row<first||row>last)continue;Path p;int x;while(in>>x)p.push_back(x);assert(valid(p));string raw;for(int i=1;i<p.size();i++)raw+='A'+countr_zero(unsigned(p[i]^p[i-1]));int n=raw.size();
 vector<array<T,200>> fw(n+1),bw(n+1);for(int at=0;at<=n;at++)for(int dir:{1,-1}){array<int,10> map;map.fill(-1);int count=0;string w;for(int len=1;len<target;len++){int t=dir==1?at+len-1:at-len;if(t<0||t>=n)break;int d=raw[t]-'A';if(map[d]<0)map[d]=count++;w+='A'+map[d];(dir==1?fw:bw)[at][len]=intern(w);}}
 for(int start=phase;start+target<=n;start+=stride){for(int a=1;a<target-1;a++){int j=start+a;
 for(int b=1;a+b<target;b++){windows++;int k=j+b,c=target-a-b;T l=bw[j][a],m=fw[j][b],mr=bw[k][b],r=fw[k][c];int la=max(1,a/grid*grid),rc=max(1,c/grid*grid);
 if((la!=a||rc!=c)&&!triple(bw[j][la],m,mr,fw[k][rc])){outerScreen++;continue;}
 if(!triple(l,m,mr,r))continue;assert(construct(l,m,r,true));auto q=vertices(answer);cout<<"HIT "<<row<<" "<<start<<" "<<a<<" "<<b<<" "<<target<<" "<<answer;for(auto e:q)cout<<" "<<e;cout<<endl;return 0;
 }}if((start/stride)%32==31)cout<<"AT "<<row<<" "<<start<<" "<<windows<<" "<<tripleMemo.size()<<" "<<exactTrials<<" "<<crossTests<<endl;}
 cout<<"ROW "<<row<<" "<<windows<<" "<<outerScreen<<" "<<exactTrials<<" "<<crossTests<<" "<<dataShape.size()<<" "<<tripleMemo.size()<<endl;
 }cout<<"DONE windows "<<windows<<" shortened_rejected "<<outerScreen<<" unique_queried "<<tripleMemo.size()<<" single_seam_rejected "<<singleScreen<<" triple_enumerated "<<exactTrials<<" distinct_seam_queries "<<oracleCalls<<" seam_nodes "<<oracleNodes<<" triple_nodes "<<exactNodes<<" first_placements "<<firstPlacements<<" final_registrations "<<crossTests<<endl;}
