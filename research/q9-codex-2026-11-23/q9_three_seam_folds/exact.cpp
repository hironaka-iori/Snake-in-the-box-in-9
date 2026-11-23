#define Q9_SEQUENTIAL_LIBRARY
#include "sequential.cpp"
#include <climits>
using U=uint64_t;using T=uint32_t;
struct Entry{const string* s=nullptr;bool ready=false;vector<string> folds;};
unordered_map<string,T> ids;vector<Entry> dataShape(1);unordered_map<U,bool> seamMemo,tripleMemo;
U windows=0,outerScreen=0,singleScreen=0,exactTrials=0,oracleCalls=0,oracleNodes=0,exactNodes=0,crossTests=0,firstPlacements=0,closedQueries=0;string answer;
T intern(const string&s){auto [it,inserted]=ids.try_emplace(s,dataShape.size());if(inserted){Entry z;z.s=&it->first;dataShape.push_back(move(z));}return it->second;}
const vector<string>& folds(T id){auto&e=dataShape[id];if(e.ready)return e.folds;e.ready=true;auto&w=*e.s;int k=*max_element(w.begin(),w.end())-'A'+1;if(k<10)e.folds.push_back(w);bool forbid[10][10]{};auto p=vertices(w);
 for(int i=0;i<p.size();i++)for(int j=0;j<i-1;j++){unsigned m=p[i]^p[j];int d=popcount(m);if(d>3)continue;assert(d==2||d==3);while(m){int a=countr_zero(m);m&=m-1;for(unsigned rest=m;rest;rest&=rest-1)forbid[a][countr_zero(rest)]=true;}}
 for(int a=0;a<k;a++)for(int b=a+1;b<k;b++)if(!forbid[a][b]){string s=w;for(char &c:s)if(c=='A'+b)c='A'+a;e.folds.push_back(canonical(s));}return e.folds;}
bool seamOK(T a,T b){if(a>b)swap(a,b);U key=(U(a)<<32)|b;auto it=seamMemo.find(key);if(it!=seamMemo.end())return it->second;oracleCalls++;auto &A=folds(a),&B=folds(b);bool possible=false;
 if(!A.empty()&&!B.empty())for(const auto& x:A){for(const auto&y:B){bool swapDir=x.size()<y.size();Glue g(swapDir?y:x,swapDir?x:y);possible=g.search(0,0);oracleNodes+=g.branches;if(possible)break;}if(possible)break;}
 seamMemo.emplace(key,possible);return possible;}
U key3(T l,T m,T r){assert(l<(1<<21)&&m<(1<<21)&&r<(1<<21));return U(l)<<42|U(m)<<21|r;}
bool construct(T li,T mi,T ri,bool want){
 bool rev=dataShape[li].s->size()<dataShape[ri].s->size();const auto&L=folds(rev?ri:li),&R=folds(rev?li:ri);for(auto m:folds(mi)){if(rev)reverse(m.begin(),m.end());for(auto&l:L){
 All first(l,m,0,INT_MAX);first.visit(0,0);assert(!first.cut);exactNodes+=first.nodes;firstPlacements+=first.list.size();
 for(auto&B:first.list){string back(B.w.rbegin(),B.w.rend());back+=l;
 for(auto&r:R){Glue third(back,r);bool hit=third.search(0,0);exactNodes+=third.branches;crossTests++;if(!hit)continue;if(want){answer=string(back.rbegin(),back.rend())+third.word;if(rev)reverse(answer.begin(),answer.end());assert(valid(vertices(answer)));}return true;}}}}return false;}
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
