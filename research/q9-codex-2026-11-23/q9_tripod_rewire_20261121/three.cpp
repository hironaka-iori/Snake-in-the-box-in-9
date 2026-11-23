#define TRIPOD_LIBRARY
#include "rewire.cpp"
struct Triple:Engine{
 P parts[3],x[2];array<bool,512> host{};int each=0,njoin=0,vary=0,maxOutside=-1;string tag;
 unsigned long long connected=0,differentPair=0,stage2=0,calls=0,alltips=0,capHits=0,paths191=0;ofstream longpaths;unordered_set<string> seen191;
 Triple(string name,int goal):Engine(name+".records",goal),longpaths(name+".long"){}
 void assemble(){
  connected++;A=parts[0];A.insert(A.end(),x[0].begin(),x[0].end());A.insert(A.end(),parts[1].begin(),parts[1].end());
  B=parts[2];mid=x[1];P p=A;p.insert(p.end(),mid.begin(),mid.end());p.insert(p.end(),B.begin(),B.end());
  if(!mids.insert(key(word(p))).second)return;localTips=0;provenance=tag;
  extend(A.front(),B.back(),true,int(p.size())-1);
 }
 void extend(int a,int b,bool active,int length){
  if(stopped)return;tipNodes++;if(++localTips>nodeCap){tipCuts++;return;}
  if(length>best)report(length);if(length>=191){
   P p(left.rbegin(),left.rend());p.insert(p.end(),A.begin(),A.end());p.insert(p.end(),mid.begin(),mid.end());p.insert(p.end(),B.begin(),B.end());p.insert(p.end(),right.begin(),right.end());
   int outside=count_if(p.begin(),p.end(),[&](int v){return !host[v];});string w=key(word(p));paths191++;
   bool newword=seen191.insert(w).second;
   if(newword||outside>maxOutside){check(p);longpaths<<length<<" "<<outside<<" "<<tag<<" "<<x[0].size()<<" "<<x[1].size()<<" "<<p.front()<<" "<<word(p)<<endl;}
   maxOutside=max(maxOutside,outside);if(length>=goal){stopped=true;return;}
  }
  if(active)extend(a,b,false,length);int z=active?a:b;auto&arm=active?left:right;
  for(int d=0;d<9&&!stopped&&localTips<=nodeCap;d++){int v=z^(1<<d);if(use[v]||adj[v]!=1)continue;
   mark(v,1);arm.push_back(v);extend(active?v:a,active?b:v,active,length+1);arm.pop_back();mark(v,-1);}
 }
 void connect(int k,int a){
  if(stopped||++localNodes>nodeCap){if(localNodes==nodeCap+1)capHits++;return;}calls++;
  int b=parts[k+1].front();int dist=popcount(unsigned(a^b));auto& arm=x[k];
  if(dist==1){if(k==0){stage2++;connect(1,parts[1].back());}else assemble();return;}
  if(int(arm.size())+dist-1>each)return;
  for(int d=0;d<9&&localNodes<=nodeCap&&!stopped;d++){int v=a^(1<<d);if(use[v])continue;
   bool last=popcount(unsigned(v^b))==1;if(adj[v]!=(last?2:1))continue;mark(v,1);arm.push_back(v);connect(k,v);arm.pop_back();mark(v,-1);}
 }
};
int main(int argc,char**argv){
 if(argc!=7&&argc!=8)return 2;bool rotate=argc==8;bool shift=rotate&&string(argv[7])=="shift";int trim=stoi(argv[1]),perClass=stoi(argv[2]),budget=stoi(argv[3]),bridge=stoi(argv[4]);Triple e(argv[6],stoi(argv[5]));e.nodeCap=budget;e.each=bridge;mt19937 rng(902831+trim);
 ifstream f("arms.words");string line;int idx=-1;
 while(getline(f,line)&&!e.stopped){idx++;replace(line.begin(),line.end(),':',' ');istringstream in(line);P arms[3];e.host.fill(false);e.host[0]=true;
  for(auto&a:arms){string w;in>>w;int v=0;for(char c:w){v^=1<<(c-'0');a.push_back(v);e.host[v]=true;}}
  set<array<int,11>> batch;
  for(int it=0;it<perClass;it++){array<int,11> j{};j[0]=rng()%3;j[1]=rng()%8;int n=it<24?0:rng()%(trim+1);
   for(int i=0;i<n;i++){int k=rng()%6;int h=k/2;if(j[2+2*h]+j[3+2*h]+1<(int)arms[h].size())j[2+k]++;}
   if(rotate){j[8]=rng()%3;j[9]=rng()%9;j[10]=rng()%8;if(j[10]>=j[9])j[10]++;if(j[10]<j[9])swap(j[9],j[10]);}
   if(!batch.insert(j).second)continue;int k=j[0];array<int,3> perm={(k+1)%3,k,(k+2)%3};
   for(int i=0;i<3;i++){int z=perm[i];P& p=e.parts[i];p.assign(arms[z].begin()+j[2+2*z],arms[z].end()-j[3+2*z]);if(j[1]>>i&1)reverse(p.begin(),p.end());}
   if(rotate){P& p=e.parts[j[8]];int anchor=p.front();int x=1<<j[9],y=1<<j[10];bool changed=false;for(int&v:p){int d=v^anchor;if(shift||bool(d&x)!=bool(d&y)){v^=x|y;changed=true;}}if(!changed||(shift&&p.size()<4))continue;}
   bool ok=true;for(auto&p:e.parts){for(int v:p)if(e.use[v]||e.adj[v])ok=false;for(int v:p)e.mark(v,1);}
   if(!ok){for(auto&p:e.parts)for(int v:p)e.mark(v,-1);continue;}
   e.tag=to_string(idx);for(int u=0;u<(rotate?11:8);u++)e.tag+=","+to_string(j[u]);if(shift)e.tag+=",1";e.localNodes=0;e.tries++;e.connect(0,e.parts[0].back());for(auto &p:e.parts)for(int v:p)e.mark(v,-1);if(e.stopped)break;
  }
 }
 cout<<"DONE classes "<<idx+1<<" jobs "<<e.tries<<" bridge_nodes "<<e.calls<<" bridge_cap "<<e.capHits<<" first_bridges "<<e.stage2<<" complete_joins "<<e.connected<<" canonical_mids "<<e.mids.size()<<" tip_nodes "<<e.tipNodes<<" tip_cap "<<e.tipCuts<<" highest "<<e.best<<" distinct191plus "<<e.seen191.size()<<" max_outside "<<e.maxOutside<<endl;
}
