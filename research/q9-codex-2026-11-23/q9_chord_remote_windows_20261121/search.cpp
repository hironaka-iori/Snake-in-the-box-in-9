#define PORTS_LIBRARY
#include "../search_q9_port_matching.cpp"
#include <utility>
using Pieces=vector<pair<int,int>>;
vector<pair<int,int>> extra(const Path&p){
 set<int> verts(p.begin(),p.end());assert(verts.size()==p.size());vector<pair<int,int>> out;
 for(int i=0;i<(int)p.size();i++){assert(p[i]>=0&&p[i]<512);if(i)assert(distanceQ(p[i],p[i-1])==1);
  for(int j=0;j+1<i;j++)if(distanceQ(p[i],p[j])==1)out.push_back({j,i});}return out;
}
Pieces core(int n,int a,int b,int c,int d){
 Pieces keep;for(int i=0;i<n;){if((a<=i&&i<=b)||(c<=i&&i<=d)){i++;continue;}int j=i;
 while(j+1<n&&!(a<=j+1&&j+1<=b)&&!(c<=j+1&&j+1<=d))j++;
 if(j>i)keep.emplace_back(i,j);i=j+1;}return keep;
}
int main(int argc,char**argv){
 if(argc!=6&&argc!=7)return 2;set<array<int,5>> pending;if(argc==7){ifstream f(argv[6]);string line;while(getline(f,line)){istringstream in(line);string tag;in>>tag;if(tag!="INCOMPLETE")continue;array<int,5> t;for(int &v:t)in>>v;pending.insert(t);}}int radius=stoi(argv[1]),width=stoi(argv[2]),nodecap=stoi(argv[3]),routecap=stoi(argv[4]),mode=stoi(argv[5]);
 int row=0;uint64_t tc=0,tu=0,tn=0,ts=0,tdup=0,tm=0;string line;
 while(getline(cin,line)){Path p;istringstream in(line);int v;while(in>>v)p.push_back(v);auto bad=extra(p);assert(bad.size()==1);auto [x,y]=bad[0];int n=p.size(),goal=n-1;
  assert(mode||n==193);uint64_t cases=0,unknown=0,nodes=0,partial=0,duplicates=0,raw=0;set<Pieces> seen;
  for(int end:{x,y}){int a=max(0,end-radius),b=min(n-1,end+radius);
   for(int c=0;c+width<=n;c++){int e=c+width-1;if(!(e+1<a||b+1<c))continue;
    if(argc==7&&!pending.count({row,a,b,c,e}))continue;auto pieces=core(n,a,b,c,e);if(mode&&pieces.size()!=3)continue;
    if(mode)swap(pieces[0],pieces[1]);raw++;
    if(!seen.insert(pieces).second){duplicates++;continue;}
    int kept=0;for(auto [lo,hi]:pieces)kept+=hi-lo+1;int missing=n-kept;assert(kept>0);
    Ports s;bool found=s.run(p,pieces,goal,missing+1,missing,nodecap,routecap);
    cases++;unknown+=s.cutoff||s.incomplete;partial+=s.incomplete;nodes+=s.nodes;
    if(found){assert(valid(s.witness));cout<<(mode?"CONTROL":"FOUND")<<" row "<<row<<" windows "<<a<<" "<<b<<" "<<c<<" "<<e<<" piece_order";for(auto [lo,hi]:pieces)cout<<" "<<lo<<"-"<<hi;cout<<" vertices";for(int v:s.witness)cout<<" "<<v;cout<<endl;return 0;}
    if(s.cutoff||s.incomplete)cout<<"INCOMPLETE "<<row<<" "<<a<<" "<<b<<" "<<c<<" "<<e<<" "<<s.cutoff<<" "<<s.incomplete<<endl;
   }
  }
  if(mode)return 4;
  cout<<"ROW "<<row<<" unique "<<cases<<" unresolved "<<unknown<<" duplicate "<<duplicates<<" nodes "<<nodes<<" partial_routes "<<partial<<endl;
  tc+=cases;tu+=unknown;tn+=nodes;ts+=partial;tdup+=duplicates;tm+=raw;row++;
 }
 cout<<"DONE rows "<<row<<" physical_windows "<<tm<<" unique "<<tc<<" resolved_negative "<<tc-tu<<" unresolved "<<tu<<" duplicates "<<tdup<<" nodes "<<tn<<" partial_routes "<<ts<<endl;return 0;
}
