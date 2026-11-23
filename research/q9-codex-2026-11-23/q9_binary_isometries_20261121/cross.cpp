#define main binary_isometries_driver
#include "search.cpp"
#undef main
// Two different one-chord ordered walks. At least one endpoint of the first chord
// must use the second placement, and at least one endpoint of the second chord
// must use the first placement. Enforce the second condition after closure.
bool mix(const Solver &p,const Path&im,int shift,int from,int c,int d,Path&w){
 array<char,512> incl{};array<int,512> q;int n=1;q[0]=from;incl[from]=1;
 auto add=[&](int j){if(!incl[j]){incl[j]=1;q[n++]=j;}};
 for(int k=0;k<n;k++){
  int i=q[k],v=im[i]^shift;
  for(int j:{i-1,i+1})if(j>=0&&j<(int)p.p.size()&&!has_single_bit(unsigned(v^p.p[j])))add(j);
  for(int h=0;h<p.count[v];h++){int j=p.nearby[v][h];if(abs(i-j)>1)add(j);}
  if(incl[c]&&incl[d])return false;
 }
 w=p.p;for(int h=0;h<n;h++)w[q[h]]=im[q[h]]^shift;
 for(int i=0;i<(int)w.size();i++)for(int j=0;j<i;j++)assert(w[i]!=w[j]&&(has_single_bit(unsigned(w[i]^w[j]))==(i==j+1)));
 return true;
}
Perm axes(const Path &p,int pivot){
 Perm map;map.fill(-1);int used=0;
 for(int r=1;r<(int)p.size();r++)for(int i:{pivot+r,pivot+1-r}){
  if(i<1||i>=(int)p.size())continue;int d=countr_zero(unsigned(p[i]^p[i-1]));if(map[d]<0)map[d]=used++;
 }
 assert(used==9);return map;
}
int main(int argc,char**argv){
 if(argc!=4)return 2;int tries=stoi(argv[1]),seed=stoi(argv[2]),rows=stoi(argv[3]);mt19937 rng(seed);
 vector<Solver> bank;string line;while(bank.size()<rows&&getline(cin,line)){istringstream in(line);int v;Path p;while(in>>v)p.push_back(v);bank.emplace_back(p);}
 uint64_t translations=0,closures=0;int pairs=0;
 while(pairs<tries){
  int x=rng()%bank.size(),y=rng()%bank.size();if(x==y)continue;
  const auto &p=bank[x],&don=bank[y];Path q=don.p;int c=don.a,d=don.b;
  if(rng()%2){reverse(q.begin(),q.end());c=q.size()-1-c;d=q.size()-1-d;}
  int pivot=rng()%q.size();
  Perm m=axes(p.p,pivot),h=axes(q,pivot),inv;for(int j=0;j<9;j++)inv[m[j]]=j;
  array<int,512> lookup{};for(int v=1;v<512;v++){int bit=countr_zero(unsigned(v));lookup[v]=lookup[v^(1<<bit)]^(1<<inv[h[bit]]);}
  for(int &v:q)v=lookup[v];
  array<bool,512> possible{};
  for(int i=1;i<(int)q.size();i++)for(int k=0;k<9;k++){possible[q[i-1]^p.p[i]^(1<<k)]=true;possible[q[i]^p.p[i-1]^(1<<k)]=true;}
  for(int sh=0;sh<512;sh++)if(possible[sh]){translations++;for(int from:{p.a,p.b}){closures++;Path w;
   if(mix(p,q,sh,from,c,d,w)){cout<<"FOUND indices "<<x<<" "<<y<<" trial "<<pairs<<" pivot "<<pivot<<" shift "<<sh<<" vertices";for(int v:w)cout<<" "<<v;cout<<endl;return 0;}
  }}
  pairs++;if(pairs%50000==0)cout<<"CHECK "<<pairs<<" translations "<<translations<<" closures "<<closures<<endl;
 }
 cout<<"DONE trials "<<pairs<<" translation_grid "<<uint64_t(pairs)*512<<" passing_crossing_filter "<<translations<<" closures "<<closures<<endl;
}
