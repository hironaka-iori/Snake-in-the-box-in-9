#define main anneal_main
#include "coupled.cpp"
#undef main
struct H{array<U,8>m;array<int,9>p;int n=0;};
struct Mate{H h;vector<array<U,8>>perms;};
int main(int argc,char**argv){
 if(argc!=4)return 2;int threshold=stoi(argv[3]);ifstream ff(argv[1]),f(argv[2]);string w;vector<string> orders;while(ff>>w)orders.push_back(w);
 vector<H>a;while(f){H h{};for(int i=0;i<8;i++){if(!(f>>h.m[i]>>h.p[i+1]))break;h.n+=popcount(h.m[i]);}if(f)a.push_back(h);}
 sort(a.begin(),a.end(),[](auto&x,auto&y){return x.n>y.n;});int mx=a[0].n;a.erase(remove_if(a.begin(),a.end(),[&](auto&h){return h.n+mx<threshold;}),a.end());
 array<int,5>p{0,1,2,3,4};vector<array<int,32>>group;do{array<int,32>g{};for(int x=1;x<32;x++)g[x]=g[x&(x-1)]|(1<<p[countr_zero(unsigned(x))]);group.push_back(g);}while(next_permutation(p.begin(),p.end()));
 vector<Mate>b;for(auto h:a){Mate v{h,{}};for(auto &g:group){array<U,8>ms{};for(int k=0;k<8;k++)for(U t=h.m[k];t;t&=t-1)ms[k]|=1u<<g[countr_zero(t)];v.perms.push_back(ms);}b.push_back(move(v));}
 uint64_t total=0;int low=10000;for(int z=0;z<orders.size();z++){
  auto w=orders[z];gray[0]=0;for(int k=0;k<15;k++)gray[k+1]=gray[k]^(1<<(w[k]-'0'));vector<pair<int,int>>edges;vector<int> left,right;
  auto valid=[&](H&h,int base){for(int i=0;i<8;i++)for(int j=i+2;j<8;j++)if(has_single_bit(unsigned(gray[base+i]^gray[base+j]))&&(h.m[i]&h.m[j]))return false;return true;};
  for(int q=0;q<a.size();q++){if(valid(a[q],0))left.push_back(q);if(valid(a[q],8))right.push_back(q);}
  for(int i=0;i<8;i++)for(int j=0;j<8;j++)if(has_single_bit(unsigned(gray[i]^gray[8+j])))edges.push_back({i,j});
  int here=999;uint64_t cases=0;for(int ix:left){auto &h=a[ix];array<U,8> lm;for(int i=0;i<8;i++)lm[i]=shift(h.m[i],h.p[8]);for(int iy:right){
   auto &v=b[iy];if(h.n+v.h.n<threshold)break;for(int j=0;j<120;j++){int c=-1;auto &m=v.perms[j];for(auto [u,vv]:edges)c+=popcount(lm[u]&m[vv]);cases++;
    if(c<here)here=c;if(c<=low){if(c<low){low=c;cout<<"NEAR "<<w<<" "<<c<<" "<<h.n+v.h.n<<" "<<ix<<" "<<iy<<" "<<j<<endl;}
     if(!c){State s;for(int i=0;i<8;i++){s.m[i]=lm[i];s.m[8+i]=m[i];s.p[i]=h.p[i]^h.p[8];s.p[8+i]=group[j][v.h.p[i]];}s.p[16]=group[j][v.h.p[8]];
      for(int q=0;q<32;q++)for(int d=0;d<5;d++)nbs[q]|=1u<<(q^(1<<d));writeBest(s,w,ix,iy);return 0;}}
   }
  }}total+=cases;cout<<"CLASS "<<z<<" "<<left.size()<<" "<<right.size()<<" "<<cases<<" "<<here<<endl;}
 cout<<"DONE halves "<<a.size()<<" threshold "<<threshold<<" tests "<<total<<" min_chords "<<low<<endl;
}
