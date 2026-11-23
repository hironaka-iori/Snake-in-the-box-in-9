#define Q9_REM_LIBRARY
#include "remove.cpp"
int main(int argc,char**argv){
 int kept=argc>1?stoi(argv[1]):94;maxEven=99;keepCap=1;
 Edges ed{};ed[0]={0,1};ed[1]={1,2};grow(ed,3);
 set<array<uint8_t,9>> fr;
 for(const Tree& tr:trees){
    array<uint8_t,9> key{};for(int j=0;j<7;j++)for(int c=0;c<9;c++)if(tr.masks[j]&(1<<c))key[c]|=1<<j;
    sort(key.begin(),key.end());fr.insert(key);
 }
 vector<array<int,7>> independent;
 for(auto& key:fr){array<int,7> b{};for(int c=0;c<9;c++)for(int i=0;i<7;i++)if(key[c]>>i&1)b[i]|=1<<c;independent.push_back(b);}
 cout<<"FORESTS "<<fr.size()<<endl;
 Tree chart;chart.off[0]=0;for(int j=0;j<8;j++){chart.off[j+1]=1<<j;chart.masks[j]=1|(2<<j);}
 string w;int row=-1;
 while(cin>>w){
    row++;Path p{0};for(char d:w)p.push_back(p.back()^(1<<(d-'0')));array<int,256> collision{};
    for(size_t i=0;i<p.size();i++)for(size_t j=0;j<i;j++)collision[p[i]^p[j]]++;
    uint64_t kernels=0,geoms=0,pre=0,finals=0;
    for(int rel=1;rel<256;rel++)if(popcount(unsigned(rel))>=2 && int(p.size())-collision[rel]>=kept){
       kernels++;int removed=bit_width(unsigned(rel))-1;
       for(auto& b:independent){
           Tree code;int last=0,j=0;
           for(int axis=0;axis<8;axis++)if(axis!=removed){
               code.masks[axis]=b[j++];if(rel>>axis&1)last^=code.masks[axis];}
           if(popcount(unsigned(last))!=2)continue;code.masks[removed]=last;geoms++;
           array<bool,256> have{};Path src;for(int x:p){int v=image(x,code)>>1;if(!have[v]){have[v]=true;src.push_back(v);}}
           assert(int(src.size())==int(p.size())-collision[rel]);
           array<int,256> ld{};int pairs=0;
           for(int v:src)for(int o:chart.off)ld[v^o]++;
           for(int a:ld)pairs+=a==2;
           int k=src.size()-kept;if(pairs+9*k<2*kept-maxEven-1)continue;
           pre++;Donor donor(src);Rem r(donor,chart,k,pairs,true);r.dfs(0,k);finals+=r.finals;
       }
    }
    cout<<"ROW "<<row<<" "<<kernels<<" "<<geoms<<" "<<pre<<" "<<finals<<endl;
 }
}
