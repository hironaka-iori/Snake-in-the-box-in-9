// A source difference z collapses to a forbidden output difference whenever z
// lies in the kernel or differs from a kernel element by a single source bit.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>
using namespace std;
using Mask=uint64_t;using Bits=vector<Mask>;
struct Census{
    int dim,length,nwindows,stride;vector<int> p,representative,group;
    vector<Bits> conflict;uint64_t count=0,nodes=0;int first=-1;vector<int> winning;
    Census(vector<int> path,int d,int len):dim(d),length(len),p(move(path)),representative(d),group(d){
        nwindows=p.size()-length;assert(nwindows>0);stride=(nwindows+63)/64;
        vector<Bits> bad(1<<dim,Bits(stride));
        for(int j=0;j<int(p.size());j++)for(int i=max(0,j-length);i+1<j;i++){
            int z=p[i]^p[j];assert(popcount(unsigned(z))>=2);
            int lo=max(0,j-length),hi=min(i,nwindows-1);if(lo>hi)continue;
            for(int k=lo/64;k<=hi/64;k++){
                Mask m=~Mask(0);if(k==lo/64)m&=~Mask(0)<<(lo%64);
                if(k==hi/64)m&=~Mask(0)>>(63-hi%64);
                bad[z][k]|=m;
            }
        }
        conflict=bad;
        for(int z=1;z<(1<<dim);z++)for(int b=0;b<dim;b++)
            for(int k=0;k<stride;k++)conflict[z][k]|=bad[z^(1<<b)][k];
    }
    void run(int i,int used,const vector<int>& kernel,const Bits& live){
        if(used+dim-i<9)return;++nodes;
        if(i==dim){
            for(int k=0;k<stride;k++)if(live[k]){if(first<0){first=64*k+countr_zero(live[k]);winning=group;}
                count+=popcount(live[k]);}
            return;
        }
        if(used<9){representative[used]=i;group[i]=used;run(i+1,used+1,kernel,live);}
        for(int a=0;a<used;a++){
            int z=(1<<i)|(1<<representative[a]);Bits next=live;vector<int> extended=kernel;bool present=true;
            for(int k:kernel){
                int m=z^k;extended.push_back(m);Mask any=0;
                for(int b=0;b<stride;b++){next[b]&=~conflict[m][b];any|=next[b];}
                if(!any){present=false;break;}
            }
            if(present){group[i]=a;run(i+1,used,extended,next);}
        }
    }
    void solve(){Bits live(stride,~Mask(0));if(nwindows%64)live.back()=(Mask(1)<<(nwindows%64))-1;run(0,0,{0},live);}
};
int main(int argc,char**argv){
    if(argc!=4)return 2;int d=stoi(argv[1]),len=stoi(argv[2]),row=0;ifstream f(argv[3]);string line;uint64_t total=0,work=0;
    while(getline(f,line)){
        istringstream s(line);int dim,x;s>>dim;if(dim!=d)continue;vector<int> p;while(s>>x)p.push_back(x);
        Census c(p,dim,len);c.solve();work+=c.nodes;total+=c.count;cout<<"ROW "<<row++<<" "<<c.count<<" "<<c.nodes<<endl;
        if(c.first>=0){
            vector<int> path{0};for(int j=0;j<len;j++){
                int mask=p[c.first+j]^p[c.first+j+1];assert(has_single_bit(unsigned(mask)));
                path.push_back(path.back()^(1<<c.winning[countr_zero(unsigned(mask))]));
            }
            for(int j=0;j<=len;j++)for(int i=0;i<j;i++){int diff=popcount(unsigned(path[j]^path[i]));assert(diff>0&&((diff==1)==(i+1==j)));}
            cout<<"PATH "<<row-1<<" "<<c.first<<" "<<len;for(int v:path)cout<<" "<<v;cout<<endl;
        }
    }
    cout<<"DONE "<<row<<" "<<total<<" "<<work<<endl;
}
