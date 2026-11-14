// Enumerate two replacements in a prescribed parity class. Keep necessary degree
// and connectivity conditions only; exact Hamilton tests inspect the survivors.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
struct Cube {
    int parity;
    array<bool,512> selected{};
    array<int,512> count{},label{},degree{},tips{};
    array<array<unsigned char,512>,512> parallel{};
    array<array<uint64_t,8>,512> edges{};
    array<uint64_t,8> occupied{};
    array<int,48> frequencies{};
    int bad_leaves=0,n=0;

    explicit Cube(int p):parity(p){frequencies[0]=0;}
    void classify(int x,int sign){
        if(selected[x]){
            frequencies[degree[x]]+=sign;
            bad_leaves+=sign*(degree[x]==1 && tips[x]==0);
        }
    }
    void degree_change(int x,int sign){
        classify(x,-1);degree[x]+=sign;classify(x,1);
    }
    void tip_change(int x,int sign){
        classify(x,-1);tips[x]+=sign;classify(x,1);
    }
    void edge_change(int x,int y,int sign){
        int old=parallel[x][y],now=old+sign;
        if(now<0 || now>2)throw logic_error("bad number of witnesses");
        parallel[x][y]=parallel[y][x]=now;
        if((old==0)==(now==0))return;
        edges[x][y/64]^=uint64_t(1)<<(y%64);
        edges[y][x/64]^=uint64_t(1)<<(x%64);
        degree_change(x,sign);degree_change(y,sign);
    }
    void account(int w,int sign){
        if(count[w]==1){tip_change(label[w],sign);return;}
        if(count[w]!=2)return;
        int first=-1;
        for(int b=0;b<9;++b){
            int x=w^(1<<b);
            if(selected[x]){first=x;break;}
        }
        if(first<0)throw logic_error("missing witness");
        edge_change(first,label[w]^first,sign);
    }
    void toggle(int x){
        int sign=selected[x]?-1:1;
        for(int b=0;b<9;++b)account(x^(1<<b),-1);
        classify(x,-1);
        selected[x]=!selected[x];n+=sign;
        occupied[x/64]^=uint64_t(1)<<(x%64);
        classify(x,1);
        for(int b=0;b<9;++b){
            int w=x^(1<<b);
            count[w]+=sign;label[w]^=x;account(w,1);
        }
    }
    bool degrees_ok()const{
        return frequencies[0]==0 && frequencies[1]<=2 && (!parity || !bad_leaves);
    }
    bool connected()const{
        array<uint64_t,8> left=occupied;
        int first=0;
        while(!left[first])++first;
        int root=64*first+countr_zero(left[first]);
        int stack[256],top=0,total=0;
        stack[top++]=root;left[first]&=left[first]-1;
        while(top){
            int x=stack[--top];++total;
            for(int i=0;i<8;++i){
                uint64_t next=left[i]&edges[x][i];
                left[i]&=~next;
                while(next){stack[top++]=64*i+countr_zero(next);next&=next-1;}
            }
        }
        return total==n;
    }
};

int main(int argc,char**argv){
    if(argc==3 && string(argv[1])=="--inspect"){
        Cube cube(stoi(argv[2]));
        int size,x;
        if(!(cin>>size) || size<2 || size>256)return 2;
        for(int i=0;i<size;++i){if(!(cin>>x))return 2;cube.toggle(x);}
        while(cin>>x){
            cube.toggle(x);
            cout<<cube.n<<' '<<cube.frequencies[0]<<' '<<cube.frequencies[1]<<' '
                <<cube.bad_leaves<<' '<<cube.connected()<<'\n';
        }
        return 0;
    }
    if(argc!=5)return 2;
    int p=stoi(argv[1]),start=stoi(argv[2]),end=stoi(argv[3]),mode=stoi(argv[4]);
    vector<int> old,other;
    Cube cube(p);
    for(int x;cin>>x;){
        if(x<0 || x>=512 || popcount(unsigned(x))%2!=p || cube.selected[x])return 2;
        old.push_back(x);cube.toggle(x);
    }
    sort(old.begin(),old.end());
    if(old.size()!=size_t(97-p) || start<0 || end>int(old.size()) || start>=end)return 2;
    for(int x=0;x<512;++x)
        if(popcount(unsigned(x))%2==p && !cube.selected[x])other.push_back(x);
    uint64_t cases=0,passing_degree=0,passing_both=0,skipped=0;
    for(int i=start;i<end;++i){
        int a=old[i];cube.toggle(a);
        for(int j=i+1;j<int(old.size());++j){
            int b=old[j];
            if(mode==1 && a!=0 && a!=6 && a!=17 && a!=18 && b!=0 && b!=6 && b!=17 && b!=18){
                ++skipped;continue;
            }
            cube.toggle(b);
            for(int s=0;s<int(other.size());++s){
                int x=other[s];cube.toggle(x);
                for(int t=s+1;t<int(other.size());++t){
                    int y=other[t];cube.toggle(y);++cases;
                    if(cube.degrees_ok()){
                        ++passing_degree;
                        if(cube.connected()){
                            ++passing_both;
                            cout<<a<<' '<<b<<' '<<x<<' '<<y<<'\n';
                        }
                    }
                    cube.toggle(y);
                }
                cube.toggle(x);
            }
            cube.toggle(b);
        }
        cube.toggle(a);
    }
    cout<<"count "<<cases<<' '<<passing_degree<<' '<<passing_both<<' '<<skipped<<'\n';
}
