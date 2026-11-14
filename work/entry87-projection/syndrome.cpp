// In odd dimension A^2 = I modulo two. Change the syndrome first and recover
// the even/odd anchor set by toggling one complete neighbourhood per symbol.
#define PARITY_CUBE_ONLY
#include "two_parity.cpp"

int main(int argc,char**argv){
    if(argc!=5)return 2;
    int geo=stoi(argv[1]),r=stoi(argv[2]),first=stoi(argv[3]),last=stoi(argv[4]);
    if(r<1 || r>3 || geo<0 || geo>1 || first<0 || first>=last || last>256)return 2;
    // For a 97-anchor trial there is no external endpoint requirement.
    bool caps=(r%2==0);
    Cube cube(caps);int x,entries=0;
    while(cin>>x){
        if(x<0 || x>511 || popcount(unsigned(x))%2!=geo || cube.selected[x])return 2;
        cube.toggle(x);++entries;
    }
    if(entries!=96)return 2;
    vector<int> dual;
    for(int v=0;v<512;++v)if(popcount(unsigned(v))%2!=geo)dual.push_back(v);
    auto flip=[&](int w){for(int b=0;b<9;++b)cube.toggle(w^(1<<b));};
    vector<int> edits;uint64_t trials=0,sizes=0,degree=0,connected=0;
    auto visit=[&](auto&& self,int depth,int begin)->void{
        int bound=depth==0?last:256;
        for(int i=begin;i<bound;++i){
            int w=dual[i];
            if(depth+1==r){
                ++trials;
                if(cube.n+9-2*cube.count[w]!=(caps?96:97))continue;
            }
            flip(w);edits.push_back(w);
            if(depth+1==r){
                ++sizes;
                if(cube.degrees_ok()){
                    ++degree;
                    if(cube.connected()){
                        ++connected;
                        for(int v:edits)cout<<v<<' ';
                        cout<<'\n';
                    }
                }
            }else self(self,depth+1,i+1);
            edits.pop_back();flip(w);
        }
    };
    visit(visit,0,first);
    cout<<"count "<<trials<<' '<<sizes<<' '<<degree<<' '<<connected<<'\n';
}
