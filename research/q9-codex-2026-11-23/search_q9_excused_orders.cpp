#include "q9_excused_rethread.hpp"
struct Bounds{
    array<unsigned char,512> occupied{},load{};
    array<int,512> room{};
    int poor=0,counts[10]{};
    int a,b; Bounds(int x,int y):a(x),b(y){room.fill(9);room[a]=8;}
    void change(int x,int sign){
        if(sign<0){poor-=room[x]<2;occupied[x]=false;}
        for(int d=0;d<9;d++){
            int odd=x^(1<<d);if(x==a&&odd==b)continue;int prev=load[odd],after=prev+sign;load[odd]=after;
            if(prev)counts[prev]--;if(after)counts[after]++;
            if((prev<=2)==(after<=2))continue;
            int delta=after<=2?1:-1;
            for(int k=0;k<9;k++){int v=odd^(1<<k);if(v==a&&odd==b)continue;int before=room[v];room[v]+=delta;
                if(occupied[v])poor+=(room[v]<2)-(before<2);}
        }
        if(sign>0){occupied[x]=true;poor+=room[x]<2;}
    }
};
int main(int argc,char**argv){
    if(argc!=5)return 2;
    int drops=stoi(argv[1]),cap=stoi(argv[2]);if(drops<0||drops>3||cap<1)return 2;
    ifstream baseline(argv[3]);ofstream out(argv[4]);if(!baseline||!out)return 2;
    set<string> known;string line;
    while(getline(baseline,line)){
        istringstream row(line);Path p;int x;while(row>>x)p.push_back(x);
        if(p.size()!=193)return 2;known.insert(encode(p));
    }
    string word;int row=0;
    while(cin>>word){
        Path p{0};for(char c:word){if(c<'0'||c>'8')return 2;p.push_back(p.back()^(1<<(c-'0')));}
        if(p.size()!=193||set<int>(p.begin(),p.end()).size()!=193)return 3;
        vector<pair<int,int>> bad;
        for(int i=0;i<p.size();i++)for(int j=0;j+1<i;j++)if(popcount(unsigned(p[i]^p[j]))==1)bad.emplace_back(p[j],p[i]);
        if(bad.empty())return 3;
        Repair repair{0,0,cap,known,out};
        for(auto [first,last]:bad)for(int side=0;side<2;side++){
            Path fixed,pool;for(int i=side;i<p.size();i+=2)fixed.push_back(p[i]);
            int n=fixed.size();bool major=n==97;
            int a=first,b=last;if(popcount(unsigned(a^fixed[0]))%2)swap(a,b);
            repair.a=a;repair.b=b;
            Bounds state(a,b);for(int x:fixed)state.change(x,1);
            for(int v=0;v<512;v++)if(!state.occupied[v] && !__builtin_parity(unsigned(v^fixed[0])))pool.push_back(v);
            auto add=[&](auto&& self,const Path& options,int start,int count)->bool{
                if(state.poor>(major?2:0))return false;
                if(!count){
                    if(state.counts[2]<n-1||(!major&&state.counts[1]<2))return false;
                    Path picked;for(int x=0;x<512;x++)if(state.occupied[x])picked.push_back(x);
                    Search s(picked,cap);return repair.run(s);
                }
                for(int j=start;j+count<=options.size();j++){
                    int v=options[j];if(state.room[v]<(major?1:2))continue;
                    state.change(v,1);if(self(self,options,j+1,count-1))return true;state.change(v,-1);
                }
                return false;
            };
            auto remove=[&](auto&& self,int start,int left)->bool{
                if(left==0){
                    if(state.poor>(major?2:0))return false;
                    if(drops<2)return add(add,pool,0,drops);
                    Path options;
                    for(int v:pool){
                        if(state.room[v]<(major?1:2))continue;
                        state.change(v,1);if(state.poor<=(major?2:0))options.push_back(v);state.change(v,-1);
                    }
                    return add(add,options,0,drops);
                }
                for(int i=start;i+left<=n;i++){
                    state.change(fixed[i],-1);if(self(self,i+1,left-1))return true;state.change(fixed[i],1);
                }
                return false;
            };
            if(remove(remove,0,drops))return 0;
        }
        cout<<"ROW "<<row++<<" "<<repair.tests<<" "<<repair.graphs<<" "<<repair.unknown<<" "<<repair.positive<<" "<<repair.lifts<<" "<<repair.fresh<<endl;
    }
    return 0;
}
