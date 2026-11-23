#define main screen_main
#include "screen.cpp"
#undef main
#include <unordered_set>
int main(int argc,char**argv){
    if(argc!=4)return 2;
    int goal=atoi(argv[1]),limit=atoi(argv[2]),minweight=atoi(argv[3]);string w;int row=0;
    while(getline(cin,w)){
        vector<int> pts{0};for(char c:w){if(c<'0'||c>'8')return 3;pts.push_back(pts.back()^(1<<(c-'0')));}
        vector<string> samples;int total=0,eligible=0;mt19937 rng(81133+row);unordered_set<B> seen;
        for(int k=1;k<512;k++)if(__builtin_popcount((unsigned)k)>=minweight){
            for(int pivot=0;pivot<9;pivot++)if(k&(1<<pivot)){B S;
                for(int x:pts){if(x&(1<<pivot))x^=k;int y=(x&((1<<pivot)-1))|((x>>(pivot+1))<<pivot);S.set(y);}
                total++;if(!seen.insert(S).second)continue;
                Screen sc(S,goal,1,0);if(sc.k<0||sc.k>(int)S.count())continue;
                State st{};for(int i=0;i<8;i++){sc.chosen.push_back(1<<i);st=st.add(sc.near[1<<i]);}
                if(!sc.eligible(st))continue;
                eligible++;int idx=samples.size();if(limit>0&&idx>=limit){uniform_int_distribution<int> d(0,eligible-1);idx=d(rng);if(idx>=limit)continue;}
                ostringstream line;line<<"CASE "<<row<<" 1 2 4 8 16 32 64 128 support";
                for(int v:sc.points)line<<" "<<v;
                if(idx==(int)samples.size())samples.push_back(line.str());else samples[idx]=line.str();
            }}
        for(auto &s:samples)cout<<s<<"\n";
        cout<<"END "<<row++<<" raw "<<total<<" unique "<<seen.size()<<" eligible "<<eligible<<" saved "<<samples.size()<<endl;
    }
    return 0;
}
