#define Q9_FLEX_LIBRARY
#include "flexible.cpp"
struct Block:State{
 array<uint16_t,8> dictionary{};
 array<uint16_t,9> component{};
 int used=0;
 Block(){reset();}
 void reset(){dictionary.fill(0);for(int i=0;i<9;i++)component[i]=1<<i;}
 bool legal(int d,int m)const{
    if(dictionary[d])return dictionary[d]==m;
    int i=countr_zero(unsigned(m)),j=bit_width(unsigned(m))-1;
    int fresh=m&~((1<<used)-1);
    if(fresh && fresh!=((1<<popcount(unsigned(fresh)))-1)<<used)return false;
    return !(component[i]&(1<<j));
 }
 void advance(int d,int m){
    int a=m&-m,b=a^m;
    if(!dictionary[d]){dictionary[d]=m;int cc=component[countr_zero(unsigned(a))]|component[countr_zero(unsigned(b))];
        for(int rest=cc;rest;rest&=rest-1)component[countr_zero(unsigned(rest))]=cc;}
    used=max(used,int(bit_width(unsigned(m))));push(a,b);
 }
};
struct Pick{float score;uint64_t hash;int parent,m;};
int main(int argc,char**argv){
 if(argc!=6)return 2;mt19937_64 rng(stoull(argv[1]));int width=stoi(argv[2]),runs=stoi(argv[3]),bl=stoi(argv[4]),target=stoi(argv[5]);
 vector<string> ws;string w;while(cin>>w)ws.push_back(w);int best=-1;uint64_t nodes=0;
 array<array<uint64_t,9>,512> salt;for(auto& a:salt)for(auto& b:a)b=rng();
 P options;for(int i=0;i<9;i++)for(int j=0;j<i;j++)options.push_back((1<<i)|(1<<j));
 for(int r=0;r<runs;r++){int row=rng()%ws.size();w=ws[row];if(rng()%2)reverse(w.begin(),w.end());
    vector<Block> cur(1);int offset=rng()%bl;
    float f=.5+float(rng()%80)/100.,h=float(rng()%180)/100.,noise=.5+float(rng()%900)/100.;
    for(int t=0;t<int(w.size());t++){
        int d=w[t]-'0';vector<Pick> picks;unordered_set<uint64_t> seen;
        for(int i=0;i<int(cur.size());i++){
            auto& p=cur[i];if((t+offset)%bl==0)p.reset();
            for(int m:options){if(!p.legal(d,m))continue;int a=m&-m,b=m^a;if(!p.possible(a,b))continue;
                int y=p.v^m;uint64_t hash=p.hash^salt[min(p.v,y)][countr_zero(unsigned(a))]^salt[max(p.v,y)][countr_zero(unsigned(b))];
                if(!seen.insert(hash^salt[y][0]).second)continue;
                Block next=p;next.advance(d,m);++nodes;
                int avail=0;
                if(t+1<int(w.size())){
                    int nd=w[t+1]-'0';
                    if((t+1+offset)%bl==0)next.reset();
                    for(int z:options){int l=z&-z;avail+=next.legal(nd,z)&&next.possible(l,z^l);}
                }
                if(!avail&&t+1<best/2)continue;
                float score=f*next.safe+h*next.empty+.6*min(avail,6)+noise*double(rng()%10000)/10000.;
                picks.push_back({score,hash,i,m});
            }
        }
        if(picks.empty())break;
        if(picks.size()>width){nth_element(picks.begin(),picks.begin()+width,picks.end(),[](auto&a,auto&b){return a.score>b.score;});picks.resize(width);}
        vector<Block> next;next.reserve(picks.size());for(const auto& c:picks){
          auto& b=next.emplace_back(cur[c.parent]);b.advance(d,c.m);b.hash=c.hash;
        }
        if(2*(t+1)>best){best=2*(t+1);P p=next[0].witness();
            if(best>=128){cout<<"BEST "<<r<<" "<<row<<" "<<best<<" "<<offset<<" "<<w.substr(0,t+1);
                for(int x:p)cout<<" "<<x;cout<<endl;}if(best>=target)return 0;}
        cur.swap(next);
    }
    if(r%4==0)cout<<"AT "<<r<<" "<<nodes<<" "<<best<<endl;
 }
}
