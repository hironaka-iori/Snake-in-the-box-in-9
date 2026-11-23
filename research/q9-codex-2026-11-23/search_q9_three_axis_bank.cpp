#define Q9_FIBER_LIBRARY
#include "search_q9_three_axis_recolor.cpp"
#include <fstream>
#include <random>
string shape(const Path& p){
 string w;for(int i=1;i<p.size();i++)w+=char('0'+countr_zero(unsigned(p[i]^p[i-1])));
 auto norm=[](string s){array<int,9> id;id.fill(-1);int n=0;for(char& c:s){int k=c-'0';if(id[k]<0)id[k]=n++;c='0'+id[k];}return s;};
 auto first=norm(w);reverse(w.begin(),w.end());return min(first,norm(w));
}
Path decode(string w){Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));return p;}
struct Bank{
 set<string> known;ofstream out;
 uint64_t calls=0,lifts=0,cuts=0,fresh=0;
 explicit Bank(const char*name):out(name){}
 bool record(const Path& p){
    lifts++;string key=shape(p);
    if(!known.insert(key).second)return false;
    for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){
        int d=popcount(unsigned(p[i]^p[j]));assert(d>0 && ((d==1)==(i==j+1)));
    }
    fresh++;out<<key<<endl;
    for(bool left:{false,true})for(int bit=1;bit<512;bit*=2){
        int v=(left?p.front():p.back())^bit, near=0;bool seen=false;
        for(int x:p){near+=popcount(unsigned(x^v))==1;seen|=x==v;}
        if(!seen&&near==1){
            Path q=p;if(left)q.insert(q.begin(),v);else q.push_back(v);
            cout<<"FOUND "<<q.size()-1;for(int x:q)cout<<" "<<x;cout<<endl;return true;
        }
    }
    return false;
 }
 bool inspect(const Path& base,int mask,int cap){
    calls++;Fiber f(base,mask,cap);if(!f.prepare())return false;
    int nodes=0;bool cut=false;
    auto visit=[&](auto&& self,int left,int used)->bool{
        if(!left){
            Path p;const int verts[]={0,3,5,6};
            for(int i=0;i<f.n;i++){
                int z=verts[f.color[f.component[i]]]^(f.localParity[i]?7:0);
                int v=f.base[i],j=0;for(int bit=1;bit<512;bit*=2)if(mask&bit){if(z&(1<<j))v|=bit;j++;}
                p.push_back(v);
            }
            return record(p);
        }
        if(++nodes>cap){cut=true;return false;}
        int chosen=-1,score=-1,forbidden=0;
        for(int i=0;i<f.adj.size();i++)if(f.color[i]<0){
            int blocked=0,open=0;for(int j:f.adj[i]){if(f.color[j]>=0)blocked|=1<<f.color[j];else open++;}
            if(blocked==15)return false;int s=256*popcount(unsigned(blocked))+open;
            if(s>score){chosen=i;score=s;forbidden=blocked;}
        }
        for(int c=0;c<min(used+1,4);c++)if(!(forbidden&(1<<c))){
            f.color[chosen]=c;if(self(self,left-1,max(used,c+1)))return true;f.color[chosen]=-1;
            if(cut)break;
        }
        return false;
    };
    bool hit=visit(visit,f.adj.size(),0);cuts+=cut;return hit;
 }
};
int main(int argc,char**argv){
 if(argc!=5)return 2;int samples=stoi(argv[1]),cap=stoi(argv[2]);Bank bank(argv[4]);ifstream prior(argv[3]);if(!prior||!bank.out)return 3;
 string w;while(prior>>w)bank.known.insert(shape(decode(w)));int row=0;mt19937 rng(91191);
 while(cin>>w){
    Path p=decode(w);if(p.size()!=(samples?191:192))return 3;
    for(int mask=1;mask<512;mask++)if(popcount(unsigned(mask))==3){
        if(!samples){if(bank.inspect(p,mask,cap))return 0;continue;}
        Path steps{0};for(int bit=1;bit<512;bit*=2)if(!(bit&mask))steps.push_back(bit);
        for(int k=0;k<samples;k++){
            int cut=rng()%p.size(),edge=steps[rng()%steps.size()];
            Path q(p.begin(),p.begin()+cut+1);for(int j=cut;j<p.size();j++)q.push_back(p[j]^edge);
            if(bank.inspect(q,mask,cap))return 0;
        }
    }
    cout<<"AT "<<++row<<" "<<bank.calls<<" "<<bank.lifts<<" "<<bank.cuts<<" "<<bank.fresh<<endl;
 }
 cout<<"DONE "<<row<<" "<<bank.calls<<" "<<bank.lifts<<" "<<bank.cuts<<" "<<bank.fresh<<endl;
}
