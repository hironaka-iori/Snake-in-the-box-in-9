#define main partial_main
#include "find.cpp"
#undef main
#include "forest.hpp"
struct General {
    Search base;
    uint64_t nodes=0,closures=0,rank_reject=0,limit;
    bool exhausted=false,hit=false;
    bool augment=false;
    vector<int> basis;
    explicit General(vector<int> p,int goal,uint64_t cap):base(p,goal),limit(cap){}
    bool independent(){
        int piv[9]{};
        for(int g:basis){
            int x=g;
            for(int i=8;i>=0;i--)if(x&(1<<i)){if(piv[i])x^=piv[i];else{piv[i]=x;break;}}
            if(x==0)return false;
        }return true;
    }
    bool dfs(const vector<int>& opts,int left,const Bits& one,const Bits& two,int caseid){
        if(++nodes>limit){exhausted=true;return false;}
        int need=9-basis.size();
        if((int)opts.size()<need)return false;
        int minimum=0;for(int i=0;i<need;i++)minimum+=base.edges[opts[i]];
        if(minimum>left)return false;
        for(int i=0;i<=(int)opts.size()-need;i++){
            int g=opts[i],weight=base.edges[g];
            if(weight*need>left)break;
            const Bits &h=base.hits[g];Bits n1=one^h,n2=two|(one&h);
            if(need==1){
                if(weight!=left)continue;
                if(!augment&&(n1.count()!=2||(n1|n2)!=base.selected))continue;
                basis.push_back(g);if(independent()){
                    base.basis=basis;closures++;if(augment ? complete_forest(basis,base.points,base.target,caseid) : base.inspect(-1,caseid))return true;
                }else rank_reject++;basis.pop_back();continue;
            }
            int nleft=left-weight;vector<int> next;next.reserve(opts.size()-i);
            int maxweight=nleft-(need-2)*weight;
            for(int j=i+1;j<(int)opts.size();j++){
                int a=opts[j];if(base.edges[a]>maxweight)break;
                if(!(base.hits[a]&n2).any())next.push_back(a);
            }
            if((int)next.size()<need-1)continue;
            int hi=0;for(int j=1;j<need;j++)hi+=base.edges[next[next.size()-j]];
            if(hi<nleft)continue;
            basis.push_back(g);bool yes=dfs(next,nleft,n1,n2,caseid);basis.pop_back();
            if(yes||exhausted)return yes;
        }
        return false;
    }
    void parity(int mask,int caseid){
        nodes=0;exhausted=false;closures=0;rank_reject=0;int n=base.points.size(),ones=0;
        for(int v:base.points)ones+=__builtin_parity((unsigned)(v&mask));
        int holes=augment?(base.target+1-n):0;
        if(abs(2*ones-n)>(augment ? holes+(base.target+1)%2 : 1))return;
        vector<int> opts;
        for(int g=1;g<512;g++)if(__builtin_parity((unsigned)(g&mask)))opts.push_back(g);
        sort(opts.begin(),opts.end(),[&](int a,int b){return base.edges[a]<base.edges[b]||(base.edges[a]==base.edges[b]&&a<b);});
        for(int removed=0;removed<=holes;removed++){hit=dfs(opts,n-1-removed,Bits(),Bits(),caseid);if(hit||exhausted)break;}
        cout<<"FORM "<<caseid<<" "<<mask<<" "<<(hit?"FOUND":exhausted?"UNKNOWN":"CLOSED")<<" "<<nodes<<" "<<closures<<" "<<rank_reject<<endl;
    }
};
int main(int argc,char**argv){
    if(argc!=4&&argc!=5)return 2;
    int target=atoi(argv[1]),single=atoi(argv[3]);uint64_t cap=stoull(argv[2]);string line;int id=0;
    while(getline(cin,line)){vector<int> p;int x=0;if(line.rfind("points ",0)==0){istringstream in(line.substr(7));while(in>>x)p.push_back(x);}else{p.push_back(0);for(char c:line){x^=1<<(c-'0');p.push_back(x);}}
        Bits s;for(int a:p)s.set(a);if(s.count()!=p.size())return 3;
        General g(p,target,cap);g.augment=argc==5;
        for(int mask=1;mask<512;mask++){if(single&&mask!=single)continue;g.parity(mask,id);if(g.hit)break;}
        cout<<"END "<<id++<<endl;if(g.hit)break;
    }return 0;
}
