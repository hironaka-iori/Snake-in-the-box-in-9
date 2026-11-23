#define main previous_pivot_main
#include "../search_q9_pivot.cpp"
#undef main
#include <cassert>
#include <sstream>
using Path=vector<int>;
struct Seam{
    Path a,b,answer;array<int,512> blocked{};uint64_t branches=0,placements=0;
    void change(int v,int k){blocked[v]+=k;for(int d=0;d<9;d++)blocked[v^(1<<d)]+=k;}
    bool visit(int free){
        branches++;
        for(int bit=1;bit<512;bit*=2){
            int u=a.back()^bit;if(blocked[u]!=1||find(a.begin(),a.end(),u)!=a.end())continue;
            a.push_back(u);change(u,1);
            if(free){if(visit(free-1))return true;}
            else{
                placements++;
                Path both=a;for(size_t j=1;j<b.size();j++)both.push_back(u^b[0]^b[j]);
                Pivot perm;
                if(perm.solve(both,int(a.size())-1)){
                    answer=a;for(size_t j=1;j<b.size();j++)answer.push_back(u^perm.mapped[b[0]^b[j]]);
                    assert(valid(answer));return true;
                }
                assert(perm.leaves==362880);
            }
            change(u,-1);a.pop_back();
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=3)return 2;int maxgap=stoi(argv[1]),control=stoi(argv[2]);string line;int row=0;
    while(getline(cin,line)){
        istringstream is(line);Path p;for(int v;is>>v;)p.push_back(v);if(p.empty())continue;
        int n=p.size(),seam=n/2;
        if(control){assert(valid(p));for(int j=seam;j<n;j++){int x=p[j];p[j]=((x<<3)&511)^(x>>6)^73;}}
        int lo=0,hi=n-2,viol=0;
        for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){
            int h=popcount(unsigned(p[i]^p[j]));
            if(!h||((h==1)!=(j==i+1))){lo=max(lo,i);hi=min(hi,j-1);viol++;}
        }
        uint64_t branches=0,placements=0,cuts=0;bool hit=false;
        for(int r=0;r<=maxgap&&!hit;r++){
            for(int k=max(0,lo-r);k<=min(hi,n-2-r);k++){
                if(control&&k!=seam-1)continue;
                Seam s;s.a.assign(p.begin(),p.begin()+k+1);s.b.assign(p.begin()+k+r+1,p.end());
                if(s.a.size()<s.b.size()){swap(s.a,s.b);reverse(s.a.begin(),s.a.end());reverse(s.b.begin(),s.b.end());}
                for(int u:s.a)s.change(u,1);++cuts;
                hit=s.visit(r);branches+=s.branches;placements+=s.placements;
                if(hit){
                    assert(int(s.answer.size())==n);
                    cout<<"FOUND "<<row<<" "<<n-1<<" "<<viol<<" "<<r<<" "<<k;
                    for(int u:s.answer)cout<<" "<<u;cout<<endl;break;
                }
            }
        }
        cout<<"ROW "<<row++<<" "<<viol<<" "<<cuts<<" "<<branches<<" "<<placements<<" "<<hit<<endl;
        if(hit&&!control)return 0;
    }
}
