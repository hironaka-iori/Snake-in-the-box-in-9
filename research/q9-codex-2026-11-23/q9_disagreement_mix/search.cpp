// Recombine locally admissible vertex sets from independent pieces of two placed paths.
#define Q9_TIP_LIBRARY
#include "../q9_catalogue_tip_core.cpp"
#include <numeric>
#include <map>
#include <sstream>
#include <unordered_set>
using Path=vector<int>;
struct Option{Path vertices,neighbors;int ends=0;};
struct Group{vector<Option> opts;int capacity;};
struct Mixer{
    array<int,512> member{},degree{},on{};
    vector<Group> groups;Path common,remaining;
    int target=192,threshold=187,budget,expanded=0,baseEnds=0,best=0;
    long long leaves=0,legal=0,novel=0;
    set<string>& saved;
    explicit Mixer(set<string>& words,int b,int t):budget(b),saved(words),threshold(t){}
    void setup(const Path& a,const Path& b){
        for(int v:a)member[v]|=1;
        for(int v:b)member[v]|=2;
        array<bool,512> seen{};
        for(int v=0;v<512;++v)if(member[v]==3){
            common.push_back(v);on[v]=1;
            for(int d=0;d<9;++d)degree[v]+=member[v^(1<<d)]==3;
        }
        for(int v=0;v<512;++v){
            if(!member[v]||member[v]==3||seen[v])continue;
            Path g{v};seen[v]=true;
            for(size_t t=0;t<g.size();++t)for(int d=0;d<9;++d){
                int x=g[t]^(1<<d);
                if((member[x]==1||member[x]==2)&&!seen[x]){seen[x]=true;g.push_back(x);}
            }
            vector<Path> patterns;
            if(g.size()<=8){
                for(int mask=0;mask<(1<<g.size());++mask){
                    Path w;for(int t=0;t<int(g.size());++t)if(mask&(1<<t))w.push_back(g[t]);patterns.push_back(w);
                }
            }else{
                Path x,y;for(int u:g)(member[u]==1?x:y).push_back(u);
                patterns={x,y,g,{}};
            }
            Group part;
            for(const Path& pick:patterns){
                Option o;o.vertices=pick;bool good=true;
                for(int x:pick)on[x]=1;
                for(int x:pick){
                    int k=0;
                    for(int d=0;d<9;++d){int u=x^(1<<d);k+=on[u];if(member[u]==3)o.neighbors.push_back(u);}
                    if(k<1||k>2){good=false;break;}
                    o.ends+=k==1;
                }
                for(int x:pick)on[x]=0;
                if(good&&o.ends<=2)part.opts.push_back(move(o));
            }
            sort(part.opts.begin(),part.opts.end(),[](const Option& x,const Option& y){return x.vertices.size()>y.vertices.size();});
            part.capacity=part.opts.front().vertices.size();
            groups.push_back(move(part));
        }
        sort(groups.begin(),groups.end(),[](const Group& x,const Group& y){return x.capacity>y.capacity;});
        remaining.assign(groups.size()+1,0);
        for(int j=int(groups.size())-1;j>=0;--j)remaining[j]=remaining[j+1]+groups[j].capacity;
    }
    bool check(int count,int ends){
        ++leaves;int tip=-1;bool usesA=false,usesB=false;
        for(int x:common){if(!degree[x]||degree[x]>2)return false;ends+=degree[x]==1;}
        if(ends!=2)return false;
        for(int x=0;x<512;++x)if(on[x]){
            int k=0;for(int d=0;d<9;++d)k+=on[x^(1<<d)];
            if(k==1)tip=x;
            usesA|=member[x]==1;usesB|=member[x]==2;
        }
        if(tip<0)return false;
        Path p{tip};int prev=-1;
        while(true){
            int u=p.back(),next=-1;
            for(int d=0;d<9;++d){int v=u^(1<<d);if(on[v]&&v!=prev){next=v;break;}}
            if(next<0)break;
            prev=u;p.push_back(next);
        }
        if(int(p.size())!=count)return false;
        ++legal;best=max(best,count-1);
        if(!(usesA&&usesB))return false;
        string w;for(size_t j=1;j<p.size();++j)w+=char('0'+countr_zero(unsigned(p[j]^p[j-1])));
        if(saved.insert(canonical(w)).second){++novel;cout<<"W "<<canonical(w)<<'\n';}
        return count>=target+1;
    }
    bool dfs(int j,int count,int ends){
        if(count+remaining[j]<threshold+1||expanded>=budget)return false;
        ++expanded;
        if(j==int(groups.size()))return check(count,ends);
        for(auto& o:groups[j].opts){
            if(ends+o.ends>2)continue;
            bool ok=true;for(int v:o.neighbors)if(++degree[v]>2)ok=false;
            if(ok){
                for(int x:o.vertices)on[x]=1;
                if(dfs(j+1,count+int(o.vertices.size()),ends+o.ends))return true;
                for(int x:o.vertices)on[x]=0;
            }
            for(int v:o.neighbors)--degree[v];
            if(expanded>=budget)break;
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=5)return 2;
    set<string> seen;string s;int index=0;
    while(getline(cin,s)){
        int row=index++;if(row%stoi(argv[3])!=stoi(argv[4]))continue;
        istringstream in(s);Path both;for(int x;in>>x;)both.push_back(x);
        if(both.size()%2)return 3;
        int n=both.size()/2;Path a(both.begin(),both.begin()+n),b(both.begin()+n,both.end());
        Mixer mix(seen,stoi(argv[1]),stoi(argv[2]));mix.setup(a,b);
        bool hit=mix.dfs(0,mix.common.size(),0);
        cout<<"D "<<row<<" "<<mix.common.size()<<" "<<mix.groups.size()<<" "<<mix.expanded<<" "<<(mix.expanded>=mix.budget)<<" "<<mix.legal<<" "<<mix.best<<" "<<hit<<endl;
        if(hit)return 0;
    }
}
