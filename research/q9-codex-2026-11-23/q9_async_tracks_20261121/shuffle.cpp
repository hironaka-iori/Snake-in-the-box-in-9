#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
using Path=vector<int>;using Mask=bitset<512>;
struct Option {Mask inside,near;string word;};
struct Cell {int start,stop;vector<Option> opts;};
int dist(int x,int y){return popcount(unsigned(x^y));}
bool valid(const Path& p){for(int j=0;j<(int)p.size();++j)for(int i=0;i<j;++i)if(!dist(p[i],p[j])||((dist(p[i],p[j])==1)!=(j==i+1)))return false;return true;}
struct Search{
 string word,groups;Path path,cuts,chosen;vector<Cell> cells;vector<Mask> forbidden;mt19937 rng;int optionCap,nodeCap,rawErrors;
 long long visits=0,cellnodes=0,totalopts=0,limitedCells=0,nobounds=0,empty=0,limitedCsp=0,solved=0,trials=0,cspnodes=0;int local=0;string answer;
 Search(int seed,int cap,int limit):rng(seed),optionCap(cap),nodeCap(limit){}
 void make(string w,string g){word=w;groups=g;path={0};for(char d:w)path.push_back(path.back()^(1<<(d-'0')));}
 void cell(int pos,int u,Mask used,Mask closed,array<string,3>&step,array<int,3>&ix,string&sw,Cell& c){
    ++cellnodes;if(pos==c.stop){assert(u==path[c.stop]);Option op;op.word=sw;int x=path[c.start];for(int j=0;j+1<(int)sw.size();j++){x^=1<<(sw[j]-'0');op.inside.set(x);op.near.set(x);for(int k=0;k<9;k++)op.near.set(x^1<<k);}c.opts.push_back(move(op));return;}
    array<int,3> o{0,1,2};shuffle(o.begin(),o.end(),rng);
    for(int g:o)if(ix[g]<(int)step[g].size()){
        int d=step[g][ix[g]],v=u^1<<(d-'0');
        if(used[v]||closed[v]||forbidden[pos+1][v])continue;
        Mask add=closed;add.set(u);for(int k=0;k<9;k++)add.set(u^1<<k);
        used.set(v);ix[g]++;sw+=(char)d;cell(pos+1,v,used,add,step,ix,sw,c);sw.pop_back();ix[g]--;used.reset(v);
        if((int)c.opts.size()>=optionCap)return;
    }
 }
 bool solve(Mask blocked,int depth){
    if(local>=nodeCap)return false;++local;
    if(depth==(int)cells.size()){answer.clear();for(int i=0;i<(int)cells.size();i++)answer+=cells[i].opts[chosen[i]].word;return true;}
    int id=-1;vector<int> list;
    for(int i=0;i<(int)cells.size();i++)if(chosen[i]<0){
        vector<int> viable;for(int j=0;j<(int)cells[i].opts.size();j++)if((cells[i].opts[j].inside&blocked).none())viable.push_back(j);
        if(viable.empty())return false;
        if(id<0||viable.size()<list.size()){id=i;list=move(viable);}
    }
    for(int j:list){chosen[id]=j;if(solve(blocked|cells[id].opts[j].near,depth+1))return true;chosen[id]=-1;if(local>=nodeCap)break;}
    return false;
 }
 bool trial(int rep,int l1,int n1,int l2,int n2){
    ++trials;int n=word.size();cuts={0};
    if(rep==0){
       for(int i=0;i<n;){int len=i==l1?n1:i==l2?n2:1;i+=len;cuts.push_back(i);}
    }else{
       // Choose checkpoints that avoid unavoidable clashes with already fixed checkpoints.
       for(int t=0;t<n;){int width=5+rng()%9;vector<pair<int,int>> opts;
         for(int j=min(n,t+max(4,width-3));j<=min(n,t+width+4);++j){
            if(n-j>0&&n-j<3)continue;int risk=0;
            for(int i:cuts)risk+=dist(path[i],path[j])<=1;
            if(j<n)risk+=dist(path[j],path[n])<=1;
            for(int i=0;i<=n;i++)if(abs(i-j)>1&&dist(path[i],path[j])<=1)risk++;
            opts.emplace_back(risk*100+int(rng()%85),j);
         }if(opts.empty()){cuts.push_back(n);break;}t=min_element(opts.begin(),opts.end())->second;cuts.push_back(t);}
    }
    for(int a:cuts)for(int b:cuts)if(b>a&&((dist(path[a],path[b])==1)!=(b==a+1)||path[a]==path[b])){++nobounds;return false;}
    forbidden.assign(n+1,{});for(int t=0;t<=n;t++)for(int a:cuts)if(abs(t-a)>1){int x=path[a];forbidden[t].set(x);for(int k=0;k<9;k++)forbidden[t].set(x^1<<k);}
    cells.clear();
    for(int j=1;j<(int)cuts.size();j++){
      int lo=cuts[j-1],hi=cuts[j];Cell c{lo,hi};array<string,3> step;array<int,3> ix{};for(int h=lo;h<hi;h++)step[groups[word[h]-'0']-'0']+=word[h];
      Mask use;use.set(path[lo]);string sw;cell(lo,path[lo],use,{},step,ix,sw,c);
      if(c.opts.empty()){++empty;return false;}totalopts+=c.opts.size();limitedCells+=c.opts.size()==optionCap;cells.push_back(move(c));
    }
    chosen.assign(cells.size(),-1);local=0;bool found=solve({},0);cspnodes+=local;limitedCsp+=local>=nodeCap;
    if(found){Path p{0};for(char c:answer)p.push_back(p.back()^(1<<(c-'0')));assert(valid(p));++solved;}return found;
 }
};
int main(int argc,char**argv){
 if(argc!=8)return 2;ifstream in(argv[1]);ofstream out(argv[2]);int rounds=stoi(argv[3]),take=stoi(argv[4]),cap=stoi(argv[5]),limit=stoi(argv[6]),seed=stoi(argv[7]);Search S(seed,cap,limit);
 string w,g;int l1,n1,l2,n2,rows=0;
 while(in>>w>>g>>l1>>n1>>l2>>n2){if(rows>=take)break;S.make(w,g);
   for(int a=0;a<rounds;a++)if(S.trial(a,l1,n1,l2,n2)){
       out<<rows<<' '<<a<<' '<<S.answer<<endl;if(S.answer.size()>=192){cout<<"FOUND192 "<<rows<<endl;return 0;}break;}
   ++rows;
 }
 cout<<"rows "<<rows<<" trials "<<S.trials<<" incompatible_checkpoints "<<S.nobounds<<" empty_cells "<<S.empty<<" local_interleaving_nodes "<<S.cellnodes<<" retained_options "<<S.totalopts<<" capped_cells "<<S.limitedCells<<" csp_nodes "<<S.cspnodes<<" capped_assignments "<<S.limitedCsp<<" foundtrue "<<S.solved<<endl;
}
