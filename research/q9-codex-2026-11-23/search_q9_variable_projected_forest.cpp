#define Q9_PROJECTED_GAP_LIBRARY
#include "search_q9_free_projected_gaps.cpp"
struct Join{
    vector<Path> parts,bridges;Path left,right,result;
    array<int,512> occ{},neighbors{};int target,limit,axes,nodes=0,size=0;bool cutoff=false;
    Join(vector<Path> p,int goal,int budget,int directions=511):parts(std::move(p)),bridges(parts.size()-1),target(goal),limit(budget),axes(directions){
        for(auto& piece:parts)for(int x:piece)change(x,1);
    }
    void change(int x,int d){occ[x]+=d;size+=d;for(int b=1;b<512;b*=2)neighbors[x^b]+=d;}
    bool enter(){if(++nodes>limit){cutoff=true;return false;}return true;}
    bool save(){
        result.assign(left.rbegin(),left.rend());
        for(int j=0;j<parts.size();j++){result.insert(result.end(),parts[j].begin(),parts[j].end());if(j<bridges.size())result.insert(result.end(),bridges[j].begin(),bridges[j].end());}
        result.insert(result.end(),right.begin(),right.end());assert(result.size()==size);
        for(int i=0;i<size;i++)for(int j=0;j<i;j++){
            int d=popcount(unsigned(result[i]^result[j]));assert(d>0 && ((d==1)==(i==j+1)));
        }
        return true;
    }
    bool arm(bool first,int x){
        if(size>=target+1)return save();if(!enter())return false;
        if(first && arm(false,parts.back().back()))return true;
        auto& path=first?left:right;
        for(int b=1;b<512&&!cutoff;b*=2){
            if(!(axes&b))continue;int v=x^b;if(occ[v]||neighbors[v]!=1)continue;
            change(v,1);path.push_back(v);if(arm(first,v))return true;
            path.pop_back();change(v,-1);
        }
        return false;
    }
    bool reachable(int x,int end){
        array<bool,512> seen{};Path queue{x};seen[x]=1;
        for(int i=0;i<queue.size();i++)for(int b=1;b<512;b*=2){
            if(!(axes&b))continue;int v=queue[i]^b;if(seen[v]||occ[v])continue;seen[v]=1;
            bool near=popcount(unsigned(v^end))==1;
            if(neighbors[v]!=(int(near)+int(popcount(unsigned(v^x))==1)))continue;
            if(near)return true;queue.push_back(v);
        }
        return false;
    }
    bool next(int j){
        if(j==bridges.size())return arm(true,parts[0][0]);
        int x=parts[j].back(),end=parts[j+1].front();
        if(!reachable(x,end))return false;
        return extend(j,x,end);
    }
    bool extend(int j,int x,int end){
        if(!enter())return false;
        for(int b=1;b<512&&!cutoff;b*=2){
            if(!(axes&b))continue;int v=x^b;if(occ[v])continue;
            bool near=popcount(unsigned(v^end))==1;if(neighbors[v]!=1+near)continue;
            change(v,1);bridges[j].push_back(v);
            if(near?next(j+1):extend(j,v,end))return true;
            bridges[j].pop_back();change(v,-1);
        }
        return false;
    }
};
#ifndef Q9_VARIABLE_FOREST_LIBRARY
int main(int argc,char**argv){
 if(argc!=7)return 2;
 int runs=stoi(argv[1]),goal=stoi(argv[2]),colorCap=stoi(argv[3]),bridgeCap=stoi(argv[4]);mt19937 rng(stoi(argv[5]));int radius=stoi(argv[6]);
 string w;vector<Path> seeds;vector<vector<pair<int,int>>> defects;Path masks;
 for(int m=1;m<512;m++)if(popcount(unsigned(m))==3)masks.push_back(m);
 while(cin>>w){Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
    vector<pair<int,int>> bad;for(int i=0;i<p.size();i++)for(int j=0;j+1<i;j++)if(popcount(unsigned(p[i]^p[j]))==1)bad.emplace_back(i,j);
    seeds.push_back(p);defects.push_back(bad);
 }
 Stats st;uint64_t arr=0;for(int t=0;t<runs;t++){
    int id=rng()%seeds.size();auto &p=seeds[id];auto& bad=defects[id];int n=p.size();
    vector<bool> removed(n);int holes=1+rng()%3;
    for(int h=0;h<holes;h++){
        int x=1+rng()%(n-2);if(h<bad.size()){auto [a,b]=bad[(t+h)%bad.size()];x=rng()%2?a:b;}
        int lo=max(0,x-1-int(rng()%radius)),hi=min(n-1,x+1+int(rng()%radius));
        for(int j=lo;j<=hi;j++)removed[j]=true;
    }
    Path keep,times,offset;int phase=0;
    for(int j=0;j<n;j++)if(!removed[j]){
        if(j==0||removed[j-1]){
            offset.push_back(keep.size());if(!times.empty())phase+=rng()%2;
        }
        keep.push_back(p[j]);times.push_back(j+phase);
    }
    offset.push_back(keep.size());if(offset.size()<3||offset.size()>5)continue;
    int mask=masks[rng()%masks.size()];
    auto tryPaths=[&](const Path& colored){
      vector<Path> parts;for(int j=0;j+1<offset.size();j++)parts.emplace_back(colored.begin()+offset[j],colored.begin()+offset[j+1]);
      int k=parts.size();Path order(k);iota(order.begin(),order.end(),0);
      do{
        if(order.front()>order.back())continue;
        for(int flips=0;flips<(1<<k);flips++){
            vector<Path> chosen;for(int j:order){chosen.push_back(parts[j]);if(flips&(1<<j))reverse(chosen.back().begin(),chosen.back().end());}
            Join join(std::move(chosen),goal,bridgeCap);arr++;bool hit=join.next(0);
            st.bridgeNodes+=join.nodes;st.bridgeLimits+=join.cutoff;
            if(hit){cout<<"FOUND "<<id<<" "<<mask<<" "<<join.result.size()-1;for(int x:join.result)cout<<" "<<x;cout<<endl;return true;}
        }
      }while(next_permutation(order.begin(),order.end()));
      return false;
    };
    if(enumerateColors(keep,times,mask,colorCap,st,tryPaths))return 0;
    if((t+1)%1000==0)cout<<"AT "<<t+1<<" "<<st.layouts<<" "<<st.colorings<<" "<<arr<<" "<<st.colorLimits<<" "<<st.bridgeLimits<<" "<<st.bridgeNodes<<endl;
 }
 cout<<"DONE "<<st.layouts<<" "<<st.colorings<<" "<<arr<<" "<<st.colorLimits<<" "<<st.bridgeLimits<<" "<<st.bridgeNodes<<endl;
}

#endif
