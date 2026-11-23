#define Q9_FIBER_LIBRARY
#include "search_q9_three_axis_recolor.cpp"
struct EditSearch{
 int mask,cap,goal;
 uint64_t checks=0,cuts=0,core=0;
 Path result;
 bool visit(Path& p,int depth,Path& used){
    Fiber f(p,mask,cap);f.trace=depth>0;int r=f.run();checks++;cuts+=r<0;
    if(r==1){result=f.result;return true;}
    if(depth==0)return false;
    Path sites=f.conflict;
    if(sites.empty()){sites.resize(p.size());iota(sites.begin(),sites.end(),0);}else core++;
    for(int i:sites){
        if(find(used.begin(),used.end(),i)!=used.end())continue;
        int pivot=i?p[i-1]:p[i+1],prev=p[i];used.push_back(i);
        for(int b=0;b<512;b=(b==0?1:2*b)){
            if(b&mask)continue;
            int v=pivot^b;if(v==prev || (i+1<p.size()&&popcount(unsigned(v^p[i+1]))>1))continue;
            p[i]=v;if(visit(p,depth-1,used))return true;
        }
        p[i]=prev;used.pop_back();
    }
    return false;
 }
};
#ifndef Q9_FIBER_EDIT_LIBRARY
int main(int argc,char**argv){
 if(argc!=5)return 2;int depth=stoi(argv[1]),cap=stoi(argv[2]),offset=stoi(argv[3]),stride=stoi(argv[4]);
 if(offset<0||offset>=stride||depth<0)return 2;
 string w;int row=-1,processed=0;uint64_t trials=0,checks=0,cuts=0,cores=0;
 while(cin>>w){
    ++row;if(row%stride!=offset)continue;
    Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
    for(int mask=1;mask<512;mask++)if(popcount(unsigned(mask))==3){
        Path projected=p;for(int& x:projected)x&=~mask;Path used;
        EditSearch e{mask,cap,int(w.size())};bool hit=e.visit(projected,depth,used);trials++;checks+=e.checks;cuts+=e.cuts;cores+=e.core;
        if(hit){cout<<"FOUND "<<row<<" "<<mask<<" "<<w.size();for(int v:e.result)cout<<" "<<v;cout<<endl;return 0;}
    }
    if(++processed%5==0)cout<<"AT "<<processed<<" "<<trials<<" "<<checks<<" "<<cuts<<" "<<cores<<endl;
 }
 cout<<"DONE "<<processed<<" "<<trials<<" "<<checks<<" "<<cuts<<" "<<cores<<endl;
}

#endif
