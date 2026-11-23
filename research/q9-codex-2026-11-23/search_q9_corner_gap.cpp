#define Q9_CORNER_DRIVER
#include "search_q9_corners_and_tips.cpp"
#include <random>
int main(int argc,char**argv){
    if(argc!=7)return 2;
    int count=stoi(argv[1]),seed=stoi(argv[2]),target=stoi(argv[3]),mode=stoi(argv[4]),budget=stoi(argv[5]),maxgap=stoi(argv[6]);
    if(mode<0 || mode>1 || maxgap<5)return 2;
    vector<Path> bank;vector<pair<int,int>> chords;string line;
    while(getline(cin,line)){
        Path p;if(mode){istringstream in(line);int x;while(in>>x)p.push_back(x);}
        else{p.push_back(0);for(char c:line)p.push_back(p.back()^(1<<(c-'0')));}
        assert(p.size()==(mode?193:192));pair<int,int> chord{-1,-1};
        for(int j=0;j<p.size();j++)for(int i=0;i<j;i++){
            int h=dist(p[i],p[j]);assert(h && (i+1!=j || h==1));
            if(i+1<j && h==1){assert(chord.first<0);chord={i,j};}
        }
        assert((chord.first>=0)==bool(mode));bank.push_back(p);chords.push_back(chord);
    }
    mt19937 rng(seed);
    uint64_t totalNodes=0,totalTests=0,totalCapped=0;int skipped=0,maxCorners=0;
    for(int trial=0;trial<count;trial++){
        int id=rng()%bank.size();const auto&p=bank[id];int n=p.size();
        int a=rng()%10,b=rng()%10,oldGap=5+rng()%(maxgap-4);
        int minStart=a+2,maxStart=n-b-oldGap-3;
        if(minStart>maxStart)abort();
        int from=minStart+rng()%(maxStart-minStart+1);
        if(mode){
            auto [u,v]=chords[id];int focus=rng()%2?u:v;
            from=clamp(focus-1-int(rng()%(oldGap-1)),minStart,maxStart);
            auto retained=[&](int i){return i>=a && i<n-b && (i<=from||i>=from+oldGap);};
            if(retained(u)&&retained(v)){skipped++;continue;}
        }
        int to=from+oldGap;
        if(dist(p[from],p[to])<2){skipped++;continue;}
        Path core(p.begin()+a,p.begin()+from+1);int split=core.size();
        core.insert(core.end(),p.begin()+to,p.end()-b);
        Engine model(core,budget,split);maxCorners=max(maxCorners,model.corners);
        // The replacement may differ in length by up to six edges in either direction.
        for(int gap=max(2,oldGap-6);gap<=oldGap+6;gap++){
            if((gap-oldGap)%2)continue;
            int ext=target+1-int(core.size())-(gap-1);
            if(ext<0)continue;
            for(int l=0;l<=ext;l++){
                model.nodes=0;model.cutoff=false;
                bool ok=model.connect(gap,l,ext-l,Forced{});
                totalNodes+=model.nodes;totalTests++;totalCapped+=model.cutoff;
                if(ok){cout<<"FOUND "<<id<<" "<<a<<" "<<b<<" "<<from<<" "<<to<<" "<<gap<<" "<<l;
                    for(int v:model.witness)cout<<" "<<v;cout<<endl;return 0;}
            }
        }
        if(trial%1000==0)cout<<"AT "<<trial<<" "<<totalTests<<" "<<totalCapped<<" "<<totalNodes<<endl;
    }
    cout<<"DONE "<<count<<" "<<skipped<<" "<<totalTests<<" "<<totalCapped<<" "<<totalNodes<<" "<<maxCorners<<endl;
}
