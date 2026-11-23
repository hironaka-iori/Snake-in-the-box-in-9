#define Q9_FIBER_LIBRARY
#include "search_q9_three_axis_recolor.cpp"
struct Sweep{
 int target,cap;
 uint64_t trials=0,unknown=0,duplicates=0;
 Path witness;
 bool run(const Path& p,int mask){
    Path base=p;for(int& x:base)x&=~mask;
    for(int edge=0;edge<512;edge=(edge?2*edge:1)){
        if(mask&edge)continue;
        // Insert one transition in the projected word. Later positions acquire
        // the same XOR displacement. Passing over equal transitions is redundant.
        for(int cut=0;cut<p.size();cut++){
            if(cut && (base[cut]^base[cut-1])==edge){duplicates++;continue;}
            Path candidate;candidate.reserve(p.size()+1);
            candidate.insert(candidate.end(),base.begin(),base.begin()+cut+1);
            for(int i=cut;i<p.size();i++)candidate.push_back(base[i]^edge);
            Fiber f(candidate,mask,cap);int r=f.run();trials++;unknown+=r<0;
            if(r==1){witness=f.result;return true;}
        }
    }
    return false;
 }
};
int main(int argc,char**argv){
 if(argc!=5)return 2;int target=stoi(argv[1]),cap=stoi(argv[2]),offset=stoi(argv[3]),stride=stoi(argv[4]);
 string w;int row=-1,done=0;Sweep s{target,cap};
 while(cin>>w){row++;if(row%stride!=offset)continue;if(w.size()!=target-1)return 2;
    Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
    for(int m=1;m<512;m++)if(popcount(unsigned(m))==3 && s.run(p,m)){
        cout<<"FOUND "<<row<<" "<<m<<" "<<target;for(int v:s.witness)cout<<" "<<v;cout<<endl;return 0;
    }
    cout<<"AT "<<++done<<" "<<s.trials<<" "<<s.unknown<<" "<<s.duplicates<<endl;
 }
 cout<<"DONE "<<done<<" "<<s.trials<<" "<<s.unknown<<" "<<s.duplicates<<endl;
}
