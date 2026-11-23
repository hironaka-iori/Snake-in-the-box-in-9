#define Q9_FIBER_LIBRARY
#include "search_q9_three_axis_recolor.cpp"
#include <random>
// Each extra projected step can translate a different suffix; both missing
// transitions may project to zero (remain entirely in the hidden Q3).
int main(int argc,char**argv){
    if(argc!=4)return 2;
    int samples=stoi(argv[1]),cap=stoi(argv[2]),seed=stoi(argv[3]);
    mt19937 rng(seed);
    string w;uint64_t tested=0,capped=0;int row=0;
    while(cin>>w){
        if(w.size()!=190)return 3;
        Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
        for(int mask=1;mask<512;mask++)if(popcount(unsigned(mask))==3){
            Path base,steps{0};for(int x:p)base.push_back(x&~mask);
            for(int bit=1;bit<512;bit*=2)if(!(mask&bit))steps.push_back(bit);
            for(int n=0;n<samples;n++){
                int c1=rng()%p.size(),c2=rng()%p.size();
                if(c1>c2)swap(c1,c2);
                int a=steps[rng()%steps.size()],b=steps[rng()%steps.size()];
                Path q;q.reserve(193);int delta=0;
                for(int i=0;i<base.size();i++){
                    q.push_back(base[i]^delta);
                    if(i==c1){delta^=a;q.push_back(base[i]^delta);}
                    if(i==c2){delta^=b;q.push_back(base[i]^delta);}
                }
                Fiber f(q,mask,cap);int result=f.run();tested++;capped+=result<0;
                if(result==1){cout<<"FOUND "<<row<<" "<<mask<<" "<<c1<<" "<<a<<" "<<c2<<" "<<b;for(int x:f.result)cout<<" "<<x;cout<<endl;return 0;}
            }
        }
        cout<<"AT "<<++row<<" "<<tested<<" "<<capped<<endl;
    }
    cout<<"DONE "<<row<<" "<<tested<<" "<<capped<<endl;
}
