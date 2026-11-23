#define DETOUR_LIBRARY
#include "detours.cpp"
int main(int argc,char**argv){
    if(argc!=2)return 2;ifstream f(argv[1]);string w;int r=0,yes=0,deep=0,caps=0;
    vector<Node> empty(1);
    while(f>>w){Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));assert(valid(p));
        int lo=55+r%42,hi=lo+8+r%15;
        Path a,b;for(int j=lo;j>=0;j--)a.push_back(p[j]^p[lo]);for(int j=hi;j<int(p.size());j++)b.push_back(p[j]^p[lo]);
        Solver job(empty,a,191);job.right=b;bool hit=job.glue();yes+=hit;deep+=job.deep;caps+=job.limits;
        cout<<"CASE "<<r++<<" "<<hit<<" "<<job.deep<<" "<<job.limits<<" "<<job.solution.size()<<endl;
    }cout<<"DONE "<<r<<" "<<yes<<" "<<deep<<" "<<caps<<endl;
}
