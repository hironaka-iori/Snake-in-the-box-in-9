#define Q9_FIBER_EDIT_LIBRARY
#include "search_q9_three_axis_repair.cpp"
#include <random>
bool brute(const Path& base,Path& built){
 int i=built.size();if(i==base.size())return true;
 for(int sub=0;sub<8;sub++){
    int v=base[i]|sub;bool ok=true;
    for(int j=0;j<i;j++){auto d=popcount(unsigned(v^built[j]));if(!d||((d==1)!=(j+1==i))){ok=false;break;}}
    if(ok){built.push_back(v);if(brute(base,built))return true;built.pop_back();}
 }
 return false;
}
int main(){
 mt19937 rng(291);int good=0,repairs=0,excluded=0;
 for(int t=0;t<220;t++){
    Path p{0};for(int i=0;i<5+t%8;i++){int d=rng()%5;p.push_back(p.back()^(d<3?0:1<<(d+0)));}
    // Translate the fiber at time zero so the fixed first vertex has local bits zero.
    Path built{p[0]};bool direct=brute(p,built);
    Fiber f(p,7,100000);assert((f.run()==1)==direct);
    bool any=direct;
    for(int i=0;!any&&i<p.size();i++){
        int before=p[i],anchor=i?p[i-1]:p[i+1];
        for(int d=-1;!any&&d<9;d++){
            if(d>=0&&d<3)continue;
            int v=anchor^(d<0?0:(1<<d));if(i+1<p.size()&&popcount(unsigned(v^p[i+1]))>1)continue;
            p[i]=v;Path temp{p[0]};any=brute(p,temp);
        }p[i]=before;
    }
    EditSearch edit{7,100000,int(p.size()-1)};Path used;bool hit=edit.visit(p,1,used);
    assert(hit==any);good+=direct;repairs+=!direct&&hit;excluded+=!hit;
 }
 cout<<"matched 220 direct "<<good<<" one_edit_only "<<repairs<<" no_lift_even_after_edit "<<excluded<<endl;
}
