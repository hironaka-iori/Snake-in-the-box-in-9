#define main q9_unused_main
#include "search_q9_short_route_join.cpp"
#undef main
int main(){
    string row;while(getline(cin,row)){
        istringstream in(row);int k,l,r;in>>k>>l>>r;Path a(k),g(k-1);for(int&v:a)in>>v;for(int&v:g)in>>v;
        Join s;bool ok=s.run(a,g,l,r,200000,1000000);cout<<ok<<" "<<s.limited;
        for(int v:s.witness)cout<<" "<<v;cout<<endl;
    }
}
