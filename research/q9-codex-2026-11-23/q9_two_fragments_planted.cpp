#define Q9_FRAGMENT_LIBRARY
#include "q9_two_fragments.cpp"
int main(int argc,char**argv){
    if(argc!=4)return 2;
    ifstream input(argv[1]);string word;input>>word;
    vector<int> path{0};for(char d:word)path.push_back(path.back()^(1<<(d-'0')));
    if(path.size()!=192)throw runtime_error("expected 191-edge control");
    vector<int> a(path.begin()+5,path.begin()+90),b(path.begin()+105,path.end()-6);
    const int offset=341;
    for(int& x:b){
        if(((x>>1)^(x>>6))&1)x^=(1<<1)|(1<<6);
        x^=offset;
    }
    int collisions=0,contacts=0;
    for(int x:a)for(int y:b){collisions+=(x==y);contacts+=JoinSearch::adjacent(x,y);}
    cout<<"PLANTED "<<a.size()<<" "<<b.size()<<" "<<collisions<<" "<<contacts<<endl;
    if(!collisions&&contacts<=1)throw runtime_error("control failed to break initial placement");
    vector<int> fragments=a;fragments.push_back(0);fragments.insert(fragments.end(),b.begin(),b.end());
    JoinSearch search;search.extension.goal=191;search.translate=true;search.swapAxes=stoi(argv[2]);
    bool found=search.run(fragments,0,0,int(a.size())-1,1);
    cout<<"RESULT "<<found<<" "<<search.shifts<<" "<<search.viable<<endl;
    return found!=bool(stoi(argv[3]));
}
