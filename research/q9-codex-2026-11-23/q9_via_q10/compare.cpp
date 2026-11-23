#define TRANSLATION_LIBRARY
#include "translations.cpp"
int main(int argc,char**argv){
    if(argc!=2)return 2;ifstream f(argv[1]);string line;vector<Path> words;
    while(getline(f,line)){istringstream s(line);int dim,v,old;s>>dim;if(dim!=10)continue;s>>old;Path w;
        while(s>>v){w.push_back(countr_zero(unsigned(old^v)));old=v;}words.push_back(w);}
    mt19937 rng(47259);int yes=0,no=0,unknown=0;
    for(int t=0;t<1000;t++){auto& w=words[rng()%words.size()];int n=10+rng()%183,st=rng()%(w.size()-n+1);
        int mask=1023^(1<<(rng()%10));if(t%5==0)mask&=~(1<<(rng()%10));
        Run r(w,st,n,mask,25000);int a=r.solve();
        CSP m(r.blocks,12000);int b=m.solve();
        if(a<0||b<0){unknown++;continue;}
        assert(a==b);
        if(b){yes++;assert(m.answer.size()==n+1);for(int j=0;j<n;j++){
            int axis=w[st+j];if(mask>>axis&1)assert((m.answer[j]^m.answer[j+1])==(1<<popcount(unsigned(mask&((1<<axis)-1)))));}}
        else no++;
    }cout<<"completed yes "<<yes<<" no "<<no<<" skipped_due_to_limit "<<unknown<<endl;
}
