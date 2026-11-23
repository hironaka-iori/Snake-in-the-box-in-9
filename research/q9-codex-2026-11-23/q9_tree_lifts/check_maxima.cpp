#define Q9_TREE_LIBRARY
#include "tree.cpp"
int main(int argc,char** argv){
    if(argc<3)return 2;
    Edges base{};base[0]={0,1};base[1]={1,2};grow(base,3);
    ifstream input(argv[1]);vector<string> words;string w;
    while(input>>w)words.push_back(w);
    set<int> covered;
    for(int i=2;i<argc;i++){
        ifstream log(argv[i]);string tag;
        int row,n,nt,cap,idx,any,least,li,deep,unk;
        while(log>>tag>>row>>n>>nt>>cap>>idx>>any>>least>>li>>deep>>unk){
            assert(tag=="ROW" && covered.insert(row).second && n==words.at(row).size()+1);
            int x=0;set<int> even{0};
            for(char c:words[row]){x^=trees.at(idx).masks[c-'0'];even.insert(x);}
            assert(even.size()==n);
            int private_count=0;
            for(int y=0;y<512;y++)if(popcount(unsigned(y))%2){
                int count=0;for(int b=0;b<9;b++)count+=even.count(y^(1<<b));
                private_count+=count==2;
            }
            assert(private_count==cap);
        }
    }
    assert(covered.size()==words.size());cout<<"verified maxima witnesses "<<covered.size()<<endl;
}
