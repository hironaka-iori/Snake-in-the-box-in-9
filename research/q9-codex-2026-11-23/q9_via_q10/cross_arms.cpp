#define main original_hinge_main
#include "hinge.cpp"
#undef main
struct Trie{
    struct Node{array<int,9> links{};bool end=false;};vector<Node> nodes{1};
    void add(const string& word){int at=0;for(char c:word){
        int x=c-'A',child=nodes[at].links[x];if(!child){nodes[at].links[x]=child=nodes.size();nodes.emplace_back();}at=child;}nodes[at].end=true;}
};
struct Matching{
    const Trie& right;array<bool,512> ban{};array<int,9> mapping;uint64_t visits=0;string word;
    Matching(const Trie& rhs,const string& left):right(rhs){mapping.fill(-1);Path p=vertices(left);assert(valid(p));for(size_t i=1;i<p.size();i++){int x=p[i];ban[x]=true;for(int b=1;b<512;b*=2)ban[x^b]=true;}}
    bool search(int at,int v,int used){
        visits++;if(right.nodes[at].end)return true;
        for(int d=0;d<9;d++){int nxt=right.nodes[at].links[d];if(!nxt)continue;
            int saved=mapping[d];int opts=saved<0?511^used:1<<saved;
            for(int m=opts;m;m&=m-1){
                int b=m&-m,x=v^b;if(ban[x])continue;
                int dest=countr_zero(unsigned(b));mapping[d]=dest;word.push_back('A'+dest);
                if(search(nxt,x,used|b))return true;
                word.pop_back();mapping[d]=saved;
            }
        }return false;
    }
};
int main(int argc,char**argv){
    if(argc!=5)return 2;ifstream a(argv[1]),b(argv[2]);set<string> lhs,rhs;string w;int mode=stoi(argv[3]);mt19937 rng(stoul(argv[4]));
    while(a>>w)lhs.insert(w);while(b>>w)rhs.insert(w);assert(!lhs.empty()&&!rhs.empty());
    Trie trie;for(auto& word:rhs){assert(valid(vertices(word))&&word==canonical(word));trie.add(word);}
    vector<string> left(lhs.begin(),lhs.end());shuffle(left.begin(),left.end(),rng);
    uint64_t total=0,hits=0;int i=0;
    for(auto& l:left){
        Matching m(trie,l);bool hit=m.search(0,0,0);total+=m.visits;i++;
        if(hit){hits++;string result=l;reverse(result.begin(),result.end());result+=m.word;
            Path p=vertices(result);assert(valid(p));assert(rhs.contains(canonical(m.word)));
            if(hits<6||!mode){cout<<"FOUND "<<i<<" "<<p.size()-1<<" "<<l<<" "<<canonical(m.word);for(int x:p)cout<<" "<<x;cout<<endl;}
            if(!mode)return 0;
        }
        if(i%300==0)cout<<"AT "<<i<<" "<<left.size()<<" "<<rhs.size()<<" "<<total<<" "<<hits<<endl;
    }
    cout<<"DONE "<<i<<" "<<rhs.size()<<" "<<total<<" "<<hits<<endl;
}
