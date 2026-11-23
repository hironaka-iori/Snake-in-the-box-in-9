// Reuse the single-end motif index and its independent path checker.
#define main single_tip_entry
#include "search.cpp"
#undef main
Seq tail[2];
int initial;
void grow(int size,int left,int right){
    if(local>=rootlimit)return;
    local++;calls++;best=max(best,size);
    if(size>=191){
        if(size==191)records++;
        Seq whole(tail[0].rbegin(),tail[0].rend());
        whole.insert(whole.end(),tail[1].begin()+initial,tail[1].end());
        if(!independent_check(whole))abort();
        auto shape=canonical(whole);
        if(size>191){cout<<"FOUND "<<size<<" "<<shape<<endl;exit(0);}
        if(!parents.contains(shape) && discovered.insert(shape).second && discovered.size()<=3)
            cout<<"NEW191 "<<shape<<"\n";
    }
    int side=(size-initial)%2;
    auto& q=tail[side];int tip=side?right:left;
    unsigned choices=511;
    if(size<free_from){
        array<int,9> rank;int next;auto found=masks.find(context(q,q.size(),rank,next));
        if(found==masks.end())return;
        choices=0;
        for(int d=0;d<9;d++)if(found->second&(1u<<(rank[d]<0?next:rank[d])))choices|=1u<<d;
    }
    int start=rng()%9;
    for(int j=0;j<9;j++){
        int d=(j+start)%9,y=tip^(1<<d);
        if(!(choices&(1u<<d))||block[y]!=1)continue;
        mark(y,1);q.push_back(d);grow(size+1,side?left:y,side?y:right);q.pop_back();mark(y,-1);
        if(local>=rootlimit)return;
    }
}
int main(int argc,char** argv){
    if(argc!=8)return 2;
    k=stoi(argv[2]);initial=stoi(argv[3]);int offset=stoi(argv[4]);free_from=stoi(argv[5]);
    rootlimit=stoll(argv[6]);rng.seed(stoull(argv[7]));
    if(k<1||k>16||initial<k||initial+offset>191||offset<0||free_from>192)return 2;
    ifstream f(argv[1]);string raw;set<string> roots;long long words=0;
    while(f>>raw){
        Seq q;for(char c:raw){if(c<'0'||c>'8')return 3;q.push_back(c-'0');}if(q.size()!=191)return 3;
        if(independent_check(q))parents.insert(canonical(q));
        words++;
        for(int side=0;side<2;side++,reverse(q.begin(),q.end())){
            Seq mid(q.begin()+offset,q.begin()+offset+initial);
            if(independent_check(mid))roots.insert(form(mid));
            for(int i=k;i<191;i++){
                array<int,9> rank;int next;auto key=context(q,i,rank,next);int r=rank[q[i]];
                masks[key]|=1u<<(r<0?next:r);
            }
        }
    }
    if(roots.empty())return 3;
    vector<string> ordered(roots.begin(),roots.end());shuffle(ordered.begin(),ordered.end(),rng);
    for(auto& w:ordered){
        tail[1].clear();block.fill(0);int x=0;mark(x,1);
        for(char c:w){int d=c-'0';tail[1].push_back(d);x^=1<<d;mark(x,1);}
        tail[0]=Seq(tail[1].rbegin(),tail[1].rend());
        local=0;grow(initial,0,x);roots_done++;truncated+=(local>=rootlimit);
    }
    cout<<"source_words "<<words<<" parents "<<parents.size()<<" contexts "<<masks.size()<<" roots "<<roots_done<<" truncated "<<truncated
        <<" nodes "<<calls<<" best_edges "<<best<<" visits191 "<<records<<" new191classes "<<discovered.size()<<endl;
}
